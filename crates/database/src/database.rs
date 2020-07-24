//! The central database of sml-analyzer

use super::*;
use crate::arena::Arena;
use std::cell::Cell;
use std::collections::HashMap;

use sml_frontend::ast;
use sml_frontend::parser::precedence::{self, Fixity, Precedence, Query};
use sml_util::diagnostics::Diagnostic;

pub struct Database<'ar> {
    // This vector contains all types defined throughout the program,
    // regardless of scope. [`Namespace`] structs are required to determine
    // which types are actually in scope
    pub types: Vec<Spanned<TypeStructure<'ar>>>,
    // And likewise for all values/bindings defined throughout the program
    values: Vec<Spanned<ValueStructure<'ar>>>,

    // Index into `namespaces`, representing the current scope
    current: usize,
    // An append-only list of [`Namespace`] structs, but this is a not stack.
    // Namespaces should only be pushed onto the end, and never deleted or re-ordered
    namespaces: Vec<Namespace>,

    // Essentially tracks the current declaration depth. This allows us to perform
    // rapid level-based type generalization
    tyvar_rank: usize,

    // stacks for alpha-renaming of explicity named type variables [x: 'a]
    tyvars: Vec<(Symbol, &'ar TypeVar<'ar>)>,

    // Generate dummy variable names, mostly for error handling
    gensym: Cell<usize>,

    // Arena for type allocation
    pub arena: &'ar Arena<'ar>,

    // Append-only vector of warnings/errors we generate
    pub diags: Vec<Diagnostic>,
}

/// An environment scope, that can hold a collection of type, expr, and infix bindings
///
/// This typically corresponds to a source-level scope (e.g. function, let bindings)
#[derive(Default, Debug)]
pub struct Namespace {
    parent: Option<usize>,
    types: HashMap<Symbol, TypeId>,
    values: HashMap<Symbol, ExprId>,
    infix: HashMap<Symbol, Fixity>,

    span: Span,
}

/// Identifier status for the Value Environment, as defined in the Defn.
#[derive(Copy, Clone, Debug)]
pub enum IdStatus {
    Exn(Constructor),
    Con(Constructor),
    Var,
}

/// Essentially a minimized Value Environment (VE) containing only datatype
/// constructors, and without the indirection of going from names->id->def
#[derive(Clone)]
pub struct Cons<'ar> {
    name: Symbol,
    span: Span,
    scheme: Scheme<'ar>,
}

/// [`TypeStructure`], a TyStr from the Defn. This is a component of the
/// Type Environment, TE
#[derive(Clone)]
pub enum TypeStructure<'ar> {
    /// TyStr (t, VE), a datatype
    Datatype(Tycon, Vec<Cons<'ar>>),
    /// TyStr (_, VE), a definition. Rather than include a whole VE hashmap,
    /// we can include just a single entry
    Scheme(Scheme<'ar>),
    /// TyStr (t, {}), a name
    Tycon(Tycon),
}

impl<'ar> TypeStructure<'ar> {
    pub fn arity(&self) -> usize {
        match self {
            TypeStructure::Tycon(con) | TypeStructure::Datatype(con, _) => con.arity,
            TypeStructure::Scheme(s) => s.arity(),
        }
    }

    pub fn apply(&self, arena: &'ar Arena<'ar>, args: Vec<&'ar Type<'ar>>) -> &'ar Type<'ar> {
        match self {
            TypeStructure::Tycon(con) | TypeStructure::Datatype(con, _) => {
                arena.alloc(Type::Con(*con, args))
            }
            TypeStructure::Scheme(s) => s.apply(arena, args),
        }
    }
}

pub struct ValueStructure<'ar> {
    scheme: Scheme<'ar>,
    status: IdStatus,
}

impl Namespace {
    pub fn with_parent(id: usize) -> Namespace {
        Namespace {
            parent: Some(id),
            types: HashMap::with_capacity(32),
            values: HashMap::with_capacity(64),
            infix: HashMap::with_capacity(16),
            span: Span::zero(),
        }
    }
}

impl<'ar> Database<'ar> {
    pub fn new(arena: &'ar Arena<'ar>) -> Database<'ar> {
        let mut ctx = Database {
            tyvars: Vec::default(),
            namespaces: Vec::default(),
            current: 0,
            tyvar_rank: 0,
            gensym: Cell::new(0),
            types: Vec::default(),
            values: Vec::default(),
            diags: Vec::default(),
            arena,
        };
        ctx.namespaces.push(Namespace::default());
        // builtin::populate_Database(&mut ctx);
        // ctx.elab_decl_fixity(&ast::Fixity::Infixr, 4, constructors::C_CONS.name);
        ctx
    }
    /// Keep track of the type variable stack, while executing the combinator
    /// function `f` on `self`. Any stack growth is popped off after `f`
    /// returns.
    fn with_tyvars<T, F: FnMut(&mut Database<'ar>) -> T>(&mut self, mut f: F) -> T {
        let n = self.tyvars.len();
        let r = f(self);
        while self.tyvars.len() != n {
            self.tyvars.pop();
        }
        r
    }

    /// Handle namespacing. The method creates a new child namespace, enters it
    /// and then calls `f`. After `f` has returned, the current scope is
    /// returned to it's previous value
    fn with_scope<T, F: FnOnce(&mut Database<'ar>) -> T>(&mut self, f: F) -> T {
        let prev = self.current;
        let next = self.namespaces.len();
        self.namespaces.push(Namespace::with_parent(prev));
        self.current = next;
        let r = f(self);

        self.current = prev;
        r
    }

    /// Globally define a type
    pub(crate) fn define_type(
        &mut self,
        sym: Symbol,
        tystr: TypeStructure<'ar>,
        span: Span,
    ) -> TypeId {
        let id = TypeId(self.types.len() as u32);
        self.types.push(Spanned::new(tystr, span));
        self.namespaces[self.current].types.insert(sym, id);
        id
    }

    /// Globally define a value
    pub(crate) fn define_value(
        &mut self,
        sym: Symbol,
        scheme: Scheme<'ar>,
        status: IdStatus,
        span: Span,
    ) -> ExprId {
        let id = ExprId(self.values.len() as u32);
        self.values
            .push(Spanned::new(ValueStructure { scheme, status }, span));
        self.namespaces[self.current].values.insert(sym, id);
        id
    }

    /// Unbind a value, replacing it's currently defined scheme with
    /// Scheme::Mono('a), where 'a is some fresh type variable
    ///
    /// # Panics
    ///
    /// This will panic if `sym` is not defined in the current namespace
    /// tree
    fn unbind_value(&mut self, sym: Symbol) {
        let id = self.namespaces[self.current]
            .values
            .get(&sym)
            .expect("error: redefine_value");
        let s = Scheme::Mono(self.fresh_tyvar());

        std::mem::replace(&mut self.values[id.0 as usize].data.scheme, s);
    }

    /// Starting from the current [`Namespace`], search for a bound name.
    /// If it's not found, then recursively search parent namespaces
    fn lookup_infix(&self, s: &Symbol) -> Option<Fixity> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.infix.get(s) {
                Some(idx) => return Some(*idx),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
    }

    /// Return the index of a symbol into the global type definition vector
    fn lookup_type_id(&self, sym: &Symbol) -> Option<TypeId> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.types.get(sym) {
                Some(idx) => return Some(*idx),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
    }

    fn lookup_type(&self, sym: &Symbol) -> Option<&TypeStructure<'ar>> {
        Some(&self.types[self.lookup_type_id(sym)?.0 as usize])
    }

    fn lookup_value(&self, sym: &Symbol) -> Option<&Spanned<ValueStructure<'ar>>> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.values.get(sym) {
                Some(idx) => return self.values.get(idx.0 as usize),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
    }

    fn lookup_tyvar(&mut self, s: &Symbol, allow_unbound: bool) -> Option<&'ar TypeVar<'ar>> {
        for (sym, tv) in self.tyvars.iter().rev() {
            if sym == s {
                return Some(tv);
            }
        }
        if allow_unbound {
            let v = self.arena.fresh_type_var(self.tyvar_rank);
            self.tyvars.push((*s, v));
            Some(v)
        } else {
            None
        }
    }

    fn fresh_tyvar(&self) -> &'ar Type<'ar> {
        self.arena.fresh_var(self.tyvar_rank)
    }

    fn fresh_var(&self) -> Symbol {
        let n = self.gensym.get();
        let s = Symbol::Gensym(n as u32);
        self.gensym.set(n + 1);
        s
    }

    fn const_ty(&self, c: &ast::Const) -> &'ar Type<'ar> {
        match c {
            ast::Const::Char(_) => self.arena.char(),
            ast::Const::Int(_) => self.arena.int(),
            ast::Const::String(_) => self.arena.string(),
            ast::Const::Unit => self.arena.unit(),
        }
    }

    /// Generic function to elaborate an ast::Row<T> into a core::Row<S>
    /// where T might be ast::Type and S is core::Type, for instance
    fn elab_row<T, S, F: FnMut(&mut Database<'ar>, &T) -> S>(
        &mut self,
        mut f: F,
        row: &ast::Row<T>,
    ) -> Row<S> {
        Row {
            label: row.label,
            span: row.span,
            data: f(self, &row.data),
        }
    }
}

impl<'ar> Database<'ar> {
    pub fn elaborate_type(&mut self, ty: &ast::Type, allow_unbound: bool) -> &'ar Type<'ar> {
        use ast::TypeKind::*;
        match &ty.data {
            Var(s) => match self.lookup_tyvar(s, allow_unbound) {
                Some(tv) => self.arena.alloc(Type::Var(tv)),
                None => {
                    self.diags.push(Diagnostic::error(
                        ty.span,
                        format!("unbound type variable {:?}", s),
                    ));
                    self.fresh_tyvar()
                }
            },
            Con(s, args) => {
                let args = args
                    .iter()
                    .map(|ty| self.elaborate_type(&ty, allow_unbound))
                    .collect::<Vec<_>>();

                let con = match self.lookup_type(s) {
                    Some(t) => t.clone(),
                    None => {
                        self.diags.push(Diagnostic::error(
                            ty.span,
                            format!("unbound type variable {:?}", s),
                        ));

                        TypeStructure::Tycon(Tycon {
                            name: self.fresh_var(),
                            arity: args.len(),
                        })
                    }
                };

                if con.arity() != args.len() {
                    self.diags.push(
                        Diagnostic::error(
                            ty.span,
                            format!(
                                "type constructor requires {} arguments, but {} are supplied",
                                con.arity(),
                                args.len()
                            ),
                        )
                        .message(ty.span, format!("in type {:?}", ty)),
                    );
                }
                con.apply(&self.arena, args)
            }
            Record(rows) => self.arena.alloc(Type::Record(SortedRecord::new(
                rows.into_iter()
                    .map(|row| self.elab_row(|f, r| f.elaborate_type(r, allow_unbound), row))
                    .collect::<Vec<Row<_>>>(),
            ))),
        }
    }
}

impl<'ar> Database<'ar> {
    fn elab_decl_fixity(&mut self, fixity: &ast::Fixity, bp: u8, sym: Symbol) {
        let fix = match fixity {
            ast::Fixity::Infix => Fixity::Infix(bp, bp + 1),
            ast::Fixity::Infixr => Fixity::Infix(bp + 1, bp),
            ast::Fixity::Nonfix => Fixity::Nonfix,
        };
        self.namespaces[self.current].infix.insert(sym, fix);
    }

    fn elab_decl_type(&mut self, tbs: &[ast::Typebind]) {
        for typebind in tbs {
            let scheme = if !typebind.tyvars.is_empty() {
                self.with_tyvars(|ctx| {
                    for s in typebind.tyvars.iter() {
                        let v = ctx.arena.fresh_type_var(ctx.tyvar_rank);
                        ctx.tyvars.push((*s, v));
                    }
                    let ty = ctx.elaborate_type(&typebind.ty, false);
                    let s = match typebind.tyvars.len() {
                        0 => Scheme::Mono(ty),
                        _ => Scheme::Poly(
                            typebind
                                .tyvars
                                .iter()
                                .map(|tv| ctx.lookup_tyvar(tv, false).unwrap().id)
                                .collect(),
                            ty,
                        ),
                    };

                    s
                })
            } else {
                Scheme::Mono(self.elaborate_type(&typebind.ty, false))
            };
            self.define_type(
                typebind.tycon,
                TypeStructure::Scheme(scheme),
                typebind.ty.span,
            );
        }
    }

    fn elab_decl_conbind(&mut self, db: &ast::Datatype) {
        let tycon = Tycon::new(db.tycon, db.tyvars.len());

        // This is safe to unwrap, because we already bound it.
        let type_id = self.lookup_type_id(&db.tycon).unwrap();

        // Should be safe to unwrap here as well, since the caller has bound db.tyvars
        let tyvars: Vec<&'ar TypeVar<'ar>> = db
            .tyvars
            .iter()
            .map(|sym| self.lookup_tyvar(sym, false).unwrap())
            .collect();

        let mut constructors = Vec::new();
        for (tag, con) in db.constructors.iter().enumerate() {
            if self.lookup_value(&con.label).is_some() {
                self.diags.push(Diagnostic::warn(
                    con.span,
                    format!("rebinding of data constructor {:?}", con.label),
                ));
                return;
            }

            let cons = Constructor {
                name: con.label,
                type_id,
                tag: tag as u8,
                arity: con.data.is_some() as u8,
                type_arity: db.constructors.len() as u8,
            };

            let res = self.arena.alloc(Type::Con(
                tycon,
                tyvars
                    .iter()
                    .map(|v| &*self.arena.alloc(Type::Var(v)))
                    .collect(),
            ));

            let ty = match &con.data {
                Some(ty) => {
                    let dom = self.elaborate_type(ty, false);
                    constructors.push((cons, Some(dom)));
                    self.arena.arrow(dom, res)
                }
                None => {
                    constructors.push((cons, None));
                    res
                }
            };

            // calling `generalize` here will actually introduce some bugs, since
            // any type vars could've already been placed in the VE, thereby
            // preventing later constructors containing the same tyvars from
            // being properly generalized
            let s = match tyvars.len() {
                0 => Scheme::Mono(ty),
                _ => Scheme::Poly(tyvars.iter().map(|tv| tv.id).collect(), ty),
            };
            self.define_value(con.label, s, IdStatus::Con(cons), con.span);
        }
        let dt = Datatype {
            tycon,
            tyvars: tyvars.iter().map(|tv| tv.id).collect(),
            constructors,
        };
    }

    fn elab_decl_datatype(&mut self, dbs: &[ast::Datatype]) {
        // Add all of the type constructors to the environment first, so that
        // we can construct data constructor arguments (e.g. recursive/mutually
        // recursive datatypes)
        for db in dbs {
            let tycon = Tycon::new(db.tycon, db.tyvars.len());
            self.define_type(db.tycon, TypeStructure::Tycon(tycon), db.span);
        }
        for db in dbs {
            self.with_tyvars(|ctx| {
                for s in &db.tyvars {
                    let v = ctx.arena.fresh_type_var(ctx.tyvar_rank);
                    ctx.tyvars.push((*s, v));
                }
                ctx.elab_decl_conbind(db)
            });
        }
    }

    fn elab_decl_exception(&mut self, exns: &[ast::Variant]) {
        for exn in exns {
            let con = Constructor {
                name: exn.label,
                type_id: TypeId(8),
                tag: 0,
                arity: exn.data.is_some() as u8,
                type_arity: exns.len() as u8,
            };

            match &exn.data {
                Some(ty) => {
                    let ty = self.elaborate_type(ty, false);
                    self.define_value(
                        exn.label,
                        Scheme::Mono(self.arena.arrow(ty, self.arena.exn())),
                        IdStatus::Exn(con),
                        exn.span,
                    );
                }
                None => {
                    self.define_value(
                        exn.label,
                        Scheme::Mono(self.arena.exn()),
                        IdStatus::Exn(con),
                        exn.span,
                    );
                }
            }
        }
    }

    pub fn dump(&self) {
        for Spanned { span, data } in &self.types {
            info!("type defined @ {:?}", span)
        }
    }

    pub fn elaborate_decl(&mut self, decl: &ast::Decl) {
        // info!("elab {:?}")
        match &decl.data {
            ast::DeclKind::Datatype(dbs) => self.elab_decl_datatype(dbs),
            ast::DeclKind::Type(tbs) => self.elab_decl_type(tbs),
            // ast::DeclKind::Function(tyvars, fbs) => self.elab_decl_fun(tyvars, fbs),
            // ast::DeclKind::Value(tyvars, pat, expr) => self.elab_decl_val(tyvars, pat, expr),
            ast::DeclKind::Exception(exns) => self.elab_decl_exception(exns),
            // ast::DeclKind::Fixity(fixity, bp, sym) => self.elab_decl_fixity(fixity, *bp, *sym),
            // ast::DeclKind::Local(decls, body) => self.elab_decl_local(decls, body),
            ast::DeclKind::Seq(decls) => {
                for d in decls {
                    self.elaborate_decl(d);
                }
            }
            _ => {}
        }
    }
}

impl<'ar> Query<ast::Pat> for &Database<'ar> {
    fn fixity(&self, t: &ast::Pat) -> Fixity {
        match &t.data {
            ast::PatKind::Variable(s) => self.lookup_infix(s).unwrap_or(Fixity::Nonfix),
            _ => Fixity::Nonfix,
        }
    }

    fn infix(&self, a: ast::Pat, b: ast::Pat, c: ast::Pat) -> Result<ast::Pat, precedence::Error> {
        // We know `a` must be a symbol, since it has a Fixity!
        match a.data {
            ast::PatKind::Variable(s) => {
                let sp_bc = b.span + c.span;
                let sp = a.span + sp_bc;
                let rec = ast::Pat::new(ast::make_record_pat(vec![b, c]), sp_bc);
                Ok(ast::Pat::new(ast::PatKind::App(s, Box::new(rec)), sp))
            }
            _ => Err(precedence::Error::InvalidOperator),
        }
    }

    fn apply(&self, a: ast::Pat, b: ast::Pat) -> Result<ast::Pat, precedence::Error> {
        match a.data {
            ast::PatKind::Variable(s) => {
                let sp = a.span + b.span;
                Ok(ast::Pat::new(ast::PatKind::App(s, Box::new(b)), sp))
            }
            _ => Err(precedence::Error::InvalidOperator),
        }
    }
}

impl<'ar> Query<ast::Expr> for &Database<'ar> {
    fn fixity(&self, t: &ast::Expr) -> Fixity {
        match &t.data {
            ast::ExprKind::Var(s) => self.lookup_infix(s).unwrap_or(Fixity::Nonfix),
            _ => Fixity::Nonfix,
        }
    }

    fn infix(
        &self,
        a: ast::Expr,
        b: ast::Expr,
        c: ast::Expr,
    ) -> Result<ast::Expr, precedence::Error> {
        let sp_bc = b.span + c.span;
        let sp = a.span + sp_bc;
        let rec = ast::Expr::new(ast::make_record(vec![b, c]), sp_bc);
        Ok(ast::Expr::new(
            ast::ExprKind::App(Box::new(a), Box::new(rec)),
            sp,
        ))
    }
    fn apply(&self, a: ast::Expr, b: ast::Expr) -> Result<ast::Expr, precedence::Error> {
        let sp = a.span + b.span;
        Ok(ast::Expr::new(
            ast::ExprKind::App(Box::new(a), Box::new(b)),
            sp,
        ))
    }
}

impl<'ar> Database<'ar> {
    pub(crate) fn expr_precedence(
        &self,
        exprs: Vec<ast::Expr>,
    ) -> Result<ast::Expr, precedence::Error> {
        Precedence::run(self, exprs)
    }

    pub(crate) fn pat_precedence(
        &self,
        exprs: Vec<ast::Pat>,
    ) -> Result<ast::Pat, precedence::Error> {
        Precedence::run(self, exprs)
    }
}
