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

    local: bool,

    // Arena for type allocation
    pub arena: &'ar Arena<'ar>,

    pub bindings: Vec<(Span, &'ar Type<'ar>)>,

    // Append-only vector of warnings/errors we generate
    pub diags: Vec<Diagnostic>,

    pub unification_errors: Vec<CantUnify<'ar>>,
}

pub struct CantUnify<'ar> {
    pub ty1: &'ar Type<'ar>,
    pub ty2: &'ar Type<'ar>,
    pub sp1: Option<Span>,
    pub sp2: Option<Span>,
    pub message: String,
    pub reason: String,
    pub originating: Option<Span>,
}

impl<'ar> CantUnify<'ar> {
    pub fn new(ty1: &'ar Type<'ar>, ty2: &'ar Type<'ar>) -> CantUnify<'ar> {
        CantUnify {
            ty1,
            ty2,
            sp1: None,
            sp2: None,
            message: String::new(),
            reason: String::new(),
            originating: None,
        }
    }

    pub fn add_message<S: Into<String>>(mut self, s: S) -> Self {
        self.message = s.into();
        self
    }

    pub fn add_reason<S: Into<String>>(mut self, s: S) -> Self {
        self.reason = s.into();
        self
    }

    pub fn span(mut self, sp: Span) -> Self {
        self.originating = Some(sp);
        self
    }

    pub fn add_spans(mut self, s1: Span, s2: Span) -> Self {
        self.sp1 = Some(s1);
        self.sp2 = Some(s2);
        self
    }
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

#[derive(Clone)]
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

/// Iterator over the namespace hierarchy, proceeding towards the root namespace
pub struct NamespaceIter<'db, 'ar> {
    ctx: &'db Database<'ar>,
    ptr: Option<usize>,
}

impl<'db, 'ar> Iterator for NamespaceIter<'db, 'ar> {
    type Item = &'db Namespace;
    fn next(&mut self) -> Option<Self::Item> {
        let n = self.ptr?;
        let ns = &self.ctx.namespaces[n];
        self.ptr = ns.parent;
        Some(ns)
    }
}

/// A partially elaborated Vec<ast::FnBinding>
struct PartialFun<'s, 'ar> {
    name: Symbol,
    clauses: Vec<PartialFnBinding<'s, 'ar>>,
    /// The resulting type
    res_ty: &'ar Type<'ar>,
    /// The overall flattened type, where for each ty_i in args, we have
    /// ty_0 -> ty_1 -> ... ty_arity -> res_ty
    ty: &'ar Type<'ar>,
}

/// A partially elaborated ast::FnBinding
struct PartialFnBinding<'s, 'ar> {
    /// Function body
    expr: &'s ast::Expr,
    /// A list of variables bound in `pats`, and fresh type variables
    /// to be associated with those symbols
    bindings: Vec<(Spanned<Symbol>, &'ar Type<'ar>)>,
    span: Span,
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
            unification_errors: Vec::default(),
            local: false,
            bindings: Vec::default(),
            arena,
        };
        ctx.namespaces.push(Namespace::default());
        builtin::populate_context(&mut ctx);
        ctx.elab_decl_fixity(&ast::Fixity::Infixr, 4, builtin::constructors::C_CONS.name);
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

    /// Naively find the [`Namespace`] idx belonging to a [`Span`]
    fn get_ns_span(&self, loc: Location) -> usize {
        self.namespaces
            .iter()
            .enumerate()
            .filter(|(_, ns)| loc.line >= ns.span.start.line && loc.line < ns.span.end.line)
            .last()
            .map(|(idx, _)| idx)
            .unwrap_or_default()
    }

    pub fn in_scope_types(&self, loc: Location) -> Vec<(Symbol, Option<&'ar Type<'ar>>)> {
        let mut v = Vec::new();
        let iter = NamespaceIter {
            ctx: &self,
            ptr: Some(self.get_ns_span(loc)),
        };
        for ns in iter {
            for (sym, id) in &ns.types {
                if let Some(Spanned { span, data }) = self.types.get(id.0 as usize) {
                    let inst = match data {
                        TypeStructure::Tycon(_) => None,
                        TypeStructure::Scheme(s) => Some(self.instantiate(&s)),
                        TypeStructure::Datatype(_, cons) => None,
                    };
                    if loc.line >= span.start.line {
                        v.push((*sym, inst));
                    }
                }
            }
        }

        v
    }

    pub fn in_scope_values(&self, loc: Location) -> Vec<(Symbol, &'ar Type<'ar>)> {
        let mut v = Vec::new();
        let iter = NamespaceIter {
            ctx: &self,
            ptr: Some(self.get_ns_span(loc)),
        };
        for ns in iter {
            for (sym, id) in &ns.values {
                if let Some(Spanned { span, data }) = self.values.get(id.0 as usize) {
                    let inst = self.instantiate(&data.scheme);
                    if loc.line >= span.start.line {
                        v.push((*sym, inst));
                    }
                }
            }
        }

        v
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
        let ns = if self.local {
            self.namespaces[self.current].parent.unwrap_or(self.current)
        } else {
            self.current
        };
        self.namespaces[ns].types.insert(sym, id);
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
        let ns = if self.local {
            self.namespaces[self.current].parent.unwrap_or(self.current)
        } else {
            self.current
        };
        self.values
            .push(Spanned::new(ValueStructure { scheme, status }, span));
        self.namespaces[ns].values.insert(sym, id);
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
    /// Note that this can only be called once per type variable!
    fn bind<F>(&mut self, var: &'ar TypeVar<'ar>, ty: &'ar Type<'ar>, f: &F)
    where
        F: Fn() -> CantUnify<'ar>,
    {
        if let Type::Var(v2) = ty {
            // TODO: Ensure that testing on id alone is ok - I believe it should be
            if v2.id == var.id {
                return;
            }
        }
        if ty.occurs_check(var) {
            let err = f().add_reason("Cyclic type detected");
            self.unification_errors.push(err);
        }

        var.data.set(Some(ty));
    }

    pub fn unify<F>(&mut self, a: &'ar Type<'ar>, b: &'ar Type<'ar>, f: &F)
    where
        F: Fn(CantUnify<'ar>) -> CantUnify<'ar>,
    {
        match (a, b) {
            (Type::Var(a1), Type::Var(b1)) => match (a1.ty(), b1.ty()) {
                (Some(a), Some(b)) => self.unify(a, b, f),
                (Some(a), None) => self.unify(a, b, f),
                (None, Some(b)) => self.unify(a, b, f),
                (None, None) => self.bind(a1, b, &|| f(CantUnify::new(a, b))),
            },
            (Type::Var(a_var), b) => match a_var.ty() {
                Some(ty) => self.unify(ty, b, f),
                None => self.bind(a_var, b, &|| f(CantUnify::new(a, b))),
            },
            (a, Type::Var(b_var)) => match b_var.ty() {
                Some(ty) => self.unify(a, ty, f),
                None => self.bind(b_var, a, &|| f(CantUnify::new(a, b))),
            },
            (Type::Con(tc1, a_args), Type::Con(tc2, b_args)) => {
                if tc1 != tc2 {
                    let err = f(CantUnify::new(a, b)).add_reason("Type constructors differ");
                    self.unification_errors.push(err);
                } else if a_args.len() != b_args.len() {
                    let err = f(CantUnify::new(a, b))
                        .add_reason("Argument lengths to type constructors differ");
                    self.unification_errors.push(err);
                } else {
                    for (c, d) in a_args.into_iter().zip(b_args) {
                        self.unify(c, d, f);
                    }
                }
            }
            (Type::Record(r1), Type::Record(r2)) => {
                if r1.len() != r2.len() {
                    let err = f(CantUnify::new(a, b))
                        .add_reason("Record types have differing number of fields");
                    self.unification_errors.push(err);
                    return;
                }

                for (ra, rb) in r1.iter().zip(r2.iter()) {
                    if ra.label != rb.label {
                        let err = f(CantUnify::new(&ra.data, &rb.data))
                            .add_reason("Record types have identical fields with differing types")
                            .add_spans(ra.span, rb.span);
                        self.unification_errors.push(err);
                        return;
                    }
                    self.unify(&ra.data, &rb.data, f);
                }
            }
            (a, b) => {
                let err = f(CantUnify::new(a, b)).add_reason("Can't unify these types");
                self.unification_errors.push(err);
            }
        }
    }

    pub fn unify_list(&mut self, sp: Span, tys: &[&'ar Type<'ar>]) {
        let fst = &tys[0];
        for ty in tys {
            self.unify(ty, fst, &|c| {
                c.span(sp).add_message("List has items of differing types")
            });
        }
    }

    pub fn generalize(&self, ty: &'ar Type<'ar>) -> Scheme<'ar> {
        let ftv = ty.ftv_rank(self.tyvar_rank);

        match ftv.len() {
            0 => Scheme::Mono(ty),
            _ => Scheme::Poly(ftv, ty),
        }
    }

    pub fn instantiate(&self, scheme: &Scheme<'ar>) -> &'ar Type<'ar> {
        match scheme {
            Scheme::Mono(ty) => ty,
            Scheme::Poly(vars, ty) => {
                let map = vars.into_iter().map(|v| (*v, self.fresh_tyvar())).collect();
                ty.apply(&self.arena, &map)
            }
        }
    }

    pub fn check_type_names(&mut self, sp: Span, ty: &'ar Type<'ar>) {
        let mut names = Vec::new();
        ty.visit(|f| match f {
            Type::Con(tc, _) => names.push(*tc),
            _ => {}
        });

        for tycon in names {
            if self.lookup_type(&tycon.name).is_none() {
                self.diags.push(Diagnostic::error(
                    sp,
                    format!("type {:?} escapes inner scope!", tycon.name),
                ));
            }
        }
    }

    pub fn walk_type(&mut self, ty: &ast::Type, allow_unbound: bool) -> &'ar Type<'ar> {
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
                    .map(|ty| self.walk_type(&ty, allow_unbound))
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
                    .map(|row| self.elab_row(|f, r| f.walk_type(r, allow_unbound), row))
                    .collect::<Vec<Row<_>>>(),
            ))),
        }
    }
}

impl<'ar> Database<'ar> {
    pub fn walk_pat(
        &mut self,
        pat: &ast::Pat,
        bind: bool,
    ) -> (&'ar Type<'ar>, Vec<(Spanned<Symbol>, &'ar Type<'ar>)>) {
        let mut bindings = Vec::new();
        let ty = self.walk_pat_inner(pat, bind, &mut bindings);
        (ty, bindings)
    }

    pub(crate) fn walk_pat_inner(
        &mut self,
        pat: &ast::Pat,
        bind: bool,
        bindings: &mut Vec<(Spanned<Symbol>, &'ar Type<'ar>)>,
    ) -> &'ar Type<'ar> {
        use ast::PatKind::*;
        match &pat.data {
            App(con, p) => {
                let arg_ty = self.walk_pat_inner(p, bind, bindings);
                match self.lookup_value(con).cloned() {
                    Some(Spanned {
                        data:
                            ValueStructure {
                                scheme,
                                status: IdStatus::Con(_),
                            },
                        span,
                    }) => {
                        let inst = self.instantiate(&scheme);

                        let (arg, res) = match inst.de_arrow() {
                            Some((a, r)) => (a, r),
                            None => {
                                let (dom, rng) = (self.fresh_tyvar(), self.fresh_tyvar());
                                let arr = self.arena.arrow(dom, rng);
                                self.unify(inst, arr, &|c| {
                                    c.span(pat.span).add_message(
                                        "expected pattern contructor to take arguments",
                                    )
                                });
                                (dom, rng)
                            }
                        };
                        self.unify(arg, arg_ty, &|c| {
                            c.span(pat.span)
                                .add_spans(p.span, span)
                                .add_message("argument to constructor is the wrong type")
                        });
                        self.bindings.push((pat.span, res));
                        res
                    }
                    _ => {
                        self.diags.push(Diagnostic::error(
                            pat.span,
                            format!("Non-constructor {:?} applied to pattern", con),
                        ));
                        let ty = self.arena.fresh_var(self.tyvar_rank);
                        self.bindings.push((pat.span, ty));
                        ty
                    }
                }
            }
            Ascribe(p, ty) => {
                let ty1 = self.walk_pat_inner(p, bind, bindings);
                let ty2 = self.walk_type(ty, true);
                self.unify(ty1, ty2, &|c| {
                    c.span(pat.span)
                        .add_spans(p.span, ty.span)
                        .add_message("pattern type and ascribed type differ")
                });
                self.bindings.push((pat.span, ty2));
                ty2
            }
            Const(c) => self.const_ty(c),
            FlatApp(pats) => {
                let p = match self.pat_precedence(pats.clone()) {
                    Ok(p) => p,
                    Err(err) => {
                        match err {
                            precedence::Error::EndsInfix => self.diags.push(Diagnostic::error(
                                pat.span,
                                "application pattern ends with an infix operator",
                            )),
                            precedence::Error::InfixInPrefix => self.diags.push(Diagnostic::error(
                                pat.span,
                                "application pattern starts with an infix operator",
                            )),
                            precedence::Error::SamePrecedence => {
                                self.diags.push(Diagnostic::error(
                                    pat.span,
                                    "application pattern mixes operators of equal precedence",
                                ))
                            }
                            precedence::Error::InvalidOperator => {
                                self.diags.push(Diagnostic::error(
                                    pat.span,
                                    "application pattern doesn't contain infix operator",
                                ))
                            }
                        }

                        // attempt error recovery
                        ast::Pat::new(ast::PatKind::Wild, pat.span)
                    }
                };
                let ty = self.walk_pat_inner(&p, bind, bindings);
                self.bindings.push((pat.span, ty));
                ty
            }
            List(pats) => {
                let tys = pats
                    .into_iter()
                    .map(|p| self.walk_pat_inner(p, bind, bindings))
                    .collect::<Vec<_>>();

                self.unify_list(pat.span, &tys);
                let ty = self.arena.list(tys[0]);
                self.bindings.push((pat.span, ty));
                ty
            }
            Record(rows) => {
                let tys = rows
                    .iter()
                    .map(|p| Row {
                        label: p.label,
                        span: p.span,
                        data: self.walk_pat_inner(&p.data, bind, bindings),
                    })
                    .collect::<Vec<Row<_>>>();

                let ty = self.arena.alloc(Type::Record(SortedRecord::new(tys)));
                self.bindings.push((pat.span, ty));
                ty
            }
            Variable(sym) => match self.lookup_value(sym) {
                // Rule 35
                Some(Spanned {
                    span,
                    data:
                        ValueStructure {
                            scheme,
                            status: IdStatus::Exn(_),
                        },
                })
                | Some(Spanned {
                    span,
                    data:
                        ValueStructure {
                            scheme,
                            status: IdStatus::Con(_),
                        },
                }) => self.instantiate(scheme),
                _ => {
                    // Rule 34
                    // let tvar = self.arena.fresh_type_var(self.tyvar_rank);
                    let ty = self.fresh_tyvar();
                    if bind {
                        self.define_value(*sym, Scheme::Mono(ty), IdStatus::Var, pat.span);
                    }
                    bindings.push((Spanned::new(*sym, pat.span), ty));
                    self.bindings.push((pat.span, ty));
                    ty
                }
            },
            Wild => {
                let ty = self.fresh_tyvar();
                self.bindings.push((pat.span, ty));
                ty
            }
        }
    }
}

type Rule<'ar> = (&'ar Type<'ar>, &'ar Type<'ar>);
impl<'ar> Database<'ar> {
    fn elab_rule(&mut self, rule: &ast::Rule, bind: bool) -> Rule<'ar> {
        let (pat, _) = self.walk_pat(&rule.pat, bind);
        let expr = self.walk_expr(&rule.expr);
        (pat, expr)
    }

    pub fn elab_rules(
        &mut self,
        sp: Span,
        rules: &[ast::Rule],
    ) -> (Vec<Rule<'ar>>, &'ar Type<'ar>) {
        self.with_scope(|ctx| {
            let rules = rules
                .into_iter()
                .map(|r| ctx.elab_rule(r, true))
                .collect::<Vec<Rule>>();

            let mut rtys = rules
                .iter()
                .map(|(p, e)| ctx.arena.arrow(p, e))
                .collect::<Vec<_>>();

            ctx.unify_list(sp, &rtys);
            let fst = rtys.remove(0);
            (rules, fst)
        })
    }

    pub fn walk_expr(&mut self, expr: &ast::Expr) -> &'ar Type<'ar> {
        match &expr.data {
            ast::ExprKind::Andalso(e1, e2) => {
                let ty1 = self.walk_expr(e1);
                let ty2 = self.walk_expr(e2);
                self.unify(ty1, self.arena.bool(), &|c| {
                    c.span(e1.span)
                        .add_message("expected bool expression in `andalso`")
                });
                self.unify(ty2, self.arena.bool(), &|c| {
                    c.span(e2.span)
                        .add_message("expected bool expression in `andalso`")
                });
                self.bindings.push((expr.span, ty1));
                ty1
            }
            ast::ExprKind::App(e1, e2) => {
                let ty1 = self.walk_expr(e1);
                let ty2 = self.walk_expr(e2);

                let f = self.fresh_tyvar();
                self.unify(ty1, self.arena.arrow(ty2, f), &|c| {
                    c.span(e1.span)
                        .add_message("expected function in application")
                });
                self.bindings.push((expr.span, f));
                f
            }
            ast::ExprKind::Case(scrutinee, rules) => {
                let casee = self.walk_expr(scrutinee);

                let (_, ty) = self.elab_rules(expr.span, rules);

                let (arg, res) = match ty.de_arrow() {
                    Some((a, r)) => (a, r),
                    None => {
                        let (dom, rng) = (self.fresh_tyvar(), self.fresh_tyvar());
                        let arr = self.arena.arrow(dom, rng);
                        self.unify(ty, arr, &|c| {
                            c.span(expr.span).add_message("mistyped match rule")
                        });
                        (dom, rng)
                    }
                };

                self.unify(casee, arg, &|c| {
                    c.span(scrutinee.span)
                        .add_message("`case` expression and patterns don't have the same type")
                });
                self.bindings.push((expr.span, res));
                res
            }
            ast::ExprKind::Const(c) => {
                let ty = self.const_ty(c);
                self.bindings.push((expr.span, ty));
                ty
            }
            ast::ExprKind::Constraint(ex, ty) => {
                let ty1 = self.walk_expr(ex);
                let ty2 = self.walk_type(ty, false);
                self.unify(ty1, ty2, &|c| {
                    c.span(expr.span)
                        .add_message("expression type and type constraint differ")
                });
                self.bindings.push((expr.span, ty1));
                ty1
            }
            ast::ExprKind::FlatApp(exprs) => {
                let p = match self.expr_precedence(exprs.clone()) {
                    Ok(p) => p,
                    Err(err) => {
                        match err {
                            precedence::Error::EndsInfix => self.diags.push(Diagnostic::error(
                                expr.span,
                                "application expr ends with an infix operator",
                            )),
                            precedence::Error::InfixInPrefix => self.diags.push(Diagnostic::error(
                                expr.span,
                                "application expr starts with an infix operator",
                            )),
                            precedence::Error::SamePrecedence => {
                                self.diags.push(Diagnostic::error(
                                    expr.span,
                                    "application expr mixes operators of equal precedence",
                                ))
                            }
                            precedence::Error::InvalidOperator => {
                                self.diags.push(Diagnostic::error(
                                    expr.span,
                                    "application expr doesn't contain infix operator",
                                ))
                            }
                        }
                        // Return a dummy variable so that we can continue elaboration
                        ast::Expr::new(ast::ExprKind::Var(self.fresh_var()), Span::dummy())
                    }
                };
                let ty = self.walk_expr(&p);
                self.bindings.push((expr.span, ty));
                ty
            }
            ast::ExprKind::Fn(rules) => {
                let (_, ty) = self.elab_rules(expr.span, rules);
                self.bindings.push((expr.span, ty));
                ty
            }
            ast::ExprKind::Handle(ex, rules) => {
                let ex = self.walk_expr(ex);
                let (_, ty) = self.elab_rules(expr.span, rules);

                let (arg, res) = match ty.de_arrow() {
                    Some((a, r)) => (a, r),
                    None => {
                        let (dom, rng) = (self.fresh_tyvar(), self.fresh_tyvar());
                        let arr = self.arena.arrow(dom, rng);
                        self.unify(ty, arr, &|c| {
                            c.span(expr.span).add_message("mistyped match rule")
                        });
                        (dom, rng)
                    }
                };

                self.unify(ex, res, &|c| {
                    c.span(expr.span)
                        .add_message("mismatch in return type of `handle`")
                });
                self.unify(arg, self.arena.exn(), &|c| {
                    c.span(expr.span)
                        .add_message("non-exception in `handle` rule")
                });
                self.bindings.push((expr.span, res));
                res
            }
            ast::ExprKind::If(e1, e2, e3) => {
                let ty1 = self.walk_expr(e1);
                let ty2 = self.walk_expr(e2);
                let ty3 = self.walk_expr(e3);
                self.unify(ty1, self.arena.bool(), &|c| {
                    c.span(e1.span)
                        .add_message("expected bool expression in `if`")
                });
                self.unify(ty2, ty2, &|c| {
                    c.span(expr.span)
                        .add_spans(e2.span, e3.span)
                        .add_message("`if` arms don't have the same type")
                });
                self.bindings.push((expr.span, ty2));
                ty2
            }
            ast::ExprKind::Let(decls, body) => {
                let ty = self.with_scope(|ctx| {
                    for decl in decls {
                        ctx.walk_decl(decl);
                    }
                    ctx.walk_expr(body)
                });
                self.check_type_names(body.span, ty);
                self.bindings.push((expr.span, ty));
                ty
            }
            ast::ExprKind::List(exprs) => {
                let exprs = exprs
                    .into_iter()
                    .map(|ex| self.walk_expr(ex))
                    .collect::<Vec<_>>();
                self.unify_list(expr.span, &exprs);
                // Pick the first type, since that was what everything was unified against
                let ty = self.arena.list(exprs[0]);
                self.bindings.push((expr.span, ty));
                ty
            }
            ast::ExprKind::Orelse(e1, e2) => {
                let ty1 = self.walk_expr(e1);
                let ty2 = self.walk_expr(e2);
                self.unify(ty1, self.arena.bool(), &|c| {
                    c.span(e1.span)
                        .add_message("expected bool expression in `orelse`")
                });
                self.unify(ty2, self.arena.bool(), &|c| {
                    c.span(e2.span)
                        .add_message("expected bool expression in `orelse`")
                });
                self.bindings.push((expr.span, ty1));
                ty1
            }
            ast::ExprKind::Primitive(prim) => {
                let name = prim.sym;
                let ty = self.walk_type(&prim.ty, false);
                self.bindings.push((expr.span, ty));
                ty
            }
            ast::ExprKind::Raise(expr) => {
                let ty = self.fresh_tyvar();
                let ex = self.walk_expr(expr);
                self.unify(ex, self.arena.exn(), &|c| {
                    c.span(expr.span)
                        .add_message("can't `raise` a non-exception type")
                });
                self.bindings.push((expr.span, ty));
                ty
            }
            ast::ExprKind::Record(rows) => {
                let tys = rows
                    .into_iter()
                    .map(|r| self.elab_row(|ec, r| ec.walk_expr(r), r))
                    .collect::<Vec<Row<&'ar Type<'ar>>>>();

                let ty = self.arena.alloc(Type::Record(SortedRecord::new(tys)));
                self.bindings.push((expr.span, ty));
                ty
            }
            ast::ExprKind::Selector(s) => {
                // FIXME

                let row = ast::Row {
                    label: *s,
                    data: ast::Pat::new(ast::PatKind::Variable(*s), Span::dummy()),
                    span: Span::dummy(),
                };
                let pat = ast::Pat::new(ast::PatKind::Record(vec![row]), Span::dummy());
                let inner = ast::Expr::new(ast::ExprKind::Var(*s), Span::dummy());
                let ty = self.walk_expr(&ast::Expr::new(
                    ast::ExprKind::Fn(vec![ast::Rule {
                        pat,
                        expr: inner,
                        span: expr.span,
                    }]),
                    expr.span,
                ));
                self.bindings.push((expr.span, ty));
                ty
            }
            ast::ExprKind::Seq(exprs) => {
                let mut ty = self.arena.unit();
                for (idx, ex) in exprs.iter().enumerate() {
                    if idx != exprs.len() - 1 {
                        let ety = self.walk_expr(ex);
                        self.unify(ety, ty, &|c| {
                            c.span(ex.span)
                                .add_message("expressions in sequence must return `unit`")
                        });
                    } else {
                        ty = self.walk_expr(ex);
                    }
                }
                self.bindings.push((expr.span, ty));
                ty
            }
            ast::ExprKind::Var(sym) => match self.lookup_value(sym) {
                Some(spanned) => {
                    let ty = self.instantiate(&spanned.data.scheme);
                    self.bindings.push((expr.span, ty));
                    ty
                }
                None => {
                    self.diags.push(Diagnostic::error(
                        expr.span,
                        format!("unbound variable {:?}", sym),
                    ));
                    let ty = self.fresh_tyvar();
                    self.bindings.push((expr.span, ty));
                    ty
                }
            },
            _ => panic!(Diagnostic::error(
                expr.span,
                format!("unknown expr {:?}", expr),
            )),
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
                    let ty = ctx.walk_type(&typebind.ty, false);
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
                Scheme::Mono(self.walk_type(&typebind.ty, false))
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
                    let dom = self.walk_type(ty, false);
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
                    let ty = self.walk_type(ty, false);
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

    /// Perform initial elaboration on a function binding, enough to build up an environment
    fn elab_decl_fnbind_ty<'s>(
        &mut self,
        name: Symbol,
        arity: usize,
        fbs: &'s [ast::FnBinding],
    ) -> PartialFun<'s, 'ar> {
        let arg_tys = (0..arity)
            .map(|_| self.fresh_tyvar())
            .collect::<Vec<&'ar Type<'ar>>>();
        let res_ty = self.fresh_tyvar();
        let mut clauses = Vec::new();

        for clause in fbs {
            if let Some(ty) = &clause.res_ty {
                let t = self.walk_type(&ty, false);
                self.unify(res_ty, t, &|c| {
                    c.span(ty.span)
                        .add_message("function clause with result constraint of different type")
                });
            }

            let mut bindings = Vec::new();
            for (idx, pat) in clause.pats.iter().enumerate() {
                if idx >= arity {
                    self.diags.push(Diagnostic::error(
                        pat.span,
                        "function clause with wrong number of arguments",
                    ));
                    continue;
                }
                let pat_ty = self.walk_pat_inner(pat, false, &mut bindings);
                self.unify(&arg_tys[idx], pat_ty, &|c| {
                    c.span(pat.span)
                        .add_message("function clause with argument of different type")
                });
            }
            clauses.push(PartialFnBinding {
                expr: &clause.expr,
                bindings,
                span: clause.span,
            })
        }

        let ty = arg_tys
            .iter()
            .rev()
            .fold(res_ty, |acc, arg| self.arena.arrow(arg, acc));

        PartialFun {
            name,
            clauses,
            res_ty,
            ty,
        }
    }

    fn elab_decl_fnbind(&mut self, fun: PartialFun<'_, 'ar>) {
        let PartialFun {
            clauses,
            res_ty,
            name,
            ty,
        } = fun;

        let mut fun_span = clauses[0].span;
        // Destructure so that we can move `bindings` into a closure
        for PartialFnBinding {
            expr,
            bindings,
            span,
        } in clauses
        {
            // Make a new scope, in which we define the pattern bindings, and proceed
            // to elaborate the body of the function clause
            self.tyvar_rank += 1;
            let expr = self.with_scope(move |ctx| {
                for (var, tv) in bindings {
                    ctx.define_value(var.data, Scheme::Mono(tv), IdStatus::Var, var.span);
                }
                ctx.walk_expr(&expr)
            });
            self.tyvar_rank -= 1;
            // Unify function clause body with result type
            self.unify(res_ty, expr, &|c| {
                c.span(span)
                    .add_message("function clause returns a different type")
            });
            fun_span += span;
        }

        // Rebind with final type. Unbind first so that generalization happens properly
        self.unbind_value(name);
        let sch = self.generalize(ty);
        self.define_value(name, sch, IdStatus::Var, fun_span);
    }

    fn elab_decl_fun(&mut self, tyvars: &[Symbol], fbs: &[ast::Fun]) {
        self.with_tyvars(|ctx| {
            let mut vars = Vec::new();
            ctx.tyvar_rank += 1;

            // First step is to bind any syntactically bound type vars
            // e.g. fun ('a, 'b) option_map ..
            for sym in tyvars {
                let f = ctx.arena.fresh_type_var(ctx.tyvar_rank + 1);
                vars.push(f.id);
                ctx.tyvars.push((*sym, f));
            }

            // Check to make sure all of the function clauses are consistent within each binding group
            let mut info = Vec::new();
            for f in fbs {
                let n = f[0].name;
                let a = f[0].pats.len();

                // Create an initial binding, and add it the value environment
                let fns = ctx.elab_decl_fnbind_ty(n, a, f);
                ctx.define_value(fns.name, Scheme::Mono(fns.ty), IdStatus::Var, f.span);
                info.push(fns);
            }
            ctx.tyvar_rank -= 1;

            // Now perform actual elaboration, we've bound the name of the function to a temp variable
            for fun in info {
                ctx.elab_decl_fnbind(fun)
            }
        })
    }

    // TODO: Properly handle scoping
    fn elab_decl_local(&mut self, decls: &ast::Decl, body: &ast::Decl, span: Span) {
        self.with_scope(|ctx| {
            ctx.walk_decl(decls);
            let prev = ctx.local;
            ctx.local = true;
            ctx.walk_decl(body);
            ctx.local = prev;
        })
    }

    fn elab_decl_val(&mut self, tyvars: &[Symbol], pat: &ast::Pat, expr: &ast::Expr) {
        self.with_tyvars(|ctx| {
            ctx.tyvar_rank += 1;
            for tyvar in tyvars {
                ctx.tyvars
                    .push((*tyvar, ctx.arena.fresh_type_var(ctx.tyvar_rank)));
            }

            let expr_ty = ctx.walk_expr(expr);
            let (pat_ty, bindings) = ctx.walk_pat(pat, false);

            ctx.tyvar_rank -= 1;
            // let non_expansive = expr.non_expansive();
            // FIXME: add to sml_frontend::ast?
            let non_expansive = true;

            ctx.unify(pat_ty, expr_ty, &|c| {
                c.span(pat.span)
                    .add_message("pattern type and expression type differ")
            });
            for (var, tv) in bindings {
                let sch = match non_expansive {
                    true => ctx.generalize(tv),
                    false => Scheme::Mono(tv),
                };
                ctx.define_value(var.data, sch, IdStatus::Var, var.span);
            }
        })
    }

    pub fn walk_decl(&mut self, decl: &ast::Decl) {
        match &decl.data {
            ast::DeclKind::Datatype(dbs) => self.elab_decl_datatype(dbs),
            ast::DeclKind::Type(tbs) => self.elab_decl_type(tbs),
            ast::DeclKind::Function(tyvars, fbs) => self.elab_decl_fun(tyvars, fbs),
            ast::DeclKind::Value(tyvars, pat, expr) => self.elab_decl_val(tyvars, pat, expr),
            ast::DeclKind::Exception(exns) => self.elab_decl_exception(exns),
            ast::DeclKind::Fixity(fixity, bp, sym) => self.elab_decl_fixity(fixity, *bp, *sym),
            ast::DeclKind::Local(decls, body) => self.elab_decl_local(decls, body, decl.span),
            ast::DeclKind::Seq(decls) => {
                for d in decls {
                    self.walk_decl(d);
                }
            }
        }
        // Expand span
        self.namespaces[self.current].span.end = decl.span.end;
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
