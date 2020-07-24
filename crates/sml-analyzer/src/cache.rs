use super::*;

use sml_core::types::Type;
use sml_core::{Datatype, Decl, Expr, ExprKind, Lambda, Pat, PatKind};
use std::collections::HashMap;
use std::fmt::Write;

#[derive(Default, Debug)]
pub struct Definitions<'a> {
    types: Vec<(Span, &'a Type<'a>)>,
    funs: Vec<(Symbol, Lambda<'a>)>,

    name_to_type: HashMap<Symbol, &'a Type<'a>>,
    datatypes: HashMap<Symbol, Datatype<'a>>,
}

#[inline]
fn in_span(pos: &Position, span: &Span) -> bool {
    if pos.line >= span.start.line as u64 && pos.line <= span.end.line as u64 {
        pos.character >= span.start.col as u64 && pos.character <= span.end.col as u64
    } else {
        false
    }
}

struct TyArrowIter<'a, 'b> {
    ty: &'b Type<'a>,
    done: bool,
}

impl<'a, 'b> Iterator for TyArrowIter<'a, 'b> {
    type Item = &'b Type<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            None
        } else {
            self.done = true;
            match self.ty {
                Type::Con(sml_core::builtin::tycons::T_ARROW, args) => {
                    let ty = &args[0];
                    self.ty = &args[1];
                    if let Type::Con(sml_core::builtin::tycons::T_ARROW, _) = ty {
                        self.done = false;
                    }
                    Some(ty)
                }
                _ => None,
            }
        }
    }
}

fn make_ty_fmt_str(ty: &Type<'_>, interner: &Interner) -> String {
    let mut alpha = crate::types::Alpha::default();
    let iter = TyArrowIter { ty, done: false };
    iter.enumerate().fold(String::new(), |mut acc, (idx, ty)| {
        let _ = write!(&mut acc, " ${{{}:(", idx + 2);
        let _ = alpha.write_type(ty, interner, &mut acc);
        let _ = write!(&mut acc, ")}}");
        acc
    })
}

impl<'a> Definitions<'a> {
    fn name_to_type(&self, name: Symbol) -> Option<&'a Type> {
        self.name_to_type.get(&name).copied()
    }

    pub fn clear(&mut self) {
        self.types.clear();
    }

    pub fn completions(&self, interner: &Interner) -> Vec<CompletionItem> {
        self.funs
            .iter()
            .map(|(name, lam)| {
                let mut alpha = crate::types::Alpha::default();
                let mut out = String::new();
                let _ = alpha.write_type(lam.ty, interner, &mut out);
                let fst = out.clone();
                let _ = write!(&mut out, " -> ");
                let _ = alpha.write_type(lam.body.ty, interner, &mut out);

                let name = interner.get(*name).unwrap_or_else(|| "?");
                let mut c = CompletionItem::new_simple(name.into(), out);
                c.kind = Some(CompletionItemKind::Function);
                c.insert_text_format = Some(InsertTextFormat::Snippet);
                c.insert_text = Some(format!(
                    "{} ${{1:({})}}{}",
                    name,
                    fst,
                    make_ty_fmt_str(lam.body.ty, interner)
                ));

                c
            })
            .collect()
    }

    pub fn position_to_type(&self, pos: Position) -> Option<&Type<'a>> {
        self.types
            .iter()
            .filter(|(sp, _)| in_span(&pos, sp))
            .last()
            .map(|(_, ty)| *ty)
    }

    pub fn walk_decl(&mut self, decl: &Decl<'a>) {
        match decl {
            Decl::Datatype(dt) => {
                self.datatypes.insert(dt.tycon.name, dt.clone());
                for (con, arg) in &dt.constructors {
                    if let Some(a) = &arg {
                        self.name_to_type.insert(con.name, a);
                    }
                }
            }
            Decl::Fun(_, lambdas) => {
                for (name, lam) in lambdas {
                    self.funs.push((*name, lam.clone()));
                    self.types.push((lam.body.span, lam.ty));
                    self.walk_expr(&lam.body);
                }
            }
            Decl::Val(rule) => {
                self.walk_pat(&rule.pat);
                self.walk_expr(&rule.expr);
            }
            Decl::Exn(_, _) => {}
        }
    }

    pub fn walk_expr(&mut self, expr: &Expr<'a>) {
        self.types.push((expr.span, expr.ty));
        match expr.expr {
            ExprKind::App(e1, e2) => {
                self.walk_expr(e1);
                self.walk_expr(e2);
            }
            ExprKind::Case(case, rules) => {
                self.walk_expr(case);
                for rule in rules {
                    self.walk_pat(&rule.pat);
                    self.walk_expr(&rule.expr);
                }
            }
            ExprKind::Lambda(Lambda { body, ty, .. }) => {
                self.walk_expr(body);
            }
            ExprKind::Let(decls, expr) => {
                for decl in decls {
                    self.walk_decl(decl);
                }
                self.walk_expr(expr);
            }
            ExprKind::Handle(expr, rules) => {
                self.walk_expr(expr);
                for rule in rules {
                    self.walk_pat(&rule.pat);
                    self.walk_expr(&rule.expr);
                }
            }
            ExprKind::Raise(expr) => self.walk_expr(expr),
            ExprKind::Record(fields) => {
                for field in fields.iter() {
                    self.walk_expr(&field.data);
                }
            }
            ExprKind::List(exprs) | ExprKind::Seq(exprs) => {
                for expr in exprs {
                    self.walk_expr(expr);
                }
            }
            _ => {}
        }
    }

    pub fn walk_pat(&mut self, pat: &Pat<'a>) {
        self.types.push((pat.span, pat.ty));
        match pat.pat {
            PatKind::List(pats) => {
                for pat in pats {
                    self.walk_pat(pat);
                }
            }
            PatKind::Record(pats) => {
                for pat in pats.iter() {
                    self.walk_pat(&pat.data);
                }
            }
            PatKind::App(con, Some(pat)) => {
                self.walk_pat(pat);
            }
            _ => {}
        }
    }
}
