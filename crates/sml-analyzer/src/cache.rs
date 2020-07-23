use super::*;

use sml_core::types::Type;
use sml_core::{Datatype, Decl, Expr, ExprKind, Lambda, Pat, PatKind};
use std::collections::HashMap;

#[derive(Default, Debug)]
pub struct Definitions<'a> {
    types: Vec<(Span, &'a Type<'a>)>,
    funs: Vec<(Span, Lambda<'a>)>,

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

impl<'a> Definitions<'a> {
    fn name_to_type(&self, name: Symbol) -> Option<&'a Type> {
        self.name_to_type.get(&name).copied()
    }

    pub fn clear(&mut self) {
        self.types.clear();
    }

    pub fn position_to_type(&self, pos: Position) -> Option<&Type<'a>> {
        self.types
            .iter()
            .filter(|(sp, _)| in_span(&pos, sp))
            .next()
            .map(|(_, ty)| *ty)

        // self.types.get(0).map(|(a, b)| *b)
        // None
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
                    self.funs.push((lam.body.span, lam.clone()));
                    self.types.push((lam.body.span, lam.ty));
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
