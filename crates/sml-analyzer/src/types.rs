use sml_core::types::*;
use sml_util::interner::*;
use std::collections::HashMap;

use database::CantUnify;

// pub struct CantUnify<'ar> {
//     pub ty1: &'ar Type<'ar>,
//     pub ty2: &'ar Type<'ar>,
//     pub sp1: Option<Span>,
//     pub sp2: Option<Span>,
//     pub message: String,
//     pub reason: String,
//     pub originating: Option<Span>,
// }

fn span_to_range(sp: sml_util::span::Span) -> lsp_types::Range {
    lsp_types::Range::new(
        lsp_types::Position::new(sp.start.line as u64, sp.start.col as u64),
        lsp_types::Position::new(sp.end.line as u64, sp.end.col as u64),
    )
}

pub fn unify_error<'a>(c: CantUnify<'a>, intern: &Interner) -> Option<lsp_types::Diagnostic> {
    let mut alpha = Alpha::default();
    let mut ty1 = String::new();
    let mut ty2 = String::new();

    alpha.write_type2(c.ty1, intern, &mut ty1).ok()?;
    alpha.write_type2(c.ty2, intern, &mut ty2).ok()?;

    let sp = c.originating?;
    let diag = lsp_types::Diagnostic::new_simple(
        span_to_range(sp),
        format!(
            "Type error: {}: {} and {}\n{}",
            c.reason, ty1, ty2, c.message
        ),
    );

    Some(diag)
}

// Alpha rename typevars to better letters
#[derive(Default)]
pub struct Alpha {
    map: HashMap<usize, String>,
}

fn fresh_name(x: usize) -> String {
    let last = ((x % 26) as u8 + 'a' as u8) as char;
    (0..x / 26)
        .map(|_| 'z')
        .chain(std::iter::once(last))
        .collect::<String>()
}

impl Alpha {
    fn gen(&mut self, id: usize) -> &str {
        let len = self.map.len();
        self.map.entry(id).or_insert_with(|| fresh_name(len))
    }

    pub fn write_type2(
        &mut self,
        ty: &database::Type<'_>,
        interner: &Interner,
        f: &mut dyn std::fmt::Write,
    ) -> std::fmt::Result {
        match ty {
            database::Type::Var(tvar) => match tvar.ty() {
                Some(bound) => self.write_type2(bound, interner, f),
                None => write!(f, "'{}", self.gen(tvar.id)),
            },
            database::Type::Con(tc, args) => match tc {
                &database::builtin::tycons::T_ARROW => {
                    self.write_type2(&args[0], interner, f)?;
                    write!(f, " -> ")?;
                    self.write_type2(&args[1], interner, f)
                }
                _ => {
                    if args.is_empty() {
                        write!(f, "{}", interner.get(tc.name).unwrap_or_else(|| "?"))
                    } else {
                        for arg in args {
                            self.write_type2(*arg, interner, f)?;
                            write!(f, " ")?;
                        }
                        write!(f, "{}", interner.get(tc.name).unwrap_or_else(|| "?"))
                    }
                }
            },
            database::Type::Record(fields) => {
                let tuple = match fields.get(0) {
                    Some(database::Row {
                        label: Symbol::Tuple(_),
                        ..
                    }) => true,
                    _ => false,
                };

                if tuple {
                    write!(f, "(")?;
                } else {
                    write!(f, "{{")?;
                }
                for (idx, field) in fields.iter().enumerate() {
                    if !tuple {
                        write!(f, "{}:", interner.get(field.label).unwrap_or_else(|| "?"))?;
                    }
                    self.write_type2(field.data, interner, f)?;
                    if idx != fields.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                if tuple {
                    write!(f, ")")
                } else {
                    write!(f, "}}")
                }
            }
        }
    }
}
