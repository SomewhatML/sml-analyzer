use sml_core::types::*;
use sml_util::interner::*;
use std::collections::HashMap;

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

    pub fn write_type(
        &mut self,
        ty: &Type<'_>,
        interner: &Interner,
        f: &mut dyn std::fmt::Write,
    ) -> std::fmt::Result {
        match ty {
            Type::Var(tvar) => match tvar.ty() {
                Some(bound) => self.write_type(bound, interner, f),
                None => write!(f, "'{}", self.gen(tvar.id)),
            },
            Type::Con(tc, args) => match tc {
                &sml_core::builtin::tycons::T_ARROW => {
                    self.write_type(&args[0], interner, f)?;
                    write!(f, " -> ")?;
                    self.write_type(&args[1], interner, f)
                }
                _ => {
                    if args.is_empty() {
                        write!(f, "{}", interner.get(tc.name).unwrap_or_else(|| "?"))
                    } else {
                        for arg in args {
                            self.write_type(*arg, interner, f)?;
                            write!(f, " ")?;
                        }
                        write!(f, "{}", interner.get(tc.name).unwrap_or_else(|| "?"))
                    }
                }
            },
            Type::Record(fields) => {
                let tuple = match fields.get(0) {
                    Some(sml_core::Row {
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
                    self.write_type(field.data, interner, f)?;
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
