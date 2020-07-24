use super::{Row, SortedRecord, Span, Symbol};
use crate::builtin;
use crate::types::{Type, TypeVar};
use std::cell::Cell;
use typed_arena;

pub struct OwnedArena<'arena> {
    types: typed_arena::Arena<Type<'arena>>,
    vars: typed_arena::Arena<TypeVar<'arena>>,
}

impl<'arena> OwnedArena<'arena> {
    pub fn new() -> OwnedArena<'arena> {
        OwnedArena {
            types: typed_arena::Arena::with_capacity(4096),
            vars: typed_arena::Arena::with_capacity(4096),
        }
    }

    // borrowck is easily assuaged here
    pub fn borrow(&'arena self) -> Arena<'arena> {
        Arena::new(&self.types, &self.vars)
    }
}

pub struct Arena<'ar> {
    types: &'ar typed_arena::Arena<Type<'ar>>,
    vars: &'ar typed_arena::Arena<TypeVar<'ar>>,
    fresh: Cell<usize>,

    // We cache the builtin nullary type constructors
    _exn: &'ar Type<'ar>,
    _bool: &'ar Type<'ar>,
    _int: &'ar Type<'ar>,
    _str: &'ar Type<'ar>,
    _char: &'ar Type<'ar>,
    _unit: &'ar Type<'ar>,
}

impl<'ar> Arena<'ar> {
    pub fn new(
        types: &'ar typed_arena::Arena<Type<'ar>>,
        vars: &'ar typed_arena::Arena<TypeVar<'ar>>,
    ) -> Arena<'ar> {
        let _exn = types.alloc(Type::Con(builtin::tycons::T_EXN, Vec::new()));
        let _bool = types.alloc(Type::Con(builtin::tycons::T_BOOL, Vec::new()));
        let _int = types.alloc(Type::Con(builtin::tycons::T_INT, Vec::new()));
        let _str = types.alloc(Type::Con(builtin::tycons::T_STRING, Vec::new()));
        let _char = types.alloc(Type::Con(builtin::tycons::T_CHAR, Vec::new()));
        let _unit = types.alloc(Type::Con(builtin::tycons::T_UNIT, Vec::new()));

        Arena {
            types,
            vars,
            fresh: Cell::new(0),
            _exn,
            _bool,
            _int,
            _str,
            _char,
            _unit,
        }
    }

    pub fn alloc(&self, ty: Type<'ar>) -> &'ar Type<'ar> {
        self.types.alloc(ty)
    }

    pub fn fresh_var(&self, rank: usize) -> &'ar Type<'ar> {
        let tvar = self.fresh_type_var(rank);
        self.types.alloc(Type::Var(tvar))
    }

    pub fn fresh_type_var(&self, rank: usize) -> &'ar TypeVar<'ar> {
        let x = self.fresh.get();
        self.fresh.set(x + 1);
        self.vars.alloc(TypeVar::new(x, rank))
    }

    pub fn alloc_tuple<I: IntoIterator<Item = Type<'ar>>>(&self, iter: I) -> &'ar Type<'ar> {
        let rows = iter
            .into_iter()
            .enumerate()
            .map(|(idx, ty)| Row {
                label: Symbol::tuple_field(idx as u32 + 1),
                data: self.alloc(ty),
                span: Span::dummy(),
            })
            .collect();

        self.alloc(Type::Record(SortedRecord::new_unchecked(rows)))
    }

    pub fn tuple<I: IntoIterator<Item = &'ar Type<'ar>>>(&self, iter: I) -> &'ar Type<'ar> {
        let rows = iter
            .into_iter()
            .enumerate()
            .map(|(idx, ty)| Row {
                label: Symbol::tuple_field(idx as u32 + 1),
                data: ty,
                span: Span::dummy(),
            })
            .collect();

        self.alloc(Type::Record(SortedRecord::new_unchecked(rows)))
    }

    pub fn exn(&self) -> &'ar Type<'ar> {
        self._exn
    }

    pub fn unit(&self) -> &'ar Type<'ar> {
        self._unit
    }

    pub fn char(&self) -> &'ar Type<'ar> {
        self._char
    }

    pub fn int(&self) -> &'ar Type<'ar> {
        self._int
    }

    pub fn bool(&self) -> &'ar Type<'ar> {
        self._bool
    }

    pub fn string(&self) -> &'ar Type<'ar> {
        self._str
    }

    pub fn reff(&self, ty: &'ar Type<'ar>) -> &'ar Type<'ar> {
        self.types
            .alloc(Type::Con(builtin::tycons::T_REF, vec![ty]))
    }

    pub fn list(&self, ty: &'ar Type<'ar>) -> &'ar Type<'ar> {
        self.types
            .alloc(Type::Con(builtin::tycons::T_LIST, vec![ty]))
    }

    pub fn arrow(&self, dom: &'ar Type<'ar>, rng: &'ar Type<'ar>) -> &'ar Type<'ar> {
        self.types
            .alloc(Type::Con(builtin::tycons::T_ARROW, vec![dom, rng]))
    }
}
