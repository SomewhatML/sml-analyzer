pub mod arena;
pub mod builtin;
pub mod check;
pub mod database;
pub mod types;

use log::*;
use sml_util::interner::Symbol;
use sml_util::span::{Location, Span, Spanned};
pub use types::*;

pub use check::Check;
pub use database::{CantUnify, Database};

#[inline]
fn in_span(pos: &Location, span: &Span) -> bool {
    if pos.line >= span.start.line && pos.line <= span.end.line {
        pos.col >= span.start.col && pos.col <= span.end.col
    } else {
        false
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct TypeId(pub u32);

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct ExprId(pub u32);

#[derive(Clone)]
pub struct Datatype<'ar> {
    pub tycon: Tycon,
    pub tyvars: Vec<usize>,
    pub constructors: Vec<(Constructor, Option<&'ar Type<'ar>>)>,
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub struct Row<T> {
    pub label: Symbol,
    pub data: T,
    pub span: Span,
}

pub struct SortedRecord<T> {
    pub rows: Vec<Row<T>>,
}

impl<T> SortedRecord<T> {
    pub fn new(mut rows: Vec<Row<T>>) -> SortedRecord<T> {
        rows.sort_by(|a, b| a.label.cmp(&b.label));
        SortedRecord { rows }
    }

    pub fn new_unchecked(rows: Vec<Row<T>>) -> SortedRecord<T> {
        SortedRecord { rows }
    }

    pub fn fmap<S, F: Fn(&T) -> S>(&self, f: F) -> SortedRecord<S> {
        let mut v = Vec::with_capacity(self.rows.len());
        for row in self.iter() {
            v.push(Row {
                label: row.label,
                span: row.span,
                data: f(&row.data),
            });
        }
        SortedRecord { rows: v }
    }

    pub fn iter(&self) -> std::slice::Iter<Row<T>> {
        self.rows.iter()
    }

    pub fn contains(&self, lab: &Symbol) -> Option<&Row<T>> {
        for row in self.iter() {
            if &row.label == lab {
                return Some(row);
            }
        }
        None
    }
}

impl<T> std::iter::IntoIterator for SortedRecord<T> {
    type Item = Row<T>;
    type IntoIter = std::vec::IntoIter<Row<T>>;
    fn into_iter(self) -> Self::IntoIter {
        self.rows.into_iter()
    }
}

impl<T> std::ops::Deref for SortedRecord<T> {
    type Target = Vec<Row<T>>;
    fn deref(&self) -> &Self::Target {
        &self.rows
    }
}
