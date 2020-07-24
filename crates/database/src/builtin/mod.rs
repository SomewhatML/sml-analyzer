pub mod constructors;
pub mod tycons;

use super::*;
use crate::database::*;

fn define_constructor<'arena>(ctx: &mut Database<'arena>, con: Constructor, sch: Scheme<'arena>) {
    ctx.define_value(con.name, sch, IdStatus::Con(con), Span::zero());
}

/// This is not pretty, but we have to handle builtins for elaboration somehow
pub fn populate_context<'arena>(ctx: &mut Database<'arena>) {
    // Build the initial type environment
    for tc in &tycons::T_BUILTINS {
        ctx.define_type(tc.name, TypeStructure::Tycon(*tc), Span::zero());
    }

    let nil = ctx.arena.fresh_var(0);

    define_constructor(
        ctx,
        constructors::C_NIL,
        Scheme::Poly(vec![nil.tyvar_id()], ctx.arena.list(nil)),
    );

    let cons = ctx.arena.fresh_var(0);

    // The inner types of cons: 'a * 'a list
    let crec = ctx.arena.tuple(vec![cons, ctx.arena.list(cons)]);

    define_constructor(
        ctx,
        constructors::C_CONS,
        Scheme::Poly(
            vec![cons.tyvar_id()],
            ctx.arena.arrow(crec, ctx.arena.list(cons)),
        ),
    );

    define_constructor(ctx, constructors::C_TRUE, Scheme::Mono(ctx.arena.bool()));

    define_constructor(ctx, constructors::C_FALSE, Scheme::Mono(ctx.arena.bool()));

    let reff = ctx.arena.fresh_var(0);
    define_constructor(
        ctx,
        constructors::C_REF,
        Scheme::Poly(
            vec![reff.tyvar_id()],
            ctx.arena.arrow(reff, ctx.arena.reff(reff)),
        ),
    );
}
