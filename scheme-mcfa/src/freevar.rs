//! Standalone `freevar` computation, shared by the `emit-egglog` subcommand.
//!
//! egglog has no negation, so the `freevar` relation used by the `(freevar ...)`
//! facts emitted for the egglog port must be precomputed here in Rust (via a
//! small dedicated `ascent!` program) and written out as ground facts. This
//! program contains only the ten `freevar` rules, copied verbatim from
//! [`crate::Mcfa`] in `src/lib.rs`, over the same EDB relations they read —
//! so it computes exactly the same relation as the main program (`freevar` is
//! a stratum that depends only on the EDB).

use ascent::ascent;

use crate::ast::Sym;
use crate::edb::Facts;

ascent! {
   struct FreevarOnly;

   // ===================== Input (EDB) relations =====================
   relation lambda(Sym, Sym, Sym);
   relation lambda_arg_list(Sym, i64, Sym);
   relation prim_call(Sym, Sym, Sym);
   relation call(Sym, Sym, Sym);
   relation call_arg_list(Sym, i64, Sym);
   relation var(Sym, Sym);
   relation if_(Sym, Sym, Sym, Sym);
   relation setb(Sym, Sym, Sym);
   relation callcc(Sym, Sym);
   relation let_(Sym, Sym, Sym);
   relation let_list(Sym, Sym, Sym);

   // ===================== Derived relation =====================
   relation freevar(Sym, Sym); // x (name), e (expr id)

   // ----- freevar -----
   freevar(x.clone(), e.clone()) <-- var(e, x);
   freevar(x.clone(), e.clone()) <--
      lambda(e, vars, body), freevar(x, body), !lambda_arg_list(vars, _, x);
   freevar(x.clone(), e.clone()) <--
      call(e, func, args), (freevar(x, func) | freevar(x, args));
   freevar(x.clone(), e.clone()) <--
      prim_call(e, _, args), freevar(x, args);
   freevar(x.clone(), e.clone()) <--
      call_arg_list(e, _, arg), freevar(x, arg);
   freevar(x.clone(), e.clone()) <--
      if_(e, eguard, et, ef), (freevar(x, eguard) | freevar(x, et) | freevar(x, ef));
   freevar(y.clone(), e.clone()) <--
      setb(e, _, ev), freevar(y, ev);
   freevar(x.clone(), e.clone()) <--
      callcc(e, ev), freevar(x, ev);
   freevar(x.clone(), e.clone()) <--
      let_(e, binds, body), (freevar(x, binds) | freevar(x, body));
   freevar(x.clone(), e.clone()) <--
      let_list(e, _, bind), freevar(x, bind), !let_list(e, x, _);
}

/// Compute the `freevar` relation for `facts` by running the dedicated
/// freevar-only `ascent!` program over its EDB relations.
pub fn freevars(facts: &Facts) -> Vec<(Sym, Sym)> {
   let mut p = FreevarOnly::default();
   p.lambda = facts.lambda.clone();
   p.lambda_arg_list = facts.lambda_arg_list.clone();
   p.prim_call = facts.prim_call.clone();
   p.call = facts.call.clone();
   p.call_arg_list = facts.call_arg_list.clone();
   p.var = facts.var.clone();
   p.if_ = facts.if_.clone();
   p.setb = facts.setb.clone();
   p.callcc = facts.callcc.clone();
   p.let_ = facts.let_.clone();
   p.let_list = facts.let_list.clone();
   p.run();
   p.freevar
}
