//! **Delta-friendly ("tuned") version of the faithful Ascent port.**
//!
//! Same analysis, same `m=1` semantics as [`crate::Mcfa`] — but with rule
//! bodies restructured so that Ascent's semi-naive evaluation is *delta-driven*
//! in every variant. Diagnosis (see README): on deep terms the fixpoint runs
//! tens of thousands of tiny iterations, and in the faithful port four rule
//! variants re-scan a large `total` index every iteration, because:
//!
//! 1. an `if` guard or `?pattern` sitting between two body atoms prevents
//!    Ascent's runtime-reorderable *simple join* (the delta=`stored_kont`
//!    variant of A-If must scan all of `state_a`), and
//! 2. in 3-atom rules (e.g. `state_e ⋈ call ⋈ peek_ctx`) the variant whose
//!    delta is the *third* atom re-enumerates the whole 2-atom prefix join.
//!
//! The fixes are purely at the rule level:
//!
//! * move guards/patterns *after* the joining atoms (A-If, A-C/cc, A-C/ccKont),
//! * split 3-atom recursive joins into binary joins via intermediate
//!   relations (`app_state`, `let_state`, `callcc_state`, `var_read`,
//!   `copy_edge`) — materializing exactly the "reader indices" the hand-written
//!   AAM worklist maintains,
//! * flatten `stored_val`'s address into columns (`Sym, Ctx, Value`) so the
//!   store can be joined by key from either side.
//!
//! `tests/tuned_check.rs` asserts this computes the same analysis as the
//! faithful port.

use crate::ast::Sym;
use crate::edb::Facts;
use crate::{AddrK, AddrV, Ctx, Kont, Value, if_true};
use ascent::ascent;
use std::sync::Arc;

fn mt() -> Sym { Arc::from("") }
fn tt() -> Sym { Arc::from("#t") }
fn ff() -> Sym { Arc::from("#f") }

ascent! {
   pub struct McfaTuned;

   // ===================== Input (EDB) relations =====================
   relation top_exp(Sym);
   relation lambda(Sym, Sym, Sym);
   relation lambda_arg_list(Sym, i64, Sym);
   relation prim(Sym, Sym);
   relation prim_call(Sym, Sym, Sym);
   relation call(Sym, Sym, Sym);
   relation call_arg_list(Sym, i64, Sym);
   relation var(Sym, Sym);
   relation num(Sym, i64);
   relation boolean(Sym, Sym);
   relation quotation(Sym, Sym);
   relation if_(Sym, Sym, Sym, Sym);
   relation setb(Sym, Sym, Sym);
   relation callcc(Sym, Sym);
   relation let_(Sym, Sym, Sym);
   relation let_list(Sym, Sym, Sym);

   // ===================== Derived relations =====================
   relation freevar(Sym, Sym);
   relation state_e(Sym, Ctx, AddrK);
   relation state_a(Value, AddrK);
   /// stored_val with the address flattened into columns: (x, ctx, v).
   relation stored_val(Sym, Ctx, Value);
   relation stored_kont(AddrK, Kont);
   relation flow_ee(Sym, Sym);
   relation flow_ea(Sym, Value);
   relation flow_aa(Value, Value);
   relation flow_ae(Value, Sym);
   relation peek_ctx(Sym, Ctx, Ctx);
   relation copy_ctx(Ctx, Ctx, Sym);

   // ---- intermediate "reader index" relations (the tuning) ----
   /// variable occurrence e (naming x) evaluated in ctx, waiting on address (x, ctx)
   relation var_read(Sym, Ctx, Sym, AddrK);
   /// flat-closure copy edge: address (fv, from) flows to (fv, to)
   relation copy_edge(Sym, Ctx, Ctx);
   /// call expression e (func, args) reached in ctx — joins with peek_ctx
   relation app_state(Sym, Sym, Sym, Ctx, AddrK);
   /// let binding (x, ebnd) of e with body — joins with peek_ctx
   relation let_state(Sym, Sym, Sym, Sym, Ctx, AddrK);
   /// call/cc expression e (lambda elam) — joins with peek_ctx
   relation callcc_state(Sym, Sym, Ctx, AddrK);

   // ----- freevar (unchanged; its SCC is stratified below the analysis) -----
   freevar(x.clone(), e.clone()) <-- var(e, x);
   freevar(x.clone(), e.clone()) <--
      lambda(e, vars, body), freevar(x, body), !lambda_arg_list(vars, _, x);
   freevar(x.clone(), e.clone()) <--
      call(e, func, args), (freevar(x, func) | freevar(x, args));
   freevar(x.clone(), e.clone()) <-- prim_call(e, _, args), freevar(x, args);
   freevar(x.clone(), e.clone()) <-- call_arg_list(e, _, arg), freevar(x, arg);
   freevar(x.clone(), e.clone()) <--
      if_(e, eguard, et, ef), (freevar(x, eguard) | freevar(x, et) | freevar(x, ef));
   freevar(y.clone(), e.clone()) <-- setb(e, _, ev), freevar(y, ev);
   freevar(x.clone(), e.clone()) <-- callcc(e, ev), freevar(x, ev);
   freevar(x.clone(), e.clone()) <--
      let_(e, binds, body), (freevar(x, binds) | freevar(x, body));
   freevar(x.clone(), e.clone()) <--
      let_list(e, _, bind), freevar(x, bind), !let_list(e, x, _);

   // ----- injection -----
   state_e(e.clone(), Ctx(mt()), AddrK { e: e.clone(), ctx: Ctx(mt()) }),
   peek_ctx(e.clone(), Ctx(mt()), Ctx(e.clone())),
   stored_kont(AddrK { e: e.clone(), ctx: Ctx(mt()) }, Kont::MT) <--
      top_exp(e);

   // ----- peek_ctx (delta = state_e; EDB probes) -----
   peek_ctx(e.clone(), old.clone(), Ctx(e.clone())) <--
      state_e(e, old, _),
      (callcc(e, _) | call(e, _, _) | let_(e, _, _) | lambda(e, _, _));

   // ----- copy_ctx, split into a binary join via copy_edge -----
   copy_edge(fv.clone(), from.clone(), to.clone()) <--
      copy_ctx(from, to, e),
      freevar(fv, e);

   stored_val(fv.clone(), to.clone(), v.clone()) <--
      copy_edge(fv, from, to),
      stored_val(fv, from, v);

   // ----- E-If (delta = state_e) -----
   state_e(eguard.clone(), ctx.clone(), AddrK { e: eguard.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: eguard.clone(), ctx: ctx.clone() },
               Kont::If { true_branch: et.clone(), false_branch: ef.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), eguard.clone()) <--
      state_e(e, ctx, ak),
      if_(e, eguard, et, ef);

   // ----- E-C/cc, split so the peek_ctx join is binary -----
   callcc_state(e.clone(), elam.clone(), ctx.clone(), ak.clone()) <--
      state_e(e, ctx, ak),
      callcc(e, elam);

   state_e(elam.clone(), ctx.clone(), AddrK { e: elam.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: elam.clone(), ctx: ctx.clone() },
               Kont::Callcc { ectx: ectx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), elam.clone()) <--
      callcc_state(e, elam, ctx, ak),
      peek_ctx(e, ctx, ectx);

   // ----- E-Set! (delta = state_e) -----
   state_e(esetto.clone(), ctx.clone(), AddrK { e: esetto.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: esetto.clone(), ctx: ctx.clone() },
               Kont::Set { loc: AddrV { x: x.clone(), ctx: ctx.clone() }, next_ak: ak.clone() }),
   flow_ee(e.clone(), esetto.clone()) <--
      state_e(e, ctx, ak),
      setb(e, x, esetto);

   // ----- E-Call, split so the peek_ctx join is binary -----
   app_state(e.clone(), efunc.clone(), eargs.clone(), ctx.clone(), ak.clone()) <--
      state_e(e, ctx, ak),
      call(e, efunc, eargs);

   state_e(efunc.clone(), ctx.clone(), AddrK { e: efunc.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: efunc.clone(), ctx: ctx.clone() },
               Kont::Arg { args: eargs.clone(), ctx: ctx.clone(), ectx: ectx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), efunc.clone()) <--
      app_state(e, efunc, eargs, ctx, ak),
      peek_ctx(e, ctx, ectx);

   // ----- E-Let, split so the peek_ctx join is binary -----
   let_state(e.clone(), x.clone(), ebnd.clone(), ebody.clone(), ctx.clone(), ak.clone()) <--
      state_e(e, ctx, ak),
      let_(e, ll, ebody),
      let_list(ll, x, ebnd);

   state_e(ebnd.clone(), ctx.clone(), AddrK { e: ebnd.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: ebnd.clone(), ctx: ctx.clone() },
               Kont::Let { av: AddrV { x: x.clone(), ctx: ectx.clone() }, ebody: ebody.clone(), ctx: ectx.clone(), next_ak: ak.clone() }),
   copy_ctx(ctx.clone(), ectx.clone(), e.clone()),
   flow_ee(e.clone(), ebnd.clone()) <--
      let_state(e, x, ebnd, ebody, ctx, ak),
      peek_ctx(e, ctx, ectx);

   // ----- E-Prim (delta = state_e) -----
   state_e(earg0.clone(), ctx.clone(), AddrK { e: earg0.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: earg0.clone(), ctx: ctx.clone() },
               Kont::Prim1 { op: op.clone(), e2: earg1.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), earg0.clone()) <--
      state_e(e, ctx, ak),
      prim_call(e, op, pl),
      call_arg_list(pl, p0, earg0), if *p0 == 0,
      call_arg_list(pl, p1, earg1), if *p1 == 1;

   // ----- Atomic evaluation -----
   state_a(Value::Number(*n), ak.clone()),
   flow_ea(e.clone(), Value::Number(*n)) <--
      state_e(e, _, ak),
      num(e, n);

   state_a(Value::Bool(b.clone()), ak.clone()),
   flow_ea(e.clone(), Value::Bool(b.clone())) <--
      state_e(e, _, ak),
      boolean(e, b);

   state_a(Value::Closure { e: e.clone(), ctx: ctx.clone() }, ak.clone()),
   flow_ea(e.clone(), Value::Closure { e: e.clone(), ctx: ctx.clone() }) <--
      state_e(e, ctx, ak),
      lambda(e, _, _);

   // E-AE for variables, split into a binary join via var_read
   var_read(x.clone(), ctx.clone(), e.clone(), ak.clone()) <--
      state_e(e, ctx, ak),
      var(e, x);

   state_a(v.clone(), ak.clone()),
   flow_ea(e.clone(), v.clone()) <--
      var_read(x, ctx, e, ak),
      stored_val(x, ctx, v);

   // ----- A-IfT (guard AFTER the join, so the join is simple & reorderable) -----
   state_e(et.clone(), ctx_k.clone(), next_ak.clone()),
   flow_ae(Value::Bool(tt()), et.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::If { true_branch: et, ctx: ctx_k, next_ak, .. }),
      if if_true(v);

   // ----- A-IfF -----
   state_e(ef.clone(), ctx_k.clone(), next_ak.clone()),
   flow_ae(Value::Bool(ff()), ef.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::If { false_branch: ef, ctx: ctx_k, next_ak, .. }),
      if let Value::Bool(b) = v, if b.as_ref() == "#f";

   // ----- A-C/cc (closure pattern AFTER the join) -----
   state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
   stored_val(x.clone(), ectx.clone(), Value::Kont(ak.clone())),
   copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
   flow_ae(Value::Closure { e: elam.clone(), ctx: ctx_clo.clone() }, ebody.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Callcc { ectx, next_ak }),
      if let Value::Closure { e: elam, ctx: ctx_clo } = v,
      lambda(elam, params, ebody),
      lambda_arg_list(params, p0, x), if *p0 == 0;

   // ----- A-C/ccKont (kont pattern AFTER the join) -----
   state_a(Value::Kont(ak.clone()), bk.clone()),
   flow_aa(Value::Kont(bk.clone()), Value::Kont(ak.clone())) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Callcc { .. }),
      if let Value::Kont(bk) = v;

   // ----- A-Ar (already an indexed simple join in the faithful port) -----
   state_e(earg.clone(), ctx.clone(), AddrK { e: earg.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: earg.clone(), ctx: ctx.clone() },
               Kont::Fn { func: v.clone(), pos: *pos, ctx: ectx.clone(), next_ak: next_ak.clone() }),
   flow_ae(v.clone(), earg.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Arg { args: eargs, ctx, ectx, next_ak }),
      call_arg_list(eargs, pos, earg);

   // ----- A-Call -----
   state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
   stored_val(x.clone(), ectx.clone(), v.clone()),
   copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
   flow_ae(v.clone(), ebody.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Fn { func: Value::Closure { e: elam, ctx: ctx_clo }, pos, ctx: ectx, next_ak }),
      lambda(elam, params, ebody),
      lambda_arg_list(params, pos, x);

   // ----- A-Call (continuation as operator) -----
   state_a(v.clone(), callcc_kont.clone()),
   flow_aa(v.clone(), v.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Fn { func: Value::Kont(callcc_kont), pos: 0, .. });

   // ----- A-Let -----
   state_e(ebody.clone(), ctx.clone(), next_ak.clone()),
   stored_val(av.x.clone(), av.ctx.clone(), v.clone()),
   flow_ae(v.clone(), ebody.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Let { av, ebody, ctx, next_ak });

   // ----- A-Prim1 -----
   state_e(earg1.clone(), ctx.clone(), AddrK { e: earg1.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: earg1.clone(), ctx: ctx.clone() },
               Kont::Prim2 { op: op.clone(), v1: v.clone(), next_ak: next_ak.clone() }),
   flow_ae(v.clone(), earg1.clone()) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Prim1 { op, e2: earg1, ctx, next_ak });

   // ----- A-Prim2 -----
   state_a(Value::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }, next_ak.clone()),
   flow_aa(v2.clone(), Value::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }) <--
      state_a(v2, ak),
      stored_kont(ak, ?Kont::Prim2 { op, v1, next_ak });

   // ----- A-Set! -----
   state_a(Value::Number(-42), next_ak.clone()),
   stored_val(loc.x.clone(), loc.ctx.clone(), v.clone()),
   flow_aa(v.clone(), Value::Number(-42)) <--
      state_a(v, ak),
      stored_kont(ak, ?Kont::Set { loc, next_ak });
}

impl Facts {
   /// Load these input facts into a fresh, un-run [`McfaTuned`] program.
   pub fn into_tuned_program(self) -> McfaTuned {
      let mut p = McfaTuned::default();
      p.top_exp = self.top_exp;
      p.lambda = self.lambda;
      p.lambda_arg_list = self.lambda_arg_list;
      p.prim = self.prim;
      p.prim_call = self.prim_call;
      p.call = self.call;
      p.call_arg_list = self.call_arg_list;
      p.var = self.var;
      p.num = self.num;
      p.boolean = self.boolean;
      p.quotation = self.quotation;
      p.if_ = self.if_;
      p.setb = self.setb;
      p.callcc = self.callcc;
      p.let_ = self.let_;
      p.let_list = self.let_list;
      p
   }
}
