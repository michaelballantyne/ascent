//! Experiment 1: the faithful flat m-CFA port with manually enumerated,
//! `delta`-marked semi-naive rule versions (the plusplus fork's explicit
//! `delta` body-atom marker), replacing `scheme_mcfa::tuned`'s materialized
//! reader-index relations with plain rule ordering.
//!
//! This is a line-for-line copy of `scheme_mcfa::Mcfa` (the faithful port of
//! Appendix A), with every rule in the analysis SCC (the mutually recursive
//! `state_e` / `state_a` / `stored_val` / `stored_kont` / `peek_ctx` /
//! `copy_ctx` relations) that joins *two* dynamic (same-SCC) atoms rewritten
//! into *two* rules, each led by a `delta`-marked atom -- one version per
//! dynamic atom, mirroring the "one semi-naive version per delta atom" a
//! Soufflé `.plan` directive would produce. Rules with only one dynamic atom
//! are left exactly as in the faithful port: Ascent's default semi-naive
//! expansion is already delta-first for those (there's only one dynamic atom
//! to pick).
//!
//! `freevar`/`value_form` are a separate, lower-stratum SCC (computed to a
//! quick fixpoint before the analysis SCC starts) — they are not part of the
//! "dynamic atom" bookkeeping above, so their rules are untouched apart from
//! expanding `(a | b)` disjunctions into separate rules (the plusplus fork's
//! 0.7-era grammar spells disjunction `(a || b)`, and rather than depend on
//! that we just duplicate the rule per disjunct, which is semantically
//! identical and avoids the syntax question entirely).
//!
//! See `README.md` (once written) for the cross-check and benchmark results.

// Ascent generates internal index accumulators (e.g. `if__indices_0_total`)
// whose names are derived from the relation names; silence the resulting
// snake-case lint noise for `if_`/`let_` (same as `scheme_mcfa::lib`).
#![allow(non_snake_case)]

use ascent::ascent;

use scheme_mcfa::{AddrK, AddrV, Ctx, Facts, Kont, Value, ff, if_true, mt, tt};

ascent! {
   pub struct McfaDelta;

   // ===================== Input (EDB) relations =====================
   relation top_exp(scheme_mcfa::Sym);
   relation lambda(scheme_mcfa::Sym, scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation lambda_arg_list(scheme_mcfa::Sym, i64, scheme_mcfa::Sym);
   relation prim(scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation prim_call(scheme_mcfa::Sym, scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation call(scheme_mcfa::Sym, scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation call_arg_list(scheme_mcfa::Sym, i64, scheme_mcfa::Sym);
   relation var(scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation num(scheme_mcfa::Sym, i64);
   relation boolean(scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation quotation(scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation if_(scheme_mcfa::Sym, scheme_mcfa::Sym, scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation setb(scheme_mcfa::Sym, scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation callcc(scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation let_(scheme_mcfa::Sym, scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation let_list(scheme_mcfa::Sym, scheme_mcfa::Sym, scheme_mcfa::Sym);

   // ===================== Derived relations =====================
   relation value_form(scheme_mcfa::Sym);
   relation freevar(scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation state_e(scheme_mcfa::Sym, Ctx, AddrK);
   relation state_a(Value, AddrK);
   relation stored_val(AddrV, Value);
   relation stored_kont(AddrK, Kont);
   relation flow_ee(scheme_mcfa::Sym, scheme_mcfa::Sym);
   relation flow_ea(scheme_mcfa::Sym, Value);
   relation flow_aa(Value, Value);
   relation flow_ae(Value, scheme_mcfa::Sym);
   relation peek_ctx(scheme_mcfa::Sym, Ctx, Ctx);
   relation copy_ctx(Ctx, Ctx, scheme_mcfa::Sym);

   // ================= Lower stratum: value_form / freevar =================
   // (Disjunctions expanded into separate rules -- see module doc.)

   value_form(id.clone()) <-- num(id, _);
   value_form(id.clone()) <-- var(id, _);
   value_form(id.clone()) <-- lambda(id, _, _);
   value_form(id.clone()) <-- quotation(id, _);
   value_form(id.clone()) <-- boolean(id, _);

   freevar(x.clone(), e.clone()) <-- var(e, x);
   freevar(x.clone(), e.clone()) <--
      lambda(e, vars, body), freevar(x, body), !lambda_arg_list(vars, _, x);
   freevar(x.clone(), e.clone()) <-- call(e, func, _args), freevar(x, func);
   freevar(x.clone(), e.clone()) <-- call(e, _func, args), freevar(x, args);
   freevar(x.clone(), e.clone()) <-- prim_call(e, _, args), freevar(x, args);
   freevar(x.clone(), e.clone()) <-- call_arg_list(e, _, arg), freevar(x, arg);
   freevar(x.clone(), e.clone()) <-- if_(e, eguard, _et, _ef), freevar(x, eguard);
   freevar(x.clone(), e.clone()) <-- if_(e, _eguard, et, _ef), freevar(x, et);
   freevar(x.clone(), e.clone()) <-- if_(e, _eguard, _et, ef), freevar(x, ef);
   freevar(y.clone(), e.clone()) <-- setb(e, _, ev), freevar(y, ev);
   freevar(x.clone(), e.clone()) <-- callcc(e, ev), freevar(x, ev);
   freevar(x.clone(), e.clone()) <-- let_(e, binds, _body), freevar(x, binds);
   freevar(x.clone(), e.clone()) <-- let_(e, _binds, body), freevar(x, body);
   freevar(x.clone(), e.clone()) <--
      let_list(e, _, bind), freevar(x, bind), !let_list(e, x, _);

   // ============================ Analysis SCC ============================

   // ----- injection of the top expression (Iˆ) -- no dynamic atoms -----
   state_e(e.clone(), Ctx(mt()), AddrK { e: e.clone(), ctx: Ctx(mt()) }),
   peek_ctx(e.clone(), Ctx(mt()), Ctx(e.clone())),
   stored_kont(AddrK { e: e.clone(), ctx: Ctx(mt()) }, Kont::MT) <--
      top_exp(e);

   // ----- peek_ctx -- one dynamic atom (state_e); default semi-naive is
   // already delta-first, so no `delta` marker needed. Disjunction expanded.
   peek_ctx(e.clone(), old.clone(), Ctx(e.clone())) <-- state_e(e, old, _), callcc(e, _);
   peek_ctx(e.clone(), old.clone(), Ctx(e.clone())) <-- state_e(e, old, _), call(e, _, _);
   peek_ctx(e.clone(), old.clone(), Ctx(e.clone())) <-- state_e(e, old, _), let_(e, _, _);
   peek_ctx(e.clone(), old.clone(), Ctx(e.clone())) <-- state_e(e, old, _), lambda(e, _, _);

   // ----- copy_ctx: copy free-variable bindings between contexts -----
   // Two dynamic atoms: copy_ctx, stored_val. `freevar` is lower-stratum
   // (static here), so it's a plain check/probe in both versions.

   // (a) delta on copy_ctx
   stored_val(AddrV { x: fv.clone(), ctx: to.clone() }, v.clone()) <--
      delta copy_ctx(from, to, e),
      freevar(fv, e),
      stored_val(AddrV { x: fv.clone(), ctx: from.clone() }, v);

   // (b) delta on stored_val (destructure the address to probe copy_ctx on
   // column 0; freevar is then a fully-bound check)
   stored_val(AddrV { x: fv.clone(), ctx: to.clone() }, v.clone()) <--
      delta stored_val(?AddrV { x: fv, ctx: from }, v),
      copy_ctx(from, to, e),
      freevar(fv, e);

   // ----- E-If -- one dynamic atom (state_e) -----
   state_e(eguard.clone(), ctx.clone(), AddrK { e: eguard.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: eguard.clone(), ctx: ctx.clone() },
               Kont::If { true_branch: et.clone(), false_branch: ef.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), eguard.clone()) <--
      state_e(e, ctx, ak),
      if_(e, eguard, et, ef);

   // ----- E-C/cc -- two dynamic atoms: state_e, peek_ctx. `callcc` (syntax)
   // is EDB/static.

   // (a) delta on state_e
   state_e(elam.clone(), ctx.clone(), AddrK { e: elam.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: elam.clone(), ctx: ctx.clone() },
               Kont::Callcc { ectx: ectx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), elam.clone()) <--
      delta state_e(e, ctx, ak),
      callcc(e, elam),
      peek_ctx(e, ctx, ectx);

   // (b) delta on peek_ctx
   state_e(elam.clone(), ctx.clone(), AddrK { e: elam.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: elam.clone(), ctx: ctx.clone() },
               Kont::Callcc { ectx: ectx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), elam.clone()) <--
      delta peek_ctx(e, ctx, ectx),
      state_e(e, ctx, ak),
      callcc(e, elam);

   // ----- E-Set! -- one dynamic atom (state_e) -----
   state_e(esetto.clone(), ctx.clone(), AddrK { e: esetto.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: esetto.clone(), ctx: ctx.clone() },
               Kont::Set { loc: AddrV { x: x.clone(), ctx: ctx.clone() }, next_ak: ak.clone() }),
   flow_ee(e.clone(), esetto.clone()) <--
      state_e(e, ctx, ak),
      setb(e, x, esetto);

   // ----- E-Call -- two dynamic atoms: state_e, peek_ctx. `call` (syntax)
   // is EDB/static.

   // (a) delta on state_e
   state_e(efunc.clone(), ctx.clone(), AddrK { e: efunc.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: efunc.clone(), ctx: ctx.clone() },
               Kont::Arg { args: eargs.clone(), ctx: ctx.clone(), ectx: ectx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), efunc.clone()) <--
      delta state_e(e, ctx, ak),
      call(e, efunc, eargs),
      peek_ctx(e, ctx, ectx);

   // (b) delta on peek_ctx
   state_e(efunc.clone(), ctx.clone(), AddrK { e: efunc.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: efunc.clone(), ctx: ctx.clone() },
               Kont::Arg { args: eargs.clone(), ctx: ctx.clone(), ectx: ectx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), efunc.clone()) <--
      delta peek_ctx(e, ctx, ectx),
      state_e(e, ctx, ak),
      call(e, efunc, eargs);

   // ----- E-Let -- two dynamic atoms: state_e, peek_ctx. `let_`/`let_list`
   // (syntax) are EDB/static.

   // (a) delta on state_e
   state_e(ebnd.clone(), ctx.clone(), AddrK { e: ebnd.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: ebnd.clone(), ctx: ctx.clone() },
               Kont::Let { av: AddrV { x: x.clone(), ctx: ectx.clone() }, ebody: ebody.clone(), ctx: ectx.clone(), next_ak: ak.clone() }),
   copy_ctx(ctx.clone(), ectx.clone(), e.clone()),
   flow_ee(e.clone(), ebnd.clone()) <--
      delta state_e(e, ctx, ak),
      let_(e, ll, ebody),
      let_list(ll, x, ebnd),
      peek_ctx(e, ctx, ectx);

   // (b) delta on peek_ctx
   state_e(ebnd.clone(), ctx.clone(), AddrK { e: ebnd.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: ebnd.clone(), ctx: ctx.clone() },
               Kont::Let { av: AddrV { x: x.clone(), ctx: ectx.clone() }, ebody: ebody.clone(), ctx: ectx.clone(), next_ak: ak.clone() }),
   copy_ctx(ctx.clone(), ectx.clone(), e.clone()),
   flow_ee(e.clone(), ebnd.clone()) <--
      delta peek_ctx(e, ctx, ectx),
      state_e(e, ctx, ak),
      let_(e, ll, ebody),
      let_list(ll, x, ebnd);

   // ----- E-Prim -- one dynamic atom (state_e) -----
   state_e(earg0.clone(), ctx.clone(), AddrK { e: earg0.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: earg0.clone(), ctx: ctx.clone() },
               Kont::Prim1 { op: op.clone(), e2: earg1.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
   flow_ee(e.clone(), earg0.clone()) <--
      state_e(e, ctx, ak),
      prim_call(e, op, pl),
      call_arg_list(pl, p0, earg0), if *p0 == 0,
      call_arg_list(pl, p1, earg1), if *p1 == 1;

   // ----- Atomic evaluation (E-AE): num / bool / lambda -- one dynamic atom
   // (state_e) each -----
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

   // ----- Atomic evaluation (E-AE): var -- two dynamic atoms: state_e,
   // stored_val. `var` (syntax) is EDB/static.

   // (a) delta on state_e
   state_a(v.clone(), ak.clone()),
   flow_ea(e.clone(), v.clone()) <--
      delta state_e(e, ctx, ak),
      var(e, x),
      stored_val(AddrV { x: x.clone(), ctx: ctx.clone() }, v);

   // (b) delta on stored_val (destructure the address; `var` probed via its
   // reverse index on `x`, then `state_e` on the now-bound `(e, ctx)`)
   state_a(v.clone(), ak.clone()),
   flow_ea(e.clone(), v.clone()) <--
      delta stored_val(?AddrV { x, ctx }, v),
      var(e, x),
      state_e(e, ctx, ak);

   // ----- A-IfT -- two dynamic atoms: state_a, stored_kont -----

   // (a) delta on state_a
   state_e(et.clone(), ctx_k.clone(), next_ak.clone()),
   flow_ae(Value::Bool(tt()), et.clone()) <--
      delta state_a(v, ak),
      if if_true(v),
      stored_kont(ak, ?Kont::If { true_branch: et, ctx: ctx_k, next_ak, .. });

   // (b) delta on stored_kont
   state_e(et.clone(), ctx_k.clone(), next_ak.clone()),
   flow_ae(Value::Bool(tt()), et.clone()) <--
      delta stored_kont(ak, ?Kont::If { true_branch: et, ctx: ctx_k, next_ak, .. }),
      state_a(v, ak),
      if if_true(v);

   // ----- A-IfF -- two dynamic atoms: state_a, stored_kont -----

   // (a) delta on state_a
   state_e(ef.clone(), ctx_k.clone(), next_ak.clone()),
   flow_ae(Value::Bool(ff()), ef.clone()) <--
      delta state_a(?Value::Bool(b), ak),
      if b.as_ref() == "#f",
      stored_kont(ak, ?Kont::If { false_branch: ef, ctx: ctx_k, next_ak, .. });

   // (b) delta on stored_kont
   state_e(ef.clone(), ctx_k.clone(), next_ak.clone()),
   flow_ae(Value::Bool(ff()), ef.clone()) <--
      delta stored_kont(ak, ?Kont::If { false_branch: ef, ctx: ctx_k, next_ak, .. }),
      state_a(?Value::Bool(b), ak),
      if b.as_ref() == "#f";

   // ----- A-C/cc -- two dynamic atoms: state_a, stored_kont. `lambda` /
   // `lambda_arg_list` (syntax) are EDB/static.

   // (a) delta on state_a
   state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
   stored_val(AddrV { x: x.clone(), ctx: ectx.clone() }, Value::Kont(ak.clone())),
   copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
   flow_ae(Value::Closure { e: elam.clone(), ctx: ctx_clo.clone() }, ebody.clone()) <--
      delta state_a(?Value::Closure { e: elam, ctx: ctx_clo }, ak),
      stored_kont(ak, ?Kont::Callcc { ectx, next_ak }),
      lambda(elam, params, ebody),
      lambda_arg_list(params, p0, x), if *p0 == 0;

   // (b) delta on stored_kont
   state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
   stored_val(AddrV { x: x.clone(), ctx: ectx.clone() }, Value::Kont(ak.clone())),
   copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
   flow_ae(Value::Closure { e: elam.clone(), ctx: ctx_clo.clone() }, ebody.clone()) <--
      delta stored_kont(ak, ?Kont::Callcc { ectx, next_ak }),
      state_a(?Value::Closure { e: elam, ctx: ctx_clo }, ak),
      lambda(elam, params, ebody),
      lambda_arg_list(params, p0, x), if *p0 == 0;

   // ----- A-C/ccKont -- two dynamic atoms: state_a, stored_kont -----

   // (a) delta on state_a
   state_a(Value::Kont(ak.clone()), bk.clone()),
   flow_aa(Value::Kont(bk.clone()), Value::Kont(ak.clone())) <--
      delta state_a(?Value::Kont(bk), ak),
      stored_kont(ak, ?Kont::Callcc { .. });

   // (b) delta on stored_kont
   state_a(Value::Kont(ak.clone()), bk.clone()),
   flow_aa(Value::Kont(bk.clone()), Value::Kont(ak.clone())) <--
      delta stored_kont(ak, ?Kont::Callcc { .. }),
      state_a(?Value::Kont(bk), ak);

   // ----- A-Ar -- two dynamic atoms: state_a, stored_kont. `call_arg_list`
   // (syntax) is EDB/static.

   // (a) delta on state_a
   state_e(earg.clone(), ctx.clone(), AddrK { e: earg.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: earg.clone(), ctx: ctx.clone() },
               Kont::Fn { func: v.clone(), pos: *pos, ctx: ectx.clone(), next_ak: next_ak.clone() }),
   flow_ae(v.clone(), earg.clone()) <--
      delta state_a(v, ak),
      stored_kont(ak, ?Kont::Arg { args: eargs, ctx, ectx, next_ak }),
      call_arg_list(eargs, pos, earg);

   // (b) delta on stored_kont
   state_e(earg.clone(), ctx.clone(), AddrK { e: earg.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: earg.clone(), ctx: ctx.clone() },
               Kont::Fn { func: v.clone(), pos: *pos, ctx: ectx.clone(), next_ak: next_ak.clone() }),
   flow_ae(v.clone(), earg.clone()) <--
      delta stored_kont(ak, ?Kont::Arg { args: eargs, ctx, ectx, next_ak }),
      state_a(v, ak),
      call_arg_list(eargs, pos, earg);

   // ----- A-Call -- two dynamic atoms: state_a, stored_kont. `lambda` /
   // `lambda_arg_list` (syntax) are EDB/static.

   // (a) delta on state_a
   state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
   stored_val(AddrV { x: x.clone(), ctx: ectx.clone() }, v.clone()),
   copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
   flow_ae(v.clone(), ebody.clone()) <--
      delta state_a(v, ak),
      stored_kont(ak, ?Kont::Fn { func: Value::Closure { e: elam, ctx: ctx_clo }, pos, ctx: ectx, next_ak }),
      lambda(elam, params, ebody),
      lambda_arg_list(params, pos, x);

   // (b) delta on stored_kont
   state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
   stored_val(AddrV { x: x.clone(), ctx: ectx.clone() }, v.clone()),
   copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
   flow_ae(v.clone(), ebody.clone()) <--
      delta stored_kont(ak, ?Kont::Fn { func: Value::Closure { e: elam, ctx: ctx_clo }, pos, ctx: ectx, next_ak }),
      state_a(v, ak),
      lambda(elam, params, ebody),
      lambda_arg_list(params, pos, x);

   // ----- A-Call (continuation as operator) -- two dynamic atoms: state_a,
   // stored_kont -----

   // (a) delta on state_a
   state_a(v.clone(), callcc_kont.clone()),
   flow_aa(v.clone(), v.clone()) <--
      delta state_a(v, ak),
      stored_kont(ak, ?Kont::Fn { func: Value::Kont(callcc_kont), pos: 0, .. });

   // (b) delta on stored_kont
   state_a(v.clone(), callcc_kont.clone()),
   flow_aa(v.clone(), v.clone()) <--
      delta stored_kont(ak, ?Kont::Fn { func: Value::Kont(callcc_kont), pos: 0, .. }),
      state_a(v, ak);

   // ----- A-Let -- two dynamic atoms: state_a, stored_kont -----

   // (a) delta on state_a
   state_e(ebody.clone(), ctx.clone(), next_ak.clone()),
   stored_val(av.clone(), v.clone()),
   flow_ae(v.clone(), ebody.clone()) <--
      delta state_a(v, ak),
      stored_kont(ak, ?Kont::Let { av, ebody, ctx, next_ak });

   // (b) delta on stored_kont
   state_e(ebody.clone(), ctx.clone(), next_ak.clone()),
   stored_val(av.clone(), v.clone()),
   flow_ae(v.clone(), ebody.clone()) <--
      delta stored_kont(ak, ?Kont::Let { av, ebody, ctx, next_ak }),
      state_a(v, ak);

   // ----- A-Prim1 -- two dynamic atoms: state_a, stored_kont -----

   // (a) delta on state_a
   state_e(earg1.clone(), ctx.clone(), AddrK { e: earg1.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: earg1.clone(), ctx: ctx.clone() },
               Kont::Prim2 { op: op.clone(), v1: v.clone(), next_ak: next_ak.clone() }),
   flow_ae(v.clone(), earg1.clone()) <--
      delta state_a(v, ak),
      stored_kont(ak, ?Kont::Prim1 { op, e2: earg1, ctx, next_ak });

   // (b) delta on stored_kont
   state_e(earg1.clone(), ctx.clone(), AddrK { e: earg1.clone(), ctx: ctx.clone() }),
   stored_kont(AddrK { e: earg1.clone(), ctx: ctx.clone() },
               Kont::Prim2 { op: op.clone(), v1: v.clone(), next_ak: next_ak.clone() }),
   flow_ae(v.clone(), earg1.clone()) <--
      delta stored_kont(ak, ?Kont::Prim1 { op, e2: earg1, ctx, next_ak }),
      state_a(v, ak);

   // ----- A-Prim2 -- two dynamic atoms: state_a, stored_kont -----

   // (a) delta on state_a
   state_a(Value::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }, next_ak.clone()),
   flow_aa(v2.clone(), Value::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }) <--
      delta state_a(v2, ak),
      stored_kont(ak, ?Kont::Prim2 { op, v1, next_ak });

   // (b) delta on stored_kont
   state_a(Value::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }, next_ak.clone()),
   flow_aa(v2.clone(), Value::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }) <--
      delta stored_kont(ak, ?Kont::Prim2 { op, v1, next_ak }),
      state_a(v2, ak);

   // ----- A-Set! -- two dynamic atoms: state_a, stored_kont -----

   // (a) delta on state_a
   state_a(Value::Number(-42), next_ak.clone()),
   stored_val(loc.clone(), v.clone()),
   flow_aa(v.clone(), Value::Number(-42)) <--
      delta state_a(v, ak),
      stored_kont(ak, ?Kont::Set { loc, next_ak });

   // (b) delta on stored_kont
   state_a(Value::Number(-42), next_ak.clone()),
   stored_val(loc.clone(), v.clone()),
   flow_aa(v.clone(), Value::Number(-42)) <--
      delta stored_kont(ak, ?Kont::Set { loc, next_ak }),
      state_a(v, ak);
}

/// Load `facts` into a fresh, un-run [`McfaDelta`] program by plain field
/// assignment -- the same mechanism as `scheme_mcfa::Facts::into_program`
/// (see `ascent_tests/src/extdb.rs`'s `tc.edge = ...; tc.run();` for the
/// fork's own confirmation that this works for ordinary, non-`extern`
/// relations).
///
/// We can't `impl Facts` here (orphan rule: `Facts` is a foreign type and
/// this isn't the crate that defines it), so this is a free function instead
/// of an inherent method.
pub fn load_facts(facts: Facts) -> McfaDelta {
   let mut p = McfaDelta::default();
   p.top_exp = facts.top_exp;
   p.lambda = facts.lambda;
   p.lambda_arg_list = facts.lambda_arg_list;
   p.prim = facts.prim;
   p.prim_call = facts.prim_call;
   p.call = facts.call;
   p.call_arg_list = facts.call_arg_list;
   p.var = facts.var;
   p.num = facts.num;
   p.boolean = facts.boolean;
   p.quotation = facts.quotation;
   p.if_ = facts.if_;
   p.setb = facts.setb;
   p.callcc = facts.callcc;
   p.let_ = facts.let_;
   p.let_list = facts.let_list;
   p
}

/// Convenience: build, load, and run the analysis on an AST. Sanity-asserts
/// that fact preloading actually took effect (a nonempty `state_e` after
/// `run()` requires `top_exp` to have been seeded correctly).
pub fn analyze(ast: &scheme_mcfa::Ast) -> McfaDelta {
   let facts = Facts::from_ast(ast);
   let mut prog = load_facts(facts);
   prog.run();
   assert!(
      !prog.state_e.is_empty(),
      "McfaDelta: state_e is empty after run() -- fact preloading via plain field \
       assignment did not take effect"
   );
   prog
}
