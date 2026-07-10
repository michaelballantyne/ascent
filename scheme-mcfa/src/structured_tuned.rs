//! **Delta-friendly ("tuned") version of the structured-syntax port.**
//!
//! [`crate::tuned`] applies three rule-level rewrites to the *faithful flat*
//! port so that every semi-naive rule variant is delta-driven (see the README's
//! diagnosis: guards/patterns between body atoms and 3-atom joins make
//! specific variants re-scan a large `total` index on every one of the
//! fixpoint's many tiny iterations). This module applies the same treatment to
//! the *structured* (labelled-syntax) port, [`crate::structured`]:
//!
//! * **guards and patterns moved after the joins** — e.g. A-If becomes
//!   `state_a(v, ak), stored_kont(ak, ?If{..}), if sif_true(v)` so the two-atom
//!   join is a simple join Ascent can start from whichever side is the delta;
//! * **`stored_val`'s address flattened** into columns (`Sym, SCtx, SValue`),
//!   and the variable-read and flat-closure-copy joins split via the
//!   `var_read`/`copy_edge` intermediate relations — the same "reader indices"
//!   the hand-written machines maintain ([`crate::aam_delta`]).
//!
//! Notably the third of the flat port's fixes is unnecessary here: with syntax
//! carried structurally, E-Call/E-Let/E-C/cc are already *binary* joins
//! (`state_e ⋈ peek_ctx` — the syntax match is a guard, not an atom), so the
//! `app_state`/`let_state`/`callcc_state` intermediates of the flat tuned port
//! have no counterpart. Structured syntax makes the tuning smaller.
//!
//! `tests/tuned_check.rs` asserts this computes the identical analysis to the
//! untuned structured port, on both labelings, at `m ∈ {0,1,2}`.

use std::collections::HashMap;
use std::rc::Rc;

use ascent::ascent_run;

use crate::ast::Sym;
use crate::structured::{E, Expr, SAddrK, SAddrV, SCtx, SKont, SValue, StructuredStats, free_vars, sextend, sif_true};
use crate::{ff, tt};

/// Run the tuned structured `m`-CFA. Same semantics (and [`StructuredStats`])
/// as [`crate::analyze_structured`]; only the join plans differ.
pub fn analyze_structured_tuned(top: &E, m: usize) -> StructuredStats {
   let empty = SCtx(Vec::new());

   // Precompute free variables (the only place the paper uses `freevar`).
   let mut cache: HashMap<E, Rc<Vec<Sym>>> = HashMap::new();
   free_vars(top, &mut cache);
   let fvs = cache;

   let prog = ascent_run! {
      relation top_expr(E) = vec![(top.clone(),)];

      relation state_e(E, SCtx, SAddrK);
      relation state_a(SValue, SAddrK);
      /// stored_val with the address flattened into columns: (x, ctx, v).
      relation stored_val(Sym, SCtx, SValue);
      relation stored_kont(SAddrK, SKont);
      relation flow_ee(E, E);
      relation flow_ea(E, SValue);
      relation flow_aa(SValue, SValue);
      relation flow_ae(SValue, E);
      relation peek_ctx(E, SCtx, SCtx);
      relation copy_ctx(SCtx, SCtx, E);

      // ---- intermediate "reader index" relations (the tuning) ----
      /// variable occurrence e (naming x) evaluated in ctx, waiting on (x, ctx)
      relation var_read(Sym, SCtx, E, SAddrK);
      /// flat-closure copy edge: address (fv, from) flows to (fv, to)
      relation copy_edge(Sym, SCtx, SCtx);

      // injection of the top expression
      state_e(top.clone(), empty.clone(), SAddrK { e: top.clone(), ctx: empty.clone() }),
      peek_ctx(top.clone(), empty.clone(), sextend(top, &empty, m)),
      stored_kont(SAddrK { e: top.clone(), ctx: empty.clone() }, SKont::MT) <--
         top_expr(top);

      // peek_ctx: contexts are created only at binding forms
      peek_ctx(e.clone(), old.clone(), sextend(e, old, m)) <--
         state_e(e, old, _),
         if matches!(&e.expr, Expr::App(..) | Expr::Let(..) | Expr::Callcc(..) | Expr::Lam(..));

      // copy_ctx, split into a binary join via copy_edge
      copy_edge(fv.clone(), from.clone(), to.clone()) <--
         copy_ctx(from, to, e),
         for fv in fvs.get(e).unwrap().iter();

      stored_val(fv.clone(), to.clone(), v.clone()) <--
         copy_edge(fv, from, to),
         stored_val(fv, from, v);

      // E-If (delta = state_e; the syntax match is a guard on the same atom)
      state_e(eg.clone(), ctx.clone(), SAddrK { e: eg.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: eg.clone(), ctx: ctx.clone() },
                  SKont::If { true_branch: et.clone(), false_branch: ef.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), eg.clone()) <--
         state_e(e, ctx, ak), if let Expr::If(eg, et, ef) = &e.expr;

      // E-C/cc (binary state_e ⋈ peek_ctx join; pattern moved after)
      state_e(elam.clone(), ctx.clone(), SAddrK { e: elam.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: elam.clone(), ctx: ctx.clone() },
                  SKont::Callcc { ectx: ectx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), elam.clone()) <--
         state_e(e, ctx, ak), peek_ctx(e, ctx, ectx), if let Expr::Callcc(elam) = &e.expr;

      // E-Set!
      state_e(esub.clone(), ctx.clone(), SAddrK { e: esub.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: esub.clone(), ctx: ctx.clone() },
                  SKont::Set { loc: SAddrV { x: x.clone(), ctx: ctx.clone() }, next_ak: ak.clone() }),
      flow_ee(e.clone(), esub.clone()) <--
         state_e(e, ctx, ak), if let Expr::Set(x, esub) = &e.expr;

      // E-Call (binary state_e ⋈ peek_ctx join; pattern moved after)
      state_e(efunc.clone(), ctx.clone(), SAddrK { e: efunc.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: efunc.clone(), ctx: ctx.clone() },
                  SKont::Arg { args: eargs.clone(), ctx: ctx.clone(), ectx: ectx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), efunc.clone()) <--
         state_e(e, ctx, ak), peek_ctx(e, ctx, ectx), if let Expr::App(efunc, eargs) = &e.expr;

      // E-Let (binary state_e ⋈ peek_ctx join; pattern and binding loop after)
      state_e(ebnd.clone(), ctx.clone(), SAddrK { e: ebnd.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: ebnd.clone(), ctx: ctx.clone() },
                  SKont::Let { av: SAddrV { x: x.clone(), ctx: ectx.clone() }, ebody: ebody.clone(), ctx: ectx.clone(), next_ak: ak.clone() }),
      copy_ctx(ctx.clone(), ectx.clone(), e.clone()),
      flow_ee(e.clone(), ebnd.clone()) <--
         state_e(e, ctx, ak),
         peek_ctx(e, ctx, ectx),
         if let Expr::Let(binds, ebody) = &e.expr,
         for (x, ebnd) in binds.iter();

      // E-Prim
      state_e(e0.clone(), ctx.clone(), SAddrK { e: e0.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: e0.clone(), ctx: ctx.clone() },
                  SKont::Prim1 { op: op.clone(), e2: e1.clone(), ctx: ctx.clone(), next_ak: ak.clone() }),
      flow_ee(e.clone(), e0.clone()) <--
         state_e(e, ctx, ak), if let Expr::Prim(op, e0, e1) = &e.expr;

      // atomic evaluation
      state_a(SValue::Number(*n), ak.clone()),
      flow_ea(e.clone(), SValue::Number(*n)) <--
         state_e(e, _, ak), if let Expr::Num(n) = &e.expr;

      state_a(SValue::Bool(b.clone()), ak.clone()),
      flow_ea(e.clone(), SValue::Bool(b.clone())) <--
         state_e(e, _, ak), if let Expr::Bool(b) = &e.expr;

      state_a(SValue::Closure { e: e.clone(), ctx: ctx.clone() }, ak.clone()),
      flow_ea(e.clone(), SValue::Closure { e: e.clone(), ctx: ctx.clone() }) <--
         state_e(e, ctx, ak), if matches!(&e.expr, Expr::Lam(..));

      // E-AE for variables, split into a binary join via var_read
      var_read(x.clone(), ctx.clone(), e.clone(), ak.clone()) <--
         state_e(e, ctx, ak), if let Expr::Var(x) = &e.expr;

      state_a(v.clone(), ak.clone()),
      flow_ea(e.clone(), v.clone()) <--
         var_read(x, ctx, e, ak),
         stored_val(x, ctx, v);

      // A-IfT (guard AFTER the join, so the join is simple & reorderable)
      state_e(et.clone(), ctx_k.clone(), next_ak.clone()),
      flow_ae(SValue::Bool(tt()), et.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::If { true_branch: et, ctx: ctx_k, next_ak, .. }),
         if sif_true(v);

      // A-IfF (pattern AFTER the join)
      state_e(ef.clone(), ctx_k.clone(), next_ak.clone()),
      flow_ae(SValue::Bool(ff()), ef.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::If { false_branch: ef, ctx: ctx_k, next_ak, .. }),
         if let SValue::Bool(b) = v, if b.as_ref() == "#f";

      // A-C/cc (closure pattern AFTER the join)
      state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
      stored_val(x.clone(), ectx.clone(), SValue::Kont(ak.clone())),
      copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
      flow_ae(v.clone(), ebody.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Callcc { ectx, next_ak }),
         if let SValue::Closure { e: elam, ctx: ctx_clo } = v,
         if let Expr::Lam(params, ebody) = &elam.expr,
         if !params.is_empty(),
         let x = params[0].clone();

      // A-C/ccKont (kont pattern AFTER the join)
      state_a(SValue::Kont(ak.clone()), bk.clone()),
      flow_aa(SValue::Kont(bk.clone()), SValue::Kont(ak.clone())) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Callcc { .. }),
         if let SValue::Kont(bk) = v;

      // A-Ar
      state_e(earg.clone(), ctx.clone(), SAddrK { e: earg.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: earg.clone(), ctx: ctx.clone() },
                  SKont::Fn { func: v.clone(), pos: pos as i64, ctx: ectx.clone(), next_ak: next_ak.clone() }),
      flow_ae(v.clone(), earg.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Arg { args, ctx, ectx, next_ak }),
         for (pos, earg) in args.iter().enumerate();

      // A-Call (closure)
      state_e(ebody.clone(), ectx.clone(), next_ak.clone()),
      stored_val(x.clone(), ectx.clone(), v.clone()),
      copy_ctx(ctx_clo.clone(), ectx.clone(), elam.clone()),
      flow_ae(v.clone(), ebody.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Fn { func: SValue::Closure { e: elam, ctx: ctx_clo }, pos, ctx: ectx, next_ak }),
         if let Expr::Lam(params, ebody) = &elam.expr,
         if (*pos as usize) < params.len(),
         let x = params[*pos as usize].clone();

      // A-Call (captured continuation as operator)
      state_a(v.clone(), callcc_kont.clone()),
      flow_aa(v.clone(), v.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Fn { func: SValue::Kont(callcc_kont), pos: 0, .. });

      // A-Let
      state_e(ebody.clone(), ctx.clone(), next_ak.clone()),
      stored_val(av.x.clone(), av.ctx.clone(), v.clone()),
      flow_ae(v.clone(), ebody.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Let { av, ebody, ctx, next_ak });

      // A-Prim1
      state_e(earg1.clone(), ctx.clone(), SAddrK { e: earg1.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: earg1.clone(), ctx: ctx.clone() },
                  SKont::Prim2 { op: op.clone(), v1: v.clone(), next_ak: next_ak.clone() }),
      flow_ae(v.clone(), earg1.clone()) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Prim1 { op, e2: earg1, ctx, next_ak });

      // A-Prim2
      state_a(SValue::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }, next_ak.clone()),
      flow_aa(v2.clone(), SValue::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v2.clone()) }) <--
         state_a(v2, ak),
         stored_kont(ak, ?SKont::Prim2 { op, v1, next_ak });

      // A-Set!
      state_a(SValue::Number(-42), next_ak.clone()),
      stored_val(loc.x.clone(), loc.ctx.clone(), v.clone()),
      flow_aa(v.clone(), SValue::Number(-42)) <--
         state_a(v, ak),
         stored_kont(ak, ?SKont::Set { loc, next_ak });
   };

   StructuredStats {
      m,
      state_e: prog.state_e.len(),
      state_a: prog.state_a.len(),
      stored_val: prog.stored_val.len(),
      stored_kont: prog.stored_kont.len(),
      flow_ee: prog.flow_ee.len(),
      flow_ea: prog.flow_ea.len(),
      flow_ae: prog.flow_ae.len(),
      flow_aa: prog.flow_aa.len(),
      peek_ctx: prog.peek_ctx.len(),
      copy_ctx: prog.copy_ctx.len(),
   }
}
