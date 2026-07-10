//! **Variation: a Datalog/Rust hybrid.** Ascent is used *only* for the joins
//! that need incremental evaluation; ordinary Rust does all the stepping.
//!
//! The observation (see the README's engine comparison): the analysis contains
//! exactly three joins in which **both sides grow** during the fixpoint —
//!
//! 1. returning values to continuations: `state_a(v, aκ) ⋈ stored_kont(aκ, κ)`,
//! 2. variable reads:                    `var_read(x, ctx, ·) ⋈ stored_val(x, ctx, v)`,
//! 3. flat-closure copies:               `copy_edge(x, from, to) ⋈ stored_val(x, from, v)`.
//!
//! Those are what semi-naive evaluation is *for*, and they stay as Ascent
//! rules. Everything else — dispatching on syntax, allocating continuations,
//! extending contexts, expanding free variables — is a pure function of a
//! single fact, so it is written as ordinary Rust ([`eval_step`]/[`apply_step`],
//! mirroring [`crate::aam`]'s machine arm-for-arm) and invoked from rules that
//! fan its output into the relations.
//!
//! Compared to the tuned Datalog ports this collapses the ~20 per-rule case
//! analyses into two `match` functions (the join over `stored_kont` is written
//! once per output *shape*, not once per continuation variant), and drops the
//! memoized `peek_ctx`/`copy_ctx` relations entirely — contexts are recomputed
//! and free variables re-expanded on each call: the "re-execute cheap pure
//! work instead of materializing it" trade the hand-written machines make.
//!
//! One Ascent-shaped wrinkle: a rule's heads all fire once per body binding,
//! so output families of *different cardinality* (one call produces two
//! successor states but three copy edges) cannot share a rule. The step
//! functions therefore group their outputs into 1:1 families (a successor
//! eval state zips with its continuation and its flow edge; a returned value
//! zips with its `flow_aa` edge), each family driven by one multi-head rule.
//! The join is still enumerated once per family — the price of not
//! materializing the (v, κ) pairs as an intermediate relation.
//!
//! `tests/hybrid_check.rs` asserts it computes the identical analysis to the
//! structured port, on both labelings, at `m ∈ {0,1,2}`.

use std::collections::HashMap;
use std::rc::Rc;

use ascent::ascent_run;

use crate::ast::Sym;
use crate::structured::{E, Expr, SAddrK, SAddrV, SCtx, SKont, SValue, StructuredStats, free_vars, sextend, sif_true};
use crate::{ff, tt};

/// Successors of an eval configuration ⟨e, ctx, aκ⟩, grouped in 1:1 families.
#[derive(Default)]
struct EvalOut {
   /// Sub-evaluations: `sub` evaluated (in the current ctx) under `kont`,
   /// allocated at ⟨sub, ctx⟩; each also yields `flow_ee(e, sub)`.
   sub_evals: Vec<(E, SKont)>,
   /// Atomic results: `e` evaluated to `v`, returned to `aκ`; each also
   /// yields `flow_ea(e, v)`.
   atomics: Vec<SValue>,
   /// Variable reads waiting on (x, ctx).
   var_read: Vec<Sym>,
   /// Flat-closure copy edges (x, from, to).
   copy_edge: Vec<(Sym, SCtx, SCtx)>,
}

/// Successors of an apply configuration ⟨v, aκ⟩ meeting κ, in 1:1 families.
/// (`Eq`/`Hash` so the memoizing variant can store it in a relation.)
#[derive(Default, PartialEq, Eq, Hash)]
pub struct ApplyOut {
   /// Sub-evaluations: `sub` evaluated in `ctx` under `kont` at ⟨sub, ctx⟩;
   /// each also yields `flow_ae(flow_v, sub)`.
   sub_evals: Vec<(E, SCtx, SKont, SValue)>,
   /// Control transfers into a body/branch: `state_e(e, ctx, aκ')` plus
   /// `flow_ae(flow_v, e)`.
   enters: Vec<(E, SCtx, SAddrK, SValue)>,
   /// Returned values: `state_a(v', aκ')` plus `flow_aa(src, v')`.
   returns: Vec<(SValue, SAddrK, SValue)>,
   /// Store writes (x, ctx, v).
   stored_val: Vec<(Sym, SCtx, SValue)>,
   /// Flat-closure copy edges (x, from, to).
   copy_edge: Vec<(Sym, SCtx, SCtx)>,
}

type Fvs = HashMap<E, Rc<Vec<Sym>>>;

fn copy_edges(out: &mut Vec<(Sym, SCtx, SCtx)>, fvs: &Fvs, e: &E, from: &SCtx, to: &SCtx) {
   for fv in fvs.get(e).expect("free_vars covers every subterm").iter() {
      out.push((fv.clone(), from.clone(), to.clone()));
   }
}

/// The eval transitions, one arm per syntactic form (same rule names as
/// [`crate::aam`]). A pure function of the configuration.
fn eval_step(e: &E, ctx: &SCtx, ak: &SAddrK, m: usize, fvs: &Fvs) -> EvalOut {
   let mut o = EvalOut::default();
   match &e.expr {
      // E-AE: atomics.
      Expr::Num(n) => o.atomics.push(SValue::Number(*n)),
      Expr::Bool(b) => o.atomics.push(SValue::Bool(b.clone())),
      Expr::Lam(..) => o.atomics.push(SValue::Closure { e: e.clone(), ctx: ctx.clone() }),
      Expr::Var(x) => o.var_read.push(x.clone()),

      // E-If.
      Expr::If(eg, et, ef) => o.sub_evals.push((eg.clone(), SKont::If {
         true_branch: et.clone(),
         false_branch: ef.clone(),
         ctx: ctx.clone(),
         next_ak: ak.clone(),
      })),

      // E-C/cc.
      Expr::Callcc(elam) => {
         let ectx = sextend(e, ctx, m);
         o.sub_evals.push((elam.clone(), SKont::Callcc { ectx, next_ak: ak.clone() }));
      },

      // E-Set!.
      Expr::Set(x, esub) => o
         .sub_evals
         .push((esub.clone(), SKont::Set { loc: SAddrV { x: x.clone(), ctx: ctx.clone() }, next_ak: ak.clone() })),

      // E-Call.
      Expr::App(efunc, eargs) => {
         let ectx = sextend(e, ctx, m);
         o.sub_evals.push((efunc.clone(), SKont::Arg {
            args: eargs.clone(),
            ctx: ctx.clone(),
            ectx,
            next_ak: ak.clone(),
         }));
      },

      // E-Let.
      Expr::Let(binds, ebody) => {
         let ectx = sextend(e, ctx, m);
         copy_edges(&mut o.copy_edge, fvs, e, ctx, &ectx);
         for (x, ebnd) in binds {
            o.sub_evals.push((ebnd.clone(), SKont::Let {
               av: SAddrV { x: x.clone(), ctx: ectx.clone() },
               ebody: ebody.clone(),
               ctx: ectx.clone(),
               next_ak: ak.clone(),
            }));
         }
      },

      // E-Prim.
      Expr::Prim(op, e0, e1) => o.sub_evals.push((e0.clone(), SKont::Prim1 {
         op: op.clone(),
         e2: e1.clone(),
         ctx: ctx.clone(),
         next_ak: ak.clone(),
      })),
   }
   o
}

/// The apply transitions, one arm per continuation form. The `state_a ⋈
/// stored_kont` join that *produces* the (v, κ) pairs stays in Ascent; this
/// pure function is the rest of each A-rule.
fn apply_step(v: &SValue, kont: &SKont, ak: &SAddrK, fvs: &Fvs) -> ApplyOut {
   let mut o = ApplyOut::default();
   // A-Call/A-C/cc shared tail: bind `x`, copy the closure's environment,
   // enter the body.
   let enter_closure =
      |o: &mut ApplyOut, x: &Sym, bound: SValue, elam: &E, ctx_clo: &SCtx, ectx: &SCtx, ebody: &E, next_ak: &SAddrK| {
         o.stored_val.push((x.clone(), ectx.clone(), bound));
         copy_edges(&mut o.copy_edge, fvs, elam, ctx_clo, ectx);
         o.enters.push((ebody.clone(), ectx.clone(), next_ak.clone(), v.clone()));
      };
   match kont {
      SKont::MT => {},

      // A-Ar.
      SKont::Arg { args, ctx, ectx, next_ak } =>
         for (pos, earg) in args.iter().enumerate() {
            o.sub_evals.push((
               earg.clone(),
               ctx.clone(),
               SKont::Fn { func: v.clone(), pos: pos as i64, ctx: ectx.clone(), next_ak: next_ak.clone() },
               v.clone(),
            ));
         },

      // A-Call (closure) / A-Call (captured continuation as operator).
      SKont::Fn { func, pos, ctx: ectx, next_ak } => match func {
         SValue::Closure { e: elam, ctx: ctx_clo } =>
            if let Expr::Lam(params, ebody) = &elam.expr {
               if let Some(x) = params.get(*pos as usize) {
                  enter_closure(&mut o, x, v.clone(), elam, ctx_clo, ectx, ebody, next_ak);
               }
            },
         SValue::Kont(target) if *pos == 0 => o.returns.push((v.clone(), target.clone(), v.clone())),
         _ => {},
      },

      // A-IfT / A-IfF.
      SKont::If { true_branch, false_branch, ctx, next_ak } => {
         if sif_true(v) {
            o.enters.push((true_branch.clone(), ctx.clone(), next_ak.clone(), SValue::Bool(tt())));
         }
         if matches!(v, SValue::Bool(b) if b.as_ref() == "#f") {
            o.enters.push((false_branch.clone(), ctx.clone(), next_ak.clone(), SValue::Bool(ff())));
         }
      },

      // A-C/cc / A-C/ccKont.
      SKont::Callcc { ectx, next_ak } => match v {
         SValue::Closure { e: elam, ctx: ctx_clo } =>
            if let Expr::Lam(params, ebody) = &elam.expr {
               if let Some(x) = params.first() {
                  enter_closure(&mut o, x, SValue::Kont(ak.clone()), elam, ctx_clo, ectx, ebody, next_ak);
               }
            },
         SValue::Kont(bk) => o.returns.push((SValue::Kont(ak.clone()), bk.clone(), SValue::Kont(bk.clone()))),
         _ => {},
      },

      // A-Let.
      SKont::Let { av, ebody, ctx, next_ak } => {
         o.stored_val.push((av.x.clone(), av.ctx.clone(), v.clone()));
         o.enters.push((ebody.clone(), ctx.clone(), next_ak.clone(), v.clone()));
      },

      // A-Set!.
      SKont::Set { loc, next_ak } => {
         o.stored_val.push((loc.x.clone(), loc.ctx.clone(), v.clone()));
         o.returns.push((SValue::Number(-42), next_ak.clone(), v.clone()));
      },

      // A-Prim1.
      SKont::Prim1 { op, e2, ctx, next_ak } => o.sub_evals.push((
         e2.clone(),
         ctx.clone(),
         SKont::Prim2 { op: op.clone(), v1: v.clone(), next_ak: next_ak.clone() },
         v.clone(),
      )),

      // A-Prim2.
      SKont::Prim2 { op, v1, next_ak } => {
         let pv = SValue::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v.clone()) };
         o.returns.push((pv, next_ak.clone(), v.clone()));
      },
   }
   o
}

/// Run the hybrid `m`-CFA: Rust step functions, Ascent for the three
/// both-sides-growing joins. Reports [`StructuredStats`]; `peek_ctx` is not
/// materialized (always 0) and `copy_ctx` reports the per-variable
/// `copy_edge` count instead of per-site `copy_ctx` facts.
pub fn analyze_structured_hybrid(top: &E, m: usize) -> StructuredStats {
   let empty = SCtx(Vec::new());
   let a0 = SAddrK { e: top.clone(), ctx: empty.clone() };

   // Precompute free variables (the only place the paper uses `freevar`).
   let mut cache: Fvs = HashMap::new();
   free_vars(top, &mut cache);
   let fvs = cache;

   let prog = ascent_run! {
      // Î: inject ⟨top, ε, a₀⟩ with σ̂κ(a₀) = {MT}.
      relation state_e(E, SCtx, SAddrK) = vec![(top.clone(), empty.clone(), a0.clone())];
      relation state_a(SValue, SAddrK);
      /// stored_val with the address flattened into columns: (x, ctx, v).
      relation stored_val(Sym, SCtx, SValue);
      relation stored_kont(SAddrK, SKont) = vec![(a0.clone(), SKont::MT)];
      /// variable occurrence e (naming x) evaluated in ctx, waiting on (x, ctx)
      relation var_read(Sym, SCtx, E, SAddrK);
      /// flat-closure copy edge: address (x, from) flows to (x, to)
      relation copy_edge(Sym, SCtx, SCtx);
      relation flow_ee(E, E);
      relation flow_ea(E, SValue);
      relation flow_ae(SValue, E);
      relation flow_aa(SValue, SValue);

      // ---- Rust does the stepping: eval transitions (single-atom rules) ----
      state_e(s.0.clone(), ctx.clone(), SAddrK { e: s.0.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: s.0.clone(), ctx: ctx.clone() }, s.1.clone()),
      flow_ee(e.clone(), s.0.clone()) <--
         state_e(e, ctx, ak), for s in eval_step(e, ctx, ak, m, &fvs).sub_evals;

      state_a(s.clone(), ak.clone()),
      flow_ea(e.clone(), s.clone()) <--
         state_e(e, ctx, ak), for s in eval_step(e, ctx, ak, m, &fvs).atomics;

      var_read(s.clone(), ctx.clone(), e.clone(), ak.clone()) <--
         state_e(e, ctx, ak), for s in eval_step(e, ctx, ak, m, &fvs).var_read;

      copy_edge(s.0, s.1, s.2) <--
         state_e(e, ctx, ak), for s in eval_step(e, ctx, ak, m, &fvs).copy_edge;

      // ---- Ascent does the joins: the three both-sides-growing joins ----

      // (1) Return values to continuations, then let Rust do the A-rule;
      //     one rule per 1:1 output family of `apply_step`.
      state_e(s.0.clone(), s.1.clone(), SAddrK { e: s.0.clone(), ctx: s.1.clone() }),
      stored_kont(SAddrK { e: s.0.clone(), ctx: s.1.clone() }, s.2.clone()),
      flow_ae(s.3.clone(), s.0.clone()) <--
         state_a(v, ak), stored_kont(ak, k), for s in apply_step(v, k, ak, &fvs).sub_evals;

      state_e(s.0.clone(), s.1.clone(), s.2.clone()),
      flow_ae(s.3.clone(), s.0.clone()) <--
         state_a(v, ak), stored_kont(ak, k), for s in apply_step(v, k, ak, &fvs).enters;

      state_a(s.0.clone(), s.1.clone()),
      flow_aa(s.2.clone(), s.0.clone()) <--
         state_a(v, ak), stored_kont(ak, k), for s in apply_step(v, k, ak, &fvs).returns;

      stored_val(s.0, s.1, s.2) <--
         state_a(v, ak), stored_kont(ak, k), for s in apply_step(v, k, ak, &fvs).stored_val;

      copy_edge(s.0, s.1, s.2) <--
         state_a(v, ak), stored_kont(ak, k), for s in apply_step(v, k, ak, &fvs).copy_edge;

      // (2) Variable reads (E-AE for variables).
      state_a(v.clone(), ak.clone()),
      flow_ea(e.clone(), v.clone()) <--
         var_read(x, ctx, e, ak),
         stored_val(x, ctx, v);

      // (3) Flat-closure copy propagation (≈ copy-hat).
      stored_val(fv.clone(), to.clone(), v.clone()) <--
         copy_edge(fv, from, to),
         stored_val(fv, from, v);
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
      peek_ctx: 0,
      copy_ctx: prog.copy_edge.len(),
   }
}

/// Like [`analyze_structured_hybrid`], but the `state_a ⋈ stored_kont` join is
/// enumerated — and `apply_step` executed — exactly **once** per (v, κ) pair:
/// the whole [`ApplyOut`] is materialized in an intermediate relation and the
/// per-family rules fan out from it with single-atom scans. This buys single
/// execution at the price Ascent's rule language exacts for it: one memoized
/// `ApplyOut` per pair, retained for the run — the same
/// re-execute-vs-materialize trade this crate keeps running into.
pub fn analyze_structured_hybrid_memo(top: &E, m: usize) -> StructuredStats {
   let empty = SCtx(Vec::new());
   let a0 = SAddrK { e: top.clone(), ctx: empty.clone() };

   let mut cache: Fvs = HashMap::new();
   free_vars(top, &mut cache);
   let fvs = cache;

   let prog = ascent_run! {
      relation state_e(E, SCtx, SAddrK) = vec![(top.clone(), empty.clone(), a0.clone())];
      relation state_a(SValue, SAddrK);
      relation stored_val(Sym, SCtx, SValue);
      relation stored_kont(SAddrK, SKont) = vec![(a0.clone(), SKont::MT)];
      relation var_read(Sym, SCtx, E, SAddrK);
      relation copy_edge(Sym, SCtx, SCtx);
      relation flow_ee(E, E);
      relation flow_ea(E, SValue);
      relation flow_ae(SValue, E);
      relation flow_aa(SValue, SValue);
      /// The memoized apply-step outputs, one per (v, κ) pair.
      relation apply_out(Rc<ApplyOut>);

      // ---- eval side: identical to `analyze_structured_hybrid` ----
      state_e(s.0.clone(), ctx.clone(), SAddrK { e: s.0.clone(), ctx: ctx.clone() }),
      stored_kont(SAddrK { e: s.0.clone(), ctx: ctx.clone() }, s.1.clone()),
      flow_ee(e.clone(), s.0.clone()) <--
         state_e(e, ctx, ak), for s in eval_step(e, ctx, ak, m, &fvs).sub_evals;

      state_a(s.clone(), ak.clone()),
      flow_ea(e.clone(), s.clone()) <--
         state_e(e, ctx, ak), for s in eval_step(e, ctx, ak, m, &fvs).atomics;

      var_read(s.clone(), ctx.clone(), e.clone(), ak.clone()) <--
         state_e(e, ctx, ak), for s in eval_step(e, ctx, ak, m, &fvs).var_read;

      copy_edge(s.0, s.1, s.2) <--
         state_e(e, ctx, ak), for s in eval_step(e, ctx, ak, m, &fvs).copy_edge;

      // ---- the apply join, enumerated once; outputs memoized ----
      apply_out(Rc::new(apply_step(v, k, ak, &fvs))) <--
         state_a(v, ak), stored_kont(ak, k);

      state_e(s.0.clone(), s.1.clone(), SAddrK { e: s.0.clone(), ctx: s.1.clone() }),
      stored_kont(SAddrK { e: s.0.clone(), ctx: s.1.clone() }, s.2.clone()),
      flow_ae(s.3.clone(), s.0.clone()) <--
         apply_out(o), for s in o.sub_evals.iter();

      state_e(s.0.clone(), s.1.clone(), s.2.clone()),
      flow_ae(s.3.clone(), s.0.clone()) <--
         apply_out(o), for s in o.enters.iter();

      state_a(s.0.clone(), s.1.clone()),
      flow_aa(s.2.clone(), s.0.clone()) <--
         apply_out(o), for s in o.returns.iter();

      stored_val(s.0.clone(), s.1.clone(), s.2.clone()) <--
         apply_out(o), for s in o.stored_val.iter();

      copy_edge(s.0.clone(), s.1.clone(), s.2.clone()) <--
         apply_out(o), for s in o.copy_edge.iter();

      // ---- the other two both-sides-growing joins ----
      state_a(v.clone(), ak.clone()),
      flow_ea(e.clone(), v.clone()) <--
         var_read(x, ctx, e, ak),
         stored_val(x, ctx, v);

      stored_val(fv.clone(), to.clone(), v.clone()) <--
         copy_edge(fv, from, to),
         stored_val(fv, from, v);
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
      peek_ctx: 0,
      copy_ctx: prog.copy_edge.len(),
   }
}
