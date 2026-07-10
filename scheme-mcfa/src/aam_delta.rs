//! **Variation: no Datalog, delta-driven.** The same `m`-CFA as a hand-written
//! *event* worklist — semi-naive evaluation by hand.
//!
//! Where [`crate::aam`] is the textbook machine — a worklist of *states*, with
//! a state re-stepped (re-scanning its whole fan-in) whenever an address it
//! read grows — this engine's worklist carries *facts*: a new state, a new
//! store binding, a new continuation, a new copy edge. Each event is processed
//! exactly once, paired against the *already-known* facts on the other side of
//! its join through reverse dependency indices:
//!
//! * `var_reads`:  value address → the variable reads waiting on it,
//! * `applies_at`: continuation address → the values applied there,
//! * `copy_from`:  context → the outgoing flat-closure copy edges.
//!
//! A new value at an address meets only its waiting readers and copy edges; a
//! new continuation meets only the values already applied at its address —
//! never a re-scan. This is precisely the delta discipline of semi-naive
//! Datalog evaluation (and these three indices are exactly the intermediate
//! relations `var_read`/`copy_edge`/reader-states that the tuned Ascent port
//! materializes to make every rule variant delta-driven).
//!
//! Originally written over the flat id-relations; ported to the labelled
//! syntax ([`E`]) and shared abstract domains so all engines are
//! content-comparable — `tests/aam_check.rs` checks it derives relations
//! identical to the Datalog fixpoint, on both labelings, at `m ∈ {0,1,2}`.

use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use crate::aam::{AamStats, AddrK, AddrV, Ctx, E, Expr, Flows, Kont, Value};
use crate::ast::Sym;
use crate::structured::free_vars;
use crate::{ff, tt};

/// A derived fact, processed exactly once.
enum Event {
   Eval(E, Ctx, AddrK),
   Apply(Value, AddrK),
   Kont(AddrK, Kont),
   Val(AddrV, Value),
   Copy(Ctx, Ctx, E),
}

pub struct Delta {
   /// Contour length `m`.
   m: usize,
   /// Free variables of every subexpression (the paper's `freevar`).
   fvs: HashMap<E, Rc<Vec<Sym>>>,

   /// σ̂ᵥ — the widened value store.
   pub store_v: HashMap<AddrV, HashSet<Value>>,
   /// σ̂κ — the widened continuation store.
   pub store_k: HashMap<AddrK, HashSet<Kont>>,
   /// Eval states reached.
   pub evals: HashSet<(E, Ctx, AddrK)>,
   /// Apply states reached.
   pub applies: HashSet<(Value, AddrK)>,
   /// The reported flow edges.
   pub flows: Flows,
   /// Events processed (each derived fact exactly once).
   pub events: usize,

   copies: HashSet<(Ctx, Ctx, E)>,

   // Reverse dependency indices: each new fact meets only its counterparts.
   var_reads: HashMap<AddrV, Vec<(E, AddrK)>>,
   applies_at: HashMap<AddrK, Vec<Value>>,
   copy_from: HashMap<Ctx, Vec<(Ctx, E)>>,

   wl: VecDeque<Event>,
}

impl Delta {
   /// Run the machine from `top` to its least fixpoint.
   pub fn run(top: &E, m: usize) -> Delta {
      let mut fvs = HashMap::new();
      free_vars(top, &mut fvs);
      let mut d = Delta {
         m,
         fvs,
         store_v: HashMap::new(),
         store_k: HashMap::new(),
         evals: HashSet::new(),
         applies: HashSet::new(),
         flows: Flows::default(),
         events: 0,
         copies: HashSet::new(),
         var_reads: HashMap::new(),
         applies_at: HashMap::new(),
         copy_from: HashMap::new(),
         wl: VecDeque::new(),
      };

      // Î: inject ⟨top, ε, a₀⟩ with σ̂κ(a₀) = {MT}.
      let empty = Ctx(Vec::new());
      let a0 = AddrK { e: top.clone(), ctx: empty.clone() };
      d.push_kont(a0.clone(), Kont::MT);
      d.push_eval(top.clone(), empty, a0);

      while let Some(ev) = d.wl.pop_front() {
         d.events += 1;
         match ev {
            Event::Eval(e, ctx, ak) => d.eval(e, ctx, ak),

            // A new apply state meets every continuation already stored at its
            // address (and registers, so future continuations meet it).
            Event::Apply(v, ak) => {
               d.applies_at.entry(ak.clone()).or_default().push(v.clone());
               let konts: Vec<Kont> = d.store_k.get(&ak).map(|s| s.iter().cloned().collect()).unwrap_or_default();
               for k in konts {
                  d.apply(&v, &ak, &k);
               }
            },

            // A new continuation meets every value already applied at its address.
            Event::Kont(ak, k) => {
               let vs: Vec<Value> = d.applies_at.get(&ak).cloned().unwrap_or_default();
               for v in vs {
                  d.apply(&v, &ak, &k);
               }
            },

            // A new store binding meets the variable reads waiting on its
            // address, and flows along the copy edges out of its context.
            Event::Val(a, v) => {
               let readers: Vec<(E, AddrK)> = d.var_reads.get(&a).cloned().unwrap_or_default();
               for (e, ak) in readers {
                  d.flows.ea.insert((e, v.clone()));
                  d.push_apply(v.clone(), ak);
               }
               let edges: Vec<(Ctx, E)> = d.copy_from.get(&a.ctx).cloned().unwrap_or_default();
               for (to, e) in edges {
                  if d.fvs[&e].contains(&a.x) {
                     d.push_val(AddrV { x: a.x.clone(), ctx: to }, v.clone());
                  }
               }
            },

            // A new copy edge copies what its source addresses already hold
            // (and registers, so future bindings flow across it).
            Event::Copy(from, to, e) => {
               d.copy_from.entry(from.clone()).or_default().push((to.clone(), e.clone()));
               let fvs = d.fvs[&e].clone();
               for fv in fvs.iter() {
                  let src = AddrV { x: fv.clone(), ctx: from.clone() };
                  let vals: Vec<Value> = d.store_v.get(&src).map(|s| s.iter().cloned().collect()).unwrap_or_default();
                  for v in vals {
                     d.push_val(AddrV { x: fv.clone(), ctx: to.clone() }, v);
                  }
               }
            },
         }
      }
      d
   }

   /// Eval transitions ⟨e, ctx, aκ⟩ ↦ …, one arm per syntactic form.
   fn eval(&mut self, e: E, ctx: Ctx, ak: AddrK) {
      match &e.expr {
         // E-AE: atomics.
         Expr::Num(n) => {
            let v = Value::Number(*n);
            self.flows.ea.insert((e, v.clone()));
            self.push_apply(v, ak);
         },
         Expr::Bool(b) => {
            let v = Value::Bool(b.clone());
            self.flows.ea.insert((e, v.clone()));
            self.push_apply(v, ak);
         },
         Expr::Lam(..) => {
            let v = Value::Closure { e: e.clone(), ctx };
            self.flows.ea.insert((e, v.clone()));
            self.push_apply(v, ak);
         },
         Expr::Var(x) => {
            let a = AddrV { x: x.clone(), ctx };
            self.var_reads.entry(a.clone()).or_default().push((e.clone(), ak.clone()));
            let vals: Vec<Value> = self.store_v.get(&a).map(|s| s.iter().cloned().collect()).unwrap_or_default();
            for v in vals {
               self.flows.ea.insert((e.clone(), v.clone()));
               self.push_apply(v, ak.clone());
            }
         },

         // E-If.
         Expr::If(eg, et, ef) => {
            let a2 = AddrK { e: eg.clone(), ctx: ctx.clone() };
            self.push_kont(a2.clone(), Kont::If {
               true_branch: et.clone(),
               false_branch: ef.clone(),
               ctx: ctx.clone(),
               next_ak: ak,
            });
            self.flows.ee.insert((e.clone(), eg.clone()));
            self.push_eval(eg.clone(), ctx, a2);
         },

         // E-C/cc.
         Expr::Callcc(elam) => {
            let ectx = self.extend(&e, &ctx);
            let a2 = AddrK { e: elam.clone(), ctx: ctx.clone() };
            self.push_kont(a2.clone(), Kont::Callcc { ectx, next_ak: ak });
            self.flows.ee.insert((e.clone(), elam.clone()));
            self.push_eval(elam.clone(), ctx, a2);
         },

         // E-Set!.
         Expr::Set(x, esub) => {
            let a2 = AddrK { e: esub.clone(), ctx: ctx.clone() };
            self.push_kont(a2.clone(), Kont::Set { loc: AddrV { x: x.clone(), ctx: ctx.clone() }, next_ak: ak });
            self.flows.ee.insert((e.clone(), esub.clone()));
            self.push_eval(esub.clone(), ctx, a2);
         },

         // E-Call.
         Expr::App(efunc, eargs) => {
            let ectx = self.extend(&e, &ctx);
            let a2 = AddrK { e: efunc.clone(), ctx: ctx.clone() };
            self.push_kont(a2.clone(), Kont::Arg { args: eargs.clone(), ctx: ctx.clone(), ectx, next_ak: ak });
            self.flows.ee.insert((e.clone(), efunc.clone()));
            self.push_eval(efunc.clone(), ctx, a2);
         },

         // E-Let.
         Expr::Let(binds, ebody) => {
            let ectx = self.extend(&e, &ctx);
            self.push_copy(ctx.clone(), ectx.clone(), e.clone());
            for (x, ebnd) in binds {
               let a2 = AddrK { e: ebnd.clone(), ctx: ctx.clone() };
               self.push_kont(a2.clone(), Kont::Let {
                  av: AddrV { x: x.clone(), ctx: ectx.clone() },
                  ebody: ebody.clone(),
                  ctx: ectx.clone(),
                  next_ak: ak.clone(),
               });
               self.flows.ee.insert((e.clone(), ebnd.clone()));
               self.push_eval(ebnd.clone(), ctx.clone(), a2);
            }
         },

         // E-Prim.
         Expr::Prim(op, e0, e1) => {
            let a2 = AddrK { e: e0.clone(), ctx: ctx.clone() };
            self.push_kont(a2.clone(), Kont::Prim1 { op: op.clone(), e2: e1.clone(), ctx: ctx.clone(), next_ak: ak });
            self.flows.ee.insert((e.clone(), e0.clone()));
            self.push_eval(e0.clone(), ctx, a2);
         },
      }
   }

   /// Apply transitions ⟨v, aκ⟩ × κ ↦ …, one arm per continuation form.
   fn apply(&mut self, v: &Value, ak: &AddrK, kont: &Kont) {
      match kont {
         Kont::MT => {},

         // A-Ar.
         Kont::Arg { args, ctx, ectx, next_ak } =>
            for (pos, earg) in args.iter().enumerate() {
               let a2 = AddrK { e: earg.clone(), ctx: ctx.clone() };
               self.push_kont(a2.clone(), Kont::Fn {
                  func: v.clone(),
                  pos: pos as i64,
                  ctx: ectx.clone(),
                  next_ak: next_ak.clone(),
               });
               self.flows.ae.insert((v.clone(), earg.clone()));
               self.push_eval(earg.clone(), ctx.clone(), a2);
            },

         // A-Call (closure) / A-Call (continuation as operator).
         Kont::Fn { func, pos, ctx: ectx, next_ak } => match func {
            Value::Closure { e: elam, ctx: ctx_clo } =>
               if let Expr::Lam(params, ebody) = &elam.expr {
                  if let Some(x) = params.get(*pos as usize) {
                     self.push_val(AddrV { x: x.clone(), ctx: ectx.clone() }, v.clone());
                     self.push_copy(ctx_clo.clone(), ectx.clone(), elam.clone());
                     self.flows.ae.insert((v.clone(), ebody.clone()));
                     self.push_eval(ebody.clone(), ectx.clone(), next_ak.clone());
                  }
               },
            Value::Kont(target) if *pos == 0 => {
               self.flows.aa.insert((v.clone(), v.clone()));
               self.push_apply(v.clone(), target.clone());
            },
            _ => {},
         },

         // A-IfT / A-IfF.
         Kont::If { true_branch, false_branch, ctx, next_ak } => {
            if truthy(v) {
               self.flows.ae.insert((Value::Bool(tt()), true_branch.clone()));
               self.push_eval(true_branch.clone(), ctx.clone(), next_ak.clone());
            }
            if matches!(v, Value::Bool(b) if b.as_ref() == "#f") {
               self.flows.ae.insert((Value::Bool(ff()), false_branch.clone()));
               self.push_eval(false_branch.clone(), ctx.clone(), next_ak.clone());
            }
         },

         // A-C/cc / A-C/ccKont.
         Kont::Callcc { ectx, next_ak } => match v {
            Value::Closure { e: elam, ctx: ctx_clo } =>
               if let Expr::Lam(params, ebody) = &elam.expr {
                  if let Some(x) = params.first() {
                     self.push_val(AddrV { x: x.clone(), ctx: ectx.clone() }, Value::Kont(ak.clone()));
                     self.push_copy(ctx_clo.clone(), ectx.clone(), elam.clone());
                     self.flows.ae.insert((v.clone(), ebody.clone()));
                     self.push_eval(ebody.clone(), ectx.clone(), next_ak.clone());
                  }
               },
            Value::Kont(bk) => {
               self.flows.aa.insert((Value::Kont(bk.clone()), Value::Kont(ak.clone())));
               self.push_apply(Value::Kont(ak.clone()), bk.clone());
            },
            _ => {},
         },

         // A-Let.
         Kont::Let { av, ebody, ctx, next_ak } => {
            self.push_val(av.clone(), v.clone());
            self.flows.ae.insert((v.clone(), ebody.clone()));
            self.push_eval(ebody.clone(), ctx.clone(), next_ak.clone());
         },

         // A-Set!.
         Kont::Set { loc, next_ak } => {
            self.push_val(loc.clone(), v.clone());
            self.flows.aa.insert((v.clone(), Value::Number(-42)));
            self.push_apply(Value::Number(-42), next_ak.clone());
         },

         // A-Prim1.
         Kont::Prim1 { op, e2, ctx, next_ak } => {
            let a2 = AddrK { e: e2.clone(), ctx: ctx.clone() };
            self.push_kont(a2.clone(), Kont::Prim2 { op: op.clone(), v1: v.clone(), next_ak: next_ak.clone() });
            self.flows.ae.insert((v.clone(), e2.clone()));
            self.push_eval(e2.clone(), ctx.clone(), a2);
         },

         // A-Prim2.
         Kont::Prim2 { op, v1, next_ak } => {
            let pv = Value::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v.clone()) };
            self.flows.aa.insert((v.clone(), pv.clone()));
            self.push_apply(pv, next_ak.clone());
         },
      }
   }

   // ---------- fact constructors: dedup, then queue exactly once ----------

   fn push_eval(&mut self, e: E, ctx: Ctx, ak: AddrK) {
      if self.evals.insert((e.clone(), ctx.clone(), ak.clone())) {
         self.wl.push_back(Event::Eval(e, ctx, ak));
      }
   }
   fn push_apply(&mut self, v: Value, ak: AddrK) {
      if self.applies.insert((v.clone(), ak.clone())) {
         self.wl.push_back(Event::Apply(v, ak));
      }
   }
   fn push_kont(&mut self, ak: AddrK, k: Kont) {
      if self.store_k.entry(ak.clone()).or_default().insert(k.clone()) {
         self.wl.push_back(Event::Kont(ak, k));
      }
   }
   fn push_val(&mut self, a: AddrV, v: Value) {
      if self.store_v.entry(a.clone()).or_default().insert(v.clone()) {
         self.wl.push_back(Event::Val(a, v));
      }
   }
   fn push_copy(&mut self, from: Ctx, to: Ctx, e: E) {
      if self.copies.insert((from.clone(), to.clone(), e.clone())) {
         self.wl.push_back(Event::Copy(from, to, e));
      }
   }

   /// ⌊e ∷ ctx⌋ₘ — the context entered at binding site `e` (≈ new-hat).
   fn extend(&self, e: &E, ctx: &Ctx) -> Ctx {
      Ctx(std::iter::once(e).chain(ctx.0.iter()).take(self.m).cloned().collect())
   }
}

/// The values the appendix's A-IfT rule treats as "true" (see [`crate::aam`]).
fn truthy(v: &Value) -> bool {
   matches!(v, Value::Closure { .. } | Value::Number(_) | Value::Kont(_))
      || matches!(v, Value::Bool(b) if b.as_ref() == "#t")
}

/// Run the delta-driven machine and report relation sizes. `steps` counts
/// events (each derived fact processed exactly once).
pub fn analyze_aam_delta(top: &E, m: usize) -> AamStats {
   let d = Delta::run(top, m);
   AamStats {
      m,
      state_e: d.evals.len(),
      state_a: d.applies.len(),
      stored_val: d.store_v.values().map(HashSet::len).sum(),
      stored_kont: d.store_k.values().map(HashSet::len).sum(),
      flow_ee: d.flows.ee.len(),
      flow_ea: d.flows.ea.len(),
      flow_ae: d.flows.ae.len(),
      flow_aa: d.flows.aa.len(),
      steps: d.events,
   }
}
