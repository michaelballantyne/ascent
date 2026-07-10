//! **Variation: no Datalog.** The same `m`-CFA as a hand-written abstract
//! machine.
//!
//! The Datalog program *is* an abstract machine in disguise: `state_e` and
//! `state_a` are its configurations, `stored_val`/`stored_kont` its (globally
//! widened) stores, and each rule one case of the transition relation. This
//! module implements that machine directly, in textbook AAM style (Van Horn &
//! Might):
//!
//! * a [`State`] is an eval configuration ⟨e, ctx, aκ⟩ or an apply
//!   configuration ⟨v, aκ⟩;
//! * [`Machine::step`] maps a state to its successors — one `match` arm per
//!   operational-semantics rule, carrying the same rule names as the Ascent
//!   version;
//! * a worklist drives the machine to its least fixpoint.
//!
//! The only part that is not textbook small-step is forced by the *global*
//! store: a step that reads a store address is stale — and must be re-run — if
//! that address later grows. The engine therefore records, per address, the
//! states whose step read it, and a write that enlarges an address re-enqueues
//! its readers: chaotic iteration with dependency tracking. This bookkeeping is
//! exactly what Datalog's semi-naive evaluation provides for free; here it is
//! the whole of the hand-rolled engine ([`Machine::vals_at`]/[`konts_at`] to
//! read, [`write_v`]/[`write_k`] to join, ~40 lines).
//!
//! Two pieces of classic worklist folklore matter enormously: the queue is
//! **FIFO** and **deduplicated** (a state woken many times before it runs
//! steps once, over the whole batch of what arrived — [`Machine::enqueue`]).
//! A re-stepped state re-scans its full fan-in, so without batching the
//! re-scans are quadratic in fan-in: this same engine with a plain LIFO `Vec`
//! and eager wakes runs the `N=10 K=3` benchmark in 83 s instead of 0.8 s.
//! The work-set is the hand-rolled stand-in for processing only the delta.
//!
//! Re-running readers also subsumes the Datalog `copy_ctx` relation. There, a
//! flat-closure copy is a *standing* subscription — `stored_val(x, to) ⊇
//! stored_val(x, from)`, forever. Here the copy happens inside the step of the
//! state that applies the closure, and that state re-fires whenever a source
//! address grows, re-performing the copy over the fuller set.
//!
//! Everything else is shared with the structured Ascent variant: the labelled
//! syntax ([`E`]), the abstract domains (re-exported minus the `S` prefix), and
//! the paper's quirky `freevar` function. The two engines are therefore
//! *content*-comparable, and `tests/aam_check.rs` checks they derive identical
//! relations — states, stores, and flow graph — on both labelings, at
//! `m ∈ {0,1,2}`.
//!
//! [`konts_at`]: Machine::konts_at
//! [`write_v`]: Machine::write_v
//! [`write_k`]: Machine::write_k

use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use crate::ast::Sym;
use crate::structured::free_vars;
pub use crate::structured::{E, Expr, SAddrK as AddrK, SAddrV as AddrV, SCtx as Ctx, SKont as Kont, SValue as Value};
use crate::{ff, tt};

/// A machine state ς.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum State {
   /// ⟨e, ctx, aκ⟩ — evaluate `e` in context `ctx`, continuation at `aκ`.
   Eval(E, Ctx, AddrK),
   /// ⟨v, aκ⟩ — return the value `v` to the continuations stored at `aκ`.
   Apply(Value, AddrK),
}

/// The flow graph the analysis reports — the Datalog version's four `flow_*`
/// output relations.
#[derive(Default)]
pub struct Flows {
   pub ee: HashSet<(E, E)>,
   pub ea: HashSet<(E, Value)>,
   pub ae: HashSet<(Value, E)>,
   pub aa: HashSet<(Value, Value)>,
}

pub struct Machine {
   /// Contour length `m`.
   m: usize,
   /// Free variables of every subexpression (the paper's `freevar`).
   fvs: HashMap<E, Rc<Vec<Sym>>>,

   /// σ̂ᵥ — the widened value store.
   pub store_v: HashMap<AddrV, HashSet<Value>>,
   /// σ̂κ — the widened continuation store.
   pub store_k: HashMap<AddrK, HashSet<Kont>>,
   /// Every state reached.
   pub seen: HashSet<State>,
   /// The reported flow edges.
   pub flows: Flows,
   /// `step` executions: first visits plus dependency-triggered re-runs.
   pub steps: usize,

   /// The work-set: FIFO queue of states to (re-)step, deduplicated by
   /// `pending` — a state woken many times before it is popped steps once.
   todo: VecDeque<State>,
   pending: HashSet<State>,
   readers_v: HashMap<AddrV, HashSet<State>>,
   readers_k: HashMap<AddrK, HashSet<State>>,
}

impl Machine {
   /// Run the machine from `top` to its least fixpoint.
   pub fn run(top: &E, m: usize) -> Machine {
      let mut fvs = HashMap::new();
      free_vars(top, &mut fvs);
      let mut mach = Machine {
         m,
         fvs,
         store_v: HashMap::new(),
         store_k: HashMap::new(),
         seen: HashSet::new(),
         flows: Flows::default(),
         steps: 0,
         todo: VecDeque::new(),
         pending: HashSet::new(),
         readers_v: HashMap::new(),
         readers_k: HashMap::new(),
      };

      // Î: inject ⟨top, ε, a₀⟩ with σ̂κ(a₀) = {MT}.
      let a0 = AddrK { e: top.clone(), ctx: Ctx(Vec::new()) };
      mach.write_k(a0.clone(), Kont::MT);
      mach.reach(State::Eval(top.clone(), Ctx(Vec::new()), a0));

      while let Some(s) = mach.todo.pop_front() {
         mach.pending.remove(&s);
         mach.steps += 1;
         mach.step(&s);
      }
      mach
   }

   /// The transition relation, ς ↦ {ς′, …}.
   fn step(&mut self, s: &State) {
      match s {
         State::Eval(e, ctx, ak) => self.eval(s, e, ctx, ak),
         // An apply state steps once against each continuation at its address.
         State::Apply(v, ak) =>
            for kont in self.konts_at(s, ak) {
               self.apply(s, v, ak, &kont);
            },
      }
   }

   /// Eval transitions ⟨e, ctx, aκ⟩ ↦ …, one arm per syntactic form.
   fn eval(&mut self, s: &State, e: &E, ctx: &Ctx, ak: &AddrK) {
      match &e.expr {
         // E-AE: atomic expressions step straight to an apply state.
         Expr::Num(n) => self.value(e, Value::Number(*n), ak),
         Expr::Bool(b) => self.value(e, Value::Bool(b.clone()), ak),
         Expr::Lam(..) => self.value(e, Value::Closure { e: e.clone(), ctx: ctx.clone() }, ak),
         Expr::Var(x) =>
            for v in self.vals_at(s, &AddrV { x: x.clone(), ctx: ctx.clone() }) {
               self.value(e, v, ak);
            },

         // E-If: evaluate the guard, remembering the branches.
         Expr::If(eg, et, ef) => self.eval_within(e, eg, ctx, Kont::If {
            true_branch: et.clone(),
            false_branch: ef.clone(),
            ctx: ctx.clone(),
            next_ak: ak.clone(),
         }),

         // E-Call: evaluate the operator, remembering the arguments and the
         // callee context ⌊e ∷ ctx⌋ₘ.
         Expr::App(efunc, eargs) => {
            let ectx = self.extend(e, ctx);
            self.eval_within(e, efunc, ctx, Kont::Arg {
               args: eargs.clone(),
               ctx: ctx.clone(),
               ectx,
               next_ak: ak.clone(),
            });
         },

         // E-Let: evaluate every binding; the body's context is ⌊e ∷ ctx⌋ₘ,
         // into which the let's free variables are copied.
         Expr::Let(binds, ebody) => {
            let ectx = self.extend(e, ctx);
            self.copy(s, ctx, &ectx, e);
            for (x, ebnd) in binds {
               self.eval_within(e, ebnd, ctx, Kont::Let {
                  av: AddrV { x: x.clone(), ctx: ectx.clone() },
                  ebody: ebody.clone(),
                  ctx: ectx.clone(),
                  next_ak: ak.clone(),
               });
            }
         },

         // E-Set!: evaluate the right-hand side, remembering the location.
         Expr::Set(x, esub) => self.eval_within(e, esub, ctx, Kont::Set {
            loc: AddrV { x: x.clone(), ctx: ctx.clone() },
            next_ak: ak.clone(),
         }),

         // E-C/cc: evaluate the receiver.
         Expr::Callcc(elam) => {
            let ectx = self.extend(e, ctx);
            self.eval_within(e, elam, ctx, Kont::Callcc { ectx, next_ak: ak.clone() });
         },

         // E-Prim: evaluate the first operand.
         Expr::Prim(op, e0, e1) => self.eval_within(e, e0, ctx, Kont::Prim1 {
            op: op.clone(),
            e2: e1.clone(),
            ctx: ctx.clone(),
            next_ak: ak.clone(),
         }),
      }
   }

   /// Apply transitions ⟨v, aκ⟩ × κ ↦ …, one arm per continuation form.
   fn apply(&mut self, s: &State, v: &Value, ak: &AddrK, kont: &Kont) {
      match kont {
         Kont::MT => {},

         // A-Ar: the operator is evaluated; evaluate every argument, each
         // remembering the operator value and its own position.
         Kont::Arg { args, ctx, ectx, next_ak } =>
            for (pos, earg) in args.iter().enumerate() {
               self.flows.ae.insert((v.clone(), earg.clone()));
               self.eval_with(earg, ctx, Kont::Fn {
                  func: v.clone(),
                  pos: pos as i64,
                  ctx: ectx.clone(),
                  next_ak: next_ak.clone(),
               });
            },

         // A-Call: an argument is evaluated; bind it to the parameter at its
         // position and enter the body (closure operator) …
         Kont::Fn { func: Value::Closure { e: elam, ctx: ctx_clo }, pos, ctx: ectx, next_ak } => {
            if let Expr::Lam(params, ebody) = &elam.expr {
               if let Some(x) = params.get(*pos as usize) {
                  self.write_v(AddrV { x: x.clone(), ctx: ectx.clone() }, v.clone());
                  self.copy(s, ctx_clo, ectx, elam);
                  self.flows.ae.insert((v.clone(), ebody.clone()));
                  self.reach(State::Eval(ebody.clone(), ectx.clone(), next_ak.clone()));
               }
            }
         },
         // … or jump, if the operator is a captured continuation.
         Kont::Fn { func: Value::Kont(target), pos: 0, .. } => {
            self.flows.aa.insert((v.clone(), v.clone()));
            self.reach(State::Apply(v.clone(), target.clone()));
         },
         Kont::Fn { .. } => {},

         // A-IfT / A-IfF.
         Kont::If { true_branch, false_branch, ctx, next_ak } => {
            if truthy(v) {
               self.flows.ae.insert((Value::Bool(tt()), true_branch.clone()));
               self.reach(State::Eval(true_branch.clone(), ctx.clone(), next_ak.clone()));
            }
            if matches!(v, Value::Bool(b) if b.as_ref() == "#f") {
               self.flows.ae.insert((Value::Bool(ff()), false_branch.clone()));
               self.reach(State::Eval(false_branch.clone(), ctx.clone(), next_ak.clone()));
            }
         },

         // A-C/cc: apply the receiver to the captured continuation `aκ` …
         Kont::Callcc { ectx, next_ak } => match v {
            Value::Closure { e: elam, ctx: ctx_clo } =>
               if let Expr::Lam(params, ebody) = &elam.expr {
                  if let Some(x) = params.first() {
                     self.write_v(AddrV { x: x.clone(), ctx: ectx.clone() }, Value::Kont(ak.clone()));
                     self.copy(s, ctx_clo, ectx, elam);
                     self.flows.ae.insert((v.clone(), ebody.clone()));
                     self.reach(State::Eval(ebody.clone(), ectx.clone(), next_ak.clone()));
                  }
               },
            // … or, if the receiver is itself a continuation (A-C/ccKont).
            Value::Kont(bk) => {
               self.flows.aa.insert((Value::Kont(bk.clone()), Value::Kont(ak.clone())));
               self.reach(State::Apply(Value::Kont(ak.clone()), bk.clone()));
            },
            _ => {},
         },

         // A-Let: bind the let variable, evaluate the body.
         Kont::Let { av, ebody, ctx, next_ak } => {
            self.write_v(av.clone(), v.clone());
            self.flows.ae.insert((v.clone(), ebody.clone()));
            self.reach(State::Eval(ebody.clone(), ctx.clone(), next_ak.clone()));
         },

         // A-Set!: perform the mutation, produce the sentinel −42.
         Kont::Set { loc, next_ak } => {
            self.write_v(loc.clone(), v.clone());
            self.flows.aa.insert((v.clone(), Value::Number(-42)));
            self.reach(State::Apply(Value::Number(-42), next_ak.clone()));
         },

         // A-Prim1: first operand evaluated; evaluate the second.
         Kont::Prim1 { op, e2, ctx, next_ak } => {
            self.flows.ae.insert((v.clone(), e2.clone()));
            self.eval_with(e2, ctx, Kont::Prim2 { op: op.clone(), v1: v.clone(), next_ak: next_ak.clone() });
         },

         // A-Prim2: both operands evaluated; produce the symbolic result.
         Kont::Prim2 { op, v1, next_ak } => {
            let pv = Value::PrimVal { op: op.clone(), v1: Box::new(v1.clone()), v2: Box::new(v.clone()) };
            self.flows.aa.insert((v.clone(), pv.clone()));
            self.reach(State::Apply(pv, next_ak.clone()));
         },
      }
   }

   // ---------- the widened store, with dependency-tracked reads ----------

   /// Read σ̂ᵥ(a), recording that `reader`'s step depends on it.
   fn vals_at(&mut self, reader: &State, a: &AddrV) -> Vec<Value> {
      self.readers_v.entry(a.clone()).or_default().insert(reader.clone());
      self.store_v.get(a).into_iter().flatten().cloned().collect()
   }

   /// Read σ̂κ(aκ), recording that `reader`'s step depends on it.
   fn konts_at(&mut self, reader: &State, a: &AddrK) -> Vec<Kont> {
      self.readers_k.entry(a.clone()).or_default().insert(reader.clone());
      self.store_k.get(a).into_iter().flatten().cloned().collect()
   }

   /// Join `v` into σ̂ᵥ(a); if the address grew, its readers step again.
   fn write_v(&mut self, a: AddrV, v: Value) {
      if self.store_v.entry(a.clone()).or_default().insert(v) {
         for s in self.readers_v.get(&a).cloned().into_iter().flatten() {
            self.enqueue(s);
         }
      }
   }

   /// Join `κ` into σ̂κ(aκ); if the address grew, its readers step again.
   fn write_k(&mut self, a: AddrK, kont: Kont) {
      if self.store_k.entry(a.clone()).or_default().insert(kont) {
         for s in self.readers_k.get(&a).cloned().into_iter().flatten() {
            self.enqueue(s);
         }
      }
   }

   /// Mark a state reached; newly-seen states are scheduled to step.
   fn reach(&mut self, s: State) {
      if self.seen.insert(s.clone()) {
         self.enqueue(s);
      }
   }

   /// Schedule a state to (re-)step, unless it is already queued.
   fn enqueue(&mut self, s: State) {
      if self.pending.insert(s.clone()) {
         self.todo.push_back(s);
      }
   }

   // ---------- shared machinery of the E-rules ----------

   /// Atomic result: `e` evaluated to `v`; return it to `aκ`.
   fn value(&mut self, e: &E, v: Value, ak: &AddrK) {
      self.flows.ea.insert((e.clone(), v.clone()));
      self.reach(State::Apply(v, ak.clone()));
   }

   /// Evaluate `e` (in `ctx`) under continuation `kont`, allocated — as in the
   /// appendix — at the address aκ = ⟨e, ctx⟩.
   fn eval_with(&mut self, e: &E, ctx: &Ctx, kont: Kont) {
      let a = AddrK { e: e.clone(), ctx: ctx.clone() };
      self.write_k(a.clone(), kont);
      self.reach(State::Eval(e.clone(), ctx.clone(), a));
   }

   /// [`eval_with`](Machine::eval_with), recording the `flow_ee` edge from the
   /// enclosing expression.
   fn eval_within(&mut self, from: &E, e: &E, ctx: &Ctx, kont: Kont) {
      self.flows.ee.insert((from.clone(), e.clone()));
      self.eval_with(e, ctx, kont);
   }

   /// ⌊e ∷ ctx⌋ₘ — the context entered at binding site `e` (≈ new-hat).
   fn extend(&self, e: &E, ctx: &Ctx) -> Ctx {
      Ctx(std::iter::once(e).chain(ctx.0.iter()).take(self.m).cloned().collect())
   }

   /// Flat-closure copy (≈ copy-hat): σ̂ᵥ(x, to) ⊇ σ̂ᵥ(x, from) for every x free
   /// in `e`. The reads are recorded against the copying state `s`, so the copy
   /// re-fires whenever a source address grows — the direct-style counterpart
   /// of the Datalog version's standing `copy_ctx` subscription.
   fn copy(&mut self, s: &State, from: &Ctx, to: &Ctx, e: &E) {
      let fvs = self.fvs.get(e).expect("free_vars covers every subterm").clone();
      for x in fvs.iter() {
         for v in self.vals_at(s, &AddrV { x: x.clone(), ctx: from.clone() }) {
            self.write_v(AddrV { x: x.clone(), ctx: to.clone() }, v);
         }
      }
   }
}

/// The values the appendix's A-IfT rule treats as "true": anything but `#f` —
/// except `PrimVal`, which (faithfully to the paper) neither A-If rule handles.
fn truthy(v: &Value) -> bool {
   matches!(v, Value::Closure { .. } | Value::Number(_) | Value::Kont(_))
      || matches!(v, Value::Bool(b) if b.as_ref() == "#t")
}

/// Relation sizes from a direct-AAM run, comparable field-for-field with
/// [`crate::StructuredStats`].
#[derive(Clone, Debug, Default)]
pub struct AamStats {
   pub m: usize,
   pub state_e: usize,
   pub state_a: usize,
   pub stored_val: usize,
   pub stored_kont: usize,
   pub flow_ee: usize,
   pub flow_ea: usize,
   pub flow_ae: usize,
   pub flow_aa: usize,
   /// `step` executions: first visits plus dependency-triggered re-runs.
   pub steps: usize,
}

impl AamStats {
   pub fn total_derived(&self) -> usize {
      self.state_e
         + self.state_a
         + self.stored_val
         + self.stored_kont
         + self.flow_ee
         + self.flow_ea
         + self.flow_ae
         + self.flow_aa
   }
}

/// Run the direct abstract machine and report relation sizes.
pub fn analyze_aam(top: &E, m: usize) -> AamStats {
   let mach = Machine::run(top, m);
   let state_e = mach.seen.iter().filter(|s| matches!(s, State::Eval(..))).count();
   AamStats {
      m,
      state_e,
      state_a: mach.seen.len() - state_e,
      stored_val: mach.store_v.values().map(HashSet::len).sum(),
      stored_kont: mach.store_k.values().map(HashSet::len).sum(),
      flow_ee: mach.flows.ee.len(),
      flow_ea: mach.flows.ea.len(),
      flow_ae: mach.flows.ae.len(),
      flow_aa: mach.flows.aa.len(),
      steps: mach.steps,
   }
}
