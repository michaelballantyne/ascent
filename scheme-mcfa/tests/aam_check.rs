//! Both hand-written machines ([`scheme_mcfa::aam`] — the textbook step
//! machine — and [`scheme_mcfa::aam_delta`] — the event-driven delta worklist)
//! compute *exactly* the Datalog fixpoint: every relation — states, stores,
//! and flow graph — is content-identical to the structured Ascent run, on both
//! labelings, at several polyvariance levels.

use std::collections::HashSet;
use std::hash::Hash;

use scheme_mcfa::aam::{Flows, Machine, State};
use scheme_mcfa::aam_delta::Delta;
use scheme_mcfa::structured::{E, StructuredRun};
use scheme_mcfa::{analyze_structured_run, church_term, feature_term, to_expr, to_expr_labeled, worst_case_term};

fn set<T: Eq + Hash>(v: Vec<T>) -> HashSet<T> { v.into_iter().collect() }

#[allow(clippy::too_many_arguments)]
fn assert_relations(
   name: &str, dl: &StructuredRun, evals: HashSet<(E, scheme_mcfa::structured::SCtx, scheme_mcfa::structured::SAddrK)>,
   applies: HashSet<(scheme_mcfa::structured::SValue, scheme_mcfa::structured::SAddrK)>,
   vals: HashSet<(scheme_mcfa::structured::SAddrV, scheme_mcfa::structured::SValue)>,
   konts: HashSet<(scheme_mcfa::structured::SAddrK, scheme_mcfa::structured::SKont)>, flows: &Flows,
) {
   assert_eq!(evals, set(dl.state_e.clone()), "{name}: state_e");
   assert_eq!(applies, set(dl.state_a.clone()), "{name}: state_a");
   assert_eq!(vals, set(dl.stored_val.clone()), "{name}: stored_val");
   assert_eq!(konts, set(dl.stored_kont.clone()), "{name}: stored_kont");
   assert_eq!(flows.ee, set(dl.flow_ee.clone()), "{name}: flow_ee");
   assert_eq!(flows.ea, set(dl.flow_ea.clone()), "{name}: flow_ea");
   assert_eq!(flows.ae, set(dl.flow_ae.clone()), "{name}: flow_ae");
   assert_eq!(flows.aa, set(dl.flow_aa.clone()), "{name}: flow_aa");
}

fn assert_same_fixpoint(name: &str, top: &E, m: usize) {
   let dl = analyze_structured_run(top, m);

   // The textbook step machine.
   let am = Machine::run(top, m);
   let mut eval = HashSet::new();
   let mut apply = HashSet::new();
   for s in &am.seen {
      match s {
         State::Eval(e, ctx, ak) => eval.insert((e.clone(), ctx.clone(), ak.clone())),
         State::Apply(v, ak) => apply.insert((v.clone(), ak.clone())),
      };
   }
   let vals: HashSet<_> = am.store_v.iter().flat_map(|(a, vs)| vs.iter().map(|v| (a.clone(), v.clone()))).collect();
   let konts: HashSet<_> = am.store_k.iter().flat_map(|(a, ks)| ks.iter().map(|k| (a.clone(), k.clone()))).collect();
   assert_relations(&format!("{name} m={m} (step machine)"), &dl, eval, apply, vals, konts, &am.flows);

   // The event-driven delta machine.
   let d = Delta::run(top, m);
   let vals: HashSet<_> = d.store_v.iter().flat_map(|(a, vs)| vs.iter().map(|v| (a.clone(), v.clone()))).collect();
   let konts: HashSet<_> = d.store_k.iter().flat_map(|(a, ks)| ks.iter().map(|k| (a.clone(), k.clone()))).collect();
   assert_relations(
      &format!("{name} m={m} (delta machine)"),
      &dl,
      d.evals.clone(),
      d.applies.clone(),
      vals,
      konts,
      &d.flows,
   );
}

#[test]
fn machines_match_datalog() {
   let terms = [
      ("feature_term", feature_term()),
      ("worst_case_term(5,2,1)", worst_case_term(5, 2, 1)),
      ("church_term(3)", church_term(3)),
   ];
   for (name, ast) in &terms {
      for m in 0..=2 {
         assert_same_fixpoint(&format!("{name} (labelled)"), &to_expr_labeled(ast), m);
         assert_same_fixpoint(&format!("{name} (hash-consed)"), &to_expr(ast), m);
      }
   }
}
