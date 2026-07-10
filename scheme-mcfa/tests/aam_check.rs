//! The direct abstract machine ([`scheme_mcfa::aam`]) computes *exactly* the
//! Datalog fixpoint: every relation — states, stores, and flow graph — is
//! content-identical to the structured Ascent run, on both labelings, at
//! several polyvariance levels.

use std::collections::HashSet;
use std::hash::Hash;

use scheme_mcfa::aam::{Machine, State};
use scheme_mcfa::structured::E;
use scheme_mcfa::{analyze_structured_run, church_term, feature_term, to_expr, to_expr_labeled, worst_case_term};

fn set<T: Eq + Hash>(v: Vec<T>) -> HashSet<T> { v.into_iter().collect() }

fn assert_same_fixpoint(name: &str, top: &E, m: usize) {
   let dl = analyze_structured_run(top, m);
   let am = Machine::run(top, m);

   let mut eval = HashSet::new();
   let mut apply = HashSet::new();
   for s in &am.seen {
      match s {
         State::Eval(e, ctx, ak) => eval.insert((e.clone(), ctx.clone(), ak.clone())),
         State::Apply(v, ak) => apply.insert((v.clone(), ak.clone())),
      };
   }
   assert_eq!(eval, set(dl.state_e), "{name} m={m}: state_e");
   assert_eq!(apply, set(dl.state_a), "{name} m={m}: state_a");

   let vals: HashSet<_> = am.store_v.iter().flat_map(|(a, vs)| vs.iter().map(|v| (a.clone(), v.clone()))).collect();
   assert_eq!(vals, set(dl.stored_val), "{name} m={m}: stored_val");

   let konts: HashSet<_> = am.store_k.iter().flat_map(|(a, ks)| ks.iter().map(|k| (a.clone(), k.clone()))).collect();
   assert_eq!(konts, set(dl.stored_kont), "{name} m={m}: stored_kont");

   assert_eq!(am.flows.ee, set(dl.flow_ee), "{name} m={m}: flow_ee");
   assert_eq!(am.flows.ea, set(dl.flow_ea), "{name} m={m}: flow_ea");
   assert_eq!(am.flows.ae, set(dl.flow_ae), "{name} m={m}: flow_ae");
   assert_eq!(am.flows.aa, set(dl.flow_aa), "{name} m={m}: flow_aa");
}

#[test]
fn aam_matches_datalog() {
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
