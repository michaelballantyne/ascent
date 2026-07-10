//! The hand-written AAM worklist must compute exactly the same analysis as the
//! Datalog (`analyze_generic`), fact for fact, at every polyvariance `m`.

use std::collections::BTreeSet;

use scheme_mcfa::{Facts, analyze_aam, analyze_generic, church_term, feature_term, worst_case_term};

fn same(name: &str, ast: &scheme_mcfa::Ast, m: usize) {
   let facts = Facts::from_ast(ast);
   let dl = analyze_generic(&facts, m);
   let aam = analyze_aam(&facts, m);

   assert_eq!(aam.state_e, dl.state_e, "{name} m={m}: state_e");
   assert_eq!(aam.state_a, dl.state_a, "{name} m={m}: state_a");
   assert_eq!(aam.stored_val, dl.stored_val, "{name} m={m}: stored_val");
   assert_eq!(aam.stored_kont, dl.stored_kont, "{name} m={m}: stored_kont");
   assert_eq!(aam.flow_ee, dl.flow_ee, "{name} m={m}: flow_ee");
   assert_eq!(aam.flow_ea, dl.flow_ea, "{name} m={m}: flow_ea");
   assert_eq!(aam.flow_ae, dl.flow_ae, "{name} m={m}: flow_ae");
   assert_eq!(aam.flow_aa, dl.flow_aa, "{name} m={m}: flow_aa");
   assert_eq!(aam.peek_ctx, dl.peek_ctx, "{name} m={m}: peek_ctx");
   assert_eq!(aam.copy_ctx, dl.copy_ctx, "{name} m={m}: copy_ctx");

   // flow_ee content (same ids on both sides) must match exactly.
   let a: BTreeSet<_> = aam.flow_ee_edges.into_iter().collect();
   let b: BTreeSet<_> = dl.flow_ee_edges.into_iter().collect();
   assert_eq!(a, b, "{name} m={m}: flow_ee content");
}

#[test]
fn aam_matches_datalog() {
   same("features", &feature_term(), 1);
   same("church_6", &church_term(6), 1);
   for m in 0..=2 {
      same("worst_6_3_1", &worst_case_term(6, 3, 1), m);
      same("worst_8_2_0", &worst_case_term(8, 2, 0), m);
   }
}
