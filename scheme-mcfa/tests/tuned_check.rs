//! The delta-friendly ("tuned") program must compute exactly the same analysis
//! as the faithful Appendix-A port — the rewrites (guard placement, binary-join
//! splits, flattened store address) are performance-only.

use std::collections::BTreeSet;

use scheme_mcfa::{Facts, analyze, church_term, feature_term, worst_case_term};

fn check(name: &str, ast: &scheme_mcfa::Ast) {
   let faithful = analyze(ast);
   let mut tuned = Facts::from_ast(ast).into_tuned_program();
   tuned.run();

   assert_eq!(tuned.state_e.len(), faithful.state_e.len(), "{name}: state_e");
   assert_eq!(tuned.state_a.len(), faithful.state_a.len(), "{name}: state_a");
   assert_eq!(tuned.stored_kont.len(), faithful.stored_kont.len(), "{name}: stored_kont");
   assert_eq!(tuned.flow_ee.len(), faithful.flow_ee.len(), "{name}: flow_ee");
   assert_eq!(tuned.flow_ea.len(), faithful.flow_ea.len(), "{name}: flow_ea");
   assert_eq!(tuned.flow_ae.len(), faithful.flow_ae.len(), "{name}: flow_ae");
   assert_eq!(tuned.flow_aa.len(), faithful.flow_aa.len(), "{name}: flow_aa");
   assert_eq!(tuned.peek_ctx.len(), faithful.peek_ctx.len(), "{name}: peek_ctx");
   assert_eq!(tuned.copy_ctx.len(), faithful.copy_ctx.len(), "{name}: copy_ctx");

   // stored_val: faithful is (AddrV{x,ctx}, v); tuned flattens to (x, ctx, v).
   let f_store: BTreeSet<String> =
      faithful.stored_val.iter().map(|(a, v)| format!("{:?}|{:?}|{v:?}", a.x, a.ctx)).collect();
   let t_store: BTreeSet<String> =
      tuned.stored_val.iter().map(|(x, c, v)| format!("{x:?}|{c:?}|{v:?}")).collect();
   assert_eq!(t_store, f_store, "{name}: stored_val content");

   // flow_ee content must match exactly.
   let f_edges: BTreeSet<_> = faithful.flow_ee.iter().cloned().collect();
   let t_edges: BTreeSet<_> = tuned.flow_ee.iter().cloned().collect();
   assert_eq!(t_edges, f_edges, "{name}: flow_ee content");
}

#[test]
fn tuned_matches_faithful() {
   check("features", &feature_term());
   check("church_6", &church_term(6));
   check("worst_6_3_1", &worst_case_term(6, 3, 1));
   check("worst_8_2_0", &worst_case_term(8, 2, 0));
}
