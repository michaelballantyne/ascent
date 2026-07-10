//! The Datalog/Rust hybrid ([`scheme_mcfa::hybrid`]) — Ascent for the three
//! both-sides-growing joins, plain Rust for all the stepping — computes the
//! identical analysis to the structured port, on both labelings, at every `m`.

use scheme_mcfa::{
   StructuredStats, analyze_structured, analyze_structured_hybrid, analyze_structured_hybrid_memo, church_term,
   feature_term, to_expr, to_expr_labeled, worst_case_term,
};

fn assert_core_relations(h: &StructuredStats, base: &StructuredStats, what: &str) {
   assert_eq!(h.state_e, base.state_e, "{what}: state_e");
   assert_eq!(h.state_a, base.state_a, "{what}: state_a");
   assert_eq!(h.stored_val, base.stored_val, "{what}: stored_val");
   assert_eq!(h.stored_kont, base.stored_kont, "{what}: stored_kont");
   assert_eq!(h.flow_ee, base.flow_ee, "{what}: flow_ee");
   assert_eq!(h.flow_ea, base.flow_ea, "{what}: flow_ea");
   assert_eq!(h.flow_ae, base.flow_ae, "{what}: flow_ae");
   assert_eq!(h.flow_aa, base.flow_aa, "{what}: flow_aa");
}

#[test]
fn hybrid_matches_structured() {
   let terms = [("features", feature_term()), ("church_4", church_term(4)), ("worst_5_2_1", worst_case_term(5, 2, 1))];
   for (name, ast) in &terms {
      for (labeling, top) in [("labelled", to_expr_labeled(ast)), ("hash-consed", to_expr(ast))] {
         for m in 0..=2 {
            let base = analyze_structured(&top, m);
            let what = format!("{name} ({labeling}) m={m}");
            assert_core_relations(&analyze_structured_hybrid(&top, m), &base, &format!("{what} (hybrid)"));
            assert_core_relations(&analyze_structured_hybrid_memo(&top, m), &base, &format!("{what} (memo)"));
         }
      }
   }
}
