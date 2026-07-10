//! `McfaDelta` (the manually-`delta`-marked flat port, `src/delta_flat.rs`)
//! must compute exactly the same analysis as `scheme_mcfa::analyze` (the
//! faithful, untuned port) -- the rewrites (delta-first rule splitting) are
//! performance-only. Follows the pattern of `scheme-mcfa/tests/tuned_check.rs`.

use std::collections::HashSet;

use scheme_mcfa::{analyze, church_term, feature_term, worst_case_term};
use scheme_mcfa_plusplus::delta_flat;

fn check(name: &str, ast: &scheme_mcfa::Ast) {
   let faithful = analyze(ast);
   let delta = delta_flat::analyze(ast);

   // Cardinality for every output relation.
   assert_eq!(delta.state_e.len(), faithful.state_e.len(), "{name}: state_e cardinality");
   assert_eq!(delta.state_a.len(), faithful.state_a.len(), "{name}: state_a cardinality");
   assert_eq!(delta.stored_val.len(), faithful.stored_val.len(), "{name}: stored_val cardinality");
   assert_eq!(delta.stored_kont.len(), faithful.stored_kont.len(), "{name}: stored_kont cardinality");
   assert_eq!(delta.flow_ee.len(), faithful.flow_ee.len(), "{name}: flow_ee cardinality");
   assert_eq!(delta.flow_ea.len(), faithful.flow_ea.len(), "{name}: flow_ea cardinality");
   assert_eq!(delta.flow_ae.len(), faithful.flow_ae.len(), "{name}: flow_ae cardinality");
   assert_eq!(delta.flow_aa.len(), faithful.flow_aa.len(), "{name}: flow_aa cardinality");
   assert_eq!(delta.peek_ctx.len(), faithful.peek_ctx.len(), "{name}: peek_ctx cardinality");
   assert_eq!(delta.copy_ctx.len(), faithful.copy_ctx.len(), "{name}: copy_ctx cardinality");
   assert_eq!(delta.freevar.len(), faithful.freevar.len(), "{name}: freevar cardinality");
   assert_eq!(delta.value_form.len(), faithful.value_form.len(), "{name}: value_form cardinality");

   // Content equality -- every relation here uses host types directly
   // (scheme_mcfa::{Ctx, AddrK, AddrV, Value, Kont}), so straight HashSet
   // comparisons work for all of them.
   let state_e_f: HashSet<_> = faithful.state_e.iter().cloned().collect();
   let state_e_d: HashSet<_> = delta.state_e.iter().cloned().collect();
   assert_eq!(state_e_d, state_e_f, "{name}: state_e content");

   let state_a_f: HashSet<_> = faithful.state_a.iter().cloned().collect();
   let state_a_d: HashSet<_> = delta.state_a.iter().cloned().collect();
   assert_eq!(state_a_d, state_a_f, "{name}: state_a content");

   let stored_val_f: HashSet<_> = faithful.stored_val.iter().cloned().collect();
   let stored_val_d: HashSet<_> = delta.stored_val.iter().cloned().collect();
   assert_eq!(stored_val_d, stored_val_f, "{name}: stored_val content");

   let stored_kont_f: HashSet<_> = faithful.stored_kont.iter().cloned().collect();
   let stored_kont_d: HashSet<_> = delta.stored_kont.iter().cloned().collect();
   assert_eq!(stored_kont_d, stored_kont_f, "{name}: stored_kont content");

   let flow_ee_f: HashSet<_> = faithful.flow_ee.iter().cloned().collect();
   let flow_ee_d: HashSet<_> = delta.flow_ee.iter().cloned().collect();
   assert_eq!(flow_ee_d, flow_ee_f, "{name}: flow_ee content");

   let flow_ea_f: HashSet<_> = faithful.flow_ea.iter().cloned().collect();
   let flow_ea_d: HashSet<_> = delta.flow_ea.iter().cloned().collect();
   assert_eq!(flow_ea_d, flow_ea_f, "{name}: flow_ea content");

   let flow_ae_f: HashSet<_> = faithful.flow_ae.iter().cloned().collect();
   let flow_ae_d: HashSet<_> = delta.flow_ae.iter().cloned().collect();
   assert_eq!(flow_ae_d, flow_ae_f, "{name}: flow_ae content");

   let flow_aa_f: HashSet<_> = faithful.flow_aa.iter().cloned().collect();
   let flow_aa_d: HashSet<_> = delta.flow_aa.iter().cloned().collect();
   assert_eq!(flow_aa_d, flow_aa_f, "{name}: flow_aa content");

   let peek_ctx_f: HashSet<_> = faithful.peek_ctx.iter().cloned().collect();
   let peek_ctx_d: HashSet<_> = delta.peek_ctx.iter().cloned().collect();
   assert_eq!(peek_ctx_d, peek_ctx_f, "{name}: peek_ctx content");

   let copy_ctx_f: HashSet<_> = faithful.copy_ctx.iter().cloned().collect();
   let copy_ctx_d: HashSet<_> = delta.copy_ctx.iter().cloned().collect();
   assert_eq!(copy_ctx_d, copy_ctx_f, "{name}: copy_ctx content");

   let freevar_f: HashSet<_> = faithful.freevar.iter().cloned().collect();
   let freevar_d: HashSet<_> = delta.freevar.iter().cloned().collect();
   assert_eq!(freevar_d, freevar_f, "{name}: freevar content");
}

#[test]
fn delta_flat_matches_faithful() {
   check("features", &feature_term());
   check("worst_8_3_0", &worst_case_term(8, 3, 0));
   check("worst_6_2_1", &worst_case_term(6, 2, 1));
   check("church_20", &church_term(20));
}
