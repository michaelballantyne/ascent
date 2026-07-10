//! Cross-check for `incremental::analyze_incremental` (`src/incremental.rs`):
//! feeding the same program's facts to the analysis in chunks and
//! continuing the fixpoint between chunks (instead of recomputing from
//! scratch) must converge to the *same* fixpoint as a single batch
//! `scheme_mcfa::analyze` run -- m-CFA is monotone Datalog, so chunk
//! boundaries are semantically invisible. Follows the same
//! cardinality-then-content pattern as `tests/delta_flat_check.rs`.

use std::collections::HashSet;

use scheme_mcfa::{analyze, church_term, feature_term, worst_case_term};
use scheme_mcfa_plusplus::incremental::analyze_incremental;

fn check(name: &str, ast: &scheme_mcfa::Ast, n_chunks: usize) {
   let faithful = analyze(ast);
   let run = analyze_incremental(ast, n_chunks);
   let incremental = &run.prog;

   let label = format!("{name} (n_chunks={n_chunks})");

   // Cardinality for every output relation.
   assert_eq!(incremental.state_e.len(), faithful.state_e.len(), "{label}: state_e cardinality");
   assert_eq!(incremental.state_a.len(), faithful.state_a.len(), "{label}: state_a cardinality");
   assert_eq!(incremental.stored_val.len(), faithful.stored_val.len(), "{label}: stored_val cardinality");
   assert_eq!(incremental.stored_kont.len(), faithful.stored_kont.len(), "{label}: stored_kont cardinality");
   assert_eq!(incremental.flow_ee.len(), faithful.flow_ee.len(), "{label}: flow_ee cardinality");
   assert_eq!(incremental.flow_ea.len(), faithful.flow_ea.len(), "{label}: flow_ea cardinality");
   assert_eq!(incremental.flow_ae.len(), faithful.flow_ae.len(), "{label}: flow_ae cardinality");
   assert_eq!(incremental.flow_aa.len(), faithful.flow_aa.len(), "{label}: flow_aa cardinality");
   assert_eq!(incremental.peek_ctx.len(), faithful.peek_ctx.len(), "{label}: peek_ctx cardinality");
   assert_eq!(incremental.copy_ctx.len(), faithful.copy_ctx.len(), "{label}: copy_ctx cardinality");
   assert_eq!(incremental.freevar.len(), faithful.freevar.len(), "{label}: freevar cardinality");
   assert_eq!(incremental.value_form.len(), faithful.value_form.len(), "{label}: value_form cardinality");

   // Content equality. HashSet (not Vec) comparisons on purpose: a
   // multi-`run()`-call continuation can, in principle, re-derive and
   // re-append already-known tuples to a relation's plain `Vec` field (see
   // `src/incremental.rs`'s module doc) without that being a correctness
   // bug, since Datalog relations are sets. Every relation here uses host
   // types directly (scheme_mcfa::{Ctx, AddrK, AddrV, Value, Kont}), so
   // straight HashSet comparisons work for all of them.
   let state_e_f: HashSet<_> = faithful.state_e.iter().cloned().collect();
   let state_e_i: HashSet<_> = incremental.state_e.iter().cloned().collect();
   assert_eq!(state_e_i, state_e_f, "{label}: state_e content");

   let state_a_f: HashSet<_> = faithful.state_a.iter().cloned().collect();
   let state_a_i: HashSet<_> = incremental.state_a.iter().cloned().collect();
   assert_eq!(state_a_i, state_a_f, "{label}: state_a content");

   let stored_val_f: HashSet<_> = faithful.stored_val.iter().cloned().collect();
   let stored_val_i: HashSet<_> = incremental.stored_val.iter().cloned().collect();
   assert_eq!(stored_val_i, stored_val_f, "{label}: stored_val content");

   let stored_kont_f: HashSet<_> = faithful.stored_kont.iter().cloned().collect();
   let stored_kont_i: HashSet<_> = incremental.stored_kont.iter().cloned().collect();
   assert_eq!(stored_kont_i, stored_kont_f, "{label}: stored_kont content");

   let flow_ee_f: HashSet<_> = faithful.flow_ee.iter().cloned().collect();
   let flow_ee_i: HashSet<_> = incremental.flow_ee.iter().cloned().collect();
   assert_eq!(flow_ee_i, flow_ee_f, "{label}: flow_ee content");

   let flow_ea_f: HashSet<_> = faithful.flow_ea.iter().cloned().collect();
   let flow_ea_i: HashSet<_> = incremental.flow_ea.iter().cloned().collect();
   assert_eq!(flow_ea_i, flow_ea_f, "{label}: flow_ea content");

   let flow_ae_f: HashSet<_> = faithful.flow_ae.iter().cloned().collect();
   let flow_ae_i: HashSet<_> = incremental.flow_ae.iter().cloned().collect();
   assert_eq!(flow_ae_i, flow_ae_f, "{label}: flow_ae content");

   let flow_aa_f: HashSet<_> = faithful.flow_aa.iter().cloned().collect();
   let flow_aa_i: HashSet<_> = incremental.flow_aa.iter().cloned().collect();
   assert_eq!(flow_aa_i, flow_aa_f, "{label}: flow_aa content");

   let peek_ctx_f: HashSet<_> = faithful.peek_ctx.iter().cloned().collect();
   let peek_ctx_i: HashSet<_> = incremental.peek_ctx.iter().cloned().collect();
   assert_eq!(peek_ctx_i, peek_ctx_f, "{label}: peek_ctx content");

   let copy_ctx_f: HashSet<_> = faithful.copy_ctx.iter().cloned().collect();
   let copy_ctx_i: HashSet<_> = incremental.copy_ctx.iter().cloned().collect();
   assert_eq!(copy_ctx_i, copy_ctx_f, "{label}: copy_ctx content");

   let freevar_f: HashSet<_> = faithful.freevar.iter().cloned().collect();
   let freevar_i: HashSet<_> = incremental.freevar.iter().cloned().collect();
   assert_eq!(freevar_i, freevar_f, "{label}: freevar content");

   // Sanity: every chunk actually ran (n_chunks phases recorded).
   assert_eq!(run.phase_times.len(), n_chunks, "{label}: expected one phase time per chunk");
}

#[test]
fn incremental_matches_batch() {
   for n_chunks in [2usize, 5] {
      check("features", &feature_term(), n_chunks);
      check("worst_6_2_1", &worst_case_term(6, 2, 1), n_chunks);
      check("worst_8_3_0", &worst_case_term(8, 3, 0), n_chunks);
      check("church_20", &church_term(20), n_chunks);
   }
}
