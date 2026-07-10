//! Benchmark: compares the faithful flat port, the delta-friendly "tuned"
//! port (materialized reader-index relations), the new `McfaDelta`
//! (plusplus fork's explicit `delta` marker, manually enumerated
//! delta-first rule versions), and the hand-written event-driven delta
//! worklist (`analyze_aam_delta`), on a small suite of terms.
//!
//! Run with:
//!   cargo run --release -p scheme-mcfa-plusplus --bin delta_bench
//!
//! Set MCFA_SUMMARY=1 to additionally print `McfaDelta`'s per-SCC iteration
//! summary (`scc_times_summary()`) for each term, to diagnose which rule
//! shape (if any) is still rescanning a large `total` index every round.

use std::time::{Duration, Instant};

use scheme_mcfa::{Ast, Facts, analyze_aam_delta, church_term, to_expr_labeled, worst_case_term};
use scheme_mcfa_plusplus::delta_flat;

fn total_derived_faithful(p: &scheme_mcfa::Mcfa) -> usize {
   p.state_e.len()
      + p.state_a.len()
      + p.stored_val.len()
      + p.stored_kont.len()
      + p.flow_ee.len()
      + p.flow_ea.len()
      + p.flow_ae.len()
      + p.flow_aa.len()
}

fn total_derived_tuned(p: &scheme_mcfa::tuned::McfaTuned) -> usize {
   p.state_e.len()
      + p.state_a.len()
      + p.stored_val.len()
      + p.stored_kont.len()
      + p.flow_ee.len()
      + p.flow_ea.len()
      + p.flow_ae.len()
      + p.flow_aa.len()
}

fn total_derived_delta(p: &delta_flat::McfaDelta) -> usize {
   p.state_e.len()
      + p.state_a.len()
      + p.stored_val.len()
      + p.stored_kont.len()
      + p.flow_ee.len()
      + p.flow_ea.len()
      + p.flow_ae.len()
      + p.flow_aa.len()
}

struct Row {
   engine: &'static str,
   derived: usize,
   time: Duration,
}

fn bench_term(name: &str, ast: &Ast) -> Vec<Row> {
   let facts = Facts::from_ast(ast);
   let top = to_expr_labeled(ast);
   let summary = std::env::var("MCFA_SUMMARY").is_ok();

   let mut rows = vec![];

   // 1. Faithful flat port.
   {
      let mut p = facts.clone().into_program();
      let t = Instant::now();
      p.run();
      let elapsed = t.elapsed();
      rows.push(Row { engine: "faithful (scheme_mcfa::analyze)", derived: total_derived_faithful(&p), time: elapsed });
   }

   // 2. Tuned flat port (materialized reader-index relations).
   {
      let mut p = facts.clone().into_tuned_program();
      let t = Instant::now();
      p.run();
      let elapsed = t.elapsed();
      rows.push(Row { engine: "tuned (McfaTuned)", derived: total_derived_tuned(&p), time: elapsed });
      if summary {
         println!("--- {name}: tuned scc summary ---\n{}", p.scc_times_summary());
      }
   }

   // 3. New: delta-marked flat port.
   {
      let mut p = delta_flat::load_facts(facts.clone());
      let t = Instant::now();
      p.run();
      let elapsed = t.elapsed();
      rows.push(Row { engine: "delta (McfaDelta)", derived: total_derived_delta(&p), time: elapsed });
      if summary {
         println!("--- {name}: delta scc summary ---\n{}", p.scc_times_summary());
      }
   }

   // 4. Hand-written event-driven delta worklist, over labelled structured
   //    syntax (m=1, matching the faithful/tuned/delta ports' m=1 contour).
   {
      let t = Instant::now();
      let d = analyze_aam_delta(&top, 1);
      let elapsed = t.elapsed();
      rows.push(Row { engine: "AAM delta worklist (analyze_aam_delta)", derived: d.total_derived(), time: elapsed });
   }

   // Sanity: faithful == tuned == delta on this term (derived count is a
   // weak check; delta_flat_check.rs does the strong content check).
   let faithful_derived = rows[0].derived;
   let tuned_derived = rows[1].derived;
   let delta_derived = rows[2].derived;
   if faithful_derived != tuned_derived || faithful_derived != delta_derived {
      println!(
         "  ** WARNING: derived-fact counts disagree on {name}: faithful={faithful_derived} tuned={tuned_derived} delta={delta_derived} **"
      );
   }

   println!("\n### {name}\n");
   println!("| engine | derived facts | time |");
   println!("|---|---:|---:|");
   for r in &rows {
      println!("| {} | {} | {:?} |", r.engine, r.derived, r.time);
   }
   println!();

   rows
}

fn main() {
   println!("# delta_bench: faithful vs. tuned vs. delta-marked vs. AAM-delta-worklist\n");

   bench_term("worst_case_term(12, 3, 0)", &worst_case_term(12, 3, 0));
   bench_term("church_term(60)", &church_term(60));
   bench_term("church_term(80)", &church_term(80));
}
