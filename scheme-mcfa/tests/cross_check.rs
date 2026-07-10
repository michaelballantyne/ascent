//! Cross-validation of the Ascent port against the original Soufflé program.
//!
//! For each test term we:
//!   1. lower it to input facts,
//!   2. run the Ascent analysis,
//!   3. write equivalent Soufflé `.facts`, run `souffle` on `souffle/mcfa.dl`,
//!   4. assert that every output relation has the same cardinality, and that
//!      the pure-id relations (`flow_ee`, `freevar`, `peek_ctx`, `copy_ctx`,
//!      `state_e`) are content-identical.
//!
//! The test is skipped (not failed) if the `souffle` binary is unavailable, so
//! the crate still tests cleanly in environments without Soufflé. Override the
//! binary with the `SOUFFLE` environment variable.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use scheme_mcfa::{AddrK, Ast, Ctx, Facts, church_term, feature_term, worst_case_term};

fn souffle_bin() -> String { std::env::var("SOUFFLE").unwrap_or_else(|_| "souffle".to_string()) }

fn souffle_available() -> bool {
   Command::new(souffle_bin()).arg("--version").output().map(|o| o.status.success()).unwrap_or(false)
}

fn fmt_ctx(c: &Ctx) -> String { format!("$Context({})", c.0) }
fn fmt_addrk(a: &AddrK) -> String { format!("$KAddress({}, {})", a.e, fmt_ctx(&a.ctx)) }

fn read_csv(path: &Path) -> BTreeSet<String> {
   std::fs::read_to_string(path)
      .unwrap_or_default()
      .lines()
      .filter(|l| !l.is_empty())
      .map(|l| l.to_string())
      .collect()
}

fn souffle_count(dir: &Path, rel: &str) -> usize { read_csv(&dir.join(format!("{rel}.csv"))).len() }

fn cross_check(name: &str, ast: &Ast) {
   let facts = Facts::from_ast(ast);

   // ---- Ascent ----
   let prog = {
      let mut p = facts.clone().into_program();
      p.run();
      p
   };

   // ---- Soufflé ----
   let tmp: PathBuf = std::env::temp_dir().join(format!("mcfa_xcheck_{name}"));
   let facts_dir = tmp.join("facts");
   let out_dir = tmp.join("out");
   let _ = std::fs::remove_dir_all(&tmp);
   std::fs::create_dir_all(&facts_dir).unwrap();
   std::fs::create_dir_all(&out_dir).unwrap();
   facts.write_souffle(&facts_dir).unwrap();

   let dl = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("souffle/mcfa.dl");
   let status = Command::new(souffle_bin())
      .args(["-F", facts_dir.to_str().unwrap(), "-D", out_dir.to_str().unwrap(), dl.to_str().unwrap()])
      .status()
      .expect("run souffle");
   assert!(status.success(), "souffle failed on term {name}");

   // ---- Compare cardinalities of all output relations ----
   let card = [
      ("state_e", prog.state_e.len()),
      ("state_a", prog.state_a.len()),
      ("stored_val", prog.stored_val.len()),
      ("stored_kont", prog.stored_kont.len()),
      ("flow_ee", prog.flow_ee.len()),
      ("flow_ea", prog.flow_ea.len()),
      ("flow_ae", prog.flow_ae.len()),
      ("flow_aa", prog.flow_aa.len()),
      ("freevar", prog.freevar.len()),
      ("peek_ctx", prog.peek_ctx.len()),
      ("copy_ctx", prog.copy_ctx.len()),
   ];
   for (rel, ascent_n) in card {
      let souffle_n = souffle_count(&out_dir, rel);
      assert_eq!(ascent_n, souffle_n, "term {name}: relation {rel} cardinality mismatch (ascent {ascent_n} vs souffle {souffle_n})");
   }

   // ---- Compare content of the pure-id relations ----
   let ascent_flow_ee: BTreeSet<String> = prog.flow_ee.iter().map(|(a, b)| format!("{a}\t{b}")).collect();
   assert_eq!(ascent_flow_ee, read_csv(&out_dir.join("flow_ee.csv")), "term {name}: flow_ee content mismatch");

   let ascent_freevar: BTreeSet<String> = prog.freevar.iter().map(|(x, e)| format!("{x}\t{e}")).collect();
   assert_eq!(ascent_freevar, read_csv(&out_dir.join("freevar.csv")), "term {name}: freevar content mismatch");

   let ascent_peek: BTreeSet<String> =
      prog.peek_ctx.iter().map(|(e, o, n)| format!("{e}\t{}\t{}", fmt_ctx(o), fmt_ctx(n))).collect();
   assert_eq!(ascent_peek, read_csv(&out_dir.join("peek_ctx.csv")), "term {name}: peek_ctx content mismatch");

   let ascent_copy: BTreeSet<String> =
      prog.copy_ctx.iter().map(|(f, t, e)| format!("{}\t{}\t{e}", fmt_ctx(f), fmt_ctx(t))).collect();
   assert_eq!(ascent_copy, read_csv(&out_dir.join("copy_ctx.csv")), "term {name}: copy_ctx content mismatch");

   let ascent_state_e: BTreeSet<String> =
      prog.state_e.iter().map(|(e, c, ak)| format!("{e}\t{}\t{}", fmt_ctx(c), fmt_addrk(ak))).collect();
   assert_eq!(ascent_state_e, read_csv(&out_dir.join("state_e.csv")), "term {name}: state_e content mismatch");

   let _ = std::fs::remove_dir_all(&tmp);
}

#[test]
fn ascent_matches_souffle() {
   if !souffle_available() {
      eprintln!("skipping cross-check: `souffle` not found on PATH (set SOUFFLE=...)");
      return;
   }
   cross_check("features", &feature_term());
   cross_check("worst_4_2_1", &worst_case_term(4, 2, 1));
   cross_check("worst_6_3_1", &worst_case_term(6, 3, 1));
   cross_check("worst_8_2_0", &worst_case_term(8, 2, 0));
   cross_check("church_6", &church_term(6));
}

/// The `.plan`-tuned Soufflé program (`souffle/mcfa_tuned.dl`) must produce
/// exactly the same output relations as the faithful one on the same input.
#[test]
fn tuned_souffle_matches_untuned() {
   if !souffle_available() {
      eprintln!("skipping souffle-tuned check: `souffle` not found on PATH (set SOUFFLE=...)");
      return;
   }
   for (name, ast) in [("features", feature_term()), ("worst_4_2_1", worst_case_term(4, 2, 1)), ("church_6", church_term(6))] {
      let tmp: PathBuf = std::env::temp_dir().join(format!("mcfa_sftuned_{name}"));
      let facts_dir = tmp.join("facts");
      let _ = std::fs::remove_dir_all(&tmp);
      std::fs::create_dir_all(&facts_dir).unwrap();
      Facts::from_ast(&ast).write_souffle(&facts_dir).unwrap();

      let mut outs = Vec::new();
      for dl in ["souffle/mcfa.dl", "souffle/mcfa_tuned.dl"] {
         let out_dir = tmp.join(dl.replace(['/', '.'], "_"));
         std::fs::create_dir_all(&out_dir).unwrap();
         let dl_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(dl);
         let status = Command::new(souffle_bin())
            .args(["-F", facts_dir.to_str().unwrap(), "-D", out_dir.to_str().unwrap(), dl_path.to_str().unwrap()])
            .status()
            .expect("run souffle");
         assert!(status.success(), "souffle failed on {dl} for term {name}");
         outs.push(out_dir);
      }

      for rel in
         ["state_e", "state_a", "stored_val", "stored_kont", "flow_ee", "flow_ea", "flow_ae", "flow_aa", "freevar", "peek_ctx", "copy_ctx"]
      {
         let a = read_csv(&outs[0].join(format!("{rel}.csv")));
         let b = read_csv(&outs[1].join(format!("{rel}.csv")));
         assert_eq!(a, b, "term {name}: relation {rel} differs between mcfa.dl and mcfa_tuned.dl");
      }
      let _ = std::fs::remove_dir_all(&tmp);
   }
}
