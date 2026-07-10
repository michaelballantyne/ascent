//! Cross-validation of the egglog port against the (tuned) Ascent program.
//!
//! For each test term we:
//!   1. lower it to input facts and run the tuned Ascent analysis,
//!   2. emit the equivalent egglog facts (including the precomputed `freevar`
//!      relation — egglog has no negation), run
//!      `egglog egglog/mcfa.egg <facts> egglog/run.egg`,
//!   3. parse `(print-size)`'s `name: count` lines and assert every output
//!      relation has the same cardinality.
//!
//! The test is skipped (not failed) if the `egglog` binary is unavailable, so
//! the crate still tests cleanly in environments without egglog. Override the
//! binary with the `EGGLOG` environment variable.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;

use scheme_mcfa::{Ast, Facts, church_term, feature_term, worst_case_term};

fn egglog_bin() -> String { std::env::var("EGGLOG").unwrap_or_else(|_| "egglog".to_string()) }

fn egglog_available() -> bool {
   Command::new(egglog_bin()).arg("--version").output().map(|o| o.status.success()).unwrap_or(false)
}

/// Emit the egglog facts file for `facts` (mirrors `mcfa emit-egglog`).
fn write_egglog_facts(path: &std::path::Path, facts: &Facts) {
   use std::fmt::Write as _;
   let mut out = String::new();
   let q = |s: &str| format!("\"{s}\"");
   for (a,) in &facts.top_exp {
      writeln!(out, "(top_exp {})", q(a)).unwrap();
   }
   for (a, b, c) in &facts.lambda {
      writeln!(out, "(lambda {} {} {})", q(a), q(b), q(c)).unwrap();
   }
   for (a, p, x) in &facts.lambda_arg_list {
      writeln!(out, "(lambda_arg_list {} {p} {})", q(a), q(x)).unwrap();
   }
   for (a, b, c) in &facts.prim_call {
      writeln!(out, "(prim_call {} {} {})", q(a), q(b), q(c)).unwrap();
   }
   for (a, b, c) in &facts.call {
      writeln!(out, "(call {} {} {})", q(a), q(b), q(c)).unwrap();
   }
   for (a, p, x) in &facts.call_arg_list {
      writeln!(out, "(call_arg_list {} {p} {})", q(a), q(x)).unwrap();
   }
   for (a, b) in &facts.var {
      writeln!(out, "(var {} {})", q(a), q(b)).unwrap();
   }
   for (a, n) in &facts.num {
      writeln!(out, "(num {} {n})", q(a)).unwrap();
   }
   for (a, b) in &facts.boolean {
      writeln!(out, "(boolean {} {})", q(a), q(b)).unwrap();
   }
   for (a, b, c, d) in &facts.if_ {
      writeln!(out, "(if_ {} {} {} {})", q(a), q(b), q(c), q(d)).unwrap();
   }
   for (a, b, c) in &facts.setb {
      writeln!(out, "(setb {} {} {})", q(a), q(b), q(c)).unwrap();
   }
   for (a, b) in &facts.callcc {
      writeln!(out, "(callcc {} {})", q(a), q(b)).unwrap();
   }
   for (a, b, c) in &facts.let_ {
      writeln!(out, "(let_ {} {} {})", q(a), q(b), q(c)).unwrap();
   }
   for (a, b, c) in &facts.let_list {
      writeln!(out, "(let_list {} {} {})", q(a), q(b), q(c)).unwrap();
   }
   for (x, e) in scheme_mcfa::freevars(facts) {
      writeln!(out, "(freevar {} {})", q(&x), q(&e)).unwrap();
   }
   std::fs::write(path, out).unwrap();
}

/// Parse `(print-size)` output: one `name: count` line per table.
fn parse_sizes(stdout: &str) -> BTreeMap<String, usize> {
   stdout
      .lines()
      .filter_map(|l| {
         let (name, count) = l.split_once(": ")?;
         Some((name.trim().to_string(), count.trim().parse().ok()?))
      })
      .collect()
}

fn cross_check(name: &str, ast: &Ast) {
   let facts = Facts::from_ast(ast);

   let prog = {
      let mut p = facts.clone().into_tuned_program();
      p.run();
      p
   };

   let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
   let tmp = std::env::temp_dir().join(format!("mcfa_egglog_xcheck_{name}.egg"));
   write_egglog_facts(&tmp, &facts);

   let out = Command::new(egglog_bin())
      .arg(dir.join("egglog/mcfa.egg"))
      .arg(&tmp)
      .arg(dir.join("egglog/run.egg"))
      .output()
      .expect("run egglog");
   assert!(out.status.success(), "egglog failed on {name}: {}", String::from_utf8_lossy(&out.stderr));
   let sizes = parse_sizes(&String::from_utf8_lossy(&out.stdout));
   let get = |rel: &str| *sizes.get(rel).unwrap_or_else(|| panic!("egglog printed no size for {rel} on {name}"));

   assert_eq!(get("state_e"), prog.state_e.len(), "state_e mismatch on {name}");
   assert_eq!(get("state_a"), prog.state_a.len(), "state_a mismatch on {name}");
   assert_eq!(get("stored_val"), prog.stored_val.len(), "stored_val mismatch on {name}");
   assert_eq!(get("stored_kont"), prog.stored_kont.len(), "stored_kont mismatch on {name}");
   assert_eq!(get("flow_ee"), prog.flow_ee.len(), "flow_ee mismatch on {name}");
   assert_eq!(get("flow_ea"), prog.flow_ea.len(), "flow_ea mismatch on {name}");
   assert_eq!(get("flow_ae"), prog.flow_ae.len(), "flow_ae mismatch on {name}");
   assert_eq!(get("flow_aa"), prog.flow_aa.len(), "flow_aa mismatch on {name}");
   assert_eq!(get("peek_ctx"), prog.peek_ctx.len(), "peek_ctx mismatch on {name}");
   assert_eq!(get("copy_ctx"), prog.copy_ctx.len(), "copy_ctx mismatch on {name}");
   assert_eq!(get("freevar"), prog.freevar.len(), "freevar mismatch on {name}");

   let _ = std::fs::remove_file(&tmp);
}

#[test]
fn egglog_matches_ascent() {
   if !egglog_available() {
      eprintln!("egglog not found; skipping egglog cross-check (set EGGLOG=/path/to/egglog)");
      return;
   }
   cross_check("feature", &feature_term());
   cross_check("worst_4_2_0", &worst_case_term(4, 2, 0));
   cross_check("worst_6_3_1", &worst_case_term(6, 3, 1));
   cross_check("church_10", &church_term(10));
}
