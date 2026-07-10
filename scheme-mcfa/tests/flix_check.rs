//! Cross-validation of the Flix port against the (tuned) Ascent program.
//!
//! For each test term we lower to input facts, run the tuned Ascent
//! analysis, write the TSV `.facts` files, run the Flix program
//! (`flix/mcfa.flix`) on them, and assert every output relation reports the
//! same cardinality.
//!
//! Because each Flix invocation recompiles the program (~30 s), this test
//! only runs when the `FLIX_JAR` environment variable points at a Flix
//! compiler jar (Java 21+ required on PATH):
//!
//! ```sh
//! FLIX_JAR=/path/to/flix.jar cargo test --release -p scheme-mcfa --test flix_check
//! ```

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::Command;

use scheme_mcfa::{Ast, Facts, church_term, feature_term, worst_case_term};

/// Parse the report lines: one `name count` pair per line.
fn parse_counts(stdout: &str) -> BTreeMap<String, usize> {
   stdout
      .lines()
      .filter_map(|l| {
         let (name, count) = l.split_once(' ')?;
         Some((name.trim().to_string(), count.trim().parse().ok()?))
      })
      .collect()
}

fn cross_check(flix_jar: &str, name: &str, ast: &Ast, flix_src: &std::path::Path) {
   let facts = Facts::from_ast(ast);

   let prog = {
      let mut p = facts.clone().into_tuned_program();
      p.run();
      p
   };

   let facts_dir = std::env::temp_dir().join(format!("mcfa_flix_xcheck_{name}"));
   let _ = std::fs::remove_dir_all(&facts_dir);
   facts.write_souffle(&facts_dir).unwrap();

   let out = Command::new("java")
      .arg("-Xmx4g")
      .arg("-jar")
      .arg(flix_jar)
      .arg(flix_src)
      .arg("--")
      .arg(&facts_dir)
      .output()
      .expect("run flix");
   assert!(out.status.success(), "flix failed on {name}: {}", String::from_utf8_lossy(&out.stderr));
   let counts = parse_counts(&String::from_utf8_lossy(&out.stdout));
   let get = |rel: &str| *counts.get(rel).unwrap_or_else(|| panic!("flix printed no count for {rel} on {name}"));

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

   let _ = std::fs::remove_dir_all(&facts_dir);
}

#[test]
fn flix_matches_ascent() {
   let Ok(flix_jar) = std::env::var("FLIX_JAR") else {
      eprintln!("FLIX_JAR not set; skipping Flix cross-check");
      return;
   };
   let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
   for src in ["flix/mcfa.flix", "flix/mcfa_tuned.flix"] {
      let src = dir.join(src);
      if !src.exists() {
         continue;
      }
      cross_check(&flix_jar, "feature", &feature_term(), &src);
      cross_check(&flix_jar, "worst_4_2_0", &worst_case_term(4, 2, 0), &src);
      cross_check(&flix_jar, "church_10", &church_term(10), &src);
   }
}
