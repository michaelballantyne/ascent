//! CLI runner and basic benchmark for the Ascent `m`-CFA reproduction.
//!
//! Usage:
//! ```text
//! mcfa run   [N] [K] [P]        # run once on the worst-case term (N calls, K pluses, P padding)
//! mcfa bench                    # sweep a few term sizes and print a timing table
//! mcfa emit-souffle DIR [N K P] # write equivalent Soufflé .facts files into DIR
//! mcfa emit-egglog FILE <termspec>  # write one egglog fact per line into FILE
//! mcfa emit-flix DIR <termspec>     # write equivalent Flix/Soufflé .facts files into DIR
//! mcfa expected <termspec>          # run the tuned program, print per-relation counts
//! ```
//! where `<termspec>` is `worst N K P` | `church N` | `feature`.

use std::env;
use std::path::Path;
use std::time::Instant;

use scheme_mcfa::{AddrK, Ctx, Facts, worst_case_term};

fn main() {
   let args: Vec<String> = env::args().collect();
   let cmd = args.get(1).map(|s| s.as_str()).unwrap_or("bench");

   match cmd {
      "run" => {
         let n = arg(&args, 2, 10);
         let k = arg(&args, 3, 3);
         let p = arg(&args, 4, 0);
         run_once(n, k, p, true);
      },
      "bench" => bench(),
      "engines" => {
         // Compare all in-process engines on one term at m=1.
         let which = args.get(2).map(|s| s.as_str()).unwrap_or("worst");
         let ast = if which == "church" {
            scheme_mcfa::church_term(arg(&args, 3, 60))
         } else {
            worst_case_term(arg(&args, 3, 12), arg(&args, 4, 3), arg(&args, 5, 0))
         };
         engines(&ast, which);
      },
      "church" => {
         let nn = arg(&args, 2, 8);
         let facts = Facts::from_ast(&scheme_mcfa::church_term(nn));
         let n_input = facts.len();
         let mut prog = facts.into_program();
         let start = Instant::now();
         prog.run();
         let elapsed = start.elapsed();
         let derived = prog.state_e.len()
            + prog.state_a.len()
            + prog.stored_val.len()
            + prog.stored_kont.len()
            + prog.flow_ee.len()
            + prog.flow_ea.len()
            + prog.flow_ae.len()
            + prog.flow_aa.len();
         println!(
            "church(sum 0..={nn}) input={n_input} state_a={} stored_val={} derived={derived} time={:.3?}",
            prog.state_a.len(),
            prog.stored_val.len(),
            elapsed
         );
      },
      "cfa" => {
         let n = arg(&args, 2, 8);
         let k = arg(&args, 3, 2);
         let p = arg(&args, 4, 0);
         cfa_sweep(n, k, p);
      },
      "church-cfa" => {
         let nn = arg(&args, 2, 2);
         let minm = arg(&args, 3, 0);
         let maxm = arg(&args, 4, 4);
         let facts = Facts::from_ast(&scheme_mcfa::church_term(nn));
         println!("church(sum 0..={nn}) polyvariance sweep ({} input facts)\n", facts.len());
         println!("{:>3}  {:>12}  {:>12}", "m", "derived", "time");
         for m in minm..=maxm {
            let start = Instant::now();
            let stats = scheme_mcfa::analyze_generic(&facts, m);
            println!("{:>3}  {:>12}  {:>12.3?}", m, stats.total_derived(), start.elapsed());
         }
      },
      "structured" => {
         let n = arg(&args, 2, 8);
         let k = arg(&args, 3, 2);
         let p = arg(&args, 4, 0);
         let m = arg(&args, 5, 1);
         structured_vs_flat(n, k, p, m);
      },
      "aam" => {
         let n = arg(&args, 2, 10);
         let k = arg(&args, 3, 3);
         let p = arg(&args, 4, 0);
         let m = arg(&args, 5, 1);
         aam_vs_datalog(&worst_case_term(n, k, p), &format!("worst-case N={n} K={k} P={p}"), m);
      },
      "aam-church" => {
         let nn = arg(&args, 2, 40);
         let m = arg(&args, 3, 1);
         aam_vs_datalog(&scheme_mcfa::church_term(nn), &format!("church(sum 0..={nn})"), m);
      },
      "church-par" => {
         // Parallel run on the Church benchmark; threads from RAYON_NUM_THREADS.
         let nn = arg(&args, 2, 60);
         let m = arg(&args, 3, 1);
         let facts = Facts::from_ast(&scheme_mcfa::church_term(nn));
         let start = Instant::now();
         let stats = scheme_mcfa::analyze_generic_par(&facts, m);
         let elapsed = start.elapsed();
         let threads = std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "default".into());
         println!(
            "ascent_par church(0..={nn}) m={m} threads={threads}  derived={}  time={:.3?}",
            stats.total_derived(),
            elapsed
         );
      },
      "par" => {
         // Parallel run; thread count comes from RAYON_NUM_THREADS.
         let n = arg(&args, 2, 12);
         let k = arg(&args, 3, 3);
         let p = arg(&args, 4, 0);
         let m = arg(&args, 5, 1);
         let facts = Facts::from_ast(&worst_case_term(n, k, p));
         let start = Instant::now();
         let stats = scheme_mcfa::analyze_generic_par(&facts, m);
         let elapsed = start.elapsed();
         let threads = std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "default".into());
         println!(
            "ascent_par N={n} K={k} P={p} m={m} threads={threads}  derived={}  time={:.3?}",
            stats.total_derived(),
            elapsed
         );
      },
      "emit-souffle" | "emit-souffle-single" | "emit-souffle-church" => {
         let dir = args.get(2).cloned().unwrap_or_else(|| {
            eprintln!("{cmd} needs a target DIR");
            std::process::exit(1);
         });
         let n = arg(&args, 3, 20);
         let k = arg(&args, 4, 3);
         let p = arg(&args, 5, 0);
         let ast = if cmd == "emit-souffle-single" {
            scheme_mcfa::worst_case_term_single(n, k, p)
         } else if cmd == "emit-souffle-church" {
            scheme_mcfa::church_term(n)
         } else {
            worst_case_term(n, k, p)
         };
         let facts = Facts::from_ast(&ast);
         facts.write_souffle(Path::new(&dir)).expect("write souffle facts");
         println!("wrote {} input facts for term N={n} K={k} P={p} into {dir}", facts.len());
      },
      "dump" => {
         let dir = args.get(2).cloned().unwrap_or_else(|| {
            eprintln!("dump needs a target DIR");
            std::process::exit(1);
         });
         let n = arg(&args, 3, 4);
         let k = arg(&args, 4, 2);
         let p = arg(&args, 5, 1);
         dump(&dir, n, k, p);
      },
      "emit-egglog" => {
         let file = args.get(2).cloned().unwrap_or_else(|| {
            eprintln!("emit-egglog needs a target FILE");
            std::process::exit(1);
         });
         let (ast, desc) = parse_termspec(&args, 3);
         let facts = Facts::from_ast(&ast);
         emit_egglog(Path::new(&file), &facts).expect("write egglog facts");
         println!("wrote {} input facts ({desc}) as egglog facts into {file}", facts.len());
      },
      "emit-flix" => {
         let dir = args.get(2).cloned().unwrap_or_else(|| {
            eprintln!("emit-flix needs a target DIR");
            std::process::exit(1);
         });
         let (ast, desc) = parse_termspec(&args, 3);
         let facts = Facts::from_ast(&ast);
         facts.write_souffle(Path::new(&dir)).expect("write souffle/flix facts");
         println!("wrote {} input facts ({desc}) as flix/souffle .facts files into {dir}", facts.len());
      },
      "expected" => {
         let (ast, desc) = parse_termspec(&args, 2);
         let facts = Facts::from_ast(&ast);
         eprintln!("expected counts for {desc} ({} input facts)", facts.len());
         let mut prog = facts.into_tuned_program();
         prog.run();
         println!("state_e {}", prog.state_e.len());
         println!("state_a {}", prog.state_a.len());
         println!("stored_val {}", prog.stored_val.len());
         println!("stored_kont {}", prog.stored_kont.len());
         println!("flow_ee {}", prog.flow_ee.len());
         println!("flow_ea {}", prog.flow_ea.len());
         println!("flow_ae {}", prog.flow_ae.len());
         println!("flow_aa {}", prog.flow_aa.len());
         println!("peek_ctx {}", prog.peek_ctx.len());
         println!("copy_ctx {}", prog.copy_ctx.len());
         println!("freevar {}", prog.freevar.len());
      },
      other => {
         eprintln!("unknown command: {other}");
         eprintln!(
            "usage: mcfa [run N K P | bench | emit-souffle DIR N K P | dump DIR N K P \
             | emit-egglog FILE <termspec> | emit-flix DIR <termspec> | expected <termspec>]"
         );
         eprintln!("  <termspec> := worst N K P | church N | feature");
         std::process::exit(1);
      },
   }
}

fn arg(args: &[String], i: usize, default: usize) -> usize {
   args.get(i).and_then(|s| s.parse().ok()).unwrap_or(default)
}

/// Parse a `<termspec>` — `worst N K P` | `church N` | `feature` — starting at
/// `args[i]`, returning the built [`scheme_mcfa::Ast`] and a short description.
/// Shared by `emit-egglog`, `emit-flix`, and `expected`.
fn parse_termspec(args: &[String], i: usize) -> (scheme_mcfa::Ast, String) {
   let kind = args.get(i).map(|s| s.as_str()).unwrap_or("worst");
   match kind {
      "worst" => {
         let n = arg(args, i + 1, 20);
         let k = arg(args, i + 2, 3);
         let p = arg(args, i + 3, 0);
         (worst_case_term(n, k, p), format!("worst N={n} K={k} P={p}"))
      },
      "church" => {
         let n = arg(args, i + 1, 8);
         (scheme_mcfa::church_term(n), format!("church(sum 0..={n})"))
      },
      "feature" => (scheme_mcfa::feature_term(), "feature".to_string()),
      other => {
         eprintln!("unknown term spec: {other}");
         eprintln!("expected: worst N K P | church N | feature");
         std::process::exit(1);
      },
   }
}

/// Write `facts` (plus the precomputed `freevar` relation) as one egglog fact
/// per line into `path`: `(relation "str-arg" ... i64-arg ...)`, strings
/// double-quoted, i64s bare. Relation names/arities mirror the Soufflé ones
/// (`bool` -> `boolean`, `if` -> `if_`, `let` -> `let_`); `prim` and
/// `quotation` are skipped since the rules never read them.
fn emit_egglog(path: &Path, facts: &Facts) -> std::io::Result<()> {
   use std::fs::File;
   use std::io::Write;

   let mut f = File::create(path)?;
   let q = |s: &str| format!("\"{s}\"");

   for (a,) in &facts.top_exp {
      writeln!(f, "(top_exp {})", q(a))?;
   }
   for (a, b, c) in &facts.lambda {
      writeln!(f, "(lambda {} {} {})", q(a), q(b), q(c))?;
   }
   for (vars, pos, x) in &facts.lambda_arg_list {
      writeln!(f, "(lambda_arg_list {} {pos} {})", q(vars), q(x))?;
   }
   for (a, op, args) in &facts.prim_call {
      writeln!(f, "(prim_call {} {} {})", q(a), q(op), q(args))?;
   }
   for (a, func, args) in &facts.call {
      writeln!(f, "(call {} {} {})", q(a), q(func), q(args))?;
   }
   for (args, pos, x) in &facts.call_arg_list {
      writeln!(f, "(call_arg_list {} {pos} {})", q(args), q(x))?;
   }
   for (a, x) in &facts.var {
      writeln!(f, "(var {} {})", q(a), q(x))?;
   }
   for (a, n) in &facts.num {
      writeln!(f, "(num {} {n})", q(a))?;
   }
   for (a, b) in &facts.boolean {
      writeln!(f, "(boolean {} {})", q(a), q(b))?;
   }
   for (a, guard, t, fa) in &facts.if_ {
      writeln!(f, "(if_ {} {} {} {})", q(a), q(guard), q(t), q(fa))?;
   }
   for (a, x, e) in &facts.setb {
      writeln!(f, "(setb {} {} {})", q(a), q(x), q(e))?;
   }
   for (a, e) in &facts.callcc {
      writeln!(f, "(callcc {} {})", q(a), q(e))?;
   }
   for (a, binds, body) in &facts.let_ {
      writeln!(f, "(let_ {} {} {})", q(a), q(binds), q(body))?;
   }
   for (binds, x, e) in &facts.let_list {
      writeln!(f, "(let_list {} {} {})", q(binds), q(x), q(e))?;
   }
   for (x, e) in scheme_mcfa::freevars(facts) {
      writeln!(f, "(freevar {} {})", q(&x), q(&e))?;
   }
   Ok(())
}

fn run_once(n: usize, k: usize, p: usize, verbose: bool) {
   let facts = Facts::from_ast(&worst_case_term(n, k, p));
   let n_input = facts.len();
   let mut prog = facts.into_program();

   let start = Instant::now();
   prog.run();
   let elapsed = start.elapsed();

   let derived = prog.state_e.len()
      + prog.state_a.len()
      + prog.stored_val.len()
      + prog.stored_kont.len()
      + prog.flow_ee.len()
      + prog.flow_ea.len()
      + prog.flow_ae.len()
      + prog.flow_aa.len();

   if verbose {
      println!("term N={n} K={k} P={p}");
      println!("  input facts:   {n_input}");
      println!("  state_e:       {}", prog.state_e.len());
      println!("  state_a:       {}", prog.state_a.len());
      println!("  stored_val:    {}", prog.stored_val.len());
      println!("  stored_kont:   {}", prog.stored_kont.len());
      println!(
         "  flow_ee/ea/ae/aa: {}/{}/{}/{}",
         prog.flow_ee.len(),
         prog.flow_ea.len(),
         prog.flow_ae.len(),
         prog.flow_aa.len()
      );
      println!("  total derived: {derived}");
      println!("  time:          {:.3?}", elapsed);
   } else {
      println!("N={n:<4} K={k:<3} P={p:<2} input={n_input:<6} derived={derived:<8} time={:>10.3?}", elapsed);
   }
}

/// Variation: run the generalized analysis at m = 0, 1, 2 on the same term,
/// reproducing the paper's headline experiment. With too little polyvariance
/// (small m) distinct calls are conflated and the analysis explodes; with
/// enough context it is precise and fast (cf. Table 1).
fn cfa_sweep(n: usize, k: usize, p: usize) {
   use scheme_mcfa::{Facts, analyze_generic, worst_case_term};
   let facts = Facts::from_ast(&worst_case_term(n, k, p));
   println!("m-CFA polyvariance sweep on worst-case term N={n} K={k} P={p} ({} input facts)\n", facts.len());
   println!("{:>3}  {:>12}  {:>12}", "m", "derived", "time");
   for m in 0..=2 {
      let start = Instant::now();
      let stats = analyze_generic(&facts, m);
      let elapsed = start.elapsed();
      println!("{:>3}  {:>12}  {:>12.3?}", m, stats.total_derived(), elapsed);
   }
}

/// Variation: compare the structured-syntax analysis (in both labelings)
/// against the flat (id-relation) analysis on the same source term, at the
/// same `m`. The occurrence-labelled run should match the flat one
/// relation-for-relation; the hash-consed one identifies structurally equal
/// subterms.
fn structured_vs_flat(n: usize, k: usize, p: usize, m: usize) {
   use scheme_mcfa::{Facts, analyze_generic, analyze_structured, to_expr, to_expr_labeled, worst_case_term};
   let ast = worst_case_term(n, k, p);

   let t0 = Instant::now();
   let flat = analyze_generic(&Facts::from_ast(&ast), m);
   let flat_t = t0.elapsed();

   let t1 = Instant::now();
   let labeled = analyze_structured(&to_expr_labeled(&ast), m);
   let labeled_t = t1.elapsed();

   let t2 = Instant::now();
   let hashconsed = analyze_structured(&to_expr(&ast), m);
   let hashconsed_t = t2.elapsed();

   println!("term N={n} K={k} P={p}, m={m}\n");
   println!("{:<14} {:>14} {:>14} {:>14}", "relation", "flat (ids)", "labelled", "hash-consed");
   let rows = [
      ("state_e", flat.state_e, labeled.state_e, hashconsed.state_e),
      ("state_a", flat.state_a, labeled.state_a, hashconsed.state_a),
      ("stored_val", flat.stored_val, labeled.stored_val, hashconsed.stored_val),
      ("stored_kont", flat.stored_kont, labeled.stored_kont, hashconsed.stored_kont),
      ("flow_ee", flat.flow_ee, labeled.flow_ee, hashconsed.flow_ee),
      ("flow_ea", flat.flow_ea, labeled.flow_ea, hashconsed.flow_ea),
      ("flow_ae", flat.flow_ae, labeled.flow_ae, hashconsed.flow_ae),
      ("flow_aa", flat.flow_aa, labeled.flow_aa, hashconsed.flow_aa),
      ("peek_ctx", flat.peek_ctx, labeled.peek_ctx, hashconsed.peek_ctx),
      ("copy_ctx", flat.copy_ctx, labeled.copy_ctx, hashconsed.copy_ctx),
   ];
   for (name, a, b, c) in rows {
      println!("{name:<14} {a:>14} {b:>14} {c:>14}");
   }
   println!(
      "{:<14} {:>14} {:>14} {:>14}",
      "total derived",
      flat.total_derived(),
      labeled.total_derived(),
      hashconsed.total_derived()
   );
   println!("{:<14} {:>14.3?} {:>14.3?} {:>14.3?}", "time", flat_t, labeled_t, hashconsed_t);
}

/// Variation: the identical analysis without Datalog — the hand-written
/// abstract machine (`aam`) vs. the structured Ascent program, on the same
/// occurrence-labelled term. The relation sizes must agree (content equality is
/// checked in `tests/aam_check.rs`); the times are the comparison.
fn aam_vs_datalog(ast: &scheme_mcfa::Ast, name: &str, m: usize) {
   use scheme_mcfa::{analyze_aam, analyze_structured, to_expr_labeled};
   let top = to_expr_labeled(ast);

   let t0 = Instant::now();
   let dl = analyze_structured(&top, m);
   let dl_t = t0.elapsed();

   let t1 = Instant::now();
   let am = analyze_aam(&top, m);
   let am_t = t1.elapsed();

   println!("{name}, m={m}\n");
   println!("{:<14} {:>14} {:>14}", "relation", "ascent", "direct AAM");
   let rows = [
      ("state_e", dl.state_e, am.state_e),
      ("state_a", dl.state_a, am.state_a),
      ("stored_val", dl.stored_val, am.stored_val),
      ("stored_kont", dl.stored_kont, am.stored_kont),
      ("flow_ee", dl.flow_ee, am.flow_ee),
      ("flow_ea", dl.flow_ea, am.flow_ea),
      ("flow_ae", dl.flow_ae, am.flow_ae),
      ("flow_aa", dl.flow_aa, am.flow_aa),
   ];
   for (rel, a, b) in rows {
      let mark = if a == b { "" } else { "   <-- MISMATCH" };
      println!("{rel:<14} {a:>14} {b:>14}{mark}");
   }
   println!("{:<14} {:>14} {:>14}", "total derived", dl.total_derived(), am.total_derived());
   println!("{:<14} {:>14.3?} {:>14.3?}", "time", dl_t, am_t);
   println!(
      "\naam steps: {} over {} states (re-steps from store growth: {})",
      am.steps,
      am.state_e + am.state_a,
      am.steps - (am.state_e + am.state_a)
   );
}

/// Compare every in-process engine on one term at `m = 1`: the three flat
/// Datalog ports (faithful `ascent!`, tuned, generic vector-context), the two
/// structured Datalog ports (labelled syntax; untuned and tuned), and the two
/// hand-written machines (textbook step machine, event-driven delta worklist).
/// Set MCFA_SUMMARY=1 to print ascent's per-SCC summaries for the item-macro
/// programs. Set MCFA_FAST_ONLY=1 to skip the naive (untuned) ports — useful
/// on large terms where they are asymptotically much slower.
fn engines(ast: &scheme_mcfa::Ast, which: &str) {
   use scheme_mcfa::{
      analyze_aam, analyze_aam_delta, analyze_generic, analyze_structured, analyze_structured_tuned, to_expr_labeled,
   };
   let facts = Facts::from_ast(ast);
   let top = to_expr_labeled(ast);
   let fast_only = std::env::var("MCFA_FAST_ONLY").is_ok();
   println!("engine comparison ({which}), m=1, {} input facts\n", facts.len());

   let row = |name: &str, derived: usize, t: std::time::Duration| {
      println!("  {name:<34} derived={derived:<8} time={t:>10.3?}");
   };

   if !fast_only {
      // Ascent, flat id-relations: faithful ascent! port.
      let mut p = facts.clone().into_program();
      let t = Instant::now();
      p.run();
      let derived = p.state_e.len()
         + p.state_a.len()
         + p.stored_val.len()
         + p.stored_kont.len()
         + p.flow_ee.len()
         + p.flow_ea.len()
         + p.flow_ae.len()
         + p.flow_aa.len();
      row("ascent (flat, faithful)", derived, t.elapsed());
      if std::env::var("MCFA_SUMMARY").is_ok() {
         println!("--- ascent! scc summary ---\n{}", p.scc_times_summary());
      }
   }

   // Ascent, flat: tuned (delta-friendly rules).
   let mut pt = facts.clone().into_tuned_program();
   let t = Instant::now();
   pt.run();
   let derived_t = pt.state_e.len()
      + pt.state_a.len()
      + pt.stored_val.len()
      + pt.stored_kont.len()
      + pt.flow_ee.len()
      + pt.flow_ea.len()
      + pt.flow_ae.len()
      + pt.flow_aa.len();
   row("ascent (flat, tuned)", derived_t, t.elapsed());
   if std::env::var("MCFA_SUMMARY").is_ok() {
      println!("--- tuned scc summary ---\n{}", pt.scc_times_summary());
   }

   if !fast_only {
      // Ascent, flat: generic (ascent_run!, vector context).
      let t = Instant::now();
      let g = analyze_generic(&facts, 1);
      row("ascent (flat, generic)", g.total_derived(), t.elapsed());

      // Ascent, labelled structured syntax.
      let t = Instant::now();
      let s = analyze_structured(&top, 1);
      row("ascent (structured)", s.total_derived(), t.elapsed());
   }

   // Ascent, labelled structured syntax, tuned.
   let t = Instant::now();
   let st = analyze_structured_tuned(&top, 1);
   row("ascent (structured, tuned)", st.total_derived(), t.elapsed());

   // Hybrid: Ascent for the both-sides-growing joins, Rust for the stepping.
   let t = Instant::now();
   let h = scheme_mcfa::analyze_structured_hybrid(&top, 1);
   row("hybrid (ascent joins + Rust step)", h.total_derived(), t.elapsed());

   // Hybrid, memoizing: the apply join enumerated once, outputs materialized.
   let t = Instant::now();
   let hm = scheme_mcfa::analyze_structured_hybrid_memo(&top, 1);
   row("hybrid (memoized apply_out)", hm.total_derived(), t.elapsed());

   // Raw Rust: textbook step machine.
   let t = Instant::now();
   let a = analyze_aam(&top, 1);
   row("AAM (step machine)", a.total_derived(), t.elapsed());

   // Raw Rust: event-driven delta worklist.
   let t = Instant::now();
   let d = analyze_aam_delta(&top, 1);
   row("AAM (delta worklist)", d.total_derived(), t.elapsed());
}

fn fmt_ctx(c: &Ctx) -> String { format!("$Context({})", c.0) }
fn fmt_addrk(a: &AddrK) -> String { format!("$KAddress({}, {})", a.e, fmt_ctx(&a.ctx)) }

/// Dump ascent's pure-id relations in Soufflé's textual format so they can be
/// diffed against Soufflé's `.csv` output on the same input (content-level
/// cross-validation of the port).
fn dump(dir: &str, n: usize, k: usize, p: usize) {
   use std::fs;
   let prog = scheme_mcfa::analyze(&worst_case_term(n, k, p));
   let dir = std::path::Path::new(dir);
   fs::create_dir_all(dir).unwrap();

   let write = |name: &str, mut rows: Vec<String>| {
      rows.sort();
      fs::write(dir.join(format!("{name}.csv")), rows.join("\n") + "\n").unwrap();
   };

   write("flow_ee", prog.flow_ee.iter().map(|(a, b)| format!("{a}\t{b}")).collect());
   write("freevar", prog.freevar.iter().map(|(x, e)| format!("{x}\t{e}")).collect());
   write("peek_ctx", prog.peek_ctx.iter().map(|(e, o, nw)| format!("{e}\t{}\t{}", fmt_ctx(o), fmt_ctx(nw))).collect());
   write("copy_ctx", prog.copy_ctx.iter().map(|(f, t, e)| format!("{}\t{}\t{e}", fmt_ctx(f), fmt_ctx(t))).collect());
   write("state_e", prog.state_e.iter().map(|(e, c, ak)| format!("{e}\t{}\t{}", fmt_ctx(c), fmt_addrk(ak))).collect());
   println!("dumped ascent relations (N={n} K={k} P={p}) to {}", dir.display());
}

/// A basic benchmark: run the faithful (appendix, `m=1`) analysis over a
/// handful of worst-case term sizes so the whole sweep takes a
/// measurable-but-modest amount of time (a few seconds total).
///
/// At `m=1` the `N` calls to `f` are conflated, so `z` takes `N` abstract
/// values which then combine through the `K` nested `+`s, producing the
/// polynomial `PrimVal` blow-up the paper studies. Cost grows with both `N`
/// and (steeply) `K`.
fn bench() {
   println!("m-CFA (Ascent, faithful m=1) — worst-case term sweep");
   println!("(N = calls to f, K = nested + applications, P = identity padding)\n");
   let configs = [(6, 2, 0), (8, 2, 0), (10, 3, 0), (12, 3, 0), (8, 4, 0)];
   for (n, k, p) in configs {
      run_once(n, k, p, false);
   }
}
