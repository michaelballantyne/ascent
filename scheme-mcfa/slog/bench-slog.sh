#!/usr/bin/env bash
#
# Benchmark the Slog m-CFA port (faithful mcfa.slog + tuned mcfa-tuned.slog)
# on the crate's benchmark terms, validating both against the Ascent
# structured analysis (per-occurrence labels, m = 1) as they run.
#
#   SLOG_DIR=/path/to/slog ./bench-slog.sh                 # default term sweep
#   SLOG_DIR=... ./bench-slog.sh "worst 8 3 0" "church 20" # chosen terms
#   REPS=5 SLOG_DIR=... ./bench-slog.sh                    # more repetitions
#
# STAGED workflow (see slog/README.md "Programs and databases"): mcfa.slog /
# mcfa-tuned.slog never change across terms, so recompiling them per term
# (a multi-minute clang -O2 build) is wasted work.  Instead, for each term:
#   1. emit a tiny per-term "loader" program (`mcfa emit-slog-db`): just the
#      syntax type declarations (`mcfa-syntax.slog`, shared with mcfa.slog /
#      mcfa-tuned.slog) plus a `(top <term>)` fact, plus a sidecar
#      `.expected` of relation cardinalities from the Ascent run;
#   2. run the loader ONCE per term with `--out-db`, saving the labelled
#      term as a Slog database -- this compiles a tiny, cheap plugin
#      regardless of term size;
#   3. run mcfa.slog / mcfa-tuned.slog with `-d` against that saved
#      database, REPS times each, reporting the median summed per-stratum
#      fixpoint time (the daemon's "(fixpoint <scc> <name> <iters> <ms>)"
#      lines -- pure evaluation, no compile/parse/CSV time). Because the
#      analysis files' rule text never changes across terms, their compiled
#      plugins are a cache hit after the very first time they are ever
#      compiled -- so only the FIRST term in a whole sweep pays their
#      clang -O2 compile.
#   4. check every output relation's row count against `.expected`, and
#      diff the tuned run's output relations against the faithful run's
#      row-for-row.
#
# The Ascent-side numbers for the same terms come from the crate's own
# benchmark:  cargo run --release -p scheme-mcfa -- engines worst N K P
set -u

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
WS_DIR="$(dirname "$(dirname "$SCRIPT_DIR")")"
SLOG_DIR="${SLOG_DIR:?set SLOG_DIR to the slog repository root}"
WORK="${WORK:-$SCRIPT_DIR/bench-out}"
REPS="${REPS:-3}"
TIMEOUT="${TIMEOUT:-900}"
# Prefix for the `data/<name>` databases this script creates under
# $SLOG_DIR, so it doesn't collide with unrelated saved databases.
DB_PREFIX="${DB_PREFIX:-mcfa-bench}"

mkdir -p "$WORK"
cargo build --release -p scheme-mcfa --manifest-path "$WS_DIR/Cargo.toml" >/dev/null || exit 1
EMIT="$WS_DIR/target/release/mcfa"

specs=("$@")
if [ ${#specs[@]} -eq 0 ]; then
  specs=("feature" "worst 8 3 0" "worst 12 3 0" "church 20" "church 40" "church 80")
fi

# Sum the fixpoint milliseconds in one run's log.
evalms() {
  awk '/^\(fixpoint / { v = $NF; gsub(/\)/, "", v); s += v + 0 }
       END { printf "%.1f", s }' "$1"
}

# Median of a list of floats.
median() {
  printf '%s\n' "$@" | LC_ALL=C sort -g | awk '{ a[NR] = $1 }
    END { print (NR % 2) ? a[(NR+1)/2] : (a[NR/2] + a[NR/2+1]) / 2 }'
}

# Output relations shared by both variants (and, minus result/freevar,
# checked against the Ascent .expected counts).
RELS="state_e state_a stored_val stored_kont flow_ee flow_ea flow_ae flow_aa peek_ctx copy_ctx"

# mcfa.slog / mcfa-tuned.slog's `include "mcfa-syntax.slog"` resolves
# relative to wherever THEY live, so copy the syntax file alongside them.
# Their text is otherwise never touched per-term -- this is exactly what
# lets their compiled plugins stay a cache hit across the whole sweep.
cp "$SCRIPT_DIR/mcfa-syntax.slog" "$SCRIPT_DIR/mcfa.slog" "$SCRIPT_DIR/mcfa-tuned.slog" "$WORK/"

printf "%-16s %-9s %5s | %12s | %s\n" "term" "variant" "reps" "fixpoint-ms" "validation"
printf '%.0s-' {1..72}; echo

for spec in "${specs[@]}"; do
  name="$(echo "$spec" | tr ' ' '-')"
  base="$WORK/$name"
  dbname="$DB_PREFIX-$name"

  # 1. Emit the loader-only program (syntax decls + this term's `(top ...)`
  #    fact) and its `.expected` sidecar.
  # shellcheck disable=SC2086
  "$EMIT" emit-slog-db "$base-loader.slog" $spec || { echo "$name: emit FAILED"; continue; }

  # 2. Load it into a saved database, once per term (shared by both
  #    variants and all REPS -- the database is the same input either way).
  #    `slog db` databases are an immutable DAG; delete any stale one from a
  #    prior run of this script before re-creating under the same name.
  rm -rf "$SLOG_DIR/data/$dbname"
  loadlog="$WORK/$name-load.log"
  (cd "$SLOG_DIR" && SLOG_NO_MEM_CAP=1 timeout "$TIMEOUT" \
     racket slog.rkt --no-banner --out-db "$dbname" "$base-loader.slog") > "$loadlog" 2>&1
  if [ $? -ne 0 ]; then
    printf "%-16s %-9s %5s | %12s | %s\n" "$name" "-" "-" "-" "load FAILED (see $loadlog)"
    continue
  fi

  for var in faithful tuned; do
    f="$WORK/mcfa.slog"
    [ "$var" = tuned ] && f="$WORK/mcfa-tuned.slog"
    outdir="$WORK/out-$name-$var"
    declare -a times=()
    fail=""
    for rep in $(seq "$REPS"); do
      rm -rf "$outdir"
      log="$WORK/$name-$var.log"
      (cd "$SLOG_DIR" && SLOG_NO_MEM_CAP=1 timeout "$TIMEOUT" \
         racket slog.rkt --no-banner -d "$dbname" --debug-dir "$outdir" "$f") > "$log" 2>&1
      if [ $? -ne 0 ]; then fail="run FAILED (see $log)"; break; fi
      times+=("$(evalms "$log")")
    done
    if [ -n "$fail" ]; then
      printf "%-16s %-9s %5s | %12s | %s\n" "$name" "$var" "-" "-" "$fail"
      continue
    fi

    # row counts vs the Ascent analysis
    ok="counts-ok"
    while read -r rel exp; do
      got=$(wc -l < "$outdir/$rel.csv" 2>/dev/null || echo 0)
      got="${got:-0}"
      [ "$got" -eq "$exp" ] || ok="MISMATCH($rel: slog=$got ascent=$exp)"
    done < "$base-loader.slog.expected"

    printf "%-16s %-9s %5s | %12s | %s\n" \
           "$name" "$var" "$REPS" "$(median "${times[@]}")" "$ok"
  done

  # tuned must agree with faithful row-for-row on every shared relation
  for rel in $RELS result freevar; do
    a="$WORK/out-$name-faithful/$rel.csv"
    b="$WORK/out-$name-tuned/$rel.csv"
    if ! diff -q <(LC_ALL=C sort "$a" 2>/dev/null) \
                 <(LC_ALL=C sort "$b" 2>/dev/null) > /dev/null 2>&1; then
      echo "  $name: tuned/faithful DIFFER on $rel"
    fi
  done
done
