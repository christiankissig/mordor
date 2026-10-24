#!/bin/bash
# W1 (#175): run a fixed set of programs with MORDOR_SMT_DUMP set, one dump
# directory per run, and record how each run ended in jobs.tsv.
#
#   evaluation/w1_smt_corpus/generate.sh OUT [MORDOR] [TIMEOUT] [THREADS]
#
# OUT      directory for the corpus (must not exist)
# MORDOR   the mordor binary (default: _build/default/cli/main.exe)
# TIMEOUT  seconds per run (default: 600)
# THREADS  --threads for each run (default: 1, so solve times are not
#          measured against each other)
#
# The program set is the tracked files only, so that it is the same on every
# checkout: every litmus test under `run`; programs/*.lit under `run` and
# `run --by-query`; the episodicity programs under `episodicity`; and rcu-2 by
# query at one iteration per loop.
set -u
OUT=$1
MORDOR=$(realpath "${2:-_build/default/cli/main.exe}")
TIMEOUT=${3:-600}
THREADS=${4:-1}
cd "$(git rev-parse --show-toplevel)"
[ -e "$OUT" ] && { echo "$OUT exists" >&2; exit 1; }
mkdir -p "$OUT"
OUT=$(realpath "$OUT")

{
  git ls-files 'litmus-tests/*.lit' | sed 's/^/run\t/'
  git ls-files 'programs/*.lit' | grep -v '^programs/.*/' | sed 's/^/run\t/'
  git ls-files 'programs/*.lit' | grep -v '^programs/.*/' | sed 's/^/run --by-query\t/'
  git ls-files 'programs/episodicity/*.lit' | sed 's/^/episodicity\t/'
  printf 'run --by-query --step-counter-per-loop 1\tevaluation/rcu-2.lit\n'
} > "$OUT/jobs.list"

printf 'job\tcommand\tprogram\texit\tseconds\n' > "$OUT/jobs.tsv"
n=0
while IFS=$'\t' read -r cmd lit; do
  n=$((n + 1))
  job=$(printf '%04d' $n)
  start=$(date +%s.%N)
  MORDOR_SMT_DUMP="$OUT/$job" timeout "$TIMEOUT" "$MORDOR" $cmd --single "$lit" \
    --threads "$THREADS" --no-progress > "$OUT/$job.log" 2>&1
  code=$?
  printf '%s\t%s\t%s\t%d\t%.1f\n' "$job" "$cmd" "$lit" $code \
    "$(echo "$(date +%s.%N) - $start" | bc)" >> "$OUT/jobs.tsv"
done < "$OUT/jobs.list"
echo "$n runs; $(awk -F'\t' 'NR>1 && $4!=0' "$OUT/jobs.tsv" | wc -l) did not exit 0"
