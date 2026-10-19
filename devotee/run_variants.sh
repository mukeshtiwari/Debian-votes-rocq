#!/bin/sh
# The differential test of the paper: devotee, unmodified and with each of
# the patches in devotee/patches applied, against the verified counter.
# Needs `make` and `sh scripts/fetch_devotee.sh` first. Writes
# devotee/results.txt (about five minutes on a laptop; runs in parallel).
#
#   fix-closure.patch   recompute transitive defeats in every round of step 7
#   fix-weakest.patch   select only the weakest defeats in step 7
#   fix-majority.patch  require V(A,D) > V(D,A) in step 3 (Constitution v1.6+)
set -e
cd "$(dirname "$0")/.."
N=${N:-20000}
SEED=${SEED:-7}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

variant() {   # variant <name> <patch>...
  name=$1; shift
  mkdir -p "$tmp/$name"
  cp devotee/src/dvt-rslt "$tmp/$name/dvt-rslt"
  for p in "$@"; do patch -s "$tmp/$name/dvt-rslt" < "devotee/patches/$p"; done
}
variant unmodified
variant closure fix-closure.patch
variant weakest fix-weakest.patch
variant closure+weakest fix-closure.patch fix-weakest.patch
variant all fix-closure.patch fix-weakest.patch fix-majority.patch

./recount --devotee-batch "$tmp/real.batch" > /dev/null
run() {   # run <variant> <mode args...>
  v=$1; shift
  DVT_RSLT="$tmp/$v/dvt-rslt" ./devotee_diff "$@" > "$tmp/out.$v.$1" 2>&1
}
run unmodified real "$tmp/real.batch" &
run all real "$tmp/real.batch" &
for v in unmodified closure weakest closure+weakest all; do
  run "$v" random-last "$N" "$SEED" &
done
for v in unmodified closure+weakest all; do
  run "$v" random "$N" "$SEED" &
done
wait

{
  echo "devotee $(git -C devotee/src log -1 --format='%h %ad' --date=short); N=$N SEED=$SEED"
  for f in "$tmp"/out.*; do
    b=$(basename "$f"); b=${b#out.}
    echo; echo "######## devotee ${b%.*}, mode ${b##*.}"
    cat "$f"
  done
} > devotee/results.txt
grep -E '^(########|agree|beatpath|  +[0-9])' devotee/results.txt
