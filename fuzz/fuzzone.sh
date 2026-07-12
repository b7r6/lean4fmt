#!/usr/bin/env bash
# fuzz one file: format(orig) vs format(perturbed_i); spine filter via harness tok/tree
cd /home/b7r6/src/straylight/continuity
f="$1"
base=$(LEAN_PATH=$FMT_LIB:$MERGE:$CORE lean --run /tmp/v2harness.lean "$f" --emit 2>/dev/null)
[ -z "$base" ] && { echo "SKIP(parse) $f"; exit 0; }
for seed in 1 2 3; do
  python3 /tmp/perturb.py "$f" $seed > /tmp/fz-$$.lean
  # spine filter: perturbed must still parse to the same tokens (harness emits or fails)
  pert=$(LEAN_PATH=$FMT_LIB:$MERGE:$CORE lean --run /tmp/v2harness.lean /tmp/fz-$$.lean --emit 2>/dev/null)
  [ -z "$pert" ] && continue   # mutation broke the parse — filtered
  if [ "$base" != "$pert" ]; then echo "DIVERGE seed=$seed $f"; fi
done
rm -f /tmp/fz-$$.lean
echo "DONE $f"
