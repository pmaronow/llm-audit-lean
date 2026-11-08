#!/bin/bash
# comparator_controls.sh: strict controls for run_comparator.py in a scratch worktree ~/sap/wt/CTRL.
# A accept; B changed definition under an unchanged theorem statement -> reject; C Solution uses sorry -> reject;
# D configured theorem missing from the Solution -> reject. Exits nonzero if any control behaves otherwise.
set -u
W=$HOME/sap/wt/CTRL; T=$HOME/sap/tools
test -d $W || $T/mkwt.sh CTRL >/dev/null
cd $W
cfg() { cat > SAP/$1/comparator.json <<EOF
{"challenge_module": "SAP.$1.Challenge", "solution_module": "SAP.$1.Solution", "theorem_names": [$2],
 "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
 "external_kernels": {"con-ron": ["con-ron", "--verified", "--jobs=2"], "nanoda": ["nanoda_bin"]}}
EOF
}
for X in A B C D; do
  rm -rf SAP/CTRL$X .lake/build/lib/lean/SAP/CTRL$X; mkdir -p SAP/CTRL$X
  printf 'import Mathlib\nnamespace SAP.CTRL%s\ndef double (n : ℕ) : ℕ := n + n\nend SAP.CTRL%s\n' $X $X > SAP/CTRL$X/Defs.lean
  printf 'import SAP.CTRL%s.Defs\n/-- control -/\ntheorem SAP.CTRL%s.T1 : SAP.CTRL%s.double 2 = 4 := by sorry\n' $X $X $X > SAP/CTRL$X/Challenge.lean
done
# A: correct
printf 'import SAP.CTRLA.Defs\ntheorem SAP.CTRLA.T1 : SAP.CTRLA.double 2 = 4 := rfl\n' > SAP/CTRLA/Solution.lean; cfg CTRLA '"SAP.CTRLA.T1"'
# B: the Solution environment defines the same name with a different body (Challenge uses Orig-style copy)
printf 'import Mathlib\nnamespace SAP.CTRLB\ndef double (n : ℕ) : ℕ := 2 * n\nend SAP.CTRLB\n' > SAP/CTRLB/Impl.lean
printf 'import SAP.CTRLB.Impl\ntheorem SAP.CTRLB.T1 : SAP.CTRLB.double 2 = 4 := rfl\n' > SAP/CTRLB/Solution.lean; cfg CTRLB '"SAP.CTRLB.T1"'
# C: sorry in the Solution
printf 'import SAP.CTRLC.Defs\ntheorem SAP.CTRLC.T1 : SAP.CTRLC.double 2 = 4 := by sorry\n' > SAP/CTRLC/Solution.lean; cfg CTRLC '"SAP.CTRLC.T1"'
# D: a configured theorem missing from the Solution
printf 'import SAP.CTRLD.Defs\ntheorem SAP.CTRLD.T1 : SAP.CTRLD.double 2 = 4 := rfl\n' > SAP/CTRLD/Solution.lean
printf '\n/-- control -/\ntheorem SAP.CTRLD.T2 : SAP.CTRLD.double 3 = 6 := by sorry\n' >> SAP/CTRLD/Challenge.lean; cfg CTRLD '"SAP.CTRLD.T1", "SAP.CTRLD.T2"'
for X in A B C D; do
  F="SAP/CTRL$X/Defs.lean"; [ $X = B ] && F="$F SAP/CTRLB/Impl.lean"
  out=$($T/sap-lean $F SAP/CTRL$X/Challenge.lean SAP/CTRL$X/Solution.lean 2>&1) || { [ $X = C ] && echo "$out" | grep -q "declaration uses 'sorry'" || { echo "compile CTRL$X failed: $out" | tail -3; exit 1; }; }
done
ok=1
expect() { # WORK expected(accept|reject) pattern
  out=$(python3 $T/run_comparator.py $W $1 --control 2>&1); rc=$?
  if [ $2 = accept ]; then [ $rc = 0 ] && echo "$1: accepted (expected)" || { echo "$1: UNEXPECTED REJECT: $out" | tail -3; ok=0; }
  else if [ $rc != 0 ] && echo "$out" | grep -qiE "$3"; then echo "$1: rejected (expected): $(echo "$out" | grep -oiE "$3" | head -1)"; else echo "$1: UNEXPECTED: rc=$rc $(echo "$out" | tail -2)"; ok=0; fi; fi
}
expect CTRLA accept
expect CTRLB reject "Const does not match between challenge and target 'SAP.CTRLB.double'"
expect CTRLC reject "rebuild from snapshot failed|sorryAx|Axiom 'sorryAx' is not permitted"
expect CTRLD reject "not found in solution|SAP.CTRLD.T2"
[ $ok = 1 ] && echo "ALL CONTROLS OK" || { echo "CONTROLS FAILED"; exit 1; }
