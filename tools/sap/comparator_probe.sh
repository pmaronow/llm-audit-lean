#!/bin/bash
# Probe: can v4.34.1 code be certified by the 4.35 Palomar Comparator via explicit exports?
# 1) build lean4export v4.34.0 with the v4.34.1 toolchain; 2) export a toy Challenge/Solution built with v4.34.1;
# 3) run v4.35.0-rc2 `lake comparator --challenge-from-export --solution-from-export`; 4) a negative control (wrong
# statement) must be rejected.
set -u
export PATH=$HOME/.elan/bin:$PATH
D=$HOME/sap/deps; P=$HOME/sap/probe; mkdir -p $D $P; cd $D
if [ ! -x lean4export/.lake/build/bin/lean4export ]; then
  rm -rf lean4export; git clone -q --depth 1 --branch v4.34.0 https://github.com/leanprover/lean4export.git
  cd lean4export && echo "leanprover/lean4:v4.34.1" > lean-toolchain && lake build 2>&1 | tail -3; cd $D
fi
EXP=$D/lean4export/.lake/build/bin/lean4export; ls -la $EXP || exit 1
rm -rf $P/toy && mkdir -p $P/toy && cd $P/toy
echo "leanprover/lean4:v4.34.1" > lean-toolchain
cat > lakefile.toml <<'EOF'
name = "toy"
defaultTargets = ["Challenge", "Solution", "Wrong"]
[[lean_lib]]
name = "Challenge"
[[lean_lib]]
name = "Solution"
[[lean_lib]]
name = "Wrong"
EOF
cat > Challenge.lean <<'EOF'
def double (n : Nat) : Nat := n + n
theorem double_two : double 2 = 4 := sorry
EOF
cat > Solution.lean <<'EOF'
def double (n : Nat) : Nat := n + n
theorem double_two : double 2 = 4 := rfl
EOF
cat > Wrong.lean <<'EOF'
def double (n : Nat) : Nat := n + n
theorem double_two : double 2 = 2 + 2 := rfl
EOF
lake build 2>&1 | tail -2
# export targets = theorem names + the Comparator's primitive targets (as in the superfluid precedent) + permitted axioms
PRIM=$(python3 - <<'PY'
import re, pathlib
src = pathlib.Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0-rc2/src/lean/lake/Lake/CLI/Check.lean"
t = src.read_text(); prim = t.split("def primitiveTargets", 1)[1].split("def builtinTargets", 1)[0]
prim = re.sub(r"--[^\n]*", "", prim)
names = re.findall(r"``([A-Za-z0-9_.]+)", prim) + ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", "propext", "Quot.sound", "Classical.choice"]
print(" ".join(dict.fromkeys(names)))
PY
)
echo "primitive targets: $(echo $PRIM | wc -w)"
for m in Challenge Solution Wrong; do lake env $EXP $m -- double_two $PRIM > $m.ndjson 2> $m.err; echo "export $m rc=$? bytes=$(wc -c < $m.ndjson)"; head -c 400 $m.err; done
head -c 300 Solution.ndjson; echo
cat > comparator.json <<'EOF'
{"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["double_two"],
 "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": true}
EOF
# run the 4.35 comparator from a 4.35 workspace
export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin:$PATH
mkdir -p $P/cmp && cd $P/cmp && echo "leanprover/lean4:v4.35.0-rc2" > lean-toolchain && printf 'name = "cmp"\n' > lakefile.toml
echo "== positive"; lake comparator --config $P/toy/comparator.json --challenge-from-export $P/toy/Challenge.ndjson --solution-from-export $P/toy/Solution.ndjson 2>&1 | tail -8
echo "== negative (statement changed)"; lake comparator --config $P/toy/comparator.json --challenge-from-export $P/toy/Challenge.ndjson --solution-from-export $P/toy/Wrong.ndjson 2>&1 | tail -5
