#!/usr/bin/env python3
"""rebuild_sap.py WORKTREE WORK: delete the worktree's compiled SAP/<WORK> outputs and recompile every SAP/<WORK> module
from source with sap-lean, in import order (topological sort of imports inside SAP/<WORK>). Also scans the sources for
forbidden tokens (comments and strings stripped): `sorry` is allowed only in SAP/<WORK>/Challenge*; never `admit`,
`axiom`, `native_decide`, `implemented_by`, `unsafe`, `opaque`. Exits nonzero on any failure."""
import re, subprocess, sys, pathlib, shutil
W, WORK = pathlib.Path(sys.argv[1]).resolve(), sys.argv[2]
SAP = W / "SAP" / WORK
out = W / ".lake/build/lib/lean/SAP" / WORK
if out.exists(): shutil.rmtree(out)
mods = {str(p.relative_to(W))[:-5].replace("/", "."): p for p in SAP.rglob("*.lean") if "verification" not in p.parts}
def strip(s):
    s = re.sub(r"/-.*?-/", "", s, flags=re.S); s = re.sub(r"--[^\n]*", "", s); return re.sub(r'"(?:\\.|[^"\\])*"', '""', s)
bad = []
for m, p in mods.items():
    code = strip(p.read_text())
    for tok in ("admit", "axiom", "native_decide", "implemented_by", "unsafe", "opaque"):
        if re.search(rf"\b{tok}\b", code): bad.append((m, tok))
    if re.search(r"\bsorry\b", code) and not m.startswith(f"SAP.{WORK}.Challenge"): bad.append((m, "sorry"))
if bad: sys.exit(f"forbidden tokens: {bad}")
deps = {m: [i for i in re.findall(r"^import\s+(\S+)", p.read_text(), re.M) if i in mods] for m, p in mods.items()}
order, seen = [], set()
def visit(m, stack=()):
    if m in seen: return
    if m in stack: sys.exit(f"import cycle at {m}")
    for d in deps[m]: visit(d, stack + (m,))
    seen.add(m); order.append(m)
for m in sorted(mods): visit(m)
for m in order:
    f = str(mods[m].relative_to(W))
    p = subprocess.run([str(pathlib.Path.home() / "sap/tools/sap-lean"), f], cwd=W, capture_output=True, text=True)
    errs = [l for l in (p.stdout + p.stderr).splitlines() if ": error" in l or l.startswith("error")]
    sorrywarn = "declaration uses 'sorry'" in p.stdout + p.stderr
    if p.returncode or errs: sys.exit(f"compile failed: {m}\n" + "\n".join(errs[:10]))
    if sorrywarn and not m.startswith(f"SAP.{WORK}.Challenge"): sys.exit(f"sorry warning outside Challenge: {m}")
print(f"rebuilt {len(order)} modules of SAP/{WORK}; token scan clean")
