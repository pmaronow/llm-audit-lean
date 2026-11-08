#!/usr/bin/env python3
"""axiom_audit.py: `#print axioms` for every distinct credited declaration, in one Lean process against the built
project (~/sap/repo2), and a list of the modules whose build emitted "declaration uses `sorry`".
Writes ~/sap/reports/axioms.json: per declaration the axioms; flags any non-standard axiom (sorryAx etc.)."""
import json, pathlib, subprocess, re, collections, os, sys
H = pathlib.Path.home(); R = H / "sap/repo2"
rows = [json.loads(l) for l in open(H / "sal/repo/catalog/results.jsonl")]
names = sorted({r["lean_name"] for r in rows if r["status"] in ("proved", "counterexample_proved")})
scratch = R / "SAPAudit"; scratch.mkdir(exist_ok=True)
src = scratch / "AxiomsAll.lean"
src.write_text("import AronowAudit.All\n\n" + "".join(f"#print axioms {n}\n" for n in names))
env = {**os.environ, "PATH": f"{H}/.elan/bin:" + os.environ["PATH"], "LEAN_NUM_THREADS": "4"}
p = subprocess.run(["nice", "-n", "15", "lake", "env", "lean", str(src)], cwd=R, env=env, capture_output=True, text=True)
out = p.stdout + p.stderr
(H / "sap/reports").mkdir(exist_ok=True); (H / "sap/reports/axioms-raw.txt").write_text(out)
STD = {"propext", "Classical.choice", "Quot.sound"}
res = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
    res[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
for m in re.finditer(r"'([^']+)' does not depend on any axioms", out):
    res[m.group(1)] = []
missing = [n for n in names if n not in res]
bad = {n: ax for n, ax in res.items() if set(ax) - STD}
json.dump({"declarations": len(names), "reported": len(res), "missing": missing, "nonstandard": bad, "lean_rc": p.returncode,
           "repo2_head": subprocess.run(["git", "-C", str(R), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip(),
           "axioms": res},
          open(H / "sap/reports/axioms.json", "w"), indent=1)
print(f"credited declarations {len(names)}; reported {len(res)}; missing {len(missing)}; nonstandard {len(bad)}; "
      f"lean rc {p.returncode}")
for n, ax in list(bad.items())[:10]: print("  NONSTANDARD", n, ax)
for n in missing[:10]: print("  MISSING", n)
errs = [l for l in out.splitlines() if "error" in l][:5]
for e in errs: print("  ", e[:200])
sys.exit(1 if (p.returncode or missing or bad) else 0)
