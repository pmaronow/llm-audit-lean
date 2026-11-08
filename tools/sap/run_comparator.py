#!/usr/bin/env python3
"""run_comparator.py WORKTREE WORK [--control]: certify SAP/<WORK> with the Palomar Comparator (strict; v2 after the
V-ORCH-SAP1 delta audit).

1. Freeze: copy SAP/<WORK> sources (no build outputs) into ~/sap/cert/<WORK>-<stamp>/snapshot and hash them before any
   build. Create a fresh certification worktree of ~/sap/repo2 HEAD (commit recorded), copy the snapshot in, and compile
   every SAP/<WORK> module from it in import order with sap-lean (pinned options); hash the resulting .olean files.
2. Completeness (skipped with --control): manifest target IDs == the work's llm-audit-listed targets; decisions in
   {whole, restricted, refuted, omitted}; each non-omitted target has a unique theorem `SAP.<WORK>.…` with proof_status
   `proved`; omitted targets give a reason; comparator theorem_names == the set of non-omitted theorems.
3. Import closures from Lean itself (compiled scratch module listing env.allImportedModuleNames): the Solution's closure
   contains no `SAP.*.Challenge*` / `SAP.*.Orig*` module; the Challenge's closure contains only Lean core / Std / Mathlib
   and its dependencies, plus SAP.<WORK>.Defs* and SAP.<WORK>.Challenge*.
4. Exports with lean4export v4.34.0 (Lean 4.34.1) of the Challenge and Solution roots (theorem names + Comparator
   primitive targets + Quot builtins + standard axioms), exit codes checked.
5. v4.35.0-rc2 `lake comparator` with con-ron --verified and nanoda; requires exit 0 and all four markers.
Writes the record to SAP/<WORK>/verification/comparator-result.json in the ORIGINAL worktree and in the cert dir; exits
nonzero on any failure."""
import json, os, re, subprocess, sys, hashlib, pathlib, time, shutil
H = pathlib.Path.home()
args = [a for a in sys.argv[1:] if not a.startswith("--")]; CONTROL = "--control" in sys.argv
W0, WORK = pathlib.Path(args[0]).resolve(), args[1]
stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
CERT = H / f"sap/cert/{WORK}-{stamp}"; SNAP = CERT / "snapshot"
T434 = H / ".elan/toolchains/leanprover--lean4---v4.34.1"; T435 = H / ".elan/toolchains/leanprover--lean4---v4.35.0-rc2"
EXP = H / "sap/deps/lean4export/.lake/build/bin/lean4export"
STD = ["propext", "Quot.sound", "Classical.choice"]
MARKERS = ["con-ron kernel accepts the solution", "nanoda kernel accepts the solution",
           "Lean default kernel accepts the solution", "Your solution is okay!"]
ALLOWED_CHALLENGE_ROOTS = ("Init", "Std", "Lean", "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "ImportGraph",
                           "LeanSearchClient", "Plausible", "Lake")
res = {"work": WORK, "control": CONTROL, "stamp": stamp, "source_worktree": str(W0), "steps": []}
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def save():
    for d in (W0 / f"SAP/{WORK}/verification", CERT):
        d.mkdir(parents=True, exist_ok=True); (d / "comparator-result.json").write_text(json.dumps(res, indent=1))
def cleanup():
    cw = res.get("cert_worktree")
    if cw: subprocess.run(["git", "-C", str(H / "sap/repo2"), "worktree", "remove", "--force", cw], capture_output=True)
def fail(msg):
    res["accepted"] = False; res["failure"] = msg; save(); cleanup(); print("FAIL:", msg); sys.exit(1)

# 1. freeze
src = W0 / f"SAP/{WORK}"
if not src.is_dir(): fail("no SAP/<WORK> directory")
SNAP.mkdir(parents=True)
shutil.copytree(src, SNAP / f"SAP/{WORK}", ignore=shutil.ignore_patterns("verification", "*.ndjson", "*.olean", "*.ilean"))
res["snapshot_sha256"] = {str(p.relative_to(SNAP)): sha(p) for p in sorted(SNAP.rglob("*")) if p.is_file()}
repo2_head = subprocess.run(["git", "-C", str(H / "sap/repo2"), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
res["base"] = {"repo2_head": repo2_head, "lean_path_sha256": sha(H / "sap/tools/lean_path.txt"),
               "toolchain_434": str(T434), "toolchain_435": str(T435)}
key = f"CERT-{WORK}-{stamp}"
p = subprocess.run([str(H / "sap/tools/mkwt.sh"), key], capture_output=True, text=True)
if p.returncode: fail("could not create certification worktree: " + p.stdout + p.stderr)
CW = H / f"sap/wt/{key}"; res["cert_worktree"] = str(CW)
shutil.copytree(SNAP / f"SAP/{WORK}", CW / f"SAP/{WORK}")
p = subprocess.run(["python3", str(H / "sap/tools/rebuild_sap.py"), str(CW), WORK], capture_output=True, text=True)
res["steps"].append({"step": "rebuild-from-snapshot", "rc": p.returncode, "out": (p.stdout + p.stderr)[-1500:]})
if p.returncode: fail("rebuild from snapshot failed")
ob = CW / f".lake/build/lib/lean/SAP/{WORK}"
res["olean_sha256"] = {str(f.relative_to(ob)): sha(f) for f in sorted(ob.rglob("*.olean"))}
cfg_path = CW / f"SAP/{WORK}/comparator.json"; cfg = json.loads(cfg_path.read_text()); res["config"] = cfg
res["config_sha256"] = sha(cfg_path)

# config shape
if cfg.get("definition_names", []) != []: fail("definition_names must be empty")
if sorted(cfg.get("permitted_axioms", [])) != sorted(STD): fail("permitted axioms must be exactly the standard three")
ek = cfg.get("external_kernels", {})
if ek.get("con-ron", [None])[0] != "con-ron" or "--verified" not in ek.get("con-ron", []) or ek.get("nanoda") != ["nanoda_bin"]:
    fail("external kernels must be con-ron --verified and nanoda_bin")
if cfg.get("enable_nanoda"): fail("use external_kernels, not enable_nanoda")
ch, so = cfg.get("challenge_module"), cfg.get("solution_module")
if ch != f"SAP.{WORK}.Challenge" or so != f"SAP.{WORK}.Solution": fail("module names must be SAP.<WORK>.Challenge/Solution")
names = cfg.get("theorem_names", [])
if not names or len(set(names)) != len(names): fail("theorem_names empty or duplicated")
if any(not n.startswith(f"SAP.{WORK}.") for n in names): fail("theorem names must be SAP.<WORK>.*")

# 2. completeness
if not CONTROL:
    man_path = CW / f"SAP/{WORK}/manifest.json"; man = json.loads(man_path.read_text())
    man = man if isinstance(man, list) else man.get("targets", man); res["manifest_sha256"] = sha(man_path)
    listed = sorted(json.load(open(H / "sap/inputs/units.json"))[WORK]["targets"])
    ids = [m.get("target_id") for m in man]
    if sorted(ids) != listed: fail(f"manifest targets differ from the listed targets: missing "
                                   f"{sorted(set(listed) - set(ids))[:5]}, extra {sorted(set(ids) - set(listed))[:5]}")
    thms = []
    for m in man:
        d = m.get("decision")
        if d not in ("whole", "restricted", "refuted", "omitted"): fail(f"{m['target_id']}: bad decision {d}")
        if d == "omitted":
            if m.get("theorem"): fail(f"{m['target_id']}: omitted target has a theorem")
            if not (m.get("restriction") or m.get("rows_not_used") or m.get("notes") or m.get("reason")):
                fail(f"{m['target_id']}: omitted target without a reason")
            continue
        if m.get("proof_status") != "proved": fail(f"{m['target_id']}: proof_status {m.get('proof_status')}")
        if d == "restricted" and not m.get("restriction"): fail(f"{m['target_id']}: restricted without a restriction")
        thms.append(m.get("theorem"))
    if len(set(thms)) != len(thms): fail("a theorem serves two targets")
    if sorted(thms) != sorted(names): fail(f"comparator theorems != non-omitted manifest theorems: "
                                           f"{sorted(set(thms) ^ set(names))[:5]}")
    res["targets"] = {"listed": len(listed), "certified": len(thms), "omitted": len(listed) - len(thms)}

# 3. import closures from Lean
LP = f"{CW}/.lake/build/lib/lean:" + (H / "sap/tools/lean_path.txt").read_text().strip()
def closure(mod):
    scr = CW / "scratch" / f"Closure_{mod.replace('.', '_')}.lean"
    scr.write_text(f"import {mod}\nopen Lean in\n#eval show CoreM Unit from do\n"
                   f"  for m in (← getEnv).allImportedModuleNames do IO.println s!\"MOD {{m}}\"\n")
    p = subprocess.run([str(T434 / "bin/lean"), "-DautoImplicit=false", str(scr)], cwd=CW, capture_output=True, text=True,
                       env={**os.environ, "LEAN_PATH": LP})
    if p.returncode: fail(f"closure listing for {mod} failed: {(p.stdout + p.stderr)[-500:]}")
    return sorted(set(re.findall(r"^MOD (\S+)$", p.stdout, re.M)))
sol_cl, ch_cl = closure(so), closure(ch)
bad = [m for m in sol_cl if re.match(r"SAP\.[^.]+\.(Challenge|Orig)", m)]
if bad: fail(f"Solution closure contains stub modules: {bad[:5]}")
badc = [m for m in ch_cl if not (m.split(".")[0] in ALLOWED_CHALLENGE_ROOTS or m == ch
        or m.startswith((f"SAP.{WORK}.Defs", f"SAP.{WORK}.Challenge")))]
if badc: fail(f"Challenge closure contains non-Mathlib modules: {badc[:5]}")
res["closures"] = {"solution": len(sol_cl), "challenge": len(ch_cl),
                   "solution_sap": [m for m in sol_cl if m.startswith("SAP.")]}

# 4. exports
srcl = (T435 / "src/lean/lake/Lake/CLI/Check.lean").read_text()
prim = re.sub(r"--[^\n]*", "", srcl.split("def primitiveTargets", 1)[1].split("def builtinTargets", 1)[0])
targets = list(dict.fromkeys(names + re.findall(r"``([A-Za-z0-9_.]+)", prim) + ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] + STD))
env = {**os.environ, "LEAN_PATH": LP, "LEAN_NUM_THREADS": "1", "PATH": f"{T434}/bin:" + os.environ["PATH"],
       "LEAN_SYSROOT": str(T434)}
exports = {}
for side, mod in (("challenge", ch), ("solution", so)):
    out = CERT / f"{side}.ndjson"; log = CERT / f"{side}.export.log"; t0 = time.monotonic()
    with open(out, "wb") as o, open(log, "w") as e:
        p = subprocess.run([str(EXP), mod, "--", *targets], cwd=CW, env=env, stdout=o, stderr=e)
    res["steps"].append({"step": f"export-{side}", "rc": p.returncode, "seconds": round(time.monotonic() - t0, 1),
                         "bytes": out.stat().st_size, "sha256": sha(out)})
    if p.returncode or out.stat().st_size == 0: fail(f"export of {side} failed (see {log})")
    exports[side] = out
res["exporter"] = {"path": str(EXP), "sha256": sha(EXP), "version": "lean4export v4.34.0 built with Lean 4.34.1"}

# 5. comparator
env2 = {**os.environ, "PATH": f"{T435}/bin:{H}/.elan/bin:" + os.environ["PATH"]}
log = CERT / "comparator.log"; t0 = time.monotonic()
with open(log, "w") as e:
    p = subprocess.run(["lake", "comparator", "--config", str(cfg_path), "--challenge-from-export", str(exports["challenge"]),
                        "--solution-from-export", str(exports["solution"])], cwd=H / "sap/probe/cmp", env=env2, stdout=e,
                       stderr=subprocess.STDOUT)
text = log.read_text(); res["comparator_log"] = str(log)
res["steps"].append({"step": "comparator", "rc": p.returncode, "seconds": round(time.monotonic() - t0, 1)})
res["markers"] = {m: m in text for m in MARKERS}
if p.returncode != 0: fail(f"comparator exit {p.returncode}: {text[-600:]}")
if not all(res["markers"].values()): fail("missing acceptance markers")
for side in exports: res[f"{side}_export_sha256"] = sha(exports[side]); exports[side].unlink()  # keep hashes, drop bulk
res["accepted"] = True; save()
shutil.copy(log, W0 / f"SAP/{WORK}/verification/comparator.log"); cleanup()
print("ACCEPTED:", WORK, len(names), "theorems", "(control)" if CONTROL else "")
