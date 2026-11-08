#!/usr/bin/env python3
"""fw_prep.py UNIT: declaration-review preparation for one unit (binding rule: tools/fw_common.py).
Copies the unit's final Defs and Challenge sources from its architect worktree to ~/sap/fw/prep/<U>/ and recompiles
them from scratch (rebuild_sap.py: topological order, forbidden-token scan). It then runs a Lean tool
(tools/fw/FwClosure.lean.tmpl) that gives:
  * the inventory of theorems declared in the Challenge modules, which must equal the manifest's theorems; the
    manifest's targets must equal the unit's targets;
  * per theorem, the unit-internal statement closure (navigation for reviewers) and a structural hash.
The review fingerprint of each item is the full sha256 over (all Defs/Challenge sources of the unit, the item's review
packet, base identifiers, closure hash). Omitted targets get an item OMIT.<target> (briefs/brief-fw-omit.md).
Writes ~/sap/fw/units/<U>.json["current"] and ["prep"]; earlier "reviews" are kept."""
import json, pathlib, shutil, subprocess, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from fw_common import src_digest, src_files, packet, packet_digest, fingerprint, sha_file, review_bound
H = pathlib.Path.home(); U = sys.argv[1]
A = H / f"sap/wt/ARCH-{U}"; D = H / f"sap/fw/prep/{U}"; UJ = H / f"sap/fw/units/{U}.json"
if D.exists(): shutil.rmtree(D)
(D / f"SAP/{U}").mkdir(parents=True); (D / "scratch").mkdir()
for part in ("Defs", "Challenge"):
    if (A / f"SAP/{U}/{part}").exists(): shutil.copytree(A / f"SAP/{U}/{part}", D / f"SAP/{U}/{part}")
    shutil.copy(A / f"SAP/{U}/{part}.lean", D / f"SAP/{U}/{part}.lean")
if src_files(D, U) != src_files(A, U): sys.exit("prep copy differs from the architect sources (changed during copy?)")
# every Challenge module must be imported (transitively) by the Challenge root, so the Lean inventory sees it (delta2 D1)
import re as _re
mods = {str(f.relative_to(D))[:-5].replace("/", "."): f for f in (D / f"SAP/{U}").rglob("*.lean")
        if str(f.relative_to(D)).startswith((f"SAP/{U}/Challenge/", f"SAP/{U}/Challenge.lean"))}
seen, stack = set(), [f"SAP.{U}.Challenge"]
while stack:
    m = stack.pop()
    if m in seen or m not in mods: continue
    seen.add(m); stack += _re.findall(r"^import\s+(\S+)", mods[m].read_text(), _re.M)
if set(mods) - seen: sys.exit(f"Challenge modules not imported by the Challenge root: {sorted(set(mods) - seen)}")
r = subprocess.run(["python3", str(H / "sap/tools/rebuild_sap.py"), str(D), U], capture_output=True, text=True)
if r.returncode: sys.exit("rebuild failed: " + (r.stdout + r.stderr)[-1500:])
man = json.load(open(A / f"SAP/{U}/manifest.json")); man = man if isinstance(man, list) else man.get("targets", man)
units = json.load(open(H / "sap/inputs/units.json"))
want = {t if isinstance(t, str) else t.get("target_id") for t in units[U]["targets"]}
have = [m["target_id"] for m in man]
if sorted(have) != sorted(want) or len(set(have)) != len(have):
    sys.exit(f"manifest targets {sorted(have)} != unit targets {sorted(want)}")
thms = [m for m in man if m.get("theorem")]
if len({m["theorem"] for m in thms}) != len(thms): sys.exit("a theorem is listed twice in the manifest")
tmpl = (H / "sap/tools/fw/FwClosure.lean.tmpl").read_text()
(D / "scratch/FwClosure.lean").write_text(tmpl.replace("<U>", U).replace("<THMS>", ", ".join(f"`{m['theorem']}" for m in thms)))
r = subprocess.run([str(H / "sap/tools/sap-lean"), "scratch/FwClosure.lean"], cwd=D, capture_output=True, text=True)
outf = D / "scratch/fw-closure.jsonl"
if r.returncode or not outf.exists(): sys.exit("closure tool failed: " + (r.stdout + r.stderr)[-1500:])
rows = [json.loads(l) for l in outf.read_text().split("\n") if l.strip()]
chal = sorted(rows[0]["challenge_theorems"]); out = {o["theorem"]: o for o in rows[1:]}
# completeness by what Lean actually loaded, not by text (V-ORCH-SAP2 delta3 MAJOR 2): every Challenge source module
# must be among the modules imported into the inventory tool's environment
src_mods = {str(f.relative_to(D))[:-5].replace("/", ".") for f in (D / f"SAP/{U}").rglob("*.lean")
            if str(f.relative_to(D)).startswith((f"SAP/{U}/Challenge/", f"SAP/{U}/Challenge.lean"))}
if src_mods != set(rows[0].get("challenge_modules") or []):
    sys.exit(f"Challenge modules not loaded by the Challenge root: {sorted(src_mods - set(rows[0].get('challenge_modules') or []))}")
if chal != sorted(m["theorem"] for m in thms):
    sys.exit(f"Challenge theorems {chal} != manifest theorems {sorted(m['theorem'] for m in thms)}")
head = subprocess.run(["git", "-C", str(H / "sap/repo2"), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
base = {"repo2_head": head, "lean_path_sha256": sha_file(H / "sap/tools/lean_path.txt"),
        "toolchain": "leanprover--lean4---v4.34.1"}
pk = json.load(open(H / f"sap/tasks/ARCH-{U}/work.json")); tg = {t["target_id"]: t for t in pk["targets"]}
sd = src_digest(D, U); cur, pkts = {}, {}
for m in man:
    om = not m.get("theorem")
    if om and m.get("decision") != "omitted": sys.exit(f"{m['target_id']}: no theorem but decision {m.get('decision')}")
    key = f"OMIT.{m['target_id']}" if om else m["theorem"]
    pd = packet_digest(packet(pk, tg[m["target_id"]], m, om)); pkts[key] = pd
    if om:
        cfp = None; mod = line = None; clo = []
    else:
        o = out.get(key)
        if not o or o.get("error"): sys.exit(f"closure missing for {key}: {o}")
        cfp, mod, line, clo = o["closure_fp"], o["module"], o["line"], o["closure"]
    cur[key] = {"target_id": m["target_id"], "fp": fingerprint(sd, pd, base, cfp), "decision": m.get("decision"),
                "omitted": om, "module": mod, "line": line, "closure": clo}
uj = json.load(open(UJ)) if UJ.exists() else {"reviews": {}}
# Re-bind every earlier review to this version (fw_common.review_bound, V-ORCH-SAP2 delta2): only v2 reviews whose task
# dir still holds exactly these sources and the packet they were given (reconstructed from the task files) equal to
# this packet, with this base and fingerprint, and whose findings entry revalidates. Pre-v2 reviews never bind.
nb = nu = 0
for key, rs in list(uj.get("reviews", {}).items()):
    lst = rs if isinstance(rs, list) else [dict(x, reviewer=k, round=x.get("round", x.get("n", 1))) for k, x in rs.items()]
    for r in lst:
        if r.get("binding") == "v2" and "given_fp" not in r and r.get("fp"):
            # v2 reviews recorded 11:36-12:15 before given_fp/base were stored: bound then means given == current fp at
            # poll time; the base (repo2 head, LEAN_PATH, toolchain) has not changed since the campaign began
            r["given_fp"] = r["fp"]; r["base"] = r.get("base") or (uj.get("prep") or {}).get("base")
        if key not in cur: r["fp"] = None; r["unbound"] = "item no longer in the unit"; nu += 1; continue
        ok, clean, why = review_bound(r, key, cur[key]["target_id"], U, sd, pkts[key], base, cur[key]["fp"])
        if ok: r["clean"] = clean
        r["fp"] = cur[key]["fp"] if ok else None; r["unbound"] = None if ok else why
        nb += ok; nu += (not ok)
    uj["reviews"][key] = lst
uj["current"] = cur
uj["prep"] = {"src_digest": sd, "files": src_files(D, U), "manifest_sha256": sha_file(A / f"SAP/{U}/manifest.json"),
              "base": base, "challenge_theorems": chal, "packets": pkts, "binding": "fw_common v2"}
UJ.parent.mkdir(parents=True, exist_ok=True)
tmp = UJ.with_suffix(".tmp"); tmp.write_text(json.dumps(uj, indent=1, ensure_ascii=False)); tmp.replace(UJ)
print(f"{U}: {len(thms)} theorems, {len(cur) - len(thms)} omitted targets; src {sd[:12]}; reviews bound {nb}, unbound {nu}")
