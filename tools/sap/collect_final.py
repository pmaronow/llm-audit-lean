#!/usr/bin/env python3
"""collect_final.py OUTDIR: stage every FAITHFUL unit for publication, after binding checks (V-ORCH-SAP2 delta D1).
OUTDIR must not exist (a fresh staging generation). A unit is staged only if all of these hold:
  1. no agent, certification, prep or Opus session of the unit is running (checked before and after copying);
  2. certification accepted, and the certified snapshot equals the architect tree exactly: the same set of SAP/<U>
     .lean files in both directions with equal sha256, and manifest.json / comparator.json equal to the certified
     manifest_sha256 / config_sha256;
  3. the declaration-review prep (binding fw_common v2) equals the architect tree: the same Defs/Challenge files in both
     directions with equal sha256 (in the prep dir as well), the same manifest, and every item's current review packet
     equal to the packet the fingerprints were computed from;
  4. the inventory is complete: the manifest targets equal the unit's targets; the review items equal the manifest's
     theorems plus OMIT.<target> for every omitted target; the certified theorem list, the manifest theorems and the
     theorems declared in the Challenge modules (from prep's Lean inventory) are equal;
  5. every item passes (fw_pass rule) and every review it rests on revalidates from its file with fw_common's validator
     and is bound to the current version (fw_common.review_bound: v2 only; the task dir still holds the current
     sources; the packet rebuilt from its actual claims/record files equals the current one; same base and fingerprint);
     the review prep base equals the certification base; the staged review evidence revalidates after copying;
  6. after copying, the staged Lean files, manifest and comparator config hash to the certified values.
Staged per unit: SAP/<U>/ sources, manifest.json, comparator.json, verification/ (certification record, Comparator log,
declaration-review.json, claims.json), ARCHITECT-REPORT.md, review/<a|b>/ (unit referees) and review/declarations/
<task>/ (reviewer files; their Lean scratch files as .lean.txt, outside the package's Lean sources). Writes
OUTDIR/SAP/INDEX.json. Exits 1 if any faithful unit fails a check; such a unit is not staged."""
import json, pathlib, shutil, sys, collections, subprocess
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import fw_common as FC
H = pathlib.Path.home(); OUT = pathlib.Path(sys.argv[1]); WT = H / "sap/wt"; TASKS = H / "sap/tasks"
FWU = H / "sap/fw/units"; FWPREP = H / "sap/fw/prep"
if OUT.exists(): sys.exit(f"{OUT} exists; collect into a fresh directory")
units = json.load(open(H / "sap/inputs/units.json"))
st = json.load(open(H / "sap/pipeline/state.json"))
def busy(u):
    live = subprocess.run("tmux ls -F '#S' 2>/dev/null", shell=True, capture_output=True, text=True).stdout.split()
    return [x for x in live if x.startswith((f"sapP-{u}-", f"sapO-{u}", f"sapW-{u}", f"sapC-{u}"))]
def reviews(uj, t):
    r = uj.get("reviews", {}).get(t)
    if r is None: return []
    return [dict(x, reviewer=k, round=x.get("round", x.get("n", 1))) for k, x in r.items()] if isinstance(r, dict) else r
def passing(uj, t):
    fp = uj["current"][t]["fp"]; rs = [r for r in reviews(uj, t) if r.get("fp") == fp]
    if not rs: return None
    m = max(r["round"] for r in rs); last = [r for r in rs if r["round"] == m]
    return last if all(r["clean"] for r in last) else None
def lean_set(root, U):
    S = root / f"SAP/{U}"
    return {str(f.relative_to(root)): FC.sha_file(f) for f in sorted(S.rglob("*.lean")) if "verification" not in f.relative_to(S).parts}

index, failures = {}, {}
for u in sorted(x for x, v in st.items() if v["stage"] == "faithful"):
    A = WT / f"ARCH-{u}"; S = A / f"SAP/{u}"; prob = []
    if busy(u): failures[u] = [f"running sessions {busy(u)}"]; continue
    cert = json.load(open(S / "verification/comparator-result.json"))
    snap = cert.get("snapshot_sha256") or {}
    if str(cert.get("accepted")) != "True": prob.append("certification not accepted")
    arch = lean_set(A, u)
    snap_lean = {k: v for k, v in snap.items() if k.endswith(".lean")}
    if arch != snap_lean:
        d = sorted(set(arch) ^ set(snap_lean)) + sorted(k for k in set(arch) & set(snap_lean) if arch[k] != snap_lean[k])
        prob.append(f"architect Lean files differ from the certified snapshot: {d[:5]}")
    if FC.sha_file(S / "manifest.json") != cert.get("manifest_sha256"): prob.append("manifest.json differs from the certified one")
    if FC.sha_file(S / "comparator.json") != cert.get("config_sha256"): prob.append("comparator.json differs from the certified one")
    try: uj = json.load(open(FWU / f"{u}.json")); prep = uj["prep"]
    except Exception as e: failures[u] = [f"no declaration-review record ({e})"]; continue
    if prep.get("binding") != "fw_common v2": prob.append("review prep predates binding v2")
    if FC.src_files(A, u) != prep.get("files") or FC.src_files(FWPREP / u, u) != prep.get("files"):
        prob.append("Defs/Challenge files differ from the reviewed prep copy")
    if FC.src_digest(A, u) != prep.get("src_digest"): prob.append("source digest differs from prep")
    if FC.sha_file(S / "manifest.json") != prep.get("manifest_sha256"): prob.append("manifest changed after the review prep")
    man = json.load(open(S / "manifest.json")); man = man if isinstance(man, list) else man.get("targets", man)
    want = {t if isinstance(t, str) else t.get("target_id") for t in units[u]["targets"]}
    if sorted(m["target_id"] for m in man) != sorted(want): prob.append("manifest targets differ from the unit's targets")
    mthms = sorted(m["theorem"] for m in man if m.get("theorem"))
    items = set(mthms) | {f"OMIT.{m['target_id']}" for m in man if not m.get("theorem")}
    if set(uj["current"]) != items: prob.append(f"review items {sorted(set(uj['current']) ^ items)[:5]} differ from the manifest")
    if sorted(cert["config"]["theorem_names"]) != mthms: prob.append("certified theorem list differs from the manifest")
    if sorted(prep.get("challenge_theorems") or []) != mthms: prob.append("Challenge theorems differ from the manifest")
    pk = json.load(open(TASKS / f"ARCH-{u}/work.json")); tg = {t["target_id"]: t for t in pk["targets"]}
    manmap = {m["target_id"]: m for m in man}; dr = {}; pds = {}
    cb = cert.get("base") or {}
    if (prep.get("base") or {}).get("repo2_head") != cb.get("repo2_head") or \
       (prep.get("base") or {}).get("lean_path_sha256") != cb.get("lean_path_sha256"):
        prob.append("review prep base (repo2 head, LEAN_PATH) differs from the certification base")
    for t, c in uj["current"].items():
        if t not in items: continue
        pd = FC.packet_digest(FC.packet(pk, tg[c["target_id"]], manmap[c["target_id"]], c.get("omitted")))
        if pd != prep["packets"].get(t): prob.append(f"{t}: review packet changed after prep"); continue
        ok = passing(uj, t)
        if not ok: prob.append(f"{t}: no clean review bound to its current version"); continue
        for r in ok:
            bound, clean, why = FC.review_bound(r, t, c["target_id"], u, prep["src_digest"], pd, prep["base"], c["fp"])
            if not bound: prob.append(f"{t}: review {r['reviewer']} not bound ({why})")
            elif not clean: prob.append(f"{t}: review {r['reviewer']} does not revalidate as clean")
        pds[t] = pd
        dr[t] = {"target_id": c["target_id"], "fingerprint": c["fp"], "decision": c.get("decision"),
                 "reviews": [{"round": r["round"], "reviewer": r["reviewer"], "verdict": r["verdict"],
                              "severity": r["severity"], "binding": r.get("binding"), "at": r.get("at"),
                              "files": f"review/declarations/{pathlib.Path(r['file']).parent.name}"} for r in ok]}
    if prob: failures[u] = prob; continue
    dst = OUT / f"SAP/{u}"
    shutil.copytree(S, dst, ignore=shutil.ignore_patterns("*.ndjson", "*.olean", "*.ilean"))
    shutil.copy(A / "REPORT.md", dst / "ARCHITECT-REPORT.md")
    for s in "ab":
        D = TASKS / f"CHFID-{u}-{s}"; R = dst / "review" / s; R.mkdir(parents=True, exist_ok=True)
        for f in sorted(D.glob("findings*.json")) + sorted(D.glob("REPORT*.md")) + [D / "reading.md", D / "claim-stage.json"]:
            if f.exists(): shutil.copy(f, R / f.name)
    for t, e in dr.items():
        for rv, r in zip(e["reviews"], passing(uj, t)):
            src = pathlib.Path(r["file"]).parent; R = dst / rv["files"]
            if R.exists(): continue
            R.mkdir(parents=True)
            for f in [src / n for n in ("findings.json", "REPORT.md", "reading.md", "claim-stage.json", "closure.json",
                                        "claims.json", "record.json", "earlier.json")] + sorted(src.glob("REPORT*.md")):
                if f.exists() and not (R / f.name).exists(): shutil.copy(f, R / f.name)
            if (src / "scratch").is_dir():
                for f in sorted((src / "scratch").glob("*.lean")):
                    (R / "scratch").mkdir(exist_ok=True); shutil.copy(f, R / "scratch" / (f.name + ".txt"))
    staged_bad = []   # the staged review evidence itself must revalidate (copy-time changes, delta2 D1)
    for t, e in dr.items():
        for rv, r in zip(e["reviews"], passing(uj, t)):
            R = dst / rv["files"]
            try:
                tp = FC.task_packets(R).get(uj["current"][t]["target_id"])
                by, _ = FC.index_findings(json.load(open(R / "findings.json")), {t: (uj["current"][t]["target_id"], r["given_fp"])})
                if tp != pds[t] or t not in by or not by[t][1]: staged_bad.append(t)
            except Exception: staged_bad.append(t)
    if staged_bad:
        failures[u] = [f"staged review evidence does not revalidate: {sorted(set(staged_bad))[:5]}"]; shutil.rmtree(dst); continue
    json.dump(dr, open(dst / "verification/declaration-review.json", "w"), indent=1, ensure_ascii=False)
    json.dump({"work_id": pk.get("work_id"), "unit_id": u, "citation": pk.get("citation"),
               "standing_assumptions": pk.get("standing_assumptions"),
               "targets": [{k: t.get(k) for k in ("target_id", "canonical_claim", "original_claim", "claim_correction",
                                                  "claim_correction_state", "no_lean") if k in t} for t in pk["targets"]]},
              open(dst / "verification/claims.json", "w"), indent=1, ensure_ascii=False, default=str)
    staged = lean_set(OUT, u)
    post = []
    if staged != snap_lean: post.append("staged Lean files differ from the certified snapshot")
    if FC.sha_file(dst / "manifest.json") != cert.get("manifest_sha256") or FC.sha_file(dst / "comparator.json") != cert.get("config_sha256"):
        post.append("staged manifest/config differ from the certified ones")
    if busy(u): post.append(f"a session started during staging: {busy(u)}")
    if post: failures[u] = post; shutil.rmtree(dst); continue
    index[u] = {"work": units[u]["work"], "targets": len(units[u]["targets"]),
                "decisions": dict(collections.Counter(m["decision"] for m in man)),
                "certified": cert.get("stamp"), "theorems": len(mthms), "items_reviewed": len(dr)}
(OUT / "SAP").mkdir(parents=True, exist_ok=True)
json.dump(index, open(OUT / "SAP/INDEX.json", "w"), indent=1)
print(len(index), "faithful units staged;", sum(v["theorems"] for v in index.values()), "theorems")
if failures:
    print("NOT STAGED:"); [print(" ", u, p[:4]) for u, p in failures.items()]; sys.exit(1)
