#!/usr/bin/env python3
"""make_chfid.py WORK: two blind Challenge-fidelity referee task dirs ~/sap/tasks/CHFID-<WORK>-{a,b}/ from the
architect worktree ~/sap/wt/ARCH-<WORK>: copies of SAP/<WORK>/Defs and Challenge sources and their compiled outputs,
claims.json (canonical claims from the packet), record.json (manifest decisions/restrictions; for step 3)."""
import json, pathlib, shutil, sys
H = pathlib.Path.home(); W = sys.argv[1]
src = H / f"sap/wt/ARCH-{W}"; pk = json.load(open(H / f"sap/tasks/ARCH-{W}/work.json"))
man = json.load(open(src / f"SAP/{W}/manifest.json")); man = man if isinstance(man, list) else man.get("targets", man)
claims = {"work_id": W, "citation": pk.get("citation"), "standing_assumptions": pk.get("standing_assumptions"),
          "targets": [{"target_id": t["target_id"], "canonical_claim": t["canonical_claim"], "no_lean": t.get("no_lean")}
                      for t in pk["targets"]]}
record = [{k: m.get(k) for k in ("target_id", "decision", "theorem", "restriction", "rows_used", "rows_not_used")}
          for m in man]
for side in "ab":
    d = H / f"sap/tasks/CHFID-{W}-{side}"
    if d.exists(): shutil.rmtree(d)
    (d / "SAP" / W).mkdir(parents=True); (d / "scratch").mkdir()
    for part in ("Defs", "Challenge"):
        if (src / f"SAP/{W}/{part}").exists(): shutil.copytree(src / f"SAP/{W}/{part}", d / f"SAP/{W}/{part}")
        shutil.copy(src / f"SAP/{W}/{part}.lean", d / f"SAP/{W}/{part}.lean")
    ob = src / f".lake/build/lib/lean/SAP/{W}"; tb = d / f".lake/build/lib/lean/SAP/{W}"; tb.mkdir(parents=True)
    for f in ob.rglob("*"):
        rel = f.relative_to(ob)
        if f.is_file() and (rel.parts[0] in ("Defs", "Challenge") or rel.name.startswith(("Defs.", "Challenge."))):
            (tb / rel).parent.mkdir(parents=True, exist_ok=True); shutil.copy(f, tb / rel)
    json.dump(claims, open(d / "claims.json", "w"), indent=1, ensure_ascii=False)
    json.dump(record, open(d / "record.json", "w"), indent=1, ensure_ascii=False)
    (d / "brief.md").write_text((H / "sap/briefs/brief-chfid.md").read_text().replace("<WORK>", W))
    print(d)
