#!/usr/bin/env python3
"""make_disputes.py: build ~/sap/tasks/DISP-NN/ (items.json + brief.md) for the 17 disputed rows of the fidelity sweep,
grouped by work into 4 tasks. Source: ~/sal/fid/final/v2/rows.jsonl and the adjudication packets (claim text, standing
assumptions, descriptions)."""
import json, pathlib, collections, re
H = pathlib.Path.home(); F = H / "sal/fid"; C = F / "chunks"; OUT = H / "sap/tasks"
rows = [json.loads(l) for l in open(F / "final/v2/rows.jsonl")]
disp = [r for r in rows if r["final_class"] == "disputed"]
dec = {(d["target_id"], d["lean_name"]): d for d in (json.loads(l) for l in open(F / "final/decisions.jsonl"))
       if not d["calibration"]}
items_by_adj = {}
for d in (C).glob("A[0-9]*"):
    j = json.load(open(d / "items.json"))
    for it in j["items"]: items_by_adj[it["item"]] = (it, j["work"])
groups = [["P001", "P002"], ["P004", "P009", "P018", "P019"], ["P029", "P042"], ["P061"]]
ID = re.compile(r"(?<![A-Z0-9-])((?:C0[12]|R\d{3}|A\d{3}|V\d{3})-\d\d)")
n = 0
for g in groups:
    sel = [r for r in disp if r["work"] in g]
    if not sel: continue
    n += 1; d = OUT / f"DISP-{n:02d}"; d.mkdir(parents=True, exist_ok=True)
    items, works = [], {}
    for k, r in enumerate(sorted(sel, key=lambda r: (r["target_id"], r["lean_name"])), 1):
        a = dec[(r["target_id"], r["lean_name"])]
        it, work = items_by_adj[a["adj_item"]]
        works[r["work"]] = work
        items.append({"item": f"DISP-{n:02d}-{k:02d}", "target_id": r["target_id"], "lean_name": r["lean_name"],
                      "file": it["file"], "line": it["line"], "status": it["status"], "claim": it["claim"],
                      "row_says": it["row_says"], "modelling_choices": it["modelling_choices"],
                      "conditional_on": it["conditional_on"], "first_pass": it["reviewer"]["final"],
                      "adjudicator": r["adjudicator"], "second_review": r["confirmer"]})
    txt = ID.sub("[another row]", json.dumps({"works": works, "items": items}, ensure_ascii=False))
    (d / "items.json").write_text(txt)
    (d / "brief.md").write_text((H / "sap/briefs/brief-dispute.md").read_text())
    print(d.name, [i["target_id"] for i in items])
