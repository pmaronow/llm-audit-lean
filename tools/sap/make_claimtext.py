#!/usr/bin/env python3
"""make_claimtext.py: build ~/sap/tasks/CT-0N/ for the 12 claim-text targets (two tasks of 6), from the self-audit-lean
work records (full texts), the final row status table (~/sap/status/rows.jsonl) and the reviewers' findings."""
import json, pathlib, collections
H = pathlib.Path.home(); OUT = H / "sap/tasks"
st = [json.loads(l) for l in open(H / "sap/status/rows.jsonl")]
tgts = sorted({r["target_id"] for r in st if "claim_text" in r["flags"]})
works = {}
def work(w):
    if w not in works: works[w] = json.load(open(H / f"sal/repo/catalog/works/{w}.json"))
    return works[w]
FIELDS = ["statement", "definitions_needed", "name_in_paper", "location", "kind", "note", "finite_lemmas"]
items = []
for t in tgts:
    w = t.split("-")[0]; wd = work(w)
    tg = next(x for x in wd["targets"] if x["target_id"] == t)
    rs = [r for r in st if r["target_id"] == t]
    items.append({"target_id": t, "work_id": w, "citation": wd.get("citation"),
                  "standing_assumptions": wd.get("standing_assumptions"),
                  "recorded": {f: tg.get(f) for f in FIELDS if tg.get(f) not in (None, "")},
                  "declarations": [{"lean_name": r["lean_name"], "file": "/home/ubuntu/sap/repo2/" + r["file"][len("lean/"):],
                                    "line": r["line"], "status": r["status"], "final_status": r["final"]} for r in rs],
                  "claim_text_findings": [r["evidence"] for r in rs if "claim_text" in r["flags"]]})
for n, g in enumerate((items[:6], items[6:]), 1):
    d = OUT / f"CT-{n:02d}"; d.mkdir(parents=True, exist_ok=True)
    json.dump({"items": g}, open(d / "items.json", "w"), indent=1, ensure_ascii=False)
    (d / "brief.md").write_text((H / "sap/briefs/brief-claimtext.md").read_text())
    print(d.name, [i["target_id"] for i in g])
