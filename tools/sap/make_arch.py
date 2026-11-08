#!/usr/bin/env python3
"""make_arch.py UNIT [UNIT ...]: build ~/sap/tasks/ARCH-<UNIT>/work.json for Challenge architects (a unit is a work or a
group of its targets, ~/sap/inputs/units.json).
Sources: self-audit-lean work records (~/sal/repo/catalog/works), the llm-audit catalog (~/sap/inputs/lean-catalog.json:
the listed targets and their descriptions), final row status (~/sap/status/rows.jsonl), the sweep's per-target coverage
judgments (~/sal/fid/chunks/R*/targets.json, ~/sal/fid/final/split.json), and claim-text corrections
(~/sap/tasks/CT-*/claimtext.json, if present)."""
import json, glob, pathlib, sys, collections
H = pathlib.Path.home()
FIELDS = ["target_id", "kind", "name_in_paper", "location", "statement", "definitions_needed", "finite_lemmas", "note",
          "asymptotic", "related_finding"]
la = json.load(open(H / "sap/inputs/lean-catalog.json"))
listed = {t["id"]: (w["work_id"], t) for w in la["works"] for t in w["targets"]}
status = collections.defaultdict(list)
for l in open(H / "sap/status/rows.jsonl"):
    r = json.loads(l); status[r["target_id"]].append(r)
cov = collections.defaultdict(list)
for f in glob.glob(str(H / "sal/fid/chunks/R*/targets.json")):
    for t in json.load(open(f)): cov[t["target_id"]].append({k: t.get(k) for k in ("coverage", "covered_here", "uncovered", "notes")})
for s in json.load(open(H / "sal/fid/final/split.json")):
    cov[s["target_id"]].append({"reconciled": True, **{k: s.get(k) for k in ("coverage", "uncovered", "notes")}})
# accepted claim-text corrections: editor's fields, replaced by the referee's edited fields when "accept_with_edits";
# a flagged target whose correction is not refereed and accepted blocks its work's packet.
ct, ref = {}, {}
for f in glob.glob(str(H / "sap/tasks/CT-*/claimtext.json")):
    for x in json.load(open(f)): ct[x["target_id"]] = x
for f in glob.glob(str(H / "sap/tasks/CT-*/ctref.json")):
    for x in json.load(open(f)): ref[x["target_id"]] = x
flagged = {r["target_id"] for r in (json.loads(l) for l in open(H / "sap/status/rows.jsonl")) if "claim_text" in r["flags"]}
def correction(tid):
    if tid not in flagged: return None, "none"
    c, r = ct.get(tid), ref.get(tid)
    if not c or not r: return None, "pending"
    if c["verdict"] == "no_change" and r["verdict"] == "accept": return None, "no_change"
    if r["verdict"] == "accept": return c["corrected_fields"], "accepted"
    if r["verdict"] == "accept_with_edits": return {**c["corrected_fields"], **r["edited_fields"]}, "accepted_with_edits"
    return None, "rejected"
units = json.load(open(H / "sap/inputs/units.json"))
for U in sys.argv[1:]:
    W = units[U]["work"]; scope = set(units[U]["targets"])
    wd = json.load(open(H / f"sal/repo/catalog/works/{W}.json"))
    rec = {t["target_id"]: t for t in wd["targets"]}
    targets = []
    for tid, (w, lt) in listed.items():
        if w != W or tid not in scope: continue
        t = rec.get(tid, {})
        original = {f: t.get(f) for f in FIELDS if t.get(f) not in (None, "")}
        fields, cstate = correction(tid)
        if cstate in ("pending", "rejected"):
            sys.exit(f"{U}: claim-text correction for {tid} is {cstate}; resolve it before building this packet")
        entry = {"target_id": tid, "canonical_claim": {**original, **(fields or {})}, "claim_correction_state": cstate}
        if fields:
            entry["original_claim"] = original
            entry["claim_correction"] = {"fields": fields, "problem": ct[tid]["problem"],
                                         "paper_quote": ct[tid].get("paper_quote"),
                                         "declarations_matching": ct[tid].get("declarations_matching"),
                                         "declarations_not_matching": ct[tid].get("declarations_not_matching"),
                                         "referee": ref[tid].get("issues")}
        entry["llm_audit"] = {"headline": lt["text"].get("headline"), "description": lt["text"].get("body"),
                              "location": lt["text"].get("location")}
        entry["coverage_judgments"] = cov.get(tid, [])
        entry["no_lean"] = not status.get(tid)
        entry["rows"] = [{"lean_name": r["lean_name"], "file": r["file"][len("lean/"):], "line": r["line"],
                          "status": r["status"], "final_status": r["final"], "conditional_on": r["conditional_on"],
                          "first_pass": r["first_pass"], "flags": r["flags"],
                          **({"evidence": r["evidence"]} if r["final"] != "ok" or r["flags"] else {})}
                         for r in status.get(tid, [])]
        targets.append(entry)
    d = H / f"sap/tasks/ARCH-{U}"; d.mkdir(parents=True, exist_ok=True)
    json.dump({"unit_id": U, "work_id": W, "unit_targets": units[U]["targets"],
               "other_units_of_work": sorted(u for u, v in units.items() if v["work"] == W and u != U), "citation": wd.get("citation"), "standing_assumptions": wd.get("standing_assumptions"),
               "targets": targets}, open(d / "work.json", "w"), indent=1, ensure_ascii=False)
    assert len(targets) == len(scope), (U, len(targets), len(scope))
    print(U, len(targets), "targets;", sum(len(t["rows"]) for t in targets), "rows;",
          collections.Counter(r["final_status"] for t in targets for r in t["rows"]))
