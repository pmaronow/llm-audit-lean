#!/usr/bin/env python3
"""make_status.py: one final status per credited row (4,795) and per target (1,021), merging the fidelity sweep's first
pass (~/sal/fid/chunks R*), adjudication + second review (~/sal/fid/final/v2/rows.jsonl, decisions.jsonl) and the
dispute decisions (~/sap/tasks/DISP-*/decisions.json). Writes ~/sap/status/rows.jsonl and targets.json.

Row status:
  ok            first pass faithful / faithful_with_notes / broader (not flagged), or adjudication rejected the flag,
                or the dispute review found no problem — usable for the component it is credited for;
  narrower      agreed statement problem (statement_repair): usable only for what the Lean statement actually states;
  wrong_credit  agreed credit_wrong: not usable for this target as it stands;
  (plus flags) description_fix, claim_text (target-level), with the reviewers' texts kept for the architects."""
import json, glob, pathlib, collections
H = pathlib.Path.home(); F = H / "sal/fid"; C = F / "chunks"; OUT = H / "sap/status"; OUT.mkdir(parents=True, exist_ok=True)
first = {}
for d in sorted(C.glob("R[0-9]*")):
    for x in json.load(open(d / "findings.json")):
        first[(x["target_id"], x["lean_name"])] = x
adj = {(d["target_id"], d["lean_name"]): d for d in (json.loads(l) for l in open(F / "final/decisions.jsonl"))
       if not d["calibration"]}
v2 = {(r["target_id"], r["lean_name"]): r for r in (json.loads(l) for l in open(F / "final/v2/rows.jsonl"))}
disp = {}
for f in sorted(glob.glob(str(H / "sap/tasks/DISP-*/decisions.json"))):
    for x in json.load(open(f)):
        k = (x["target_id"], x["lean_name"]); assert k not in disp, ("duplicate dispute", k)
        assert x["kind"] in ("statement", "claim_text", "description_only", "not_a_problem"), x["kind"]
        assert x["consequence"] in ("statement_repair", "credit_wrong", "fix_description", "claim_description_wrong", "none")
        disp[k] = x
needed = {k for k, r in v2.items() if r["final_class"] == "disputed"}
assert needed <= set(disp), ("unresolved disputes", sorted(needed - set(disp))[:5])
rows = [json.loads(l) for l in open(H / "sal/repo/catalog/results.jsonl")]
rows = [r for r in rows if r["status"] in ("proved", "counterexample_proved")]
out, cnt = [], collections.Counter()
for r in rows:
    k = (r["target_id"], r["lean_name"]); fp = first[k]
    rec = {"target_id": r["target_id"], "work": r["work_id"], "lean_name": r["lean_name"], "file": r["file"],
           "line": r["line"], "status": r["status"], "conditional_on": r.get("conditional_on") or [],
           "first_pass": {"fidelity": fp["fidelity"], "severity": fp["severity"], "notes": fp.get("notes"),
                          "differences": fp.get("differences")}}
    st, why, flags = "ok", None, []
    if k in disp:
        x = disp[k]
        st = {"not_a_problem": "ok", "description_only": "ok"}.get(x["kind"], "wrong_credit" if x["consequence"] ==
              "credit_wrong" else "narrower" if x["kind"] == "statement" else "ok")
        why = {"source": "dispute", "reason": x["reason"], "defensible_statement": x["defensible_statement"]}
        if x.get("claim_text_fix") or x["kind"] == "claim_text":
            flags.append("claim_text"); why["claim_text_fix"] = x.get("claim_text_fix")
        if x["kind"] == "description_only": flags.append("description_fix")
    elif k in v2:
        x = v2[k]; c = x["final_class"]
        assert c in ("statement", "claim_text", "description_fix"), ("unexpected class", k, c)
        if c == "statement": st = "wrong_credit" if x["repair"] == "credit_wrong" else "narrower"
        elif c == "claim_text": flags.append("claim_text")
        elif c == "description_fix": flags.append("description_fix")
        why = {"source": "adjudication+second review", "adjudicator": x["adjudicator"]["what"],
               "suggested_fix": x["adjudicator"]["suggested_fix"], "second_review": x["confirmer"]["reason"],
               "severity": x.get("severity")}
    elif k in adj:
        x = adj[k]
        if x["consequence"] == "fix_description": flags.append("description_fix")
        why = {"source": "adjudication", "decision": x["decision"], "what": x["what"]}
    rec.update(final=st, flags=flags, evidence=why); out.append(rec); cnt[st] += 1
    for fl in flags: cnt["flag:" + fl] += 1
with open(OUT / "rows.jsonl", "w") as fh:
    for r in out: fh.write(json.dumps(r, ensure_ascii=False) + "\n")
by = collections.defaultdict(list)
for r in out: by[r["target_id"]].append(r)
la = json.load(open(H / "sap/inputs/lean-catalog.json"))
listed = [t["id"] for w in la["works"] for t in w["targets"]]
assert len(listed) == 1021 and len(set(listed)) == 1021
assert set(by) <= set(listed), sorted(set(by) - set(listed))[:5]
for t in listed: by.setdefault(t, [])
tg = {t: {"rows": len(rs), "no_lean": len(rs) == 0, "ok": sum(r["final"] == "ok" for r in rs),
          "narrower": sum(r["final"] == "narrower" for r in rs),
          "wrong_credit": sum(r["final"] == "wrong_credit" for r in rs),
          "claim_text": any("claim_text" in r["flags"] for r in rs)} for t, rs in by.items()}
json.dump(tg, open(OUT / "targets.json", "w"), indent=1)
assert len(tg) == 1021
print(dict(cnt), "targets", len(tg), "no-Lean targets", sum(v["no_lean"] for v in tg.values()), "targets with any non-ok row", sum(1 for v in tg.values() if v["ok"] < v["rows"]),
      "claim_text targets", sorted(t for t, v in tg.items() if v["claim_text"]))
