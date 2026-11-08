"""Explicitly synthetic diagnostic inputs; never collection or certificate authority."""
import argparse
from work_package import config,digest,json_bytes,read_json,sha,source_files,MARKERS

def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(value.encode() if isinstance(value, str) else json_bytes(value))

def fixture(root, skip_omission=False, duplicate_target=False):
    """Small real Lean sources with intentionally SYNTHETIC structural certificate records."""
    source, cat, site = root / "source", root / "catalog", root / "site"
    meta = {"title": "Synthetic work for structural controls", "citation": "Synthetic fixture, no certification evidence."}
    targets = [{"id": "P900-T1"}, {"id": "P900-T2"}, {"id": "P900-T3"}]
    write(cat / "works.json", [{"work_id": "P900", "work":meta}])
    write(cat / "works/P900.json", {"work_id": "P900", "work":meta, "targets":targets})
    write(site / "P900.json", {"work": {**meta,"id":"P900"}, "lean":{"applicable":True, "targets":targets}})
    write(site / "P901.json", {"work": {"id":"P901", "title":"Synthetic inapplicable work", "citation":"Fixture."},
                              "lean":{"applicable":False, "targets":[], "reason":"Synthetic prose-only work."}})
    index = {}
    for unit, tid in (("P900a", "P900-T1"), ("P900b", "P900-T1" if duplicate_target else "P900-T2")):
        base = source / "SAP" / unit
        name = "SAP." + unit + ".T" + tid.rsplit("T",1)[-1]
        rows = [{"target_id":tid, "theorem":name, "decision":"whole", "restriction":None,
                 "proof_status":"proved", "axioms":[], "rows_used":[], "rows_not_used":[]}]
        if unit == "P900a" and not skip_omission:
            rows.append({"target_id":"P900-T3", "theorem":None, "decision":"omitted", "proof_status":None,
                         "restriction":"Deliberately unformalized synthetic target.", "rows_used":[], "rows_not_used":[]})
        write(base / "Defs.lean", f"import Mathlib\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\ndef SAP.{unit}.Statement : Prop := True\n")
        write(base / "Challenge.lean", f"import SAP.{unit}.Defs\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\ntheorem {name} : SAP.{unit}.Statement := by sorry\n")
        write(base / "Solution.lean", f"import SAP.{unit}.Defs\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\ntheorem {name} : SAP.{unit}.Statement := by exact True.intro\n")
        write(base / "manifest.json", rows)
        write(base / "comparator.json", config(f"SAP.{unit}.Challenge", f"SAP.{unit}.Solution", [name]))
        task = base / "review/declarations/synthetic-fixture"
        claims = {"work_id":"P900", "unit_id":unit,"citation":meta["citation"],"standing_assumptions":[],
                  "targets":[{"target_id":r["target_id"],"canonical_claim":{"statement":"True (synthetic)."}} for r in rows]}
        write(base / "verification/claims.json", claims); write(task / "claims.json", claims)
        write(task / "record.json", [{k:v for k,v in r.items() if k not in ("proof_status","proof_plan","axioms")} for r in rows])
        findings, reviews = [], {}
        for r in rows:
            item = r["theorem"] or "OMIT." + r["target_id"]
            fp = digest([unit,r["target_id"],"SYNTHETIC"])
            verdict = "omission_ok" if r["theorem"] is None else "faithful"
            findings.append({"target_id":r["target_id"], "theorem":r["theorem"], "fingerprint":fp,
                             "verdict":verdict,"severity":"none","issues":[]})
            reviews[item] = {"target_id":r["target_id"],"decision":r["decision"],"fingerprint":fp,
                             "reviews":[{"binding":"v2","verdict":verdict,"severity":"none",
                                         "files":"review/declarations/synthetic-fixture"}]}
        write(task / "findings.json", findings)
        write(base / "verification/declaration-review.json", reviews)
        write(base / "verification/comparator.log", "SYNTHETIC STRUCTURAL FIXTURE; NOT A KERNEL RUN\n" + "\n".join(MARKERS))
        index[unit] = {"work":"P900", "targets":len(rows),"theorems":1,"items_reviewed":len(rows),
                       "decisions":{"whole":1,**({"omitted":1} if len(rows)==2 else {})}}
        recertify(source, unit)
    write(source / "SAP/INDEX.json", index)
    return argparse.Namespace(source=source,catalog=cat,site=site,base_source=None,kind="baseline_fixture",
                              attestation=None,routes=None,entries=root/"entries",work=None)

def recertify(source, unit):
    """SYNTHETIC ONLY: shape a fake receipt so deeper static guards are exercised."""
    base = source / "SAP" / unit
    rows = read_json(base / "manifest.json")
    names = [r["theorem"] for r in rows if r.get("theorem")]
    c = read_json(base / "comparator.json")
    write(base / "verification/comparator-result.json", {"accepted":True,"control":False,"work":unit,
        "stamp":"SYNTHETIC-NOT-CERTIFIED", "base":{"fixture":True},"config":c,
        "snapshot_sha256":source_files(source,unit),"config_sha256":sha(base/"comparator.json"),
        "manifest_sha256":sha(base/"manifest.json"), "targets":{"listed":len(rows),"certified":len(names),"omitted":len(rows)-len(names)},
        "steps":[{"step":s,"rc":0} for s in ("rebuild-from-snapshot","export-challenge","export-solution","comparator")],
        "markers":{m:True for m in MARKERS}})
