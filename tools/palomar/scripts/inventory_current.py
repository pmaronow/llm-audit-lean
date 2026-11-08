#!/usr/bin/env python3
"""Inventory current A2 target routes WITHOUT pretending the local RC is current.

This report is not a generated final package. Only manifests matching the current
attestation supply disclosures. Missing current bytes are explicit nulls.
"""
import sys
if __name__ == "__main__":
    raise SystemExit("Use python3 -I -S -B /absolute/palomar.py inventory ...; direct backend startup is unsupported")
sys.dont_write_bytecode = True
import argparse
import collections
from pathlib import Path
import re
import sys

from work_package import (Invalid, catalogs, check_manifest, digest, json_bytes, key, manifest_rows,
                          read_json, require, sha, source_files)
from boundaries import guard_paths, inputs_for


from _palomar_installation import entry as _entry, entry_sha256 as _entry_sha256

def pair(value):
    require("=" in value, "expected UNIT=/absolute/path")
    unit, path = value.split("=",1)
    return unit,Path(path)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for flag in ("catalog","site","routes","attestation","baseline-source","out"):
        parser.add_argument("--"+flag,type=Path,required=True)
    parser.add_argument("--unit-source",action="append",default=[],help="UNIT=root, e.g. integration/candidate")
    parser.add_argument("--review-evidence",action="append",default=[],help="UNIT=authoritative review task directory")
    parser.add_argument("--collection-failure",type=Path,help="latest actual failed normal collection receipt")
    parser.add_argument("--parent-update",type=Path,help="parent's contemporaneous explanation; hashed as evidence")
    args=parser.parse_args()
    reads=inputs_for(args,code_root=Path(__file__).resolve())
    for i,value in enumerate(args.unit_source+args.review_evidence):
        reads[f"extra_input_{i}"]=pair(value)[1]
    if args.collection_failure:
        reads["retained_collection_log"]=args.collection_failure.parent/"collect.log"
    args.out=guard_paths({"out":args.out},reads)["out"]
    require(not args.out.exists(),"inventory output exists; choose a new path")
    formal,site=catalogs(args.catalog,args.site)
    routes,att=read_json(args.routes),read_json(args.attestation)
    require(att.get("status")=="READ_ONLY_MATCH","source attestation is not a read-only match")
    unit_work=read_json(args.baseline_source/"SAP/INDEX.json")
    att_units={u["unit"]:u for u in att["units"]}
    require(len(att_units)==len(att["units"])==att["unit_count"],"duplicate or missing attested unit")
    require(set(unit_work)==set(att_units),"baseline/current unit identity mismatch")
    target_rows=routes["target_rows"]
    tids=[r["target_id"] for r in target_rows]
    catalog_ids=[t["id"] for c in formal.values() for t in c["targets"]]
    require(len(set(tids))==len(tids)==att["target_count"] and set(tids)==set(catalog_ids),"current target coverage mismatch")
    overrides={}
    for value in args.unit_source:
        u,p=pair(value);require(u not in overrides and u in att_units,"duplicate/unknown source override")
        overrides[u]=p
    review_evidence=collections.defaultdict(list)
    for value in args.review_evidence:
        u,p=pair(value);require(u in att_units and p.is_dir(),"missing/unknown review evidence")
        findings=read_json(p/"findings.json");findings=findings if isinstance(findings,list) else [findings]
        require(findings and all(f.get("severity")=="none" and f.get("issues")==[] and
                f.get("verdict") in ("faithful","omission_ok") for f in findings),"review evidence is not clean")
        review_evidence[u].append({"local_path":str(p.resolve()),"scope":"authoritative_fresh_review_evidence_not_collector_rebinding",
            "target_ids":[f["target_id"] for f in findings],"files_sha256":{str(f.relative_to(p)):sha(f)
                for f in sorted(p.rglob("*")) if f.is_file()}})
    units,current_manifests={},{}
    for unit,a in sorted(att_units.items()):
        source=overrides.get(unit,args.baseline_source)
        base=source/"SAP"/unit
        man_match=(base/"manifest.json").is_file() and sha(base/"manifest.json")==a["manifest_sha256"]
        sources_match=source_files(source,unit)==a["source_sha256"]
        cert_match=(base/"verification/comparator-result.json").is_file() and sha(base/"verification/comparator-result.json")==a["certificate_sha256"]
        if unit in overrides:
            require(man_match and sources_match and cert_match,f"{unit}: override differs from current attestation")
        if man_match:
            rows=manifest_rows(read_json(base/"manifest.json"),base)
            check_manifest(rows,unit_work[unit]["work"],unit)
            current_manifests[unit]={r["target_id"]:r for r in rows}
        units[unit]={"work_id":unit_work[unit]["work"],"authoritative_current_hashes":a,
            "local_source_root_checked":str(source.resolve()),"local_source_matches":sources_match,
            "local_manifest_matches":man_match,"local_certificate_matches":cert_match,
            "authoritative_fresh_review_evidence":review_evidence[unit],
            "collected_current_review_export_available":False}
    failure=None
    blocked=[]
    if args.collection_failure:
        receipt=read_json(args.collection_failure)
        require(receipt.get("status")=="FAILED_NOT_ACCEPTED" and receipt.get("collector_exit_code")!=0,
                "collection-failure input is not a failed normal collection")
        log_path=args.collection_failure.parent/"collect.log"
        log=log_path.read_text()
        for unit,name in re.findall(r"^\s+(P[0-9]{3}[a-z]?) \['(SAP\.[^: ]+): no clean review bound to its current version",log,re.M):
            rows=[r for r in target_rows if r["unit"]==unit and r["theorem"]==name]
            require(len(rows)==1,"failed review does not match exact current target route")
            blocked.append({"unit_id":unit,"target_id":rows[0]["target_id"],"theorem":name,
                            "reason":"normal_collector_no_clean_current_bound_review"})
        require(blocked,"no exact blocked target IDs could be reconciled with failed collection")
        failure={"status":receipt["status"],"receipt_sha256":sha(args.collection_failure),
                 "collect_log_sha256":sha(log_path),"blocked_current_items":blocked,
                 "all_81_normal_certificates_do_not_establish_uniformly_clean_current_reviews":True,
                 "partial_collection_is_final_input":False}
        if args.parent_update:
            failure["parent_update_sha256"]=sha(args.parent_update)
    works=[]
    for work in sorted(site):
        meta=site[work]["work"]
        row={"work_id":work,"title":meta["title"],"citation":meta["citation"],
             "formal_catalog_member":work in formal,"proposed_entry_directory":f"SAP/Works/{work}",
             "baseline_preview_directory":f"baseline-preview/SAP/Works/{work}","combined_certificate":None}
        if work not in formal:
            row.update({"coverage_disposition":"not_applicable_per_site_catalog","reason":site[work]["lean"]["reason"],
                        "unit_ids":[],"targets":[],"target_count":0,"theorem_count":0,"decisions":{}})
        else:
            unit_ids=sorted(u for u,x in unit_work.items() if x["work"]==work)
            mapped=[]
            for r in sorted((r for r in target_rows if r["unit"] in unit_ids),key=lambda r:key(r["target_id"])):
                unit=r["unit"];m=current_manifests.get(unit,{}).get(r["target_id"])
                if m:
                    require(all(m.get(k)==r.get(k) for k in ("decision","theorem")),"A2 route/current manifest mismatch")
                mapped.append({**r,"manifest_disclosure_available":m is not None,
                    "current_manifest_entry":m,
                    "disclosure_status":"current_attested_manifest_available" if m else "await_fresh_collected_current_manifest",
                    "challenge_module":f"SAP.{unit}.Challenge" if r.get("theorem") else None,
                    "solution_module":f"SAP.{unit}.Solution" if r.get("theorem") else None,
                    "unit_certificate_path":f"SAP/{unit}/verification/comparator-result.json",
                    "unit_certificate_sha256":att_units[unit]["certificate_sha256"],
                    "review_key":r.get("theorem") or "OMIT."+r["target_id"]})
            require({r["target_id"] for r in mapped}=={t["id"] for t in formal[work]["targets"]},"wrong work/target assignment")
            row.update({"coverage_disposition":"current_target_mapping_attested_complete_source_snapshot_pending",
                "unit_ids":unit_ids,"target_count":len(mapped),"theorem_count":sum(r["theorem"] is not None for r in mapped),
                "decisions":dict(collections.Counter(r["decision"] for r in mapped)),"targets":mapped,
                "work_modules":{part:f"SAP.Works.{work}.{part}" for part in ("Defs","Challenge","Solution")}})
            row["current_normal_collection_review_blocks"]=[b for b in blocked if b["unit_id"] in unit_ids]
        works.append(row)
    inv={"schema":"palomar-current-work-inventory-v1","status":"CURRENT_A2_MAPPING_NOT_FINAL_SOURCE_VALIDATION",
        "counts":{"formal_works":len(formal),"site_works":len(site),"units":len(units),"targets":len(tids),
                  "theorems":sum(r["theorem"] is not None for r in target_rows),
                  "decisions":dict(collections.Counter(r["decision"] for r in target_rows)),
                  "current_unit_sources_locally_matched":sum(u["local_source_matches"] for u in units.values()),
                  "current_manifests_locally_matched":len(current_manifests)},
        "source_evidence":{"attestation_sha256":sha(args.attestation),"route_plan_sha256":sha(args.routes),
            "route_plan_recorded_status":routes.get("status"),"attestation_recorded_status":att.get("status"),
            "route_plan_pending_apply_field_is_historical":routes.get("pending_guarded_apply_units"),
            "a3_replay":False,"final_candidate_content_sha256":None},
        "work_identity_reconciliation":{"formal_ids":sorted(formal),"site_ids":sorted(site),
            "site_only_ids":sorted(set(site)-set(formal)),"formal_only_ids":sorted(set(formal)-set(site)),
            "unresolved_work_id_issues":[],"rule":"Exact catalog IDs; absent numeric IDs are not inferred works."},
        "missing_complete_current_source_units":[u for u,x in units.items() if not x["local_source_matches"]],
        "latest_normal_collection":failure or {"status":"not_supplied_not_assessed"},
        "units":units,"works":works}
    args.out.write_bytes(json_bytes(inv))
    print(json_bytes({"status":inv["status"],"counts":inv["counts"],"inventory_sha256":sha(args.out)}).decode().strip())


if __name__=="__main__":
    try:
        main()
    except (Invalid,OSError,KeyError,TypeError) as exc:
        print(f"INVALID: {exc}",file=sys.stderr);sys.exit(1)
