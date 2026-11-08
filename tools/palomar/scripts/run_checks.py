#!/usr/bin/env python3
"""Persist local structural checks, with exact argv and no claimed Lean execution."""
import sys
if __name__ == "__main__":
    raise SystemExit("Use python3 -I -S -B /absolute/palomar.py checks ...; direct backend startup is unsupported")
import os
sys.dont_write_bytecode = True
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

from generate_work_packages import prepare
from work_package import Invalid, digest, json_bytes, read_json, require, sha, verify_collection
from boundaries import guard_paths, inputs_for, plan_outputs


from _palomar_installation import entry as _entry, entry_sha256 as _entry_sha256

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for flag in ("source","catalog","site","entries","attestation","routes","out"):
        p.add_argument("--"+flag,type=Path,required=True)
    p.add_argument("--failed-collection-receipt",type=Path)
    args=p.parse_args()
    plan=plan_outputs({"out":args.out,"scratch":args.out/"scratch"},args,code_root=Path(__file__).resolve())
    args.out=plan["out"]
    require(not args.out.exists(),"check output must be new")
    args.out.mkdir(parents=True)
    root=Path(__file__).resolve().parents[1]
    scripts=root/"scripts"
    common=["--source",str(args.source),"--catalog",str(args.catalog),"--site",str(args.site),"--kind","baseline_fixture"]
    def inventory():
        return {str(f.relative_to(args.source)):sha(f) for f in sorted((args.source/"SAP").rglob("*"))
                if f.is_file() and "__pycache__" not in f.parts}
    before=inventory()
    checks=[]
    def run(name,argv,expected_rc=0):
        proc=subprocess.run(argv,capture_output=True,text=True,env={**os.environ,
            "PALOMAR_TEST_SCRATCH_ROOT":str(plan["scratch"]),"PYTHONDONTWRITEBYTECODE":"1"})
        log=args.out/(name+".log");log.write_text(proc.stdout+proc.stderr)
        checks.append({"name":name,"argv":argv,"rc":proc.returncode,"expected_rc":expected_rc,
                       "passed":proc.returncode==expected_rc,"log_sha256":sha(log)})
        require(proc.returncode==expected_rc,f"{name}: unexpected return code; see {log}")
        return proc
    run("baseline-all-works",[sys.executable,"-I","-S","-B",str(_entry),"--expected-entry-sha256",_entry_sha256,"validate",*common,"--entries",str(args.entries)])
    run("baseline-one-work",[sys.executable,"-I","-S","-B",str(_entry),"--expected-entry-sha256",_entry_sha256,"validate",*common,"--entries",str(args.entries),"--work","P001"])
    run("inapplicable-work",[sys.executable,"-I","-S","-B",str(_entry),"--expected-entry-sha256",_entry_sha256,"validate",*common,"--entries",str(args.entries),"--work","P048"])
    absent=args.out/"intentionally-absent-source"
    negative_out=args.out/"must-not-be-generated"
    missing=run("missing-final-source",[sys.executable,"-I","-S","-B",str(_entry),"--expected-entry-sha256",_entry_sha256,"generate","--source",str(absent),
        "--catalog",str(args.catalog),"--site",str(args.site),"--kind","collected_candidate",
        "--attestation",str(args.attestation),"--routes",str(args.routes),"--out",str(negative_out)],1)
    require("no RC fallback" in missing.stderr and not negative_out.exists(),"missing-source failure was not atomic")
    stale=run("rc-cannot-be-final",[sys.executable,"-I","-S","-B",str(_entry),"--expected-entry-sha256",_entry_sha256,"generate","--source",str(args.source),
        "--catalog",str(args.catalog),"--site",str(args.site),"--kind","collected_candidate",
        "--attestation",str(args.attestation),"--routes",str(args.routes),"--out",str(negative_out)],1)
    require("complete collected file inventory required" in stale.stderr and not negative_out.exists(),
            "RC without mandatory full collection evidence was not rejected atomically")
    failed_receipt_check=None
    if args.failed_collection_receipt:
        try:
            verify_collection(args.source,args.attestation,args.failed_collection_receipt,
                args.failed_collection_receipt.parent/"collected-file-inventory.json",
                read_json(args.source/"SAP/INDEX.json"),1021)
            raise RuntimeError("actual failed collection receipt was accepted")
        except Invalid as exc:
            require("partial snapshots are rejected" in str(exc),"failed receipt rejected for an unrelated reason")
            failed_receipt_check={"passed":True,"receipt_sha256":sha(args.failed_collection_receipt),"diagnostic":str(exc)}
    fixture_args=argparse.Namespace(source=args.source,catalog=args.catalog,site=args.site,base_source=None,
                                    kind="baseline_fixture",attestation=None,routes=None)
    first,second=prepare(fixture_args),prepare(fixture_args)
    require(first==second,"generator is not byte deterministic")
    require(all((args.entries/n).read_bytes()==b for n,b in first.items()),"staged preview differs from generator")
    after=inventory();require(before==after,"read-only baseline source/evidence changed")
    result={"status":"all_local_structural_checks_passed","checks":checks,
            "deterministic_generation":{"files":len(first),"bytes_equal":True,
                "content_sha256":digest({n:sha(args.entries/n) for n in first})},
            "baseline_source_evidence_unchanged":{"files":len(before),"before_sha256":digest(before),"after_sha256":digest(after)},
            "baseline_counts":read_json(args.entries/"WORK-INVENTORY.json")["counts"],
            "lean_available_on_PATH":shutil.which("lean") is not None,"lean_compilation":"not_run","comparator_replay":"not_run",
            "new_combined_certificates":0,"final_candidate_validation":"pending_explicit_collected_source"}
    result["actual_failed_collection_receipt_rejected"]=failed_receipt_check
    (args.out/"RESULTS.json").write_bytes(json_bytes(result))
    print(json_bytes(result).decode())


if __name__=="__main__":
    main()
