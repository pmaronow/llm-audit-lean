#!/usr/bin/env python3
"""One explicit final-source refresh, confined to a fresh output overlay and validation receipt."""
import sys
if __name__ == "__main__":
    raise SystemExit("Use python3 -I -S -B /absolute/palomar.py refresh ...; direct backend startup is unsupported")
sys.dont_write_bytecode = True
import argparse
from pathlib import Path
import subprocess
import sys

from work_package import Invalid, json_bytes, require, sha
from boundaries import guard_paths, inputs_for, plan_outputs


from _palomar_installation import entry as _entry, entry_sha256 as _entry_sha256

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for flag in ("source","catalog","site","base-source","attestation","routes","collection-receipt","collected-file-inventory","out",
                 "admission-root","admission-review"):
        parser.add_argument("--"+flag,type=Path,required=True)
    parser.add_argument("--expected-admission-review-sha256",required=True)
    for flag in ("expected-admission-pin-sha256","expected-admission-result-sha256","expected-reviewed-tool-lock-sha256"):
        parser.add_argument("--"+flag,required=True)
    parser.add_argument("--read-only-root",type=Path,action="append",default=[])
    args=parser.parse_args()
    planned=plan_outputs({"out":args.out,"receipt":args.out.with_name(args.out.name+"-STRUCTURAL-VALIDATION.json")},args,code_root=Path(__file__).resolve())
    args.out=planned["out"]
    require(args.source.is_absolute() and args.source.is_dir(),
            "explicit absolute collected source root is absent; no RC fallback is permitted")
    require(not args.out.exists(),"refresh --out must not exist")
    path=planned["receipt"]
    require(not path.exists(),f"refresh receipt already exists: {path}")
    scripts=Path(__file__).resolve().parent
    common=[]
    for flag in ("source","catalog","site","base-source","attestation","routes","collection-receipt","collected-file-inventory",
                 "admission-root","admission-review","expected-admission-review-sha256","expected-admission-pin-sha256",
                 "expected-admission-result-sha256","expected-reviewed-tool-lock-sha256"):
        common.extend(["--"+flag,str(getattr(args,flag.replace("-","_")))])
    for root in args.read_only_root:
        common.extend(["--read-only-root",str(root)])
    common.extend(["--kind","collected_candidate"])
    run=subprocess.run([sys.executable,"-I","-S","-B",str(_entry),"--expected-entry-sha256",_entry_sha256,"generate",*common,"--out",str(args.out)],capture_output=True,text=True)
    if run.returncode:
        print(run.stdout+run.stderr,file=sys.stderr);sys.exit(run.returncode)
    check=subprocess.run([sys.executable,"-I","-S","-B",str(_entry),"--expected-entry-sha256",_entry_sha256,"validate",*common,"--entries",str(args.out)],capture_output=True,text=True)
    receipt={"status":"candidate_structural_pass" if check.returncode==0 else "candidate_structural_failure",
             "generation_stdout":run.stdout,"validation_stdout":check.stdout,"validation_stderr":check.stderr,
             "validation_exit_code":check.returncode,"inventory_sha256":sha(args.out/"WORK-INVENTORY.json"),
             "combined_compilation":"not_run","combined_certification":"not_run","a3_replay":"not_claimed"}
    # Keep the receipt OUTSIDE the overlay: managed files remain byte deterministic.
    path.write_bytes(json_bytes(receipt))
    print(json_bytes(receipt).decode())
    sys.exit(check.returncode)


if __name__=="__main__":
    try:
        main()
    except (Invalid,OSError,KeyError,TypeError) as exc:
        print(f"INVALID: {exc}",file=sys.stderr);sys.exit(1)
