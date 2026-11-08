#!/usr/bin/env python3
"""Parent-executed tiny controls: work replay plus isolated inspector probes.

All unit certificate/review records in these inputs are explicitly synthetic. Only
the new replay output, if actually accepted, reports a real *fixture* Comparator run.
"""
import sys
if __name__ == "__main__":
    raise SystemExit("Use python3 -I -S -B /absolute/palomar.py runtime-controls ...; direct backend startup is unsupported")
sys.dont_write_bytecode = True
import argparse
from pathlib import Path
import subprocess
import sys

from work_package import Invalid, json_bytes, read_json, require, sha
from live_control_fixtures import (WORK_CASES, credit_admitted_generation,
                                   credit_work_replay, make_work_fixture)
from run_definition_probe import run_probe
from boundaries import guard_paths, inputs_for, plan_outputs


from _palomar_installation import entry as _entry, entry_sha256 as _entry_sha256

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for flag in ("lean","comparator-lake","primitive-check-file","exporter","lean-path-file","out"):
        parser.add_argument("--"+flag,type=Path,required=True)
    parser.add_argument("--read-only-root",type=Path,action="append",default=[])
    args=parser.parse_args()
    cwds=[args.out/case/"replay/work" for case in WORK_CASES]+[
        args.out/("isolated_"+variant)/"work" for variant in ("equal_definitions","different_definitions")]
    args.out=plan_outputs({"out":args.out},args,code_root=Path(__file__).resolve(),compiler_cwds=cwds)["out"]
    require(not args.out.exists(),"runtime control output must be fresh")
    args.out.mkdir(parents=True)
    scripts=Path(__file__).resolve().parent
    tool_args=[]
    for flag in ("lean","comparator-lake","primitive-check-file","exporter","lean-path-file"):
        tool_args.extend(["--"+flag,str(getattr(args,flag.replace("-","_")))])
    results=[]
    for case in WORK_CASES:
        root=args.out/case
        f=make_work_fixture(root,case)
        common=["--source",str(f.source),"--catalog",str(f.catalog),"--site",str(f.site),"--kind","baseline_fixture"]
        gen=subprocess.run([sys.executable,"-I","-S","-B",str(_entry),"--expected-entry-sha256",_entry_sha256,"generate",*common,"--out",str(f.entries)],capture_output=True,text=True)
        (root/"generation.log").write_text(gen.stdout+gen.stderr)
        if case=="admitted_solution":
            results.append(credit_admitted_generation(gen.returncode,gen.stderr,f.entries))
            (args.out/"PROGRESS.json").write_bytes(json_bytes({"status":"incomplete", "completed":results}))
            continue
        require(gen.returncode==0,f"{case} generation unexpectedly failed; see generation.log")
        out=root/"replay"
        proc=subprocess.run([sys.executable,"-I","-S","-B",str(_entry),"--expected-entry-sha256",_entry_sha256,"replay",*common,"--entries",str(f.entries),
            "--work","P900",*tool_args,"--out",str(out),"--allow-baseline-fixture"],capture_output=True,text=True)
        (root/"replay.log").write_text(proc.stdout+proc.stderr)
        results.append(credit_work_replay(case,out,proc.returncode))
        # Persist progress separately: a later failure never creates RESULTS.json.
        (args.out/"PROGRESS.json").write_bytes(json_bytes({"status":"incomplete", "completed":results}))
    for variant in ("equal_definitions","different_definitions"):
        probe_out=args.out/("isolated_"+variant)
        record=run_probe(probe_out,args.lean,args.lean_path_file,variant)
        results.append({"case":"isolated_"+variant,"passed":record["passed"],
            "scope":record["scope"],"stage":record["stage"],"comparator_invoked":False,
            "definition_non_value_fields_equal":record["definition_non_value_fields_equal"],
            "definition_non_value_fields_checked":record["definition_non_value_fields_checked"],
            "comparator_definition_rejection_exercised":False,
            "probe_record_sha256":sha(probe_out/"probe-result.json")})
        (args.out/"PROGRESS.json").write_bytes(json_bytes({"status":"incomplete", "completed":results}))
    receipt={"status":"live_fixture_controls_passed","results":results,"production_source_touched":False,
             "certifies_any_real_work":False,"a3_replay":False,
             "comparator_definition_rejection_exercised":False,
             "coverage_note":"Only the positive work fixture invokes Comparator. Other controls check explicit pre-Comparator guards; isolated probes exercise the unchanged inspector equality boundary outside shared Defs."}
    (args.out/"RESULTS.json").write_bytes(json_bytes(receipt))
    print(json_bytes(receipt).decode())


if __name__=="__main__":
    try:
        main()
    except (Invalid,OSError,KeyError,TypeError) as exc:
        print(f"INVALID: {exc}",file=sys.stderr);sys.exit(1)
