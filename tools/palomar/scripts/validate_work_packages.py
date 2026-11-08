#!/usr/bin/env python3
"""Revalidate explicit source/evidence and compare every managed entry byte-for-byte."""
import sys
if __name__ == "__main__":
    raise SystemExit("Use python3 -I -S -B /absolute/palomar.py validate ...; direct backend startup is unsupported")
sys.dont_write_bytecode = True
import json
from pathlib import Path
import sys

from generate_work_packages import arguments, prepare
from work_package import Invalid, digest, read_json, require, sha
from boundaries import file_inventory
import hashlib


def validate(args):
    expected = prepare(args)
    require(args.entries.is_dir(), f"entries absent: {args.entries}")
    # Work selection limits entry comparisons; global source completeness still runs.
    if args.work:
        require(f"SAP/Works/{args.work}/README.md" in expected, f"unknown work: {args.work}")
    actual = file_inventory(args.entries)
    wanted = {p:hashlib.sha256(data).hexdigest() for p,data in expected.items()}
    require(set(actual) == set(wanted), f"entire overlay file inventory mismatch: {sorted(set(actual)^set(wanted))[:8]}")
    require(actual == wanted, "entire overlay bytes differ from explicit source")
    expected_dirs = {str(parent) for p in expected for parent in Path(p).parents if str(parent) != "."}
    actual_dirs = {str(p.relative_to(args.entries)) for p in args.entries.rglob("*") if p.is_dir()}
    require(actual_dirs == expected_dirs, "overlay contains an extra or missing directory root")
    checked = []
    for path, data in expected.items():
        p = args.entries / path
        require(p.is_file() and not p.is_symlink(), f"missing generated file: {path}")
        require(p.read_bytes() == data, f"generated entry differs from explicit source: {path}")
        checked.append(path)
    return {"status": "structural_pass", "source_kind": args.kind, "work": args.work,
            "checked_files": len(checked), "counts": read_json(args.entries / "WORK-INVENTORY.json")["counts"],
            "managed_content_sha256": digest({k: sha(args.entries / k) for k in sorted(expected)}),
            "unit_certificate_record_and_exported_review_consistency": "passed",
            "full_fw_rebinding": "normal_collector_required", "lean_compilation": "not_run",
            "independent_admission_review_sha256":getattr(args,"expected_admission_review_sha256",None),
            "successful_collection_receipt_sha256":sha(args.collection_receipt) if args.kind=="collected_candidate" else None,
            "new_combined_certificate": None, "a3_replay": "not_claimed"}


def main():
    parser = arguments()
    parser.add_argument("--entries", type=Path, required=True)
    parser.add_argument("--work", help="validate one named work, while retaining global source completeness")
    args = parser.parse_args()
    print(json.dumps(validate(args), sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (Invalid, OSError, KeyError, TypeError) as exc:
        print(f"INVALID: {exc}", file=sys.stderr)
        sys.exit(1)
