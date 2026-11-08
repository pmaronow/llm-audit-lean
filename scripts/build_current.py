#!/usr/bin/env python3
"""Build the full library and each current statement/proof entry, then check axioms.

An optional --work checks only that work, and is explicitly a partial check.
Challenge and Solution roots are compiled separately: importing both would
duplicate the statement names and is not a valid verification environment.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from current_package import check_current


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", help="Check one work only, e.g. P038")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    index = check_current(root)
    works = [row for row in index["works"] if row["target_count"]]
    if args.work:
        works = [row for row in works if row["work_id"] == args.work]
        if not works:
            parser.error("Unknown formal work")
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "2")
    if not args.work:
        print("Building all library modules via AronowAudit.All", flush=True)
        subprocess.run(["lake", "build", "AronowAudit.All"], cwd=root, env=env, check=True)
    for work in works:
        wid = work["work_id"]
        for kind in ("Challenge", "Solution"):
            module = f"SAP.Works.{wid}.{kind}"
            print(f"Building {module}", flush=True)
            subprocess.run(["lake", "build", module], cwd=root, env=env, check=True)
    command = [sys.executable, str(root / "scripts/print_axioms.py")]
    if args.work:
        command.extend(["--work", args.work])
    subprocess.run(command, cwd=root, env=env, check=True)
    print("Partial work check complete." if args.work else "Full library, statements and proofs checked.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, subprocess.CalledProcessError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(1)
