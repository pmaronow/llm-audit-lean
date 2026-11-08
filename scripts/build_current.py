#!/usr/bin/env python3
"""Build the full library and each current statement/proof entry, then check axioms.

An optional --work checks only that work, and is explicitly a partial check.
Challenge and Solution roots are compiled separately: importing both would
duplicate the statement names and is not a valid verification environment.
"""
import argparse
import fcntl
import os
from pathlib import Path
import subprocess
import sys

from current_package import check_current
from prune_setup_metadata import prune_completed, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", help="Check one work only, e.g. P038")
    parser.add_argument("--priority-work", help="Build one work before the full library, then complete the entire check")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    index = check_current(root)
    works = [row for row in index["works"] if row["target_count"]]
    if args.work:
        works = [row for row in works if row["work_id"] == args.work]
        if not works:
            parser.error("Unknown formal work")
    if args.work and args.priority_work:
        parser.error("--work is partial; --priority-work retains the full check. Choose one.")
    if args.priority_work and args.priority_work not in {row["work_id"] for row in works}:
        parser.error("Unknown priority work")
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "2")
    def build(module):
        print(f"Building {module}", flush=True)
        subprocess.run(["lake", "build", module], cwd=root, env=env, check=True)
        # The owned subprocess has exited successfully. Delete no proof output;
        # retain incomplete/rebuilding metadata and skip if another compiler runs.
        report(prune_completed(root))

    def build_work(work):
        wid = work["work_id"]
        for kind in ("Challenge", "Solution"):
            build(f"SAP.Works.{wid}.{kind}")

    lock_path = root / ".lake/current-build.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a") as lock:
        # Serialize supported invocations; process inspection additionally
        # protects independently launched Lean/Lake compilers during cleanup.
        fcntl.flock(lock, fcntl.LOCK_EX)
        report(prune_completed(root))
        if args.priority_work:
            priority = next(row for row in works if row["work_id"] == args.priority_work)
            print(f"Checking {args.priority_work} first; the full library and remaining works still follow.", flush=True)
            build_work(priority)
            subprocess.run([sys.executable, str(root / "scripts/print_axioms.py"),
                            "--work", args.priority_work], cwd=root, env=env, check=True)
        if not args.work:
            print("Building all library modules via AronowAudit.All", flush=True)
            build("AronowAudit.All")
        for work in works:
            if work["work_id"] != args.priority_work:
                build_work(work)
        command = [sys.executable, str(root / "scripts/print_axioms.py")]
        if args.work:
            command.extend(["--work", args.work])
        subprocess.run(command, cwd=root, env=env, check=True)
        report(prune_completed(root))
    print("Partial work check complete." if args.work else "Full library, statements and proofs checked.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, subprocess.CalledProcessError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(1)
