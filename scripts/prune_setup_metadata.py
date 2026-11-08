#!/usr/bin/env python3
"""Reclaim completed Lake setup metadata, never source or proof artifacts.

Call only between synchronous build phases. A compiler uses its setup JSON as
input while running; an old OLean alone is not evidence that deletion is safe.
"""
import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import stat
import sys


@dataclass(frozen=True)
class CleanupResult:
    files: int = 0
    bytes: int = 0
    skipped: str = ""


def compiler_activity(proc_root=Path("/proc")):
    """Return a reason to skip, or empty only after inspecting process states."""
    try:
        processes = list(proc_root.iterdir())
    except OSError as exc:
        return f"process inspection unavailable: {exc}"
    for process in processes:
        if not process.name.isdigit():
            continue
        try:
            name = (process / "comm").read_text().strip()
            if name not in {"lean", "lake"}:
                continue
            status = (process / "stat").read_text()
            # comm is parenthesized and may itself contain spaces or ')'.
            state = status[status.rfind(")") + 2:].split()[0]
            if state not in {"Z", "X"}:
                return f"live {name} process {process.name}"
        except (FileNotFoundError, ProcessLookupError):
            continue  # A process that exited cannot retain a setup-file handle.
        except (OSError, IndexError) as exc:
            return f"process inspection incomplete: {exc}"
    return ""


def regular_file(path):
    """Check every component without following a generated-directory symlink."""
    for parent in path.parents:
        if parent.is_symlink():
            return None
    try:
        info = path.lstat()
    except FileNotFoundError:
        return None
    return info if stat.S_ISREG(info.st_mode) and info.st_size else None


def completed_setup(path, build):
    relative = path.relative_to(build / "ir").as_posix()
    if not relative.endswith(".setup.json"):
        return None
    module = relative[:-len(".setup.json")]
    setup = regular_file(path)
    olean = regular_file(build / "lib/lean" / (module + ".olean"))
    trace_path = build / "lib/lean" / (module + ".trace")
    trace = regular_file(trace_path)
    if not setup or not olean or not trace:
        return None
    if min(olean.st_mtime_ns, trace.st_mtime_ns) < setup.st_mtime_ns:
        return None  # Previous outputs can remain while a rebuild is unfinished.
    try:
        record = json.loads(trace_path.read_bytes())
    except (OSError, ValueError):
        return None
    if (not isinstance(record, dict) or record.get("schemaVersion") != "2025-09-10"
            or record.get("synthetic") is not False):
        return None
    outputs = record.get("outputs")
    if not isinstance(outputs, dict):
        return None
    oleans = outputs.get("o")
    inputs = record.get("inputs")
    log = record.get("log")
    if (not isinstance(oleans, list) or not oleans or not all(isinstance(item, str) and item for item in oleans)
            or not isinstance(inputs, list) or not isinstance(log, list)
            or not all(isinstance(item, dict) for item in log)):
        return None
    # Cleanup is valid for this Lake trace format only when setup metadata is
    # absent from both inputs and outputs. The command in log may mention it.
    declared = json.dumps({"inputs": inputs, "outputs": outputs})
    if ".setup.json" in declared:
        return None
    if any(item.get("level") == "error" for item in log):
        return None
    return setup


def prune_completed(root, dry_run=False, activity_probe=compiler_activity):
    root = root.resolve(strict=True)
    build = root / ".lake/build"
    for path in (root / ".lake", build, build / "ir", build / "lib", build / "lib/lean"):
        if path.is_symlink():
            return CleanupResult(skipped=f"generated directory is a symlink: {path}")
    if not (build / "ir").is_dir():
        return CleanupResult()
    reason = activity_probe()
    if reason:
        return CleanupResult(skipped=reason)
    count = size = 0
    for path in sorted((build / "ir").rglob("*.setup.json")):
        info = completed_setup(path, build)
        if info is None:
            continue
        reason = activity_probe()
        if reason:
            return CleanupResult(count, size, reason)
        # Recheck identity immediately before deletion. The caller holds the
        # build lock; no owned build is launched during this phase.
        current = regular_file(path)
        if current is None or (current.st_dev, current.st_ino, current.st_mtime_ns, current.st_size) != (
                info.st_dev, info.st_ino, info.st_mtime_ns, info.st_size):
            continue
        if not dry_run:
            path.unlink()
        count += 1
        size += info.st_size
    return CleanupResult(count, size)


def report(result, dry_run=False):
    action = "Eligible completed setup metadata" if dry_run else "Removed completed setup metadata"
    print(f"{action}: {result.files} files, {result.bytes / 2**30:.2f} GiB", flush=True)
    if result.skipped:
        print(f"Setup cleanup skipped: {result.skipped}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    # Share the current-build lock even when invoked manually. The process probe
    # also protects independently launched Lean/Lake commands that lack it.
    import fcntl
    lock_path = args.root / ".lake/current-build.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        report(prune_completed(args.root, args.dry_run), args.dry_run)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except OSError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(1)
