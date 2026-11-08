"""Check current repository material without treating retained evidence as prose.

Only exact hash-bound imported files in the archive's source/evidence locations
are exempt. README, docs, scripts and workflow changes always receive the scan.
Diagnostics identify the file, line and kind, never the matched content.
"""
import hashlib
from pathlib import PurePosixPath
import re


ARCHIVE_PREFIXES = ("AronowAudit/", "SAP/", "release-evidence/", "tools/", "catalog/")
ARCHIVE_ROOT_FILES = {"AronowAudit.lean", "LICENSE", "NOTICE", "lake-manifest.json",
                      "lakefile.toml", "lean-toolchain"}
REMOVED_OPERATIONAL_FILES = {"sap_pipeline.py", "run_pipeline.sh"}

PATTERNS = {
    "local-path": re.compile(
        r"(?<![\w])(?:/(?:Users|home|workspace|private|codex)/[^\s/\"'`]+|"
        r"~" r"/[^\s/\"'`]+)"),
    "email-address": re.compile(
        r"[A-Za-z0-9.!#$%&\x27*+/=?^_`{|}~-]+@[A-Za-z0-9](?:[A-Za-z0-9.-]*[A-Za-z0-9])?\.[A-Za-z]{2,}"),
    "internal-account-detail": re.compile(
        r"\b(?:Yale|gmail)\s+(?:account|home|token)\b|\.(?:codex|claude)-(?:yale|gmail)\b|"
        r"\b(?:Yale|gmail)\s+(?:go\s+to\s+)?credits\b", re.I),
    "internal-author-instruction": re.compile(
        r"\b(?:author|user)\s+(?:instructions?|requests?|said|told|directed)\s*[:(]|"
        r"\b(?:author|user)\s+\d{4}-\d{2}-\d{2}\s*:|"
        r"Use\s+the\s+API\s+for\s+any\s+Opus\s+tasks", re.I),
    "credential": re.compile(
        r"\b(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{30,}|"
        r"sk-(?:proj-|ant-)[A-Za-z0-9_-]{15,}|xox[baprs]-[A-Za-z0-9-]{15,}|"
        r"(?:AKIA|ASIA)[A-Z0-9]{16}|AIza[A-Za-z0-9_-]{35})\b|"
        r"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----|"
        r"https?://[^\s/@:]+:[^\s/@]+@|"
        r"\b(?:api[_-]?key|access[_-]?token|password|secret)\s*[:=]\s*['\"][A-Za-z0-9_/+=.-]{12,}", re.I),
}


def archive_file(path, data, manifest):
    """Directory membership alone never exempts a file from the current scan."""
    if not (path.startswith(ARCHIVE_PREFIXES) or path in ARCHIVE_ROOT_FILES):
        return False
    expected = manifest.get("files", {}).get(path)
    if expected is None:
        expected = manifest.get("historical_catalog", {}).get("files", {}).get(path)
    return expected is not None and hashlib.sha256(data).hexdigest() == expected


def hygiene_hits(files, manifest):
    hits = []
    for path, data in sorted(files.items()):
        archived = archive_file(path, data, manifest)
        evidence = path.startswith(("SAP/", "release-evidence/")) and archived
        if PurePosixPath(path).name in REMOVED_OPERATIONAL_FILES and not evidence:
            hits.append({"file": path, "line": 1, "kind": "excluded-operational-script"})
        if archived:
            continue
        text = data.decode("utf-8", errors="replace")
        for kind, pattern in PATTERNS.items():
            for match in pattern.finditer(text):
                hits.append({"file": path, "line": text.count("\n", 0, match.start()) + 1, "kind": kind})
    return hits


def check_hygiene(files, manifest):
    hits = hygiene_hits(files, manifest)
    if hits:
        locations = "; ".join(f"{h['file']}:{h['line']}: {h['kind']}" for h in hits[:20])
        more = f"; and {len(hits) - 20} more" if len(hits) > 20 else ""
        raise ValueError(f"Repository content hygiene failed: {locations}{more}")
    return 0
