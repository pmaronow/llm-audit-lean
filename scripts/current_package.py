#!/usr/bin/env python3
"""Generate and check the current statement/proof index without changing source evidence.

These checks reconcile source identities and import separation. They do not run
Lean or establish correspondence to a paper; use build_current.py for compilation.
"""
from collections import Counter
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

from check_repository import _mask_lean, scan_declarations, safe_relative, check_links
from reader_disclosures import reader_disclosure

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DECISIONS = {"whole", "restricted", "refuted", "omitted"}
CHALLENGE = re.compile(r"^SAP/P\d{3}[a-z]?/Challenge(?:/[^/]+)*\.lean$")

# Reader annotations of the bound definitions, separate from certified outcomes.
# P005b: Defs/Part7 and Defs/WholeW1; P015a: Defs/WholeW1.T8WholeStatement;
# P029b: Defs/WholeW2.T27WholeStatement.
READER_NOTES = {
    "P001-T6": "The population consistency theorem assumes a uniform bound on conditional residual variance. It covers that sufficient repair, not the broader finite-unconditional-residual-variance repair in P001-C04-E001. The recorded whole classification does not certify the broader repair.",
    "P005-T25": "The asymptotic result assumes invertibility of the noninteracted sample matrix for every treatment assignment at all sufficiently large sample sizes.",
    "P005-T26": "The asymptotic result assumes invertibility of the noninteracted sample matrix for every treatment assignment at all sufficiently large sample sizes.",
    "P005-T27": "The asymptotic result assumes invertibility of both arm sample matrices for every treatment assignment at all sufficiently large sample sizes.",
    "P011-T16": "The positive asymptotic results additionally require nested observed induced graphs. Nesting of the full graphs alone, with arbitrary observed subsets, does not imply this condition. Their coverage of the paper's repair is therefore restricted despite the recorded whole classification; the explicit counterexamples are unaffected.",
    "P011-T19": "The positive asymptotic branch additionally requires nested observed induced graphs, beyond the paper's nesting of full graphs. Its coverage is restricted by that extra condition despite the recorded whole classification. The explicit nested counterexample remains valid.",
    "P015-T8": "The square-link illustration permits misspecification of the working conditional-mean model.",
    "P023-T12": "The theorem proves a refutation of printed Proposition 2 under the fixed-law reading. The recorded whole classification concerns completeness of that adopted refutation, not truth of the printed positive proposition.",
    "P029-T27": "The counterexample refutes only the blanket claim that failure of Assumption 1 must cause bias. It does not refute the integral-limit or constant-score identities.",
    "P032-T5": "The theorem refutes all four stated universal lower-bound readings. The recorded whole classification concerns completeness of that negative result, not proof of the printed lower bound.",
}


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load(root, path):
    return json.loads((root / safe_relative(path)).read_bytes())


def location(path, line, sources):
    return {"path": path, "line": line, "sha256": digest(sources[path])}


def inspect_sources(root):
    sources, declarations, imports = {}, {}, {}
    for path in sorted((root / "SAP").rglob("*.lean")):
        relative = path.relative_to(root).as_posix()
        data = path.read_bytes()
        sources[relative] = data
        clean = _mask_lean(data.decode())
        for name, lines in scan_declarations(data.decode()).items():
            declarations.setdefault(name, []).extend((relative, line) for line in lines)
        module_imports = []
        for line in clean.splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+)$", line)
            if match:
                module_imports.extend(match[1].split())
        imports[relative] = module_imports
    return sources, declarations, imports


def unique_location(name, declarations, sources, predicate, label):
    found = [(path, line) for path, line in declarations.get(name, []) if predicate(path)]
    if len(found) != 1:
        raise ValueError(f"Expected one {label} declaration for {name}, got {found}")
    return location(*found[0], sources)


def build_index(root):
    source_manifest = load(root, "package/source-manifest.json")
    unit_index = load(root, "SAP/INDEX.json")
    work_index = load(root, "SAP/Works/INDEX.json")
    sources, declarations, _ = inspect_sources(root)
    targets, seen, unit_counts = [], set(), {}
    for unit_id, summary in sorted(unit_index.items()):
        manifest_path = f"SAP/{unit_id}/manifest.json"
        manifest = load(root, manifest_path)
        if isinstance(manifest, dict):
            manifest = manifest["targets"]
        comparator = load(root, f"SAP/{unit_id}/comparator.json")
        theorem_names = []
        decisions = Counter()
        for entry in manifest:
            tid, decision = entry["target_id"], entry["decision"]
            if tid in seen or decision not in DECISIONS:
                raise ValueError(f"Duplicate target or invalid decision: {tid}")
            if not tid.startswith(summary["work"] + "-T"):
                raise ValueError(f"Target has the wrong work: {tid}")
            seen.add(tid)
            decisions[decision] += 1
            theorem = entry.get("theorem")
            axioms = entry.get("axioms") or []
            if set(axioms) - STANDARD_AXIOMS:
                raise ValueError(f"Nonstandard recorded axioms: {tid}")
            row = {
                "target_id": tid, "work_id": summary["work"], "unit_id": unit_id,
                "decision": decision, "theorem": theorem,
                "restriction": entry.get("restriction"),
                "omission_reason": (entry.get("omission_reason") or entry.get("reason")
                                    or entry.get("restriction")) if decision == "omitted" else None,
                "manifest": {"path": manifest_path, "sha256": digest((root / manifest_path).read_bytes())},
                "recorded_axioms": axioms,
                "challenge": None, "solution": None, "definitions": [],
                "verification": f"SAP/{unit_id}/verification/declaration-review.json",
            }
            if decision == "omitted":
                if theorem or not row["omission_reason"]:
                    raise ValueError(f"Omission lacks its explanation or claims a theorem: {tid}")
            else:
                if not theorem or not theorem.startswith(f"SAP.{unit_id}."):
                    raise ValueError(f"Invalid theorem name: {tid}")
                theorem_names.append(theorem)
                row["challenge"] = unique_location(theorem, declarations, sources,
                    lambda path: bool(CHALLENGE.fullmatch(path)), "Challenge")
                row["solution"] = unique_location(theorem, declarations, sources,
                    lambda path: path == f"SAP/{unit_id}/Solution.lean", "Solution")
                statement = entry.get("statement_definition")
                if statement:
                    row["definitions"].append(unique_location(statement, declarations, sources,
                        lambda path: not CHALLENGE.fullmatch(path) and "/Solution" not in path,
                        "statement definition"))
                row["definitions_root"] = f"SAP/{unit_id}/Defs.lean"
            targets.append(row)
        if (dict(decisions) != summary["decisions"] or len(manifest) != summary["targets"]
                or len(theorem_names) != summary["theorems"]):
            raise ValueError(f"Unit summary differs from its manifest: {unit_id}")
        if set(theorem_names) != set(comparator["theorem_names"]) or len(theorem_names) != len(comparator["theorem_names"]):
            raise ValueError(f"Comparator target list differs: {unit_id}")
        if set(comparator["permitted_axioms"]) - STANDARD_AXIOMS:
            raise ValueError(f"Comparator permits extra axioms: {unit_id}")
        unit_counts[unit_id] = decisions
    works = []
    for work_id, entry in sorted(work_index.items()):
        rows = [row for row in targets if row["work_id"] == work_id]
        decisions = Counter(row["decision"] for row in rows)
        if len(rows) != entry["target_count"] or dict(decisions) != entry["decisions"]:
            raise ValueError(f"Work index differs from target manifests: {work_id}")
        target_map = load(root, f"SAP/Works/{work_id}/TARGET-MAP.json") if rows else []
        mapped = {row["target_id"]: row for row in target_map}
        if set(mapped) != {row["target_id"] for row in rows}:
            raise ValueError(f"Work target map has missing/extra targets: {work_id}")
        for row in rows:
            other = mapped[row["target_id"]]
            for key in ("decision", "theorem", "restriction", "unit_id"):
                if row[key] != other.get(key):
                    raise ValueError(f"Work target map differs for {row['target_id']}: {key}")
        works.append({"work_id": work_id, "title": entry["title"], "citation": entry["citation"],
                      "target_count": len(rows), "decisions": dict(sorted(decisions.items())),
                      "guide": f"docs/works/{work_id}.md", "unit_ids": entry["unit_ids"]})
    historical_targets = {row["id"] for path in (root / "catalog/works").glob("*.json")
                          for row in json.loads(path.read_bytes())["targets"]}
    if seen != historical_targets:
        raise ValueError("Current package target scope differs from the historical catalog")
    decisions = Counter(row["decision"] for row in targets)
    return {"schema_version": "1.0", "source_package": source_manifest["source_package"],
            "counts": {"targets": len(targets), "theorems": sum(row["theorem"] is not None for row in targets),
                       "formal_works": sum(bool(work["target_count"]) for work in works),
                       "units": len(unit_index), "decisions": dict(sorted(decisions.items()))},
            "works": works, "targets": sorted(targets, key=lambda row: (row["work_id"], int(row["target_id"].split("-T")[1])))}


def historical_notice(path):
    if path == "SAP/Works/BUILD.md":
        return ("> **Historical replay instructions.** These describe the original certification workflow and its external inputs. "
                "See [current verification commands](../../docs/VERIFICATION.md) and the "
                "[paper guides](../../docs/works/README.md).\n\n").encode()
    if path == "SAP/Works/README.md":
        guide = "[current paper guides](../../docs/works/README.md)"
        verification = "../../docs/VERIFICATION.md"
    elif re.fullmatch(r"SAP/Works/P\d{3}/README\.md", path):
        work = path.split("/")[2]
        guide = f"[current paper guide](../../../docs/works/{work}.md)"
        verification = "../../../docs/VERIFICATION.md"
    else:
        raise ValueError(f"Unsupported documentation overlay: {path}")
    return ("> **Historical packaging record.** Any pending states below describe that earlier stage. "
            f"See the {guide} and [verification]({verification}).\n\n").encode()


def check_packaging(root, manifest):
    """Allow only recorded operational exclusions and notice-only doc overlays."""
    operational = {"tools/sap/sap_pipeline.py", "tools/sap/run_pipeline.sh"}
    for field in ("excluded_files", "documentation_overlays"):
        for path, record in manifest.get(field, {}).items():
            safe_relative(path)
            if (set(record) != {"original_sha256", "reason"}
                    or not re.fullmatch(r"[0-9a-f]{64}", record["original_sha256"])
                    or not isinstance(record["reason"], str) or not record["reason"].strip()):
                raise ValueError(f"Invalid packaging record: {path}")
            if field == "excluded_files":
                if path not in operational or path in manifest["files"] or (root / path).exists() or (root / path).is_symlink():
                    raise ValueError(f"Invalid operational exclusion: {path}")
            else:
                if path not in manifest["files"]:
                    raise ValueError(f"Documentation overlay is not retained: {path}")
                prefix = historical_notice(path)
                content = (root / path).read_bytes()
                if not content.startswith(prefix) or digest(content[len(prefix):]) != record["original_sha256"]:
                    raise ValueError(f"Historical documentation body changed: {path}")


def check_sources(root):
    manifest = load(root, "package/source-manifest.json")
    check_packaging(root, manifest)
    for group in (manifest["files"], manifest["historical_catalog"]["files"]):
        for path, expected in group.items():
            p = root / safe_relative(path)
            if p.is_symlink() or not p.is_file() or digest(p.read_bytes()) != expected:
                raise ValueError(f"Imported source/evidence bytes changed: {path}")
    # Prevent unrecorded source additions from bypassing the imported package lock.
    for directory in ("AronowAudit", "SAP", "release-evidence", "tools", "catalog"):
        expected = {path for group in (manifest["files"], manifest["historical_catalog"]["files"])
                    for path in group if path.startswith(directory + "/")}
        actual = {p.relative_to(root).as_posix() for p in (root / directory).rglob("*")
                  if p.is_file() and "__pycache__" not in p.parts}
        if actual != expected:
            raise ValueError(f"Imported {directory} inventory changed: {sorted(actual ^ expected)}")


def check_proof_sources(root):
    imports = {}
    for directory in ("AronowAudit", "SAP"):
        for path in sorted((root / directory).rglob("*.lean")):
            relative = path.relative_to(root).as_posix()
            if path.is_symlink():
                raise ValueError(f"Source symlink: {relative}")
            clean = _mask_lean(path.read_text())
            tokens = set(re.findall(r"(?<![\w'«])(?:sorry|admit|axiom|native_decide|implemented_by|opaque)(?![\w'»])", clean))
            # The inherited library has unused statement stubs. Its exact bytes
            # are locked above; live per-theorem axiom checks reject reliance on
            # sorryAx. Importing a module is not the same as using each theorem.
            allowed = {"sorry"} if CHALLENGE.fullmatch(relative) or directory == "AronowAudit" else set()
            if tokens - allowed:
                raise ValueError(f"Forbidden proof token in {relative}: {sorted(tokens - allowed)}")
            if re.search(r"^\s*(?:(?:private|noncomputable|partial)\s+)*unsafe\s+(?:def|opaque|theorem|instance)\b", clean, re.M):
                raise ValueError(f"Unsafe declaration in {relative}")
            imports[relative] = [module for match in re.finditer(r"^\s*(?:public\s+)?import\s+([^\n]+)", clean, re.M)
                                 for module in match[1].split()]
    def closure(path, seen):
        if path in seen:
            return
        seen.add(path)
        for module in imports.get(path, []):
            dependency = module.replace(".", "/") + ".lean"
            if dependency in imports:
                closure(dependency, seen)
    for path in imports:
        if path.startswith("SAP/") and path.endswith("/Solution.lean"):
            dependencies = set()
            closure(path, dependencies)
            bad = sorted(p for p in dependencies if CHALLENGE.fullmatch(p))
            if bad:
                raise ValueError(f"Solution imports Challenge stubs: {path}: {bad}")
        if CHALLENGE.fullmatch(path):
            dependencies = set()
            closure(path, dependencies)
            bad = sorted(p for p in dependencies if p.startswith("AronowAudit/") or
                         (p.startswith("SAP/") and not (CHALLENGE.fullmatch(p) or "/Defs" in p)))
            if bad:
                raise ValueError(f"Challenge imports proof sources: {path}: {bad}")


def work_guide(index, work):
    rows = [row for row in index["targets"] if row["work_id"] == work["work_id"]]
    lines = [f"# {work['work_id']}: {work['title']}", "", work["citation"], ""]
    if not rows:
        return "\n".join(lines + ["This work has no formal targets in this archive.", ""])
    counts = "; ".join(f"{n} {label}" for label, n in work["decisions"].items())
    target_label = "target" if len(rows) == 1 else "targets"
    lines += [f"{len(rows)} {target_label}; recorded release outcomes: {counts}.", "", "The labels reproduce the certified release's classifications. A target may formalize a corrected statement, a counterexample, or a compound containing proof assertions. Current scope notes below qualify correspondence to the paper; a recorded whole label does not establish every positive assertion in the quoted passage. Challenge files contain intentional statement stubs; import the Solution for proofs.", "", "| Target | Recorded release outcome | Sources |", "| --- | --- | --- |"]
    def link(label, item):
        return f"[{label}](../../{item['path']}#L{item['line']})"
    for row in rows:
        if row["theorem"]:
            links = [link("Statement", row["challenge"]), link("Proof", row["solution"])]
            if row["definitions"]:
                links.append(link("Definitions", row["definitions"][0]))
        else:
            links = [f"[Explanation](../../{row['manifest']['path']})"]
        lines.append(f"| [{row['target_id']}](#{row['target_id'].lower()}) | {row['decision']} | {' · '.join(links)} |")
    disclosures = [row for row in rows if row["restriction"] or row["omission_reason"] or row["target_id"] in READER_NOTES]
    if disclosures:
        lines += ["", "## Scope and restrictions", ""]
        for row in rows:
            lines += [f"<a id=\"{row['target_id'].lower()}\"></a>"]
            disclosure = " ".join(note for note in (
                reader_disclosure(row["target_id"], row["restriction"] or row["omission_reason"]),
                READER_NOTES.get(row["target_id"])) if note)
            if disclosure:
                lines += [f"**{row['target_id']} ({row['decision']}).** {disclosure}", ""]
    else:
        lines += ["", *[f"<a id=\"{row['target_id'].lower()}\"></a>" for row in rows], ""]
    return "\n".join(lines).rstrip() + "\n"


def generated_files(index):
    output = {"package/current-results.json": encoded(index)}
    lines = ["# Formal results by work", "", "Each guide links to the exact formal statements, proofs and definitions, with restrictions and omissions.", "", "| Work | Title | Targets |", "| --- | --- | --- |"]
    for work in index["works"]:
        output[work["guide"]] = work_guide(index, work).encode()
        lines.append(f"| [{work['work_id']}]({work['work_id']}.md) | {work['title']} | {work['target_count']} |")
    output["docs/works/README.md"] = ("\n".join(lines) + "\n").encode()
    return output


def check_current(root, write=False):
    check_sources(root)
    check_proof_sources(root)
    index = build_index(root)
    for path, content in generated_files(index).items():
        target = root / path
        if write:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
        elif not target.is_file() or target.read_bytes() != content:
            raise ValueError(f"Generated file differs: {path}; run scripts/current_package.py --write")
    # Check reader guides and their actual declaration anchors. Original review
    # artifacts are retained records, not rewritten reader documentation.
    files = {p.relative_to(root).as_posix(): p.read_bytes() for p in root.rglob("*")
             if p.is_file() and not any(part in {".git", ".lake", "__pycache__"} for part in p.relative_to(root).parts)}
    for path in list(files):
        if path.endswith(".md") and path != "README.md" and not path.startswith("docs/"):
            files[path] = b""
    check_links(files)
    return index


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", nargs="?", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    try:
        index = check_current(args.root, args.write)
    except (ValueError, KeyError, OSError, UnicodeError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    counts = index["counts"]
    print(f"Checked {counts['targets']} targets, {counts['theorems']} statement/proof pairs, {counts['units']} units; source/evidence bytes preserved.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
