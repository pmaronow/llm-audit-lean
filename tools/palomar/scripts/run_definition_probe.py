#!/usr/bin/env python3
"""Isolated LIVE inspector probe, deliberately outside the shared-Defs work layout.

Two separately imported environments can contain the same definition name with
different bodies. Neither root imports work Defs. This is NOT a valid composed
work package, a normal replay, a Comparator check, or a certificate. It exercises
only the unchanged inspector + check_audits type/definition comparison boundary.
"""
import sys
if __name__ == "__main__":
    raise SystemExit("Use python3 -I -S -B /absolute/palomar.py definition-probe ...; direct backend startup is unsupported")
sys.dont_write_bytecode = True
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from live_control_fixtures import role_index
from replay_work import check_audits, order_modules
from work_package import Invalid, config, json_bytes, require, sha
from boundaries import guard_paths, plan_outputs
from types import SimpleNamespace

PROBE_NAME = "SAP.P900a.ProbeValue"
TARGET_NAME = "SAP.P900a.T1"
VARIANTS = ("equal_definitions", "different_definitions")
# All non-value semantic fields emitted by this inspector for a definition.
# name/role are fixed by the exact inventories below. module and the raw
# type/value repr strings are origin/diagnostic fields; canonical encodings
# carry expression semantics. Keep level parameters and axiom metadata exact
# as well, so these tiny controls isolate only canonical_value.
DEFINITION_NON_VALUE_FIELDS = ("kind", "universe_count", "canonical_type", "constructors", "level_params", "axioms")


def probe_sources(variant):
    require(variant in VARIANTS, f"unknown isolated probe variant: {variant}")
    files = {}
    for side in ("Challenge", "Solution"):
        value = 2 if variant == "different_definitions" and side == "Solution" else 1
        files[f"SAP/P900a/{side}.lean"] = (
            "import Lean\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n"
            f"def {PROBE_NAME} : Nat := {value}\n"
            f"theorem {TARGET_NAME} : {PROBE_NAME} = {PROBE_NAME} := by rfl\n")
        files[f"SAP/Works/P900/{side}.lean"] = f"import SAP.P900a.{side}\n"
    return files


def compare_probe(challenge, solution, cfg, provenance, variant):
    """Credit value comparison only after every non-value semantic field agrees."""
    require(variant in VARIANTS, f"unknown isolated probe variant: {variant}")
    ce, se = role_index(challenge, "expected"), role_index(solution, "expected")
    cs, ss = role_index(challenge, "statement"), role_index(solution, "statement")
    require(set(ce) == set(se) == {TARGET_NAME}, "isolated probe target inventory mismatch")
    require(set(cs) == set(ss) == {PROBE_NAME}, "isolated probe definition inventory mismatch")
    require(all(not r.get("error") for r in challenge[1:] + solution[1:]), "probe inspection missing a declaration")
    require(ce[TARGET_NAME]["canonical_type"] == se[TARGET_NAME]["canonical_type"],
            "probe changed the target type instead of only a definition body")
    require(cs[PROBE_NAME]["kind"] == ss[PROBE_NAME]["kind"] == "definition", "probe constant is not a definition")
    for field in DEFINITION_NON_VALUE_FIELDS:
        require(field in cs[PROBE_NAME] and field in ss[PROBE_NAME],
                "probe missing definition non-value semantic field: " + field)
        require(cs[PROBE_NAME][field] == ss[PROBE_NAME][field],
                "probe changed definition non-value semantic field: " + field + "; value branch not credited")
    same = cs[PROBE_NAME]["canonical_value"] == ss[PROBE_NAME]["canonical_value"]
    require(same == (variant == "equal_definitions"), "probe definition bodies do not have the intended relation")
    error, checked = None, None
    try:
        checked = check_audits(challenge, solution, cfg, ["P900a"], "P900", provenance)
    except Invalid as exc:
        error = str(exc)
    if variant == "different_definitions":
        require(error == "statement/definition mismatch: " + PROBE_NAME,
                f"isolated definition probe failed for an unrelated reason: {error}")
    else:
        require(error is None and checked["canonical_equality"] == "passed", f"positive definition probe failed: {error}")
    return {"passed": True, "stage": "inspector_definition_value_comparison",
            "canonical_target_types_equal": True, "canonical_definition_values_equal": same,
            "definition_non_value_fields_equal": True,
            "definition_non_value_fields_checked": list(DEFINITION_NON_VALUE_FIELDS),
            "comparison_failure": error, "positive_inspection": checked,
            "comparator_invoked": False, "comparator_definition_rejection_exercised": False,
            "ordinary_work_replay": False, "valid_compositional_package": False}


def run_probe(out, lean, lean_path_file, variant, read_only_roots=()):
    context=SimpleNamespace(lean=lean,lean_path_file=lean_path_file,read_only_root=list(read_only_roots))
    out=plan_outputs({"out":out},context,code_root=Path(__file__).resolve())["out"]
    lean, lean_path_file = lean.resolve(), lean_path_file.resolve()
    require(not out.exists(), "isolated probe output must be fresh")
    require(lean.is_file() and lean_path_file.is_file(), "missing isolated probe tool/input")
    files = probe_sources(variant)
    out.mkdir(parents=True)
    work, logs = out / "work", out / "logs"
    work.mkdir(); logs.mkdir()
    record = {"schema": "palomar-isolated-definition-probe-v1", "variant": variant, "passed": False,
              "scope": "isolated_inspector_boundary_only", "comparator_invoked": False,
              "comparator_definition_rejection_exercised": False, "ordinary_work_replay": False,
              "valid_compositional_package": False, "certifies_any_real_work": False, "a3_replay": False, "steps": []}
    def save():
        (out / "probe-result.json").write_bytes(json_bytes(record))
    save()
    try:
        for rel, text in files.items():
            p = work / rel; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
        source_hashes = {rel: sha(work / rel) for rel in files}
        template = Path(__file__).resolve().parent / "WorkAudit.lean.tmpl"
        tool_hashes = {str(p): sha(p) for p in (lean, lean_path_file, template)}
        lp = lean_path_file.read_text().strip()
        require(lp and "\n" not in lp, "invalid explicit LEAN_PATH")
        build = work / ".lake/build/lib/lean"
        env = {**os.environ, "LEAN_PATH": str(build) + os.pathsep + lp, "LEAN_NUM_THREADS": "2",
               "LEAN_SYSROOT": str(lean.parent.parent),
               "PATH": str(lean.parent) + os.pathsep + os.environ.get("PATH", "")}
        def run(label, argv):
            p = subprocess.run(argv, cwd=work, env=env, capture_output=True, text=True)
            log = logs / (label + ".log"); log.write_text(p.stdout + p.stderr)
            record["steps"].append({"step": label, "argv": [str(x) for x in argv], "rc": p.returncode, "log_sha256": sha(log)})
            save()
            require(p.returncode == 0, f"isolated probe {label} failed before comparison; see {log}")
            require("declaration uses 'sorry'" not in p.stdout + p.stderr, "probe unexpectedly uses a stub")
            return p.stdout + p.stderr
        version = run("lean-version", [str(lean), "--version"])
        require(re.search(r"\b4\.34\.1\b", version), "expected Lean 4.34.1")
        modules = {rel[:-5].replace("/", "."): work / rel for rel in files}
        for mod in order_modules(modules):
            target = build / (mod.replace(".", "/") + ".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            run("build-" + mod, [str(lean), "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                                str(modules[mod].relative_to(work)), "-o", str(target)])
        cfg = config("SAP.Works.P900.Challenge", "SAP.Works.P900.Solution", [TARGET_NAME])
        rows = {}
        for side in ("challenge", "solution"):
            output = out / (side + "-inspection.jsonl")
            replacements = {"<IMPORT>": cfg[side + "_module"], "<NAMES>": "#[`" + TARGET_NAME + "]",
                "<TARGETS>": "#[`" + TARGET_NAME + "]",
                "<CHALLENGE_PREFIXES>": "#[`SAP.P900a.Challenge, `SAP.Works.P900.Challenge]",
                "<AUDIT_USED>": "true" if side == "solution" else "false", "<OUTPUT>": json.dumps(str(output))}
            text = template.read_text()
            for placeholder, value in replacements.items():
                text = text.replace(placeholder, value)
            script = work / (side + "-Inspect.lean"); script.write_text(text)
            run("inspect-" + side, [str(lean), "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", str(script)])
            require(output.is_file(), "probe inspector did not write output")
            rows[side] = [json.loads(line) for line in output.read_text().splitlines() if line.strip()]
        provenance = {"units": {"P900a": {"source_sha256": {p: h for p, h in source_hashes.items() if p.startswith("SAP/P900a/")}}}}
        record.update(compare_probe(rows["challenge"], rows["solution"], cfg, provenance, variant))
        require(all(sha(work / rel) == h for rel, h in source_hashes.items()), "probe source drift")
        require(all(sha(p) == h for p, h in tool_hashes.items()), "probe input/tool drift")
        record.update({"source_sha256": source_hashes, "tool_sha256": tool_hashes,
                       "inspection_sha256": {side: sha(out / (side + "-inspection.jsonl")) for side in rows},
                       "olean_sha256": {str(p.relative_to(build)): sha(p) for p in sorted(build.rglob("*.olean"))}})
        save()
        return record
    except Exception as exc:
        record.update(passed=False, failure=str(exc)); save(); raise


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for flag in ("lean", "lean-path-file", "out"):
        p.add_argument("--" + flag, type=Path, required=True)
    p.add_argument("--variant", choices=VARIANTS, required=True)
    p.add_argument("--read-only-root",type=Path,action="append",default=[])
    args = p.parse_args()
    print(json_bytes(run_probe(args.out, args.lean, args.lean_path_file, args.variant,args.read_only_root)).decode())


if __name__ == "__main__":
    try:
        main()
    except (Invalid, OSError, KeyError, TypeError) as exc:
        print(f"INVALID: {exc}", file=sys.stderr); sys.exit(1)
