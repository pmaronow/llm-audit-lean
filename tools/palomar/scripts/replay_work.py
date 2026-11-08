#!/usr/bin/env python3
"""Explicit, isolated ordinary work Comparator replay; never run by the generator.

Rebuilds SAP from the copied sources, reuses the explicit base artifacts, and records
a NEW result only in --out. This is not the full A3 dependency rebuild or a review.
The adapter and Lean inspector require independent review and live controls.
"""
import sys
if __name__ == "__main__":
    raise SystemExit("Use python3 -I -S -B /absolute/palomar.py replay ...; direct backend startup is unsupported")
sys.dont_write_bytecode = True
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from generate_work_packages import arguments
from validate_work_packages import validate
from boundaries import guard_paths, inputs_for, plan_outputs
from work_package import (AXIOMS, EXTERNAL_ROOTS, MARKERS, Invalid, canonical, digest, imports,
                          in_module, json_bytes, read_json, require, sha)


from _palomar_installation import entry as _entry, entry_sha256 as _entry_sha256

def order_modules(modules):
    seen, active, result = set(), set(), []
    def visit(m):
        require(m not in active, f"build import cycle: {m}")
        if m in seen:
            return
        active.add(m)
        for dep in imports(modules[m].read_text()):
            if dep in modules:
                visit(dep)
            else:
                require(not dep.startswith("SAP."), f"SAP fallback forbidden: {dep}")
        active.remove(m); seen.add(m); result.append(m)
    for m in sorted(modules):
        visit(m)
    return result


def check_audits(challenge, solution, cfg, units, work, provenance):
    require(challenge and solution, "empty Lean inspection output")
    ci, si = challenge[0], solution[0]
    expected_modules = {p[:-5].replace("/", ".") for u in units
                        for p in provenance["units"][u]["source_sha256"]
                        if in_module(p[:-5].replace("/", "."), f"SAP.{u}.Challenge")}
    expected_modules.add(cfg["challenge_module"])
    require(set(ci["challenge_modules"]) == expected_modules, "Lean Challenge module inventory mismatch")
    require(sorted(ci["challenge_theorems"]) == sorted(cfg["theorem_names"]), "Lean Challenge theorem inventory mismatch")
    require(not si["challenge_modules"] and not si["challenge_theorems"], "Solution loaded a Challenge module")
    for side, inv in (("challenge", ci), ("solution", si)):
        for mod in inv["imports"]:
            if side == "challenge":
                allowed = mod.split(".")[0] in EXTERNAL_ROOTS or any(
                    in_module(mod, f"SAP.{u}.{part}") for u in units for part in ("Defs", "Challenge"))
                allowed |= any(in_module(mod, f"SAP.Works.{work}.{part}") for part in ("Defs", "Challenge"))
                require(allowed, f"Lean Challenge import leakage: {mod}")
            else:
                require(not re.match(r"^SAP\.(?:Works\.[^.]+|[^.]+)\.(Challenge|Orig)(?:\.|$)", mod),
                        f"Lean Solution imported a stub: {mod}")
                if mod.startswith("SAP."):
                    require(any(in_module(mod, f"SAP.{u}") for u in units) or in_module(mod, f"SAP.Works.{work}"),
                            f"Lean Solution cross-work import: {mod}")
    def rows_by_role(rows, role):
        rows = [r for r in rows[1:] if r.get("role") == role]
        require(all(not r.get("error") for r in rows), f"Lean {role} missing declaration")
        require(len(rows) == len({r["name"] for r in rows}), f"duplicate Lean {role} result")
        return {r["name"]: r for r in rows}
    expected_ch, expected_so = rows_by_role(challenge, "expected"), rows_by_role(solution, "expected")
    require(set(expected_ch) == set(expected_so) == set(cfg["theorem_names"]), "Lean expected name inventory mismatch")
    statement_ch, statement_so = rows_by_role(challenge, "statement"), rows_by_role(solution, "statement")
    require(set(statement_ch) == set(statement_so), "project statement definition closure inventory mismatch")
    fields = ("kind", "universe_count", "canonical_type", "canonical_value", "constructors")
    for left, right in ((expected_ch, expected_so), (statement_ch, statement_so)):
        for name in left:
            require(all(left[name][k] == right[name][k] for k in fields), f"statement/definition mismatch: {name}")
    require(all(r["kind"] == "theorem" for r in expected_so.values()), "target is not a theorem")
    used = rows_by_role(solution, "used")
    require(set(cfg["theorem_names"]) <= set(used), "used-closure omitted a target")
    for r in [*expected_so.values(), *statement_so.values(), *used.values()]:
        require(set(r["axioms"]) <= AXIOMS, f"nonstandard axioms for {r['name']}: {r['axioms']}")
    return {"target_count": len(expected_so), "statement_project_declarations": len(statement_so),
            "used_project_declarations": len(used), "per_target_axioms": {n:r["axioms"] for n,r in expected_so.items()},
            "canonical_equality": "passed", "namespace_composition": "Lean_imports_and_exact_inventory_passed"}


def main():
    parser = arguments()
    parser.add_argument("--entries", type=Path, required=True)
    parser.add_argument("--work", required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--comparator-lake", type=Path, required=True)
    parser.add_argument("--primitive-check-file", type=Path, required=True)
    parser.add_argument("--exporter", type=Path, required=True)
    parser.add_argument("--lean-path-file", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--allow-baseline-fixture", action="store_true")
    args = parser.parse_args()
    args.out = plan_outputs({"out":args.out}, args,code_root=Path(__file__).resolve())["out"]
    require(args.kind != "baseline_fixture" or args.allow_baseline_fixture,
            "baseline_fixture replay requires --allow-baseline-fixture; it cannot certify current sources")
    preflight = validate(args)
    require(not args.out.exists(), "replay output must be a fresh directory")
    out = args.out.resolve()
    for root in (args.source, args.entries, args.base_source):
        if root:
            root = root.resolve()
            require(root != out and root not in out.parents, "replay output must be outside read-only input trees")
    work_entry = args.entries / "SAP/Works" / args.work
    require((work_entry / "comparator.json").is_file(), "work has no applicable Comparator target set")
    cfg = read_json(work_entry / "comparator.json")
    provenance = read_json(work_entry / "PROVENANCE.json")
    units = sorted(provenance["units"])
    for path in (args.lean, args.comparator_lake, args.exporter, args.primitive_check_file, args.lean_path_file):
        require(path.is_file(), f"missing replay tool/input: {path}")
    out.mkdir(parents=True)
    record = {"schema": "palomar-work-comparator-v1", "work_id": args.work, "source_kind": args.kind,
              "scope": "ordinary_work_comparator_base_reused", "accepted": False,
              "a3_dependency_replay": False, "semantic_review": False,
              "adapter_independent_review": "required_before_release_reliance", "steps": []}
    def save():
        (out / "comparator-result.json").write_bytes(json_bytes(record))
    save()
    try:
        work, logs = out / "work", out / "logs"
        logs.mkdir(); work.mkdir()
        paths = {}
        for unit in units:
            u = provenance["units"][unit]
            paths.update(u["source_sha256"])
            paths.update(u["review"]["files_sha256"])
            paths[f"SAP/{unit}/manifest.json"] = u["manifest_sha256"]
            paths[f"SAP/{unit}/comparator.json"] = u["comparator_sha256"]
        for rel, h in paths.items():
            src = args.source / rel
            require(sha(src) == h, f"input drift during snapshot: {rel}")
            dest = work / rel; dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(src.read_bytes())
            require(sha(dest) == h, f"snapshot copy mismatch: {rel}")
        for src in sorted(work_entry.iterdir()):
            if src.is_file():
                dest = work / "SAP/Works" / args.work / src.name
                dest.parent.mkdir(parents=True, exist_ok=True); dest.write_bytes(src.read_bytes())
        frozen = {str(p.relative_to(work)):sha(p) for p in sorted(work.rglob("*")) if p.is_file()}
        record.update({"snapshot_sha256": frozen, "preflight": preflight, "base_source_sha256": provenance["base_source_sha256"],
                       "input_tools_sha256": {str(p.resolve()): sha(p) for p in
                         (args.lean, args.comparator_lake, args.exporter, args.primitive_check_file, args.lean_path_file)}})
        lp = args.lean_path_file.read_text().strip()
        require(lp and "\n" not in lp, "LEAN_PATH must be a nonempty single line")
        build = work / ".lake/build/lib/lean"
        env = {**os.environ, "LEAN_PATH": str(build) + os.pathsep + lp, "LEAN_NUM_THREADS": "2",
               "LEAN_SYSROOT": str(args.lean.resolve().parent.parent),
               "PATH": str(args.lean.resolve().parent) + os.pathsep + os.environ.get("PATH", "")}
        def run(label, command, *, cwd=work, environment=env, stdout_path=None):
            start = time.monotonic()
            if stdout_path:
                with stdout_path.open("wb") as stream:
                    proc = subprocess.run(command, cwd=cwd, env=environment, stdout=stream, stderr=subprocess.PIPE)
                output = proc.stderr.decode(errors="replace")
            else:
                proc = subprocess.run(command, cwd=cwd, env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                output = proc.stdout.decode(errors="replace")
            log = logs / (label + ".log"); log.write_text(output)
            record["steps"].append({"step": label, "argv": [str(x) for x in command], "rc": proc.returncode,
                                    "seconds": round(time.monotonic()-start, 3), "log_sha256": sha(log)})
            save(); require(proc.returncode == 0, f"{label} failed; see {log}")
            return output
        version = run("lean-version", [str(args.lean.resolve()), "--version"])
        require(re.search(r"\b4\.34\.1\b", version), "expected Lean 4.34.1")
        cmp_lean = args.comparator_lake.resolve().parent / "lean"
        require(cmp_lean.is_file(), "missing Comparator's Lean executable")
        record["input_tools_sha256"][str(cmp_lean)] = sha(cmp_lean)
        cmp_version = run("comparator-lean-version", [str(cmp_lean), "--version"])
        require("4.35.0-rc2" in cmp_version, "expected Comparator Lean 4.35.0-rc2")
        modules = {str(p.relative_to(work))[:-5].replace("/", "."):p
                   for p in (work / "SAP").rglob("*.lean") if "review" not in p.parts and "verification" not in p.parts}
        for mod in order_modules(modules):
            dest = build / (mod.replace(".", "/") + ".olean")
            dest.parent.mkdir(parents=True, exist_ok=True)
            output = run("build-" + mod, [str(args.lean.resolve()), "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                                        str(modules[mod].relative_to(work)), "-o", str(dest)])
            require("declaration uses 'sorry'" not in output or any(in_module(mod, f"SAP.{u}.Challenge") for u in units),
                    f"compiled sorry outside Challenge: {mod}")
        template = Path(__file__).resolve().parent / "WorkAudit.lean.tmpl"
        if not template.is_file():
            template = Path(__file__).resolve().parent.parent / "lean/WorkAudit.lean.tmpl"
        record["inspector_template_sha256"] = sha(template)
        inspected = {}
        for side in ("challenge", "solution"):
            dest = out / (side + "-inspection.jsonl")
            text = template.read_text().replace("<IMPORT>", cfg[side + "_module"])
            names = "#[" + ", ".join("`" + n for n in cfg["theorem_names"]) + "]"
            prefixes = "#[" + ", ".join("`" + n for n in [f"SAP.{u}.Challenge" for u in units] + [cfg["challenge_module"]]) + "]"
            for placeholder, value in {"<NAMES>":names, "<TARGETS>":names, "<CHALLENGE_PREFIXES>":prefixes,
                    "<AUDIT_USED>":"true" if side == "solution" else "false", "<OUTPUT>":json.dumps(str(dest))}.items():
                text = text.replace(placeholder, value)
            scr = work / f"{side}-Inspect.lean"; scr.write_text(text)
            run("inspect-" + side, [str(args.lean.resolve()), "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", str(scr)])
            require(dest.is_file(), f"missing {side} inspection output")
            inspected[side] = [json.loads(l) for l in dest.read_text().splitlines() if l.strip()]
        record["inspection"] = check_audits(inspected["challenge"], inspected["solution"], cfg, units, args.work, provenance)
        record["inspection_sha256"] = {s:sha(out / (s + "-inspection.jsonl")) for s in inspected}
        primitive_source = args.primitive_check_file.read_text()
        require("def primitiveTargets" in primitive_source and "def builtinTargets" in primitive_source,
                "pinned primitive target list not found")
        primitive = primitive_source.split("def primitiveTargets", 1)[1].split("def builtinTargets", 1)[0]
        primitive = re.sub(r"--[^\n]*", "", primitive)
        primitives = re.findall(r"``([A-Za-z0-9_.]+)", primitive)
        require(primitives, "empty primitive target inventory")
        targets = list(dict.fromkeys(cfg["theorem_names"] + primitives +
                                    ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] + sorted(AXIOMS)))
        record["export_targets"] = targets
        for side in ("challenge", "solution"):
            export = out / (side + ".ndjson")
            run("export-" + side, [str(args.exporter.resolve()), cfg[side + "_module"], "--", *targets], stdout_path=export)
            require(export.stat().st_size > 0, f"empty {side} export")
        cmp_env = {**os.environ, "PATH": str(args.comparator_lake.resolve().parent) + os.pathsep + os.environ.get("PATH", "")}
        for binary in ("con-ron", "nanoda_bin"):
            resolved = shutil.which(binary, path=cmp_env["PATH"])
            require(resolved, f"external kernel absent from explicit execution PATH: {binary}")
            record["input_tools_sha256"][str(Path(resolved).resolve())] = sha(Path(resolved).resolve())
        cmp_cwd = out / "comparator"; cmp_cwd.mkdir()
        output = run("comparator", [str(args.comparator_lake.resolve()), "comparator", "--config",
            str(work / "SAP/Works" / args.work / "comparator.json"), "--challenge-from-export", str(out / "challenge.ndjson"),
            "--solution-from-export", str(out / "solution.ndjson")], cwd=cmp_cwd, environment=cmp_env)
        record["markers"] = {m:m in output for m in MARKERS}
        require(all(record["markers"].values()), "Comparator missing acceptance marker")
        record["exports_sha256"] = {s:sha(out / (s + ".ndjson")) for s in ("challenge", "solution")}
        record["olean_sha256"] = {str(p.relative_to(build)):sha(p) for p in sorted(build.rglob("*.olean"))}
        require(validate(args)["managed_content_sha256"] == preflight["managed_content_sha256"], "source/entry drift after build")
        require(all(sha(work / rel) == h for rel,h in frozen.items()), "snapshot changed during replay")
        require(all(sha(p) == h for p,h in record["input_tools_sha256"].items()), "tool/dependency-path input drift")
        record["accepted"] = True
        record["stamp"] = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
        save()
        print(canonical({"work_id": args.work, "accepted": True, "source_kind": args.kind,
                         "scope": record["scope"], "certificate": str(out / "comparator-result.json")}))
    except Exception as exc:
        record["failure"] = str(exc); save(); raise


if __name__ == "__main__":
    try:
        main()
    except (Invalid, OSError, KeyError, TypeError, ValueError) as exc:
        print(f"INVALID: {exc}", file=sys.stderr)
        sys.exit(1)
