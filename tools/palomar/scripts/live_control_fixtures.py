"""Synthetic control inputs and exact stage checks; no production acceptance rules.

The inspector and logical comparison gates retain the reviewed delivered bytes;
v3 strengthens structural intake and writer boundaries. Negative controls must
fail at their intended guard after its required predecessors succeed. Any
earlier/unrelated error fails the control suite.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import sys

from work_package import Invalid, MARKERS, json_bytes, read_json, require, sha

from fixture_support import fixture, recertify

WORK_CASES = ("positive", "changed_target_type", "shared_defs_redefinition",
              "missing_solution_theorem", "namespace_collision", "admitted_solution")
UNITS = ("P900a", "P900b")
TARGETS = ("SAP.P900a.T1", "SAP.P900b.T2")
BUILD_STEPS = (
    "build-SAP.P900a.Defs", "build-SAP.P900a.Challenge", "build-SAP.P900a.Solution",
    "build-SAP.P900b.Defs", "build-SAP.P900b.Challenge", "build-SAP.P900b.Solution",
    "build-SAP.Works.P900.Defs", "build-SAP.Works.P900.Challenge", "build-SAP.Works.P900.Solution")
INSPECT_STEPS = ("inspect-challenge", "inspect-solution")
FINAL_STEPS = ("export-challenge", "export-solution", "comparator")
VERSION_STEPS = ("lean-version", "comparator-lean-version")


def make_work_fixture(root, case):
    require(case in WORK_CASES, f"unknown control: {case}")
    f = fixture(root)
    original_defs = {u: sha(f.source / "SAP" / u / "Defs.lean") for u in UNITS}
    if case == "changed_target_type":
        # Import the exact shared Defs and use its Statement on both conjuncts.
        # This changes the target type while preserving the project definition
        # closure inventory, so check_audits reaches its type/value equality loop.
        p = f.source / "SAP/P900a/Solution.lean"
        p.write_text("import SAP.P900a.Defs\nset_option autoImplicit false\n"
            "set_option relaxedAutoImplicit false\n"
            "theorem SAP.P900a.T1 : SAP.P900a.Statement ∧ SAP.P900a.Statement := by\n"
            "  exact ⟨True.intro, True.intro⟩\n")
        recertify(f.source, "P900a")
    elif case == "shared_defs_redefinition":
        # Preserve the old failing source mutation, but credit it only as a
        # namespace/import guard. It cannot reach definition comparison.
        p = f.source / "SAP/P900a/Solution.lean"
        p.write_text("import Mathlib\nset_option autoImplicit false\n"
            "set_option relaxedAutoImplicit false\n"
            "def SAP.P900a.Statement : Prop := True ∧ True\n"
            "theorem SAP.P900a.T1 : SAP.P900a.Statement := by\n"
            "  exact ⟨True.intro, True.intro⟩\n")
        recertify(f.source, "P900a")
    elif case == "missing_solution_theorem":
        p = f.source / "SAP/P900b/Solution.lean"
        p.write_text("\n".join(line for line in p.read_text().splitlines()
                                if not line.startswith("theorem ")) + "\n")
        recertify(f.source, "P900b")
    elif case == "namespace_collision":
        for i, u in enumerate(UNITS, 1):
            p = f.source / "SAP" / u / "Defs.lean"
            p.write_text(p.read_text() + f"\ndef WorkControlCollision : Nat := {i}\n")
            recertify(f.source, u)
    elif case == "admitted_solution":
        p = f.source / "SAP/P900a/Solution.lean"
        p.write_text(p.read_text().replace("exact True.intro", "sorry"))
        recertify(f.source, "P900a")
    if case != "namespace_collision":
        require(all(sha(f.source / "SAP" / u / "Defs.lean") == original_defs[u] for u in UNITS),
                f"{case}: shared Defs unexpectedly changed")
    return f


def step_index(record):
    steps = record.get("steps", [])
    names = [s.get("step") for s in steps]
    require(len(names) == len(set(names)), "duplicate execution stage")
    return {s["step"]: s for s in steps}


def exact_steps(record, names, failing=None):
    steps = step_index(record)
    require([s["step"] for s in record["steps"]] == list(names), "execution stage order/inventory mismatch")
    for name in names:
        if name == failing:
            require(type(steps[name].get("rc")) is int and steps[name]["rc"] != 0,
                    f"{name}: expected a nonzero exit")
        else:
            require(type(steps[name].get("rc")) is int and steps[name]["rc"] == 0, f"required predecessor did not succeed: {name}")
    return steps


def audit_rows(out, side):
    p = out / (side + "-inspection.jsonl")
    require(p.is_file(), f"missing live {side} inspection")
    import json
    rows = [json.loads(line) for line in p.read_text().splitlines() if line.strip()]
    require(rows and rows[0].get("record") == "inventory", "missing live inspection inventory header")
    return rows


def role_index(rows, role):
    selected = [r for r in rows[1:] if r.get("role") == role]
    require(len(selected) == len({r.get("name") for r in selected}), f"duplicate {role} row")
    return {r["name"]: r for r in selected}


def credit_work_replay(case, out, process_rc):
    """Strictly credit the intended stage; never accepts an arbitrary nonzero exit."""
    require(case in WORK_CASES and case != "admitted_solution", "not a replay control")
    record = read_json(out / "comparator-result.json")
    require(record.get("source_kind") == "baseline_fixture" and
            record.get("scope") == "ordinary_work_comparator_base_reused", "unexpected replay scope")
    require(record.get("work_id") == "P900", "unexpected fixture work")
    if case == "positive":
        exact_steps(record, VERSION_STEPS + BUILD_STEPS + INSPECT_STEPS + FINAL_STEPS)
        require(type(process_rc) is int and process_rc == 0 and record.get("accepted") is True and not record.get("failure"),
                "positive live fixture failed; no negative control is credited")
        require(set(record.get("markers", {})) == set(MARKERS) and
                all(v is True for v in record["markers"].values()), "positive fixture missing kernel markers")
        log = out / "logs/comparator.log"
        require(all(m in log.read_text() for m in MARKERS), "positive Comparator log missing markers")
        require(sha(log) == step_index(record)["comparator"].get("log_sha256"), "positive log hash drift")
        stage = "real_fixture_comparator_acceptance"
    else:
        require(type(process_rc) is int and process_rc != 0 and record.get("accepted") is False, "negative fixture was accepted")
        require(not record.get("inspection") and not record.get("markers"), "unexpected late-stage acceptance metadata")
        if case in ("changed_target_type", "missing_solution_theorem"):
            exact_steps(record, VERSION_STEPS + BUILD_STEPS + INSPECT_STEPS)
            ch, so = audit_rows(out, "challenge"), audit_rows(out, "solution")
            require(sorted(ch[0]["challenge_theorems"]) == sorted(TARGETS) and
                    not so[0]["challenge_theorems"], "wrong live Challenge inventory")
            ce, se = role_index(ch, "expected"), role_index(so, "expected")
            require(set(ce) == set(se) == set(TARGETS), "unexpected inspection target inventory")
            if case == "changed_target_type":
                require(record.get("failure") == "statement/definition mismatch: SAP.P900a.T1",
                        "changed target did not reach the exact target-type comparison")
                require(all(not r.get("error") for r in ch[1:] + so[1:]), "inspection had an earlier missing declaration")
                require(ce[TARGETS[0]]["canonical_type"] != se[TARGETS[0]]["canonical_type"],
                        "the intended target type did not change")
                require(ce[TARGETS[1]]["canonical_type"] == se[TARGETS[1]]["canonical_type"],
                        "unrelated target type changed")
                cs, ss = role_index(ch, "statement"), role_index(so, "statement")
                fields = ("kind", "universe_count", "canonical_type", "canonical_value", "constructors")
                require(set(cs) == set(ss) == {"SAP.P900a.Statement", "SAP.P900b.Statement"},
                        "shared definition closure inventory changed")
                require(all(all(cs[n][k] == ss[n][k] for k in fields) for n in cs),
                        "shared definition bodies changed")
                stage = "inspector_target_type_comparison"
            else:
                require(record.get("failure") == "Lean expected missing declaration", "wrong missing-Solution guard")
                require(not ce[TARGETS[1]].get("error") and se[TARGETS[1]].get("error") == "missing" and
                        not se[TARGETS[0]].get("error"), "wrong missing Solution declaration")
                stage = "inspector_missing_solution_declaration"
        else:
            failing = "build-SAP.Works.P900.Solution" if case == "shared_defs_redefinition" else "build-SAP.Works.P900.Defs"
            prefix = BUILD_STEPS[:BUILD_STEPS.index(failing) + 1]
            exact_steps(record, VERSION_STEPS + prefix, failing=failing)
            require(record.get("failure", "").startswith(failing + " failed; see "), "wrong compile failure stage")
            log = out / "logs" / (failing + ".log")
            text = log.read_text()
            expected = ("import SAP.P900a.Solution failed", "environment already contains 'SAP.P900a.Statement'", "from SAP.P900a.Defs") \
                if case == "shared_defs_redefinition" else \
                ("import SAP.P900b.Defs failed", "environment already contains 'WorkControlCollision'", "from SAP.P900a.Defs")
            require(all(token in text for token in expected), "compile error was not the intended namespace collision")
            require(sha(log) == step_index(record)[failing].get("log_sha256"), "collision log hash drift")
            stage = "shared_defs_redefinition_import_guard" if case == "shared_defs_redefinition" else "cross_unit_namespace_collision"
    return {"case": case, "passed": True, "stage": stage,
            "replay_record_sha256": sha(out / "comparator-result.json"),
            "scope": "synthetic_inputs_real_fixture_execution_only",
            "comparator_invoked": case == "positive",
            "comparator_definition_rejection_exercised": False}


def credit_admitted_generation(returncode, stderr, entries):
    require(type(returncode) is int and returncode != 0 and stderr.strip() == "INVALID: sorry outside unit Challenge: SAP.P900a.Solution",
            "admitted Solution did not fail at the exact source token guard")
    require(not entries.exists(), "failed admitted-Solution generation left an entry directory")
    return {"case": "admitted_solution", "passed": True, "stage": "source_token_guard",
            "comparator_invoked": False, "comparator_definition_rejection_exercised": False}
