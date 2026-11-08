"""Bounded local documentary joins; never imports or runs reviewed producers."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
A = REPO / "reports/A3-2026-11-05"
refs = {}
checks = []


def read(name, relative, expected=None):
    path = REPO / relative
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if expected is not None and digest != expected:
        raise ValueError(f"Changed documentary input: {name}")
    refs[name] = {"path": str(path), "sha256": digest, "bytes": len(data)}
    return json.loads(data)


def check(name, condition):
    if not condition:
        raise ValueError(name)
    checks.append(name)


def a(name, relative, expected=None):
    return read(name, "reports/A3-2026-11-05/" + relative, expected)


index = a("unit_index", "parent-a3-unit-terminal-execution-001/assembly-export-001/metadata/DISPATCH-INDEX.json",
          "6d785d2a654e9de7331c4b9a01b54942d56b9d186d3d3445db1891c01227c8be")
op = a("unit_operational_validation", "parent-a3-unit-terminal-execution-001/assembly-export-001/metadata/OPERATIONAL-VALIDATION.json")
native = a("unit_index_native_binding", "parent-a3-unit-terminal-execution-001/assembly-export-001/metadata/CONTROLLER-NATIVE.json",
           "4d5974cbcd694a029dea66e084a536a9b00cc0d66bbfdbd86d1e38321298f27d")
capture = a("previously_reviewed_unit_capture", "parent-a3-unit-terminal-execution-001/capture-export-001/metadata/CAPTURE.json",
            "ad5bea0c95aad4e4912d27117337421aa45944094d2ccfb10ddd3dd972a3efa5")
prior_review = a("reused_unit_native_capture_review", "a3-unit-native-actual-provenance-review-001/REVIEW.json",
                 "8bc99b75d36cc0c93137a64ac5aaebcf1019ec6f62ec8ae63086eb23039aa1bf")
plan = a("unit_plan", "parent-a3-unit-continuation-bindings-001/actual/PLAN.json",
         "f23108e7cbb6ff90a169764f1f373d9d4fe4d57306f844f091dc7c41bdfb5907")
selection = a("combined_selection", "parent-a3-unit-terminal-execution-001/selection-export-001/metadata/READONLY-SELECTION.json",
              "ec6a3a7c5d81ad0c66ce8d31cb998fae1198811b35dc2dc026690f83dda83777")
aggregate = a("accepted_work_aggregate", "parent-a3-work-terminal-execution-002/aggregate-export-002/metadata/WORK-AGGREGATE.json",
              "2584aa6413774e398df632970aa75faacd6cc111853e18589a7548da20ca5547")
assembly_intake = a("unit_assembly_parent_intake", "parent-a3-unit-terminal-execution-001/assembly-export-001/PARENT-INTAKE.json")
selection_intake = a("combined_selection_parent_intake", "parent-a3-unit-terminal-execution-001/selection-export-001/PARENT-INTAKE.json")
producer_review = a("reused_producer_v2_code_review", "a3-work-continuation-membership-independent-v2/REVIEW.json",
                    "c9fbbd5cbaca9e9ca2a9df83a9b380ce64cefdc268c326307f40edbf8895c11c")
consumer_review = a("external_consumer_code_review", "a3-work-continuation-consumers-independent-001/REVIEW.json",
                    "491006681f4a614619544c347942fe7019a37fe09b1458f76ec2f2562a786f25")
scan_review = a("reused_scan_boundary_review", "a3-work-continuation-scan-boundary-review-001/REVIEW.json",
                "3da8f3377f7b3f980854c6fd20b25d28b6e4e6bf9a84825bfe149ff9582603b8")
wrapup = read("adopted_A2_documentary_wrapup", "reports/A2-ledger-2026-11-05/final-wrapup/WRAPUP.json",
              "55cceb68a2eb2ff9f17f806d0f59af25d05abc595984b8c32e09cec942c490c0")

ids = {job["work"] for job in plan["jobs"]}
check("unit81_unique_plan_members", len(ids) == len(plan["jobs"]) == 81)
for key in ("assignments", "run_receipts", "result_receipts"):
    check(f"unit_index_{key}_equal_previously_reviewed_capture", index[key] == capture[key] and set(index[key]) == ids)
for key in ("phase_plan", "terminal_observation", "events", "parent_result"):
    check(f"unit_index_{key}_equal_previously_reviewed_capture", index[key] == capture[key])
check("unit_index_native_ref", index["controller_native"]["sha256"] == refs["unit_index_native_binding"]["sha256"])
check("unit_index_plan_ref", index["phase_plan"]["sha256"] == refs["unit_plan"]["sha256"] == op["plan_sha256"])
check("unit_index_native_plan_ref", native["input_binding"] == index["phase_plan"])
check("operational_result_maps_equal_index", op["assignments"] == index["assignments"] and op["result_receipts"] == index["result_receipts"])
profile = {
    "pool": producer_review["controller_sha256"], "dispatcher": producer_review["executor_sha256"],
    "protocol": producer_review["protocol_sha256"], "ordinary": producer_review["ordinary_sha256"],
    "consumer_profile": producer_review["consumer_profile"],
}
check("operational_profile_equal_external_reviewed_profile", op["source_profile"] == profile)
cp = profile["consumer_profile"]
check("external_consumer_review_matches_operational_tuple", all(consumer_review["source_pins"][key] == cp[key] for key in ("Replay", "work_replay", "A1_readonly_factory")))
check("execution_lock394_distinct_from_historical8652", cp["work_runner_lock_sha256"] == "394aa16684b38aba71cff858b15202ac240b9c2bbb7c8ce5fc6e82f309ef5953" and cp["work_runner_lock_sha256"] != "86520d69bf147b291d0527557e20ccb30cb554a06019a62a3fbfd8c9bd36a373")
check("operational_physical_fact_does_not_issue_approval", op["physical_raw_rechecked"] is True and op["is_approval"] is False and assembly_intake["formal_unit_acceptance"] is False)
check("reused_native_capture_review_is_not_formal_acceptance", prior_review["capture_sha256"] == refs["previously_reviewed_unit_capture"]["sha256"] and prior_review["formal_unit_or_final_A3_A1_acceptance_issued"] is False and prior_review["required_findings"] == [])
check("selection_requires_actual_unit_index", selection["unit_phase_index"] == assembly_intake["index"] and selection["unit_phase_index"]["sha256"] == refs["unit_index"]["sha256"])
check("selection_accepted_full50_work_aggregate", selection["work_aggregate"]["sha256"] == refs["accepted_work_aggregate"]["sha256"] and len(aggregate["winners"]) == 50)
check("selection_same_context_as_plan_and_work_aggregate", selection["continuation_context"] == plan["continuation_context"] == aggregate["continuation_context"])
check("selection_parent_intake_retains_nonacceptance_scope", selection_intake["selection"]["sha256"] == refs["combined_selection"]["sha256"] and selection_intake["unit_count"] == 81 and selection_intake["work_count"] == 50 and selection_intake["formal_unit_or_release_acceptance"] is False)

# Counts are read from an already adopted documentary result; no type ledger is scanned.
def decision_counts(value):
    if isinstance(value, dict):
        if set(value) == {"whole", "restricted", "refuted", "omitted"}:
            return value
        for child in value.values():
            found = decision_counts(child)
            if found is not None:
                return found
    return None

counts = decision_counts(wrapup)
check("adopted_coverage_denominator_roles", counts == {"whole": 805, "restricted": 110, "refuted": 73, "omitted": 33})
check("external_code_reviews_have_no_required_findings", producer_review["required_findings"] == consumer_review["required_findings"] == scan_review["required_findings"] == [])
output = {
    "schema": "final-sol-a7-a1-incremental-documentary-joins-v1",
    "scope": "NEW_UNIT_INDEX_SELECTION_AND_REUSED_EVIDENCE_ROLE_JOINS_ONLY",
    "completed_documentary_joins": checks,
    "unit_index_members": len(ids),
    "work_aggregate_members": len(aggregate["winners"]),
    "adopted_coverage_counts": counts,
    "source_profile": profile,
    "prior_reviews_reused_without_rerun": ["reused_unit_native_capture_review", "reused_producer_v2_code_review", "external_consumer_code_review", "reused_scan_boundary_review"],
    "new_physical_or_mathematical_validation_performed": False,
    "final_acceptance_issued": False,
    "pending": {"final_all_summary_and_native": None, "actual_current_A1": None, "completed_A7_trust_report": None, "actual_package_bindings": None, "final_combined_decision": None, "once_only_completed_trust_report_review": None},
    "source_refs": refs,
}
(HERE / "BASE-JOINS.json").write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
print(json.dumps({"documentary_joins": len(checks), "unit_members": len(ids), "work_members": len(aggregate["winners"]), "final_acceptance_issued": False}, sort_keys=True))
