"""Authenticate the frozen pending A7 document packet and its documentary roles.

This reads only small retained metadata. It does not re-run any source, semantic,
physical, mathematical, process, site or replay predicate.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
A = REPO / "reports/A3-2026-11-05"
P = A / "a7-current-trust-report-preparation-001"
checks, refs = [], {}


def raw(name, path, expected=None):
    if path.stat().st_size > 8_000_000:
        raise ValueError("Outside small documentary scope: " + name)
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if expected is not None and digest != expected:
        raise ValueError("Changed documentary bytes: " + name)
    refs[name] = {"path": str(path), "sha256": digest, "bytes": len(data)}
    return data


def read(name, path, expected=None):
    return json.loads(raw(name, path, expected))


def check(name, ok):
    if not ok:
        raise ValueError(name)
    checks.append(name)


seal = read("author_A7_preparation_seal", P / "SEAL.json", "138b5c2b2fdca99fff96bd4b2a48c0f25f667633cf94969080a07f9474bccf93")
check("exact10_regular_files_no_extra_members", {p.name for p in P.iterdir()} == set(seal["files"]) | {"SEAL.json"} and all(p.is_file() and not p.is_symlink() for p in P.iterdir()))
for name, expected in seal["files"].items():
    data = raw("A7_packet/" + name, P / name, expected["sha256"])
    check("packet_size/" + name, len(data) == expected["bytes"])

evidence = json.loads((P / "EVIDENCE-MAP.json").read_bytes())
source = json.loads((P / "SOURCE-MAP.json").read_bytes())
remaining = json.loads((P / "REMAINING-JOINS.PENDING.json").read_bytes())
accounting = json.loads((P / "CORRECTION-AND-ACCOUNTING-REFS.json").read_bytes())
base = json.loads((HERE / "BASE-JOINS.json").read_bytes())
prior_by_path = {v["path"]: v for v in base["source_refs"].values()}
external_refs = dict(evidence["metadata_refs"])
external_refs.update({row["path"]: row for row in accounting["refs"].values()})
new_hash_reads, reused_hash_reads = 0, 0
for path, expected in external_refs.items():
    if path in prior_by_path:
        check("reuse_prior_documentary_digest/" + Path(path).name, prior_by_path[path] == expected)
        refs["reused/" + path] = expected
        reused_hash_reads += 1
    else:
        data = raw("retained/" + path, Path(path), expected["sha256"])
        check("retained_metadata_size/" + path, len(data) == expected["bytes"])
        new_hash_reads += 1

check("fourteen_role_records_and39_metadata_refs", len(evidence["records"]) == 14 and len(evidence["metadata_refs"]) == 39)
check("A7_preparation_is_not_approval", evidence["is_approval"] is False and remaining["formal_final_A1_A3_or_release_approval_issued"] is False)
check("A7_coverage_counts_match_adopted_roles", source["declared_decision_counts"] == base["adopted_coverage_counts"])
check("A7_current_A1_has_no_invented_result", source["actual_current_A1_result"] is None and remaining["final_A1"]["reconciliation"] is None and remaining["final_A1"]["native_capture"] is None)
pending = read("sealed_current_A1_pending_config", A / "a3-continuation-final-certification-bindings-001/FINAL-A1.CONFIG.PENDING.json", "cd20945ef896df7c44811f7386df149b4ab5502ba5d8921a849672ae94a2b6e0")
check("A7_ten_A1_input_refs_match_existing_preparation", source["current_A1_ten_reliance_inputs"] == pending["inputs"] and len(pending["inputs"]) == 10)
check("A7_historical_lock_role_matches_A1_outer_data", source["historical_generation_runner_lock"]["sha256"] == pending["a3"]["work_runner_lock_sha256"] == "86520d69bf147b291d0527557e20ccb30cb554a06019a62a3fbfd8c9bd36a373")
check("A7_execution_lock_role_matches_external_profile", source["execution_runner_lock"]["sha256"] == base["source_profile"]["consumer_profile"]["work_runner_lock_sha256"])
for name, key in (("Replay", "Replay"), ("work_replay", "work_replay"), ("A1", "A1_readonly_factory")):
    check("A7_source_role/" + name, source["runtime_sources"][name]["sha256"] == base["source_profile"]["consumer_profile"][key])
for name, key in (("producer_pool", "pool"), ("dispatcher", "dispatcher"), ("ordinary", "ordinary"), ("protocol", "protocol")):
    check("A7_source_role/" + name, source["runtime_sources"][name]["sha256"] == base["source_profile"][key])
check("A7_final_vs_terminal_protocol_paths_remain_distinct", source["terminal_vs_final_protocol_path_rule"]["final_Replay_A1_dispatch_protocol"] == pending["a3"]["dispatch"]["protocol"]["path"] and source["terminal_vs_final_protocol_path_rule"]["terminal_sources_protocol"] != pending["a3"]["dispatch"]["protocol"]["path"])
check("A7_frozen_and_generation_match_A1_outer_data", source["generation"] == pending["a3"]["generation"] and source["frozen_inputs"]["sha256"] == pending["a3"]["input_lock_sha256"])
check("A7_accounting_roles_remain_separate", accounting["separate_purposes"] == {"A3_work_accepted": 50, "A3_work_launches": 67, "formal_unit_final_acceptance": None, "ordinary_accepted": 50, "ordinary_launches": 51, "unit_first_launches": 81, "unit_native_zero": 81})
check("A7_final_summary_and_native_are_pending", remaining["final_all"]["canonical_summary"]["sha256"] is None and remaining["final_all"]["native_completion"] is None and remaining["final_all"]["native_readback_capture"] is None)
check("A7_final_package_and_decisions_pending", all(remaining["final_package"][k] is None for k in ("commit", "tree", "filemap_sha256", "reviewed_export_and_site_bindings")) and remaining["final_Sol"]["decision"] is None and remaining["Opus"]["completed_trust_report_review"] is None)
check("A7_does_not_reopen_publication_permission", remaining["publication"]["prior_user_authorization_preserved"] is True and remaining["publication"]["new_permission_request_created"] is False)
output = {
    "schema": "final-sol-a7-preparation-documentary-joins-v1",
    "scope": "SEALED_PENDING_REPORT_AND_EXISTING_ACCEPTED_DOCUMENTARY_ROLES",
    "completed_documentary_joins": checks,
    "metadata_ref_count": len(external_refs),
    "documentary_hashes_reused_from_base_checkpoint": reused_hash_reads,
    "additional_small_metadata_hash_reads": new_hash_reads,
    "source_refs": refs,
    "draft_wording_clarification": {"issue": "A source/schema limitation was phrased as if a current actual A1 result existed.", "status": "CLOSED_BEFORE_AUTHOR_SEAL", "corrected_draft_sha256": seal["files"]["TRUST-REPORT.DRAFT.md"]["sha256"]},
    "new_upstream_predicates_or_reviews_run": False,
    "final_A1_A3_or_release_acceptance_issued": False,
    "remaining_actuals": "Genuine final-all/native, actual current A1 and completed report/package joins. Later closure inspects those deltas only.",
}
(HERE / "A7-PREPARATION-JOINS.json").write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
print(json.dumps({"documentary_joins": len(checks), "external_metadata_refs": len(external_refs), "final_acceptance_issued": False}, sort_keys=True))
