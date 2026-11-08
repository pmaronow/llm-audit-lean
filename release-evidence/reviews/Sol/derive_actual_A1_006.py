"""Finite documentary joins for genuine A1 outputs; no upstream code execution."""
import base64
import hashlib
import json
from collections import Counter
from pathlib import Path

R = Path(__file__).resolve().parent
REPO = R.parents[2]
A = REPO / "reports/A3-2026-11-05"
P = A / "parent-a3-continuation-final-validation-001/final-a1-001"
B = P / "native-readback"
refs, checks = {}, {}


def read(name, path, expected=None):
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if expected is not None and digest != expected:
        raise ValueError("Changed documentary bytes: " + name)
    refs[name] = {"path": str(path), "sha256": digest, "bytes": len(data)}
    return json.loads(data)


def check(name, ok):
    if not ok:
        raise ValueError(name)
    checks[name] = True


capture = read("A1_capture", B / "ACTUAL-CAPTURE.json", "e1b2a688c4d05740ea241154fb0a25bc1763e06fac664206b93a6276f225cd53")
binding = read("A1_binding", P / "BINDINGS.json", "c91ae849a0a085802dbdddcbb139003cfe0ff4b4ef3ad9cb8117079c0ba2c8cf")
parent = read("A1_parent_binding_review", P / "PARENT-BINDING-REVIEW.json", "e8ca910f158b3cd426a855126e50e4528631f4ef366e5933db52d3d9b332f5ef")
transport_intent = read("A1_transport_intent", P / "TRANSPORT-INTENT.json")
invocation = read("A1_transport_invocation", P / "INVOCATION.json")
transport = read("A1_transport_stdout", P / "SSH.stdout")
raw = read("A1_readback_stream", B / "SSH.stdout", capture["readback_stdout_sha256"])
check("complete_readback0_no_reexecution", capture["capture_complete"] is True and capture["native_exit_code"] == capture["readback_ssh_exit_code"] == 0 and capture["program_rerun"] is False and (B / "SSH.exit").read_bytes() == b"0\n" and (B / "SSH.stderr").read_bytes() == b"")
native_names = {"INTENT.json", "LAUNCH.json", "COMPLETION.json", "exit", "stdout.log", "stderr.log"}
check("six_native_records_no_error_substitute", set(capture["native"]["native"]) == set(raw["native"]) == {p.name for p in (B / "native").iterdir()} == native_names)
for group, names in (("native", native_names), ("semantic", {"summary", "report", "reconciliation"})):
    for name in names:
        data = (B / group / name).read_bytes()
        row, stream = capture["native"][group][name], raw[group][name]
        digest = hashlib.sha256(data).hexdigest()
        check("stream_copy/" + group + "/" + name, len(data) == row["bytes"] == stream["bytes"] and digest == row["sha256"] == stream["sha256"] and data == base64.b64decode(stream["base64"], validate=True) and row["path"] == stream["path"] and row["mode"] == stream["mode"])
        refs[group + "/" + name] = {"path": str(B / group / name), "sha256": digest, "bytes": len(data), "native_path": row["path"], "native_mode": row["mode"]}
check("unchanged_all_summary_and_no_pending_marker", refs["semantic/summary"]["sha256"] == "58b93d9a3f77703bd3b89c1706ef1068d6dd1f318af7da8721866543a81f2c2a" and raw["semantic"]["pending_summary"] is capture["native"]["semantic"]["pending_summary"] is None and set(raw["semantic"]) == {"summary", "pending_summary", "report", "reconciliation"})
check("operation_and_semantic_output_targets_match_binding", capture["phase"] == binding["phase"] == "a1" and raw["root"] == capture["native"]["root"] == binding["operation_root"] and refs["semantic/reconciliation"]["native_path"] == binding["a1_output"] + "/RECONCILIATION.json" and refs["semantic/report"]["native_path"] == binding["a1_output"] + "/REPORT.md" and refs["semantic/summary"]["native_path"] == binding["summary_path"])
intent = json.loads((B / "native/INTENT.json").read_bytes())
launch = json.loads((B / "native/LAUNCH.json").read_bytes())
completion = json.loads((B / "native/COMPLETION.json").read_bytes())
result = json.loads((B / "semantic/reconciliation").read_bytes())
summary = json.loads((B / "semantic/summary").read_bytes())
check("same_original_bound_argv", intent["argv"] == launch["argv"] == binding["argv"] == parent["actual_bindings"]["argv"] == transport_intent["exact_native_argv"])
check("source1fd_config8d_and_fresh_output", intent["source_sha256"] == binding["source_sha256"] == "1fd7a893d409efa87cae64e7727eb8a63a7e67860c8f8f1e7fc2da694458517b" and intent["input_binding"]["role"] == "config" and intent["input_binding"]["sha256"] == "8d4c2c06eb364b391c707daf73c7626f97ae88d880fae8443b8c7dde8b836a86" and intent["preflight"] == {"A1_output_absent": True, "canonical_summary_sha256": refs["semantic/summary"]["sha256"], "pending_summary_absent": True} and intent["retry"] is False)
tail = launch["proc_stat"][launch["proc_stat"].rfind(")") + 2:].split()
identity = {"pid": launch["pid"], "start_ticks": int(tail[19]), "pgid": int(tail[2]), "sid": int(tail[3]), "uid": launch["uid"], "boot_id": launch["boot_id"]}
check("original_full_native_identity", identity == capture["identity"] == {"pid": 3734339, "start_ticks": 59406110, "pgid": 3734339, "sid": 3734339, "uid": 1000, "boot_id": "787d8ad1-3854-4eb0-9229-b44214fc6ee7"} and completion["pid"] == transport["pid"] == identity["pid"])
check("native_transport_exit0_and_native_elapsed_order", completion["exit_code"] == transport["exit_code"] == invocation["ssh_exit_code"] == 0 and (B / "native/exit").read_bytes() == b"0\n" and completion["ended_unix_ns"] > launch["started_unix_ns"])
check("native_logs_bound_to_completion_and_transport", all(completion[k] == transport[k] == refs["native/" + n]["sha256"] for k, n in (("stdout_sha256", "stdout.log"), ("stderr_sha256", "stderr.log"))))
check("sole_transport_raw_and_reviewed_wrapper", invocation["stdout_sha256"] == refs["A1_transport_stdout"]["sha256"] and invocation["stderr_sha256"] == hashlib.sha256((P / "SSH.stderr").read_bytes()).hexdigest() and (P / "SSH.stderr").read_bytes() == b"" and invocation["remote_script_sha256"] == transport_intent["bound_remote_source_sha256"] == parent["materialized_files"]["REMOTE.py"]["sha256"] == "85d492fd205f14d3d547f655dd0543df640cf1be761540266f342bb0720514c6" and transport_intent["automatic_retries"] is False)
cfg = read("actual_A1_config", A / "parent-a3-continuation-final-validation-001/FINAL-A1.CONFIG.ACTUAL.json", "8d4c2c06eb364b391c707daf73c7626f97ae88d880fae8443b8c7dde8b836a86")
check("actual_A3_tuple_equals_parent_config", result["actual_A3_bindings"] == cfg["a3"])
check("all10_fixed_refs_and_config_observed", len(cfg["inputs"]) == 10 and all(result["input_files"].get(v["path"], {}).get("sha256") == v["sha256"] for v in cfg["inputs"].values()) and result["input_files"][intent["input_binding"]["path"]] == {"sha256": refs["actual_A1_config"]["sha256"], "bytes": refs["actual_A1_config"]["bytes"]})
ctx = result["read_only_A3_validator_context"]
check("reviewed_readonly_factory_and_historical_execution_roles", ctx["reviewed_replay_source_sha256"] == "dca61c208b7d3bfa46d1dc2a6ba9836de9e6ce60064433abe9744b85fa610cdb" and ctx["executed_readonly_source_sha256"] == "b0daeb6f706cc5fc46defdadd7706e61db000b0e91c2861980a8ad9d50b78922" and ctx["execution_work_runner_lock_sha256"] == "394aa16684b38aba71cff858b15202ac240b9c2bbb7c8ce5fc6e82f309ef5953" and ctx["historical_work_runner_lock_sha256"] == cfg["a3"]["work_runner_lock_sha256"] == "86520d69bf147b291d0527557e20ccb30cb554a06019a62a3fbfd8c9bd36a373" and ctx["mkdir_calls_replaced_by_existing_directory_checks"] == 2 and ctx["dispatch"] == cfg["a3"]["dispatch"])
M = REPO / "reports/A1-2026-11-05"
migration = read("accepted_historical_migration", M / "parent-quiet-operations/migration-v3-actual/current-migration.json", "c825f9d3fb71fc5d10ca07be748f7532d8793efcd5f147f4784a3475ef62cb8b")
plan = read("accepted_row_plan", M / "final-reliance-completion-preparation/ROW-JOIN-PLAN.json", "24330eaba693bcd4ab1b07ab49ba863b67dcdd7d5ae1edea97a29094e945e074")
original = {(r["group"], r.get("target_id")): r for r in migration["rows"]}
planned = {(r["legacy_group"], r["target_id"]): r for r in plan["rows"]}
rows = {tuple(r["historical_key"]): r for r in result["historical_rows"]}
check("452_unique_keys_exact_migration_and_plan", len(original) == len(planned) == len(rows) == len(result["historical_rows"]) == 452 and set(original) == set(planned) == set(rows))
check("452_original_rows_and_statuses_unchanged", all(rows[k]["original_migration_row"] == row and row["status"] == planned[k]["original_status_to_preserve"] for k, row in original.items()))
counts = {"current_fw_supersedes_legacy_gate_pending_replay": 416, "PRESERVE_SUPERSEDED_ROUTE": 29, "PRESERVE_KEPT_RESTRICTED_NO_GATE_RERUN": 4, "PRESERVE_RETIRED_GROUP": 3}
check("416_29_4_3_preserved_and_no_rebinding", dict(Counter(r["status"] for r in original.values())) == result["status_counts_preserved"] == counts and result["historical_rebindings"] == 0 and all(r["legacy"]["historical_input_fingerprint"] is None and r["legacy"]["automatic_legacy_rebind"] is False for r in original.values()))
route_counts, decisions, direct = Counter(), Counter(), []
active = 0
for key, wrapped in rows.items():
    row, evidence = wrapped["original_migration_row"], wrapped["deterministic_evidence"]
    if row["status"] != "current_fw_supersedes_legacy_gate_pending_replay":
        if evidence is not None:
            raise ValueError("New attachment on preserved disposition")
        continue
    active += 1
    groups = planned[key]["current_changed_route_group_ids"]
    route = "assigned_current_group" if groups else "direct_final_theorem"
    if evidence["unit_receipt_sha256"] != summary["units"][row["unit"]] or evidence["work_receipt_sha256"] != summary["works"][row["target_id"][:4]] or evidence["theorem"] != row["final_theorem"] or evidence["theorem"] != planned[key]["final_theorem"] or evidence["route_kind"] != route or evidence["current_group_id"] != (groups[0] if groups else None):
        raise ValueError("Wrong current attachment: " + row["target_id"])
    if set(evidence["type_contract"]) != {"canonical_type", "universe_count"}:
        raise ValueError("Missing producer-validated type attachment")
    route_counts[route] += 1
    decisions[row["final_decision"]] += 1
    if not groups:
        direct.append(row["target_id"])
check("416_current_attachments_406_routed10_direct", active == 416 and dict(route_counts) == {"assigned_current_group": 406, "direct_final_theorem": 10} and sorted(direct) == sorted(plan["pending_without_changed_assignment"]))
base = json.loads((R / "BASE-JOINS.json").read_bytes())
aggregate = json.loads(Path(base["source_refs"]["accepted_work_aggregate"]["path"]).read_bytes())
index = json.loads(Path(base["source_refs"]["unit_index"]["path"]).read_bytes())
selected = [r["result_receipt"] for r in aggregate["winners"].values()] + list(index["result_receipts"].values())
check("selected131_receipt_refs_recorded", all(result["input_files"].get(r["path"], {}).get("sha256") == r["sha256"] for r in selected))
check("existing_bulk_authority_review_refs_not_invented_enumerator_rule", cfg["inputs"]["contract_review"]["sha256"] == "39088a8b5afaad2ff020f8858b4c7d84b7f4f033fc5b6bee3bd2505527395948" and cfg["inputs"]["ledger_review"]["sha256"] == "d26c5f0e00789219650724320673f440e9f02fa5ee5fefa9eea222a75a80ab75" and cfg["a3"]["input_lock_sha256"] == "8c913e20bc27ad7ca604e2c09dbe5f19b6fc2ecdd2682a1ea6b46091ae1dc68e")
flags = ["A1_full_signoff_or_release_approval", "automatic_promotion_enabled", "independent_final_A1_approval", "operational_deployment_assessed", "paper_fidelity_or_coverage_adjudication"]
check("producer_approval_and_deployment_boundaries_remain_false", all(result[k] is False for k in flags) and capture["semantic_acceptance_or_review_issued"] is False)
check("stdout_actual_counts_without_approval", json.loads((B / "native/stdout.log").read_bytes()) == {"output": binding["a1_output"], "rows": 452, "pending_rows_joined": 416, "approval": False})
out = {"schema": "final-sol-actual-current-A1-reconciliation-delta-v1", "scope": "ACTUAL_A1_NATIVE_CONFIG_HISTORICAL_ROWS_AND_CURRENT_ATTACHMENT_METADATA_ONLY", "checks": checks, "source_refs": refs, "native_identity": identity, "native_elapsed_seconds": (completion["ended_unix_ns"] - launch["started_unix_ns"]) / 1e9, "historical_rows_unchanged": 452, "current_attachments": 416, "route_counts": dict(route_counts), "current_decision_counts": dict(decisions), "status_counts_preserved": counts, "observed_input_file_ref_count": len(result["input_files"]), "type_contracts_native_validated_not_rechecked_against_bulk_ledger": 416, "failed_interpretation_preserved": "A1-JOIN-ATTEMPT-001.json", "new_source_math_caller_audit_retained_validator_test_SSH_or_runtime_by_reviewer": False, "required_findings": [], "final_report_or_package_verdict_issued": False}
(R / "A1-ACTUAL-JOINS-006.json").write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
print(json.dumps({"documentary_joins": len(checks), "historical_rows": 452, "current_rows": active, "current_decisions": dict(decisions), "native_elapsed_seconds": out["native_elapsed_seconds"]}, sort_keys=True))
