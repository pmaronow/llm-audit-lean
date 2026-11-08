"""Compare prepared copy-map data to accepted metadata and literal site interface.

No producer/site predicate is imported or executed; no source payload is copied.
"""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
A = REPO / "reports/A3-2026-11-05"
P = A / "final-package-projection-preparation-001"
refs, checks = {}, []


def read(name, path, expected=None):
    data = path.read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if expected is not None and actual != expected:
        raise ValueError(f"Changed prepared input: {name}")
    refs[name] = {"path": str(path), "sha256": actual, "bytes": len(data)}
    return json.loads(data)


def check(name, ok):
    if not ok:
        raise ValueError(name)
    checks.append(name)


unit = read("unit_candidate_map", P / "UNIT-CANDIDATE-COPY-MANIFEST.PREPARED.json", "54abd2cba331accd3293e6824a2d36b3c35b7726cd9062c4cb8e72c046d0a901")
works = read("Works_map", P / "WORKS-COPY-MANIFEST.PREPARED.json", "2c2a8ad62da31934d77e81c0d7241b85ed497a8b4877a4aa59fb0aaf3f288db1")
admission = read("site_admission_view_map", P / "SITE-ADMISSION-COPY-MANIFEST.PREPARED.json", "0edcfb58c07da3790cb5bc3d366da677a7380081875ef62e996b97331d24a356")
inventory = read("accepted_candidate_file_map", Path(unit["collection_inventory"]["path"]), unit["collection_inventory"]["sha256"])
native = read("retained_native_admission_transport_map", Path(admission["native_transport_manifest"]["path"]), admission["native_transport_manifest"]["sha256"])
work_transport = read("retained_Works_transport_map", Path(works["source_manifest"]["path"]), works["source_manifest"]["sha256"])
closure_path = Path(admission["local_source_root"]) / "collector-input-closure-before.json"
closure = read("retained_declared_raw_membership", closure_path, native["files"][closure_path.name]["sha256"])

code_path = REPO / "llm-audit/scripts/collection_inputs.py"
code = code_path.read_bytes()
refs["site_consumer_interface_read_only"] = {"path": str(code_path), "sha256": hashlib.sha256(code).hexdigest(), "bytes": len(code)}
constants = {}
for node in ast.parse(code).body:
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name) and node.targets[0].id in {"NAMES", "RUNNER_FILES", "INTERFACE"}:
        constants[node.targets[0].id] = ast.literal_eval(node.value)

check("unit_map_exact_accepted_candidate_paths_and_hashes", {k: v["sha256"] for k, v in unit["files"].items()} == inventory)
check("unit_map_all6413_keys_with_SAP_prefix", len(unit["files"]) == unit["file_count"] == 6413 and all(k.startswith("SAP/") for k in unit["files"]))
check("unit_sizes_total59321483", sum(v["bytes"] for v in unit["files"].values()) == unit["bytes"] == 59321483)
check("candidate_unit_and_formal_Work_paths_disjoint", set(unit["files"]).isdisjoint(works["files"]))
work_rows = {k.removeprefix("overlay/"): v for k, v in work_transport["files"].items() if k.startswith("overlay/")}
check("Works_map_exact480_overlay_transport_rows", works["files"] == work_rows and len(work_rows) == works["file_count"] == 480)
check("Works_sizes_total4690759", sum(v["bytes"] for v in works["files"].values()) == works["bytes"] == 4690759)
check("Works_scope50_formal52_site_and_two_inapplicable", works["formal_works"] == 50 and works["site_works"] == 52 and works["inapplicable_formal_works"] == ["P048", "P050"])

excluded = {"a3-admission-check.json", "target-routes.json"}
native_rows = dict(native["files"])
check("only_two_native_files_excluded_from_consumer_view", set(admission["excluded_from_this_view_only"]) == excluded)
for key in excluded:
    recorded = dict(admission["excluded_from_this_view_only"][key])
    recorded.pop("local_source")
    check("original_excluded_reference_retained_" + key, recorded == native_rows.pop(key))
check("only_contract_filename_renamed", admission["rename_only"] == {"approved-contract-inventory.json": "contract-inventory.json"})
native_rows["contract-inventory.json"] = native_rows.pop("approved-contract-inventory.json")
check("consumer_view_exact_unchanged_native_rows", admission["files"] == native_rows)
expected_names = set(constants["NAMES"].values()) | {"contract-inventory.json"} | {"runner/" + name for name in constants["RUNNER_FILES"]} | {"collector-inputs/" + name for name in closure["files"]}
check("consumer_view_exact_literal_data_v2_member_names", set(admission["files"]) == expected_names)
check("member_arithmetic20_plus1_plus12_plus10180", len(constants["NAMES"]) == 20 and len(constants["RUNNER_FILES"]) == 12 and len(closure["files"]) == 10180 and len(expected_names) == admission["file_count"] == 10213)
check("consumer_view_sizes_total666009558", sum(v["bytes"] for v in admission["files"].values()) == admission["bytes"] == 666009558)
check("full_native_original10215_preserved_as_source", len(native["files"]) == admission["full_native_archive_file_count"] == 10215 and native["ledger_included"] is admission["ledger_included"] is False)
for name, data, keys in (
    ("unit", unit, ("actual_export_root", "actual_export_archive_sha256")),
    ("Works", works, ("actual_destination",)),
    ("admission", admission, ("actual_projection_root", "actual_projection_sha256")),
):
    check(name + "_actual_copy_facts_remain_null", all(data[key] is None for key in keys))

output = {
    "schema": "final-sol-package-projection-data-boundary-joins-v1",
    "scope": "PREPARED_COPY_MAPS_AND_EXISTING_LITERAL_SITE_INTERFACE_ONLY",
    "completed_documentary_joins": checks,
    "source_refs": refs,
    "required_boundary": {
        "unit_site_intake": "Fresh isolated parent contains only SAP/**; --package-root is its SAP child. No Works/evidence/baseline sibling may enter this exact_tree scope.",
        "formal_package": "Separate fresh root combines the selected preserved baseline with exact SAP and Works maps. Actual file map, commit and tree remain parent-owned pending facts.",
        "admission_view": "Independent regular copies, exact10213 membership, same contract bytes under consumer filename; original10215-file native archive remains unchanged.",
        "directories": "Only file-parent directories; no extra empty directory, symlink or hardlink under either exact input view.",
    },
    "physical_payload_checks_or_copies_performed": False,
    "site_predicates_or_source_modules_executed": False,
    "actual_package_or_release_approved": False,
}
(HERE / "PROJECTION-JOINS.json").write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
print(json.dumps({"documentary_joins": len(checks), "unit_files": len(unit["files"]), "Works_files": len(work_rows), "site_admission_files": len(expected_names), "actual_package_approved": False}, sort_keys=True))
