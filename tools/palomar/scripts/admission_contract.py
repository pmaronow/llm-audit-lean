"""Read-only compatibility join to an EXTERNALLY approved real A3 collection.

No approval/pin/receipt is generated here. No A3/v2 Python module is imported or
executed. The caller must supply a parent-independent expected review digest.
That authority input must come from review records, never from hashing an
untrusted candidate's own JSON. A digest cannot itself prove reviewer identity.
"""
import sys
sys.dont_write_bytecode = True
import ast
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

from boundaries import Invalid, exact_collection_tree, collection_layout, file_inventory, need, overlap, sha_regular, tree_rows

from _palomar_installation import blobs as _installation_blobs
from counts import integer, decisions as decision_counts, promised
import closure_data

PROTOCOL = json.loads(_installation_blobs["scripts/PROTOCOL.json"])
NAMES = PROTOCOL["archived_admission_names"]
HASH_FIELDS = PROTOCOL["archive_hash_fields"]
HELPERS = {"inventory_helper": "inventory.py", "admission_helper": "collection_admission.py",
           "bootstrap_helper": "runner_bootstrap.py"}
RUNNER_NAMES = set(PROTOCOL["runner_file_set"])
RESULT_FIELDS = {"schema", "status", "candidate_content_sha256", "unit_count", "target_count", "decisions", "pin_sha256",
                 "a1_receipt_sha256", "collection_receipt_sha256", "collection_inventory_sha256", "contract_inventory_sha256",
                 "reviewed_tool_lock_sha256", "fw_common_sha256", "runner_content_sha256",
                 "collection_input_archive_sha256", "collection_input_closure_before_sha256", "collection_input_closure_after_sha256"}
REVIEW_FIELDS = {"schema", "verdict", "reviewer", "evidence", "materialized_source_root", "admission_root",
                 "files_sha256", "account_home", "original_candidate_root", "original_collector_input_archive_root", "provenance_checks"}
CHECKS = {"actual_os_account_home", "canonical_sap_root_and_collector", "fresh_A1_validator_identity",
          "transitive_helpers_verified_before_import_and_after_execution", "successful_full_normal_collection",
          "actual_admission_result_validated_complete_data_closure", "producer_protocol_reviewed_for_actual_layout"}
HEX = re.compile(r"[0-9a-f]{64}\Z")
V5_WRAPPER_SHA256 = "9ba0a4b85a7f5729d76ed15f04c9b02531ddd72bab091289bff0d226ccbafdbc"
EMPTY_BRIDGE_UNITS = frozenset({"P001b", "P008a", "P008b", "P018b", "P023", "P024", "P053"})


def parse_json(text):
    def unique(pairs):
        out = {}
        for k, v in pairs:
            need(k not in out, "duplicate admission JSON key: " + k); out[k] = v
        return out
    def nonjson(value):
        raise Invalid("non-JSON admission constant: " + value)
    return json.loads(text, object_pairs_hook=unique, parse_constant=nonjson)


def load(path):
    sha_regular(path)
    return parse_json(Path(path).read_text())


def compact(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode()


def hashed(value):
    return hashlib.sha256(compact(value)).hexdigest()


def origin(value):
    need(isinstance(value, str) and value.startswith("/") and ".." not in PurePosixPath(value).parts and
         str(PurePosixPath(value)) == value, "noncanonical recorded collection origin")
    return PurePosixPath(value)


def validate_collection_log(text, theorem_count, receipt, closure, snapshot, inventory):
    """Two complete log shapes; archived observations never assert live emptiness."""
    line = rf"81 faithful units staged; {theorem_count} theorems"
    if receipt.get("script_sha256") != V5_WRAPPER_SHA256 and re.fullmatch(rf"\s*{line}\s*", text) is not None:
        return
    match = re.fullmatch(line + r"\n\n([^\r\n]+)\n", text)
    need(match is not None, "retained normal collector log is not a complete successful collection")
    need(receipt.get("script_sha256") == V5_WRAPPER_SHA256,
         "collection log event requires the exact reviewed v5 wrapper")
    event = parse_json(match[1])
    need(isinstance(event, dict) and set(event) == {"event", "removed", "closure_before_sha256",
         "closure_after_sha256", "raw_archive_sha256"} and
         event["event"] == "source-bound-empty-bridge-canonicalization-v1",
         "closed v5 Bridge canonicalization event required")
    for key, field in (("closure_before_sha256", "collection_input_closure_before_sha256"),
                       ("closure_after_sha256", "collection_input_closure_after_sha256"),
                       ("raw_archive_sha256", "collection_input_archive_sha256")):
        need(isinstance(event[key], str) and HEX.fullmatch(event[key]) and event[key] == receipt.get(field),
             "v5 Bridge event archive/closure hash differs: " + key)
    need(event["closure_before_sha256"] == event["closure_after_sha256"],
         "v5 Bridge event requires unchanged observed closure")
    sap = origin(closure["sap_root"])
    need(str(sap) == receipt.get("sap_root") and closure["units"] == sorted(snapshot["units"]),
         "v5 Bridge event source observation scope differs")
    occupied = {str(parent) for name in inventory for parent in PurePosixPath(name).parents}
    expected = []
    # copytree preserves ARCH directories. The normalizer plans every candidate
    # empty allowed Bridge, even when the plan is empty. File-occupied Bridges
    # are not plans; source absence is not an empty source directory witness.
    for unit in sorted(EMPTY_BRIDGE_UNITS & set(closure["units"])):
        root = "wt/ARCH-" + unit + "/SAP/" + unit
        source_name, candidate_name = root + "/Bridge", "SAP/" + unit + "/Bridge"
        members = closure["directories"].get(root) or {}
        if members.get("Bridge") != "directory" or candidate_name in occupied:
            continue
        own = snapshot["units"][unit]
        need(own["arch_source_path"] == str(sap / root) and
             closure["directories"].get(source_name) == {} and
             not any(n == source_name or n.startswith(source_name + "/") for n in closure["files"]) and
             not any(n == "Bridge" or n.startswith("Bridge/") for n in own["arch_source_files_sha256"]) and
             candidate_name not in inventory,
             "v5 candidate empty Bridge lacks exact archived empty source membership: " + candidate_name)
        expected.append({"unit": unit, "candidate_path": candidate_name,
                         "source_path": str(sap / source_name), "observed_source_members": []})
    need(event["removed"] == expected,
         "v5 Bridge event must list every exact sorted unique source-bound empty candidate Bridge")


def validate(source, args, units, target_count):
    review_path = getattr(args, "admission_review", None)
    expected = getattr(args, "expected_admission_review_sha256", None)
    root_arg = getattr(args, "admission_root", None)
    need(review_path is not None and root_arg is not None and isinstance(expected, str) and HEX.fullmatch(expected),
         "independently expected parent admission review/root/digest required; self-consistent receipts are not approval")
    need(sha_regular(review_path) == expected, "independent parent admission review identity mismatch")
    review = load(review_path)
    need(isinstance(review, dict) and set(review) == REVIEW_FIELDS and
         review["schema"] == "palomar-parent-collection-admission-v4" and
         review["verdict"] == "READY_FOR_SOURCE_COLLECTION_ONLY" and
         all(isinstance(review[k], str) and review[k].strip() for k in ("reviewer", "evidence")),
         "parent review is not a closed independent source-collection approval")
    need(set(review["provenance_checks"]) == CHECKS and all(v is True for v in review["provenance_checks"].values()),
         "parent review did not approve every required provenance boundary")
    source, root = Path(source).resolve(), Path(root_arg).resolve()
    need(not overlap(Path(review_path).resolve(), root) and not overlap(Path(review_path).resolve(), source) and
         not overlap(source, root), "independent parent review, source and admission archive must be separate")
    need(review["materialized_source_root"] == str(source) and review["admission_root"] == str(root),
         "approved materialized source/admission root identity differs")
    # Names are derived only from the closed closure inventory, never a prefix exemption.
    closure = load(root / NAMES["closure_before"])
    raw_files = closure_data.schema(closure)
    allowed={"collector-inputs/" + name for name in raw_files} | set(NAMES.values())|{"target-routes.json","a3-admission-check.json","approved-contract-inventory.json"}|{
        "runner/"+name for name in RUNNER_NAMES}
    need(isinstance(review["files_sha256"],dict) and set(review["files_sha256"]) == allowed,
         "parent review must pin the exact complete admission artifact set")
    need(file_inventory(root) == review["files_sha256"], "entire independently approved admission evidence inventory differs")
    wanted_dirs={str(parent) for name in allowed for parent in PurePosixPath(name).parents if str(parent)!="."}
    actual_dirs={p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_dir()}
    need(actual_dirs==wanted_dirs,"entire admission evidence directory membership differs")
    paths = {k: root / name for k, name in NAMES.items()}
    docs = {k: load(p) for k, p in paths.items() if k not in {"collector", "wrapper", "fw_common", "log", *HELPERS}}
    pin, receipt, lock = docs["pin"], docs["receipt"], docs["tool_lock"]
    fields = set(PROTOCOL["admission_pin_fields"])
    need(set(pin) == fields and pin["schema"] == "a3-reviewed-collection-admission-v3" and pin["verdict"] == "READY",
         "A3 independent admission pin is absent, obsolete or unreviewed")
    need(all(isinstance(pin[k],str) and pin[k].strip() for k in ("reviewer","evidence")), "admission pin review metadata absent")
    for option, artifact in (("expected_admission_pin_sha256", paths["pin"]),
                             ("expected_admission_result_sha256", root/"a3-admission-check.json"),
                             ("expected_reviewed_tool_lock_sha256", paths["tool_lock"])):
        value = getattr(args, option, None)
        need(isinstance(value, str) and HEX.fullmatch(value) and sha_regular(artifact) == value,
             "independently expected actual artifact identity required/differs: " + option)
    for kind, field in HASH_FIELDS.items():
        need(isinstance(pin[field], str) and HEX.fullmatch(pin[field]) and sha_regular(paths[kind]) == pin[field],
             "actual pinned admission artifact differs: " + kind)
    need(set(lock) == {"schema","verdict","reviewer","evidence","collector_sha256","fw_common_sha256","runner_files_sha256"}, "closed reviewed tool lock required")
    need(all(isinstance(lock[k],str) and lock[k].strip() for k in ("reviewer","evidence")), "tool lock review metadata absent")
    need(lock.get("schema") == "a3-reviewed-collection-tools-v2" and
         lock.get("verdict") == "READY_FOR_SOURCE_COLLECTION_AND_A3_INPUT_CHECKS", "externally reviewed tool lock required")
    runner = lock.get("runner_files_sha256", {})
    need(set(runner) == RUNNER_NAMES and all(isinstance(h, str) and HEX.fullmatch(h) for h in runner.values()),
         "complete transitive reviewed runner inventory required")
    need(file_inventory(root / "runner") == runner and pin["runner_content_sha256"] == hashed(runner),
         "archived reviewed runner/helper closure differs")
    for kind, filename in HELPERS.items():
        need(pin[HASH_FIELDS[kind]] == runner[filename], "archived wrapper helper differs from reviewed closure: " + kind)
    need(pin["collector_sha256"] == lock["collector_sha256"] and pin["fw_common_sha256"] == lock["fw_common_sha256"] and
         pin["collection_wrapper_sha256"] == runner["collect_review_snapshot_v2.py"], "collector/wrapper/validator tool identity differs")
    need(receipt.get("schema") == "sap-review-collection-v4" and receipt.get("status") == "SOURCE_BOUND_REVIEW_INPUT" and
         type(receipt.get("collector_exit_code")) is int and receipt["collector_exit_code"] == 0 and
         receipt.get("source_and_input_stability") is True and receipt.get("stability_scope") == closure_data.STABILITY_SCOPE and
         receipt.get("source_collection_only") is True and
         receipt.get("exclusive_writer_fence_claimed") is False and
         all(receipt.get(k) is False for k in ("A3_freeze", "A3_build", "A3_replay")),
         "actual successful normal collection execution evidence required")
    need(type(receipt.get("units")) is int and receipt["units"] == len(units) == 81 and
         type(receipt.get("targets")) is int and receipt["targets"] == target_count == 1021,
         "real admission cannot use synthetic fixture scope")
    for field in HASH_FIELDS.values():
        if field != "collection_receipt_sha256":
            key = "script_sha256" if field == "collection_wrapper_sha256" else field
            need(receipt.get(key) == pin[field], "receipt identity differs from independent pin: " + key)
    need(receipt.get("runner_files_sha256") == runner and receipt.get("runner_content_sha256") == hashed(runner),
         "receipt did not bind the complete reviewed helper closure")
    before, after = docs["inputs"], docs["inputs_after"]
    need(isinstance(before, dict) and before == after and docs["source"] == docs["source_after"],
         "actual source/input before and after inventories differ")
    need(all(origin(k) and isinstance(h, str) and HEX.fullmatch(h) for k, h in before.items()), "malformed exact input inventory")
    home = origin(review["account_home"]); sap = home / "sap"
    candidate, runner_root = origin(review["original_candidate_root"]), origin(receipt.get("runner_root"))
    need(receipt.get("sap_root") == str(sap) and receipt.get("home_sap_root") == str(sap) and
         receipt.get("candidate_path") == str(candidate) and (sap / "assure") in candidate.parents,
         "canonical OS-account HOME/sap/candidate provenance differs from independent review")
    origins = receipt.get("input_paths", {})
    origin_kinds = {"a1", "snapshot", "a2", "collector", "wrapper", "fw_common", "tool_lock", *HELPERS}
    need(set(origins) == origin_kinds, "actual collection input origins incomplete")
    origins = {k: origin(v) for k, v in origins.items()}
    need(origins["collector"] == sap / "tools/collect_final.py" and origins["fw_common"] == sap / "tools/fw_common.py" and
         origins["wrapper"] == runner_root / "collect_review_snapshot_v2.py" and
         all(origins[k] == runner_root / name for k, name in HELPERS.items()), "canonical executed collector/sibling/helper paths differ")
    for kind in origin_kinds:
        need(before.get(str(origins[kind])) == pin[HASH_FIELDS[kind]], "executed input missing from exact inventory: " + kind)
    for name, h in runner.items():
        need(before.get(str(runner_root / name)) == h, "transitive helper missing before/after execution: " + name)
    for name in ("inputs/units.json", "wh/state.json", "pipeline/state.json"):
        need(str(sap / name) in before, "required campaign input absent: " + name)
    for unit in units:
        for name in (f"tasks/ARCH-{unit}/work.json", f"fw/units/{unit}.json", f"wt/ARCH-{unit}/REPORT.md"):
            need(str(sap / name) in before, "full unit collection input absent: " + name)
    # Parse a pinned literal; never import/execute the unreviewed A3 code.
    syntax = ast.parse((root / "runner/runner_bootstrap.py").read_text())
    launches = [ast.literal_eval(n.value) for n in syntax.body if isinstance(n, ast.Assign) and
                any(isinstance(t, ast.Name) and t.id == "COLLECTOR_LAUNCH" for t in n.targets)]
    need(len(launches) == 1 and isinstance(launches[0], str), "reviewed collector bootstrap literal absent")
    python = origin(receipt.get("python_executable"))
    command = [str(python), "-I", "-S", "-B", "-c", launches[0], str(origins["collector"]), str(sap),
               str(candidate), lock["collector_sha256"], lock["fw_common_sha256"]]
    python_hash=receipt.get("python_executable_sha256")
    need(receipt.get("command") == command and isinstance(python_hash,str) and HEX.fullmatch(python_hash) and
         before.get(str(python)) == python_hash,
         "actual isolated collector invocation/interpreter identity differs")
    expected_inputs = {str(sap/name) for name in ("inputs/units.json", "wh/state.json", "pipeline/state.json")}
    expected_inputs.update(str(p) for p in origins.values())
    expected_inputs.update(str(runner_root/name) for name in RUNNER_NAMES)
    expected_inputs.add(str(python))
    for unit in units:
        expected_inputs.update(str(sap/name) for name in (f"tasks/ARCH-{unit}/work.json", f"fw/units/{unit}.json",
                                                         f"wt/ARCH-{unit}/REPORT.md"))
    need(set(before) == expected_inputs, "exact successful collection input path inventory differs")
    need(origin(receipt.get("collector_input_archive_path")) == origin(review["original_collector_input_archive_root"]) and
         origin(receipt["collector_input_archive_path"]) == candidate.parent/"collector-inputs",
         "original raw collector input archive identity differs")
    need(sha_regular(paths["closure_before"]) == sha_regular(paths["closure_after"]),
         "collector data closure before/after bytes differ")
    a1, snapshot, a2 = docs["a1"], docs["snapshot"], docs["a2"]
    for label, document in (("receipt",receipt),("A1",a1),("snapshot",snapshot),("A2",a2)):
        promised(document,label)
    integer(a1.get("source_snapshot",{}).get("units"), "A1.source_snapshot.units",81)
    integer(a1.get("source_snapshot",{}).get("targets"), "A1.source_snapshot.targets",1021)

    need(a1.get("schema") == "sap-a1-pre-a3-current-reconciliation-receipt-v1" and
         a1.get("verdict") == "CONDITIONAL_READY_AS_A3_SOURCE_REPLAY_INPUT" and
         a1.get("remaining_gates",{}).get("A1_full_signoff") is False and
         a1.get("remaining_gates",{}).get("A3_certificate_replay_completed") is False and
         a1.get("policy", {}).get("fw_validator_sha256") == snapshot.get("fw_validator_sha256") == pin["fw_common_sha256"],
         "actual FW validator differs from fresh A1 receipt/snapshot and independent tool pin")
    need(a1["source_snapshot"]["sha256"] == pin["a1_source_snapshot_sha256"] and
         a1["source_snapshot"]["file"] == str(origins["snapshot"]) and
         snapshot.get("schema") == "sap-a1-current-source-snapshot-v1" and
         a1["source_snapshot"]["units_digest"] == snapshot.get("units_digest") and
         a1["source_snapshot"]["wh_state_sha256"] == snapshot.get("wh_state_sha256") and
         before.get(str(sap/"wh/state.json")) == snapshot.get("wh_state_sha256"),
         "fresh A1 source snapshot identity differs")
    need(a2.get("schema") == "a2-current-81-source-attestation-v1" and a2.get("status") == "READ_ONLY_MATCH" and
         a2.get("wh_state_sha256") == snapshot.get("wh_state_sha256") and
         type(a2.get("unit_count")) is int and a2["unit_count"] == 81 and
         type(a2.get("target_count")) is int and a2["target_count"] == 1021 and
         len(a2.get("units", [])) == len({u["unit"] for u in a2["units"]}) == 81, "A2 exact real scope differs")
    attested = {u["unit"]: u for u in a2["units"]}
    need(set(attested) == set(units) == set(docs["source"]) == set(snapshot.get("units",{})) and
         type(snapshot.get("unit_count")) is int and snapshot["unit_count"] == 81 and
         type(snapshot.get("target_count")) is int and snapshot["target_count"] == 1021,
         "A1/A2/collection/current unit sets differ")
    for unit, data in units.items():
        observed = docs["source"][unit]
        need(observed == {k: attested[unit][k] for k in ("source_sha256", "manifest_sha256", "comparator_config_sha256", "certificate_sha256")},
             "attestation/collection unit identity differs: " + unit)
        need(observed["source_sha256"] == data["source_sha256"] and observed["manifest_sha256"] == data["manifest_sha256"] and
             observed["comparator_config_sha256"] == data["comparator_sha256"] and observed["certificate_sha256"] == data["certificate_sha256"],
             "real current unit differs from admitted collection: " + unit)
        own=snapshot["units"][unit]["arch_source_files_sha256"]
        need(snapshot["units"][unit]["arch_source_path"] == str(sap/"wt"/("ARCH-"+unit)/"SAP"/unit) and
             all(own.get(name) == observed[key] for name,key in (
                 ("manifest.json","manifest_sha256"),("comparator.json","comparator_config_sha256"),
                 ("verification/comparator-result.json","certificate_sha256"))),
             "fresh A1 canonical unit origin/manifest/config/certificate differs: "+unit)
        own_lean={f"SAP/{unit}/{name}":h for name,h in own.items() if name.endswith(".lean") and
                  not name.startswith(("review/","verification/"))}
        need(own_lean == data["source_sha256"],"fresh A1 exact Lean source differs: "+unit)
    decisions = {}
    for data in units.values():
        for row in data["rows"]:
            decisions[row["decision"]] = decisions.get(row["decision"],0)+1
    for label, counts in (("receipt.decisions",receipt.get("decisions")),("snapshot.decisions",snapshot.get("decisions")),
                          ("A1.source_snapshot.decisions",a1["source_snapshot"].get("decisions"))):
        decision_counts(counts,label,decisions)
    manifests = exact_candidate_counts(source, units, snapshot, load)
    archive_hash = closure_data.validate(root/"collector-inputs",closure,sap,units,
        {k:pin[k] for k in ("collector_sha256","fw_common_sha256")},before,snapshot,manifests,load,hashed)
    need(archive_hash == pin.get("collection_input_archive_sha256") == receipt.get("collection_input_archive_sha256"),
         "raw collector input archive digest differs")
    collection_layout(source,units)
    exact_collection_tree(source, docs["inventory"])
    # A3 inventory.tree_rows orders Path components, unlike ordinary work snapshots.
    content = hashed(sorted(tree_rows(source), key=lambda row: PurePosixPath(row["path"])))
    need(pin["candidate_content_sha256"] == receipt.get("candidate_content_sha256") == content and
         type(receipt.get("collected_file_count")) is int and receipt["collected_file_count"] == len(docs["inventory"]),
         "entire collection content/count differs")
    theorem_count = sum(len(d["names"]) for d in units.values())
    validate_collection_log(paths["log"].read_bytes().decode("utf-8"), theorem_count, receipt, closure, snapshot, docs["inventory"])
    check_path, contract_path = root / "a3-admission-check.json", root / "approved-contract-inventory.json"
    check, contract = load(check_path), load(contract_path)
    need(set(check) == RESULT_FIELDS, "closed actual admission result required")
    promised(check,"admission_result"); promised(contract,"contract_inventory")
    integer(check.get("unit_count"),"admission_result.unit_count",81)
    integer(check.get("target_count"),"admission_result.target_count",1021)
    decision_counts(check.get("decisions"),"admission_result.decisions",decisions)
    need(all(check.get(k) == pin.get(k) for k in ("collection_input_archive_sha256", "collection_input_closure_before_sha256", "collection_input_closure_after_sha256")),
         "actual admission result closure identity differs")
    need(check.get("schema") == "a3-collection-admission-result-v3" and check.get("status") == "accepted_for_freeze_input_only" and
         type(check.get("unit_count")) is int and check["unit_count"] == 81 and
         type(check.get("target_count")) is int and check["target_count"] == 1021 and
         check.get("pin_sha256") == sha_regular(paths["pin"]) and check.get("candidate_content_sha256") == content and
         check.get("a1_receipt_sha256") == pin["a1_receipt_sha256"] and
         check.get("collection_receipt_sha256") == pin["collection_receipt_sha256"] and
         check.get("collection_inventory_sha256") == pin["collection_inventory_sha256"] and
         check.get("reviewed_tool_lock_sha256") == pin["reviewed_tool_lock_sha256"] and
         check.get("fw_common_sha256") == pin["fw_common_sha256"] and
         check.get("runner_content_sha256") == pin["runner_content_sha256"] and
         sha_regular(contract_path) == pin["contract_inventory_sha256"] == check.get("contract_inventory_sha256") and
         contract.get("schema") == "a3-approved-contract-inventory-v1" and
         contract.get("candidate_content_sha256") == content and contract.get("a1_receipt_sha256") == pin["a1_receipt_sha256"],
         "independently reviewed A3 admission result/contract identity differs")
    for supplied, archived in ((args.attestation, paths["a2"]), (args.collection_receipt, paths["receipt"]),
                               (args.collected_file_inventory, paths["inventory"]), (args.routes, root / "target-routes.json")):
        need(sha_regular(supplied) == sha_regular(archived), "supplied receipt/attestation/routes/inventory identity differs from parent pin")
    return {"independently-expected-admission-result.json": getattr(args,"expected_admission_result_sha256"),
            "independently-expected-reviewed-tool-lock.json": getattr(args,"expected_reviewed_tool_lock_sha256"),
            "independently-expected-admission-pin.json": getattr(args,"expected_admission_pin_sha256"),
            "collector-input-archive-content":archive_hash,
            "independent-parent-admission-review.json": expected,
            "admission-evidence-inventory": hashed(review["files_sha256"]),
            "actual-successful-collection-receipt.json": pin["collection_receipt_sha256"],
            "independently-expected-attestation.json": pin["a2_source_attestation_sha256"]}


def exact_candidate_counts(source, units, snapshot, load):
    from work_package import MARKERS
    index = load(Path(source)/"SAP/INDEX.json")
    need(set(index) == set(units), "candidate INDEX unit scope differs")
    manifests = {}
    target_ids = []
    for unit, data in units.items():
        base = Path(source)/"SAP"/unit
        manifest = load(base/"manifest.json")
        rows = manifest if isinstance(manifest,list) else manifest.get("targets")
        need(isinstance(rows,list), "candidate manifest rows required")
        manifests[unit] = rows
        ids = [r["target_id"] for r in rows]
        keys = {r.get("theorem") or "OMIT."+r["target_id"]:r["target_id"] for r in rows}
        need(len(ids)==len(set(ids))==len(keys), "E2 duplicate target/theorem/OMIT ownership")
        reviews = load(base/"verification/declaration-review.json")
        need(set(reviews)==set(keys) and all(reviews[k].get("target_id")==tid for k,tid in keys.items()),
             "E2 exact review key/target alignment differs")
        target_ids.extend(ids)
        counts = {}
        for r in rows: counts[r["decision"]] = counts.get(r["decision"],0)+1
        info = index[unit]
        promised(info,"INDEX."+unit); promised(snapshot["units"][unit],"snapshot.units."+unit)
        integer(info.get("targets"),"INDEX."+unit+".targets",len(rows))
        if "theorems" in info: integer(info["theorems"],"INDEX."+unit+".theorems",len(data["names"]))
        if "items_reviewed" in info: integer(info["items_reviewed"],"INDEX."+unit+".items_reviewed",len(rows))
        decision_counts(info.get("decisions"),"INDEX."+unit+".decisions",counts)
        decision_counts(snapshot["units"][unit].get("decisions"),"snapshot.units."+unit+".decisions",counts)
        cert=load(base/"verification/comparator-result.json")
        promised(cert,"certificate."+unit)
        need(set(cert.get("targets",{})) == {"listed","certified","omitted"}, "certificate target counters absent")
        for name,expected in (("listed",len(rows)),("certified",len(data["names"])),("omitted",len(rows)-len(data["names"]))):
            integer(cert["targets"][name],"certificate."+unit+".targets."+name,expected)
        need(cert.get("accepted") is True and cert.get("control") is False and
             set(cert.get("markers",{})) == set(MARKERS) and all(v is True for v in cert["markers"].values()),
             "certificate literal success/kernel markers required")
        steps=cert.get("steps")
        need(isinstance(steps,list) and len(steps)==len({step.get("step") for step in steps}) and
             {step.get("step") for step in steps} >= {"rebuild-from-snapshot","export-challenge","export-solution","comparator"} and
             all(type(step.get("rc")) is int and step["rc"]==0 for step in steps),
             "certificate strict successful exits required")
    need(len(target_ids)==len(set(target_ids))==1021, "candidate exact 1021 target inventory differs")
    return manifests
