"""Data-only joins for the final producer's explicitly reviewed data-v2 model.

No archived Python is imported or executed. The externally expected actual
admission result authenticates the producer's full dependency-selection replay;
these checks additionally verify exact raw bytes, memberships and relational
joins. They do not claim an independent reimplementation of that producer.
"""
import fnmatch
import json
from pathlib import Path, PurePosixPath
import re

from boundaries import need, tree_rows
from counts import integer
from _palomar_installation import blobs

HEX = re.compile(r"[a-f0-9]{64}\Z")
MODEL = "collect_final+fw_common/data-v2"
PROTOCOL = json.loads(blobs["scripts/PROTOCOL.json"])
ASSURE_TASKS = PROTOCOL["review_layout_rules"]["assure_exact_by_unit"]
STABILITY_SCOPE = {"model": MODEL, "observed": "selected-file-bytes-and-examined-directory-membership",
                   "unobserved": ["unselected-file-contents", "tmux-and-process-session-state",
                                  "OS-and-standard-library-runtime", "restored-transient-mutations"]}
FIELDS = {"schema", "read_model", "sap_root", "units", "code_hashes", "files", "directories",
          "selectors", "review_references", "roots"}
need(PROTOCOL["schema"] == "a3-admission-protocol-description-v3" and
     PROTOCOL["data_read_model"] == MODEL and PROTOCOL["stability_scope"] == STABILITY_SCOPE,
     "reviewed protocol description/model differs")


def review_directory(sap, unit, finding):
    """Location eligibility only; never source, review or approval authority."""
    need(isinstance(finding, str), "noncanonical/external review reference")
    p = PurePosixPath(finding)
    need(p.is_absolute() and p.is_relative_to(sap) and ".." not in p.parts and str(p) == finding,
         "noncanonical/external review reference")
    relative(p.name)
    root = p.parent.relative_to(sap).as_posix()
    need(re.fullmatch(r"tasks/FW-" + re.escape(unit) + r"-r[1-9][0-9]*(?:g[1-9][0-9]*)?", root) or
         re.fullmatch(r"opusrev/" + re.escape(unit) + r"/o[1-9][0-9]*", root) or
         root in ASSURE_TASKS.get(unit, []), "unsupported same-unit review task layout")
    return root, p.relative_to(sap).as_posix()


def latest_reviews(meta, key):
    current = meta["current"][key]
    rows = meta.get("reviews", {}).get(key)
    if rows is None:
        return []
    if isinstance(rows, dict):
        need(all(isinstance(r, dict) for r in rows.values()), "FW review metadata missing")
        rows = [dict(r, round=r.get("round", r.get("n", 1))) for r in rows.values()]
    need(isinstance(rows, list) and all(isinstance(r, dict) for r in rows), "FW review metadata missing")
    rows = [r for r in rows if r.get("fp") == current["fp"]]
    for row in rows:
        integer(row.get("round"), "FW review round")
    if not rows:
        return []
    last = max(r["round"] for r in rows)
    selected = [r for r in rows if r["round"] == last]
    need(all("clean" in r for r in selected), "missing current FW clean metadata")
    # Match passing(): an adverse latest row suppresses the whole latest group.
    # A selected truthy nonboolean still fails bound_review's literal-true gate.
    return selected if all(r["clean"] for r in selected) else []


def current_packet(pk, target, manifest, omitted, hashed):
    given = {"target_id": target["target_id"], "canonical_claim": target["canonical_claim"]}
    if omitted:
        given.update({k: target.get(k) for k in ("no_lean", "rows", "coverage_judgments")})
    record = {k: v for k, v in manifest.items() if k not in ("proof_status", "proof_plan", "axioms")}
    return hashed({"citation": pk.get("citation"), "standing_assumptions": pk.get("standing_assumptions"),
                   "target": given, "record": record})


def relative(name):
    need(isinstance(name, str) and name and not name.startswith("/") and "\\" not in name and "\x00" not in name and
         all(part not in {"", ".", ".."} for part in name.split("/")) and PurePosixPath(name).as_posix() == name,
         "unsafe closure relative path")
    return name


def schema(closure):
    need(isinstance(closure, dict) and set(closure) == FIELDS and
         closure["schema"] == "sap-collector-data-closure-v1" and closure["read_model"] == MODEL,
         "closed collector data closure schema required")
    need(isinstance(closure["files"], dict) and closure["files"], "complete raw closure file inventory required")
    for name, row in closure["files"].items():
        relative(name)
        need(isinstance(row, dict) and set(row) == {"sha256", "bytes", "mode"} and
             isinstance(row["sha256"], str) and HEX.fullmatch(row["sha256"]) and row["mode"] in {"100644", "100755"},
             "malformed raw closure file record: " + name)
        integer(row["bytes"], "closure.files." + name + ".bytes")
    return closure["files"]


def validate(archive, closure, sap, units, code_hashes, inputs, a1_snapshot, manifests, load, hashed):
    files = schema(closure)
    need(closure["sap_root"] == str(sap) and closure["units"] == sorted(units) and
         closure["code_hashes"] == code_hashes, "closure origin/unit/code identity differs")
    actual_rows = tree_rows(archive)
    actual = {r["path"]: {k: r[k] for k in ("sha256", "bytes", "mode")} for r in actual_rows}
    need(actual == files, "exact raw collector-inputs file/size/mode inventory differs")
    occupied = {str(parent) for name in files for parent in PurePosixPath(name).parents if str(parent) != "."}
    actual_dirs = {p.relative_to(archive).as_posix() for p in Path(archive).rglob("*") if p.is_dir()}
    need(actual_dirs == occupied, "raw collector-inputs has untracked empty or missing directories")
    directories = closure["directories"]
    need(isinstance(directories, dict), "closure directory inventory required")
    for root, members in directories.items():
        relative(root)
        need(members is None or isinstance(members, dict), "closure membership must be object or null")
        if members is not None:
            need(all(relative(n) == n and "/" not in n and kind in {"file", "directory"}
                     for n, kind in members.items()), "invalid closure member name/type")
        parent, leaf = str(PurePosixPath(root).parent), PurePosixPath(root).name
        if parent in directories:
            record = directories[parent]
            need((record is None or leaf not in record) if members is None else
                 record is not None and record.get(leaf) == "directory", "inconsistent closure nested directory membership")
    for name in files:
        parts = PurePosixPath(name).parts
        for i in range(1, len(parts)):
            parent, child = "/".join(parts[:i]), parts[i]
            if parent in directories:
                record = directories[parent]
                wanted = "file" if i == len(parts)-1 else "directory"
                need(record is not None and record.get(child) == wanted,
                     "selected raw file contradicts recorded directory membership: " + name)
    selectors = closure["selectors"]
    need(isinstance(selectors, dict), "closure selectors required")
    for key, matches in selectors.items():
        need(isinstance(key, str) and key.count("|") == 1, "malformed closure selector")
        root, selection = key.split("|")
        relative(root)
        need(selection.startswith(("glob:", "rglob:")), "unsupported closure selector")
        recursive = selection.startswith("rglob:")
        pattern = selection.split(":", 1)[1]
        need(pattern in {"*.lean", "REPORT*.md", "findings*.json"}, "unreviewed closure selector pattern")
        def selected(directory):
            need(directory in directories, "selector omitted examined directory membership")
            members = directories[directory]
            result = []
            for leaf, kind in (members or {}).items():
                child = directory + "/" + leaf
                if fnmatch.fnmatchcase(leaf, pattern):
                    need(kind == "file", "selector matched a directory")
                    result.append(child)
                if recursive and kind == "directory":
                    result.extend(selected(child))
            return result
        need(isinstance(matches, list) and matches == sorted(set(selected(root))) and all(n in files for n in matches),
             "closure selector selection differs from exact recorded membership")
    roots = sorted(set(directories) | {str(PurePosixPath(n).parent) for n in files})
    need(closure["roots"] == roots, "closure protected roots differ from exact observed roots")
    need(all(name in files for name in ("inputs/units.json","pipeline/state.json","wh/state.json")),
         "required raw campaign input class absent")
    for origin, h in inputs.items():
        p = PurePosixPath(origin)
        if p.is_relative_to(sap):
            name = p.relative_to(sap).as_posix()
            if name in files:
                need(files[name]["sha256"] == h, "raw closure/flat input join differs: " + name)
    for unit in units:
        prefix = "wt/ARCH-" + unit + "/SAP/" + unit + "/"
        own = {name[len(prefix):]: row["sha256"] for name, row in files.items() if name.startswith(prefix)}
        need(own == a1_snapshot["units"][unit]["arch_source_files_sha256"], "raw complete ARCH/A1 source join differs: " + unit)
        for name in (f"wt/ARCH-{unit}/REPORT.md", f"tasks/ARCH-{unit}/work.json", f"fw/units/{unit}.json"):
            need(name in files, "required raw input class absent: " + name)
        prep = f"fw/prep/{unit}/SAP/{unit}"
        need(prep in directories and directories[prep] is not None, "FW prep membership absent: " + unit)
        for part in ("Defs", "Challenge"):
            direct = prep + "/" + part + ".lean"
            if directories[prep].get(part + ".lean") == "file":
                need(direct in files, "selected FW prep bytes absent")
            need(prep + "/" + part + "|rglob:*.lean" in selectors, "FW prep selector absent")
    need(files.get("wh/state.json", {}).get("sha256") == a1_snapshot["wh_state_sha256"], "raw WH/A1 identity differs")
    def document(name):
        need(name in files, "selected review raw dependency absent: " + name)
        return load(Path(archive) / name)

    def source_files(root, unit):
        base = root + "/SAP/" + unit
        need(base in directories and directories[base] is not None, "review source membership absent: " + base)
        selected = []
        for part in ("Defs", "Challenge"):
            direct = base + "/" + part + ".lean"
            if part + ".lean" in directories[base]:
                need(directories[base][part + ".lean"] == "file" and direct in files,
                     "selected review source bytes absent")
                selected.append(direct)
            selector = base + "/" + part + "|rglob:*.lean"
            need(selector in selectors, "review source selector absent")
            selected.extend(selectors[selector])
        return {name[len(root)+1:]: files[name]["sha256"] for name in selected}

    packets = {}
    def task_packets(root, unit):
        if root not in packets:
            claims, records = document(root + "/claims.json"), document(root + "/record.json")
            need(isinstance(claims, dict) and isinstance(claims.get("targets"), list) and isinstance(records, list),
                 "selected review claims/record shape differs")
            need(claims.get("unit_id", unit) == unit and claims.get("unit", unit) == unit,
                 "selected review unit metadata differs")
            targets = claims["targets"]
            need(all(isinstance(r, dict) for r in targets + records), "selected review packet row is not an object")
            tids, rids = [r.get("target_id") for r in targets], [r.get("target_id") for r in records]
            need(all(isinstance(t, str) for t in tids + rids) and len(tids) == len(set(tids)) and
                 len(rids) == len(set(rids)) and set(tids) == set(rids), "selected review packet target inventory differs")
            by = {r["target_id"]: r for r in records}
            packets[root] = {t["target_id"]: hashed({"citation": claims.get("citation"),
                "standing_assumptions": claims.get("standing_assumptions"), "target": t, "record": by[t["target_id"]]})
                for t in targets}
        return packets[root]

    def finding_identity(name, key, current):
        findings = document(name)
        findings = [findings] if isinstance(findings, dict) else findings
        need(isinstance(findings, list), "selected review findings shape differs")
        matches = [r for r in findings if isinstance(r, dict) and "theorem" in r and
                   (r["theorem"] if r["theorem"] is not None else "OMIT." + str(r.get("target_id"))) == key]
        need(len(matches) == 1, "selected review findings key/duplicate binding differs")
        row = matches[0]
        need(row.get("target_id") == current["target_id"] and row.get("fingerprint") == current["fp"] and
             row.get("theorem") == (None if key.startswith("OMIT.") else key),
             "selected review findings target/fingerprint binding differs")
        need(row.get("verdict") == ("omission_ok" if key.startswith("OMIT.") else "faithful") and
             row.get("severity") == "none" and row.get("issues") == [], "selected review findings do not revalidate clean")

    def copied_observations(root):
        need(root in directories and directories[root] is not None and
             root + "|glob:REPORT*.md" in selectors and root + "/scratch|glob:*.lean" in selectors,
             "current declaration report/scratch selectors absent")
        for leaf in ("REPORT.md", "reading.md", "claim-stage.json", "closure.json", "earlier.json"):
            if leaf in directories[root]:
                need(directories[root][leaf] == "file" and root + "/" + leaf in files,
                     "current declaration optional selected bytes absent")

    refs = closure["review_references"]
    need(isinstance(refs, dict) and set(refs) == set(units), "closure review-reference unit inventory differs")
    for unit in units:
        meta = document(f"fw/units/{unit}.json")
        rows = manifests[unit]
        targets = {r.get("theorem") or "OMIT." + r["target_id"]: r["target_id"] for r in rows}
        need(isinstance(meta.get("prep"), dict) and set(meta.get("current", {})) == set(targets) and
             isinstance(refs[unit], dict) and set(refs[unit]) == set(targets), "FW/closure exact target review keys differ")
        prep = meta["prep"]
        src = source_files("wt/ARCH-" + unit, unit)
        src_digest = hashed(sorted(src.items())) if src else None
        need(src and source_files("fw/prep/" + unit, unit) == src == prep.get("files") and
             prep.get("src_digest") == src_digest, "FW prep/source digest binding differs")
        cert = document(f"wt/ARCH-{unit}/SAP/{unit}/verification/comparator-result.json")
        need(isinstance(prep.get("base"), dict) and all(prep["base"].get(k) == (cert.get("base") or {}).get(k)
             for k in ("repo2_head", "lean_path_sha256")), "FW prep/certificate base differs")
        pk = document(f"tasks/ARCH-{unit}/work.json")
        need(isinstance(pk.get("targets"), list) and all(isinstance(t, dict) for t in pk["targets"]),
             "ARCH packet targets are missing")
        by_id = {t["target_id"]: t for t in pk["targets"]}
        need(len(by_id) == len(pk["targets"]) and set(targets.values()).issubset(by_id), "ARCH packet target inventory differs")
        by_manifest = {r["target_id"]: r for r in rows}
        copied_tasks = []
        unit_passes = True
        # JSON insertion order matters: first task basename wins in the collector.
        for key, current in meta["current"].items():
            tid = targets[key]
            need(isinstance(current, dict) and current.get("target_id") == tid and
                 isinstance(current.get("fp"), str) and HEX.fullmatch(current["fp"]), "FW current target/fingerprint differs")
            packet = current_packet(pk, by_id[tid], by_manifest[tid], current.get("omitted"), hashed)
            need(prep.get("packets", {}).get(key) == packet, "current packet differs from FW prep")
            expected = []
            for row in latest_reviews(meta, key):
                root, name = review_directory(sap, unit, row.get("file"))
                need(row.get("binding") == "v2", "selected review metadata binding is not v2")
                need(source_files(root, unit) == src and row.get("src_digest") == src_digest,
                     "selected review source/digest binding differs")
                actual_packets = task_packets(root, unit)
                need(tid in actual_packets and actual_packets[tid] == row.get("pkt") == packet,
                     "selected review packet/digest binding differs")
                need(row.get("base") == prep["base"], "selected review dependency base differs")
                need(row.get("fp") == row.get("given_fp") == current["fp"], "selected review fingerprint metadata differs")
                need(row.get("clean") is True, "selected review clean metadata is not a boolean true")
                finding_identity(name, key, current)
                expected.append(name)
                copied_tasks.append((root, key, current))
            if not expected:
                unit_passes = False
            need(refs[unit][key] == sorted(set(expected)), "closure/current latest review references differ")
        if not unit_passes:
            # Full successful collection/admission is an independent obligation.
            # Adverse units have no task-report/CHFID copy phase in the read model.
            continue
        destinations = {}
        for root, key, current in copied_tasks:
            destination = PurePosixPath(root).name
            if destination not in destinations:
                destinations[destination] = root
                copied_observations(root)
            copied = destinations[destination]
            need(task_packets(copied, unit).get(current["target_id"]) == prep["packets"][key],
                 "copied review packet binding differs")
            finding_identity(copied + "/findings.json", key, current)
        for side in "ab":
            root = "tasks/CHFID-" + unit + "-" + side
            need(root in directories and root + "|glob:findings*.json" in selectors and root + "|glob:REPORT*.md" in selectors,
                 "CHFID examined membership/selectors absent")
            for leaf in ("reading.md", "claim-stage.json"):
                if (directories[root] or {}).get(leaf) == "file":
                    need(root + "/" + leaf in files, "CHFID optional selected bytes absent")
    # A3 raw-archive identity uses producer Path-component order, with no LF.
    # Keep boundaries.tree_rows' ordinary work-snapshot ordering unchanged.
    return hashed(sorted(actual_rows, key=lambda row: PurePosixPath(row["path"])))
