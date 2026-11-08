"""Pure structural checks and deterministic rendering for compositional work entries.

This is an adapter for the existing unit package, not a replacement for collect_final,
semantic review, Lean, Comparator, or A3. No source declarations are rewritten.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True

import collections
import hashlib
import json
import re
from pathlib import Path
from boundaries import Invalid, exact_collection_tree, collection_layout
from counts import promised

VERSION = "palomar-work-entries-v4"
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
MARKERS = ["con-ron kernel accepts the solution", "nanoda kernel accepts the solution",
           "Lean default kernel accepts the solution", "Your solution is okay!"]
EXTERNAL_ROOTS = {"Init", "Std", "Lean", "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets",
                  "ImportGraph", "LeanSearchClient", "Plausible", "Lake"}
DECISIONS = {"whole", "restricted", "refuted", "omitted"}


def require(condition, message):
    if not condition:
        raise Invalid(message)


def read_json(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), f"missing regular input: {path}")
    try:
        def unique(pairs):
            out = {}
            for key, value in pairs:
                require(key not in out, f"duplicate JSON key {key!r}: {path}")
                out[key] = value
            return out
        def nonjson(value):
            raise Invalid(f"non-JSON constant {value}: {path}")
        return json.loads(path.read_text(), object_pairs_hook=unique, parse_constant=nonjson)
    except (json.JSONDecodeError, UnicodeError) as exc:
        raise Invalid(f"invalid JSON {path}: {exc}") from exc


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def digest(value):
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def sha(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), f"missing regular file: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, ensure_ascii=False, indent=2) + "\n").encode()


def key(value):
    return [int(x) if x.isdigit() else x for x in re.split(r"(\d+)", value)]


def in_module(module, prefix):
    return module == prefix or module.startswith(prefix + ".")


def source_files(source, unit):
    base = source / "SAP" / unit
    require(base.is_dir(), f"missing unit source: {base}")
    return {str(p.relative_to(source)): sha(p) for p in sorted(base.rglob("*.lean"))
            if not {"verification", "review"}.intersection(p.relative_to(base).parts)}


def strip_comments(text):
    """Remove nested Lean comments; preserve strings so imports can reject odd syntax.

    Also used for token scans, with strings removed separately. Unlike the old runner's
    regex this handles nested block comments and comment markers inside string literals.
    """
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        c, two = text[i], text[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1; out.extend("  "); i += 2; continue
            if two == "-/":
                depth -= 1; out.extend("  "); i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if quoted:
            out.append(c); i += 1
            if c == "\\" and i < len(text):
                out.append(text[i]); i += 1
            elif c == '"':
                quoted = False
            continue
        if two == "/-":
            depth = 1; out.extend("  "); i += 2; continue
        if two == "--":
            j = text.find("\n", i)
            if j < 0:
                out.extend(" " * (len(text) - i)); break
            out.extend(" " * (j - i)); i = j; continue
        quoted = c == '"'
        out.append(c); i += 1
    require(depth == 0 and not quoted, "unclosed Lean comment or string")
    return "".join(out)


def imports(text):
    out = []
    for line in strip_comments(text).splitlines():
        parts = line.strip().split()
        if not parts or parts[0] != "import":
            continue
        require(len(parts) > 1, "empty import")
        for name in parts[1:]:
            require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name), f"unsupported import syntax: {line}")
            out.append(name)
    return out


def scan_tokens(module, text):
    code = re.sub(r'"(?:\\.|[^"\\])*"', '""', strip_comments(text))
    for tok in ("admit", "axiom", "native_decide", "implemented_by", "unsafe", "opaque"):
        require(not re.search(rf"\b{tok}\b", code), f"forbidden token {tok}: {module}")
    challenge = bool(re.match(r"^SAP\.[^.]+\.Challenge(?:\.|$)", module))
    require(challenge or not re.search(r"\bsorry\b", code), f"sorry outside unit Challenge: {module}")


def manifest_rows(value, where):
    rows = value if isinstance(value, list) else value.get("targets") if isinstance(value, dict) else None
    require(isinstance(rows, list), f"manifest must be list or targets object: {where}")
    return rows


def check_manifest(rows, work, unit=None):
    ids, names = [], []
    for row in rows:
        tid = row.get("target_id")
        require(isinstance(tid, str) and re.fullmatch(rf"{work}-T[1-9][0-9]*", tid), f"bad target ID: {tid}")
        ids.append(tid)
        decision, theorem = row.get("decision"), row.get("theorem")
        require(decision in DECISIONS, f"{tid}: unknown decision {decision}")
        if decision == "omitted":
            require(theorem is None, f"{tid}: omission names a theorem")
            require(row.get("proof_status") in (None, "omitted"), f"{tid}: omission claims a proof")
            require(any(row.get(x) for x in ("restriction", "rows_not_used", "notes", "reason")),
                    f"{tid}: omission without a reason")
            continue
        require(isinstance(theorem, str) and theorem, f"{tid}: missing theorem")
        if unit:
            require(theorem.startswith(f"SAP.{unit}."), f"{tid}: wrong theorem namespace")
        require(row.get("proof_status") == "proved", f"{tid}: theorem is not proved")
        require(decision != "restricted" or row.get("restriction"), f"{tid}: undisclosed restriction")
        require(isinstance(row.get("axioms"), list) and set(row["axioms"]) <= AXIOMS,
                f"{tid}: absent/forbidden recorded axioms")
        names.append(theorem)
    require(len(ids) == len(set(ids)), f"duplicate target in {work}/{unit}")
    require(len(names) == len(set(names)), f"duplicate theorem in {work}/{unit}")
    return ids, names


def config(challenge, solution, names):
    return {"challenge_module": challenge, "solution_module": solution,
            "theorem_names": names, "definition_names": [],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "external_kernels": {"con-ron": ["con-ron", "--verified", "--jobs=2"], "nanoda": ["nanoda_bin"]}}


def check_config(cfg, challenge, solution, names):
    require(cfg.get("challenge_module") == challenge and cfg.get("solution_module") == solution,
            "comparator root mismatch")
    require(sorted(cfg.get("theorem_names", [])) == sorted(names), "comparator theorem inventory mismatch")
    require(len(set(cfg["theorem_names"])) == len(cfg["theorem_names"]) and names,
            "empty or duplicate comparator theorem inventory")
    require(cfg.get("definition_names", []) == [], "definition_names must be empty; closure is checked by Comparator")
    require(sorted(cfg.get("permitted_axioms", [])) == sorted(AXIOMS), "permitted axiom inventory mismatch")
    ek = cfg.get("external_kernels", {})
    cr = ek.get("con-ron", [])
    require(cr and cr[0] == "con-ron" and "--verified" in cr and ek.get("nanoda") == ["nanoda_bin"],
            "external kernel configuration mismatch")
    require(not cfg.get("enable_nanoda"), "use the external NanoDa kernel")


def review_evidence(source, unit, rows, cert):
    """Check the exported evidence, without inventing missing FW binding inputs.

    Exported reviews lack some original prep/base/closure-fingerprint fields. Full
    fingerprint revalidation belongs to the fresh normal collector, not this adapter.
    """
    base = source / "SAP" / unit
    dr = read_json(base / "verification/declaration-review.json")
    claims = read_json(base / "verification/claims.json")
    expected = {r["theorem"] if r.get("theorem") else "OMIT." + r["target_id"]: r for r in rows}
    require(set(dr) == set(expected), f"{unit}: review inventory mismatch, including omissions")
    ct = claims.get("targets", [])
    require(len(ct) == len({r["target_id"] for r in ct}) and
            {r["target_id"] for r in ct} == {r["target_id"] for r in rows}, f"{unit}: claims inventory mismatch")
    require(claims.get("unit_id") == unit, f"{unit}: claims unit mismatch")
    canonical_claims = {r["target_id"]: r["canonical_claim"] for r in ct}
    files, records = {}, {}
    for item, row in expected.items():
        e = dr[item]
        require(e.get("target_id") == row["target_id"] and e.get("decision") == row["decision"],
                f"{unit}/{item}: review target or decision mismatch")
        fp = e.get("fingerprint", "")
        require(re.fullmatch(r"[0-9a-f]{64}", fp) is not None, f"{item}: bad review fingerprint")
        rs = e.get("reviews")
        require(isinstance(rs, list) and rs, f"{item}: no reviews")
        paths = []
        for rv in rs:
            rel = Path(rv.get("files", ""))
            require(not rel.is_absolute() and ".." not in rel.parts and rel.parts[:2] == ("review", "declarations"),
                    f"{item}: unsafe review evidence path")
            td = base / rel
            findings = read_json(td / "findings.json")
            findings = findings if isinstance(findings, list) else [findings]
            keys = [f.get("theorem") or "OMIT." + f.get("target_id", "") for f in findings]
            require(len(keys) == len(set(keys)), f"{item}: duplicate findings")
            found = [f for f in findings if (f.get("theorem") or "OMIT." + f.get("target_id", "")) == item]
            require(len(found) == 1, f"{item}: missing findings entry")
            f = found[0]
            verdict = "omission_ok" if row["decision"] == "omitted" else "faithful"
            require(f.get("target_id") == row["target_id"] and f.get("fingerprint") == fp and
                    f.get("verdict") == verdict and f.get("severity") == "none" and f.get("issues") == [],
                    f"{item}: findings are stale or unclean")
            require(rv.get("binding") == "v2" and rv.get("verdict") == verdict and rv.get("severity") == "none",
                    f"{item}: exported review is not clean v2")
            packet = read_json(td / "claims.json")
            recs = read_json(td / "record.json")
            require(isinstance(recs, list), f"{item}: bad review record")
            tids = [t["target_id"] for t in packet.get("targets", [])]
            rids = [r["target_id"] for r in recs]
            require(len(tids) == len(set(tids)) and len(rids) == len(set(rids)) and set(tids) == set(rids),
                    f"{item}: ambiguous review packet")
            pc = [t for t in packet["targets"] if t["target_id"] == row["target_id"]]
            require(len(pc) == 1 and pc[0].get("canonical_claim") == canonical_claims[row["target_id"]],
                    f"{item}: reviewed canonical claim mismatch")
            require(all(packet.get(x) == claims.get(x) for x in ("citation", "standing_assumptions")),
                    f"{item}: reviewed standing assumptions mismatch")
            rc = [r for r in recs if r["target_id"] == row["target_id"]]
            semantic = {k: v for k, v in row.items() if k not in ("proof_status", "proof_plan", "axioms")}
            require(len(rc) == 1 and rc[0] == semantic, f"{item}: reviewed manifest packet mismatch")
            for p in sorted(td.rglob("*")):
                if p.is_file():
                    files[str(p.relative_to(source))] = sha(p)
            paths.append(str(td.relative_to(source)))
        records[item] = {"target_id": row["target_id"], "fingerprint": fp, "evidence": paths}
    for p in (base / "verification").iterdir():
        if p.is_file():
            files[str(p.relative_to(source))] = sha(p)
    return {"status": "exported_evidence_consistent_not_full_fw_rebinding", "items": records, "files_sha256": files}


def load_units(source, catalog, attestation=None, routes=None):
    require(source.is_dir(), f"source snapshot absent: {source}; no RC fallback is permitted")
    idx = read_json(source / "SAP/INDEX.json")
    require(isinstance(idx, dict) and idx, "missing or empty unit index")
    att = {u["unit"]: u for u in attestation["units"]} if attestation else None
    if att is not None:
        require(len(att) == len(attestation["units"]) and set(att) == set(idx), "attested unit inventory mismatch")
    out, all_targets, all_names = {}, [], []
    for unit, info in sorted(idx.items()):
        require(re.fullmatch(r"P[0-9]{3}[a-z]?", unit) is not None, f"invalid unit ID: {unit}")
        work = info["work"]
        require(work in catalog, f"{unit}: work absent from formal catalog")
        base = source / "SAP" / unit
        rows = manifest_rows(read_json(base / "manifest.json"), base)
        ids, names = check_manifest(rows, work, unit)
        require(all(type(info.get(k)) is int for k in ("targets", "theorems", "items_reviewed")) and
                all(type(v) is int for v in info.get("decisions", {}).values()) and
                len(ids) == info.get("targets") and len(names) == info.get("theorems") and
                len(ids) == info.get("items_reviewed") and
                dict(collections.Counter(r["decision"] for r in rows)) == info.get("decisions"),
                f"{unit}: stale unit INDEX")
        promised(info,"unit INDEX."+unit)
        cfg = read_json(base / "comparator.json")
        check_config(cfg, f"SAP.{unit}.Challenge", f"SAP.{unit}.Solution", names)
        cert = read_json(base / "verification/comparator-result.json")
        promised(cert,"unit certificate."+unit)
        require(cert.get("accepted") is True and cert.get("control") is False and cert.get("work") == unit,
                f"{unit}: no normal accepted unit certificate")
        require(isinstance(cert.get("markers"), dict) and set(cert["markers"]) == set(MARKERS) and
                all(value is True for value in cert["markers"].values()),
                f"{unit}: certificate missing kernel markers")
        log = (base / "verification/comparator.log").read_text()
        require(all(m in log for m in MARKERS), f"{unit}: comparator log missing markers")
        sources = source_files(source, unit)
        certified_sources = {p: h for p, h in cert.get("snapshot_sha256", {}).items() if p.endswith(".lean")}
        require(sources and sources == certified_sources, f"{unit}: source differs from certified inventory")
        require(sha(base / "manifest.json") == cert.get("manifest_sha256") and
                sha(base / "comparator.json") == cert.get("config_sha256") and cert.get("config") == cfg,
                f"{unit}: certified manifest/config mismatch")
        require(isinstance(cert.get("targets"), dict) and all(type(v) is int for v in cert["targets"].values()) and
                cert.get("targets") == {"listed": len(ids), "certified": len(names), "omitted": len(ids)-len(names)},
                f"{unit}: certified target inventory mismatch")
        require(isinstance(cert.get("steps"), list) and
                all(type(s.get("rc")) is int and s["rc"] == 0 for s in cert["steps"]) and
                len(cert["steps"]) == len({s.get("step") for s in cert["steps"]}) and
                {s.get("step") for s in cert.get("steps", [])} >=
                {"rebuild-from-snapshot", "export-challenge", "export-solution", "comparator"},
                f"{unit}: incomplete certificate steps")
        if att is not None:
            a = att[unit]
            require(a["source_sha256"] == sources and a["certificate_sha256"] == sha(base / "verification/comparator-result.json")
                    and a["manifest_sha256"] == sha(base / "manifest.json") and
                    a["comparator_config_sha256"] == sha(base / "comparator.json"), f"{unit}: current attestation mismatch")
        evidence = review_evidence(source, unit, rows, cert)
        out[unit] = {"work": work, "rows": rows, "names": names, "source_sha256": sources,
                     "manifest_sha256": sha(base / "manifest.json"), "comparator_sha256": sha(base / "comparator.json"),
                     "certificate_sha256": sha(base / "verification/comparator-result.json"),
                     "certificate_stamp": cert["stamp"], "base": cert["base"], "review": evidence}
        all_targets.extend(ids); all_names.extend(names)
    require(len(all_targets) == len(set(all_targets)), "duplicate target across units")
    require(len(all_names) == len(set(all_names)), "duplicate theorem across units / namespace collision")
    expected = [t["id"] for c in catalog.values() for t in c["targets"]]
    require(len(expected) == len(set(expected)) and set(all_targets) == set(expected), "catalog target coverage mismatch")
    for work, cat in catalog.items():
        got = [r["target_id"] for u in out.values() if u["work"] == work for r in u["rows"]]
        require(set(got) == {t["id"] for t in cat["targets"]}, f"{work}: target assigned to wrong work")
    if routes:
        actual = sorted(({"unit": u, "target_id": r["target_id"], "theorem": r.get("theorem"), "decision": r["decision"]}
                         for u, d in out.items() for r in d["rows"]), key=lambda r: r["target_id"])
        expected_routes = sorted(({k: r.get(k) for k in ("unit", "target_id", "theorem", "decision")}
                                  for r in routes["target_rows"]), key=lambda r: r["target_id"])
        require(actual == expected_routes, "current route-plan target/decision/theorem inventory mismatch")
    return out


def verify_collection(source, attestation_path, receipt_path, inventory_path, unit_ids, target_count, *, args=None, units=None):
    """Strict actual collection intake. No self-issued success receipt is authority."""
    require(receipt_path is not None and inventory_path is not None,
            "collected_candidate requires --collection-receipt AND --collected-file-inventory")
    receipt = read_json(receipt_path)
    require(receipt.get("status") == "SOURCE_BOUND_REVIEW_INPUT" and
            type(receipt.get("collector_exit_code")) is int and receipt["collector_exit_code"] == 0 and
            receipt.get("source_and_input_stability") is True,
            "normal collection failed or has no stable successful receipt; partial snapshots are rejected")
    collection_layout(source,unit_ids)
    exact_collection_tree(source, read_json(inventory_path))
    from admission_contract import validate
    return validate(source, args, units, target_count)


def catalogs(catalog_root, site_root):
    index = read_json(catalog_root / "works.json")
    formal, site = {}, {}
    for entry in index:
        work = entry["work_id"]
        require(re.fullmatch(r"P[0-9]{3}", work) and work not in formal, f"duplicate/bad formal work: {work}")
        c = read_json(catalog_root / "works" / f"{work}.json")
        require(c["work_id"] == work and c.get("work") == entry.get("work"), f"{work}: inconsistent work catalog")
        formal[work] = c
    for path in sorted(site_root.glob("*.json")):
        d = read_json(path); work = d["work"]["id"]
        require(path.stem == work and work not in site, f"duplicate site work: {work}")
        site[work] = d
    require(set(formal) <= set(site), "formal work missing from site inventory")
    for work in set(site) - set(formal):
        lean = site[work].get("lean", {})
        require(lean.get("applicable") is False and lean.get("targets") == [] and lean.get("reason"),
                f"unreconciled site-only work: {work}")
    require(formal and site, "empty work catalog")
    return formal, site


def import_graph(source, unit_ids, work, overlay_files, base_source=None):
    modules = {}
    for unit in unit_ids:
        for rel in source_files(source, unit):
            modules[rel[:-5].replace("/", ".")] = (source / rel).read_text()
    for rel, data in overlay_files.items():
        if rel.endswith(".lean") and rel.startswith(f"SAP/Works/{work}/"):
            modules[rel[:-5].replace("/", ".")] = data.decode()
    for mod, text in modules.items():
        if in_module(mod, f"SAP.Works.{work}"):
            require(len(text.splitlines()) <= 300, f"over 300 lines: {mod}")
        scan_tokens(mod, text)
    def closure(root, side):
        seen, active = set(), set()
        def visit(mod):
            require(mod not in active, f"import cycle: {mod}")
            if mod in seen:
                return
            if side in ("Defs", "Challenge"):
                allowed = mod.split(".")[0] in EXTERNAL_ROOTS or in_module(mod, f"SAP.Works.{work}.Defs")
                if side == "Challenge":
                    allowed |= in_module(mod, f"SAP.Works.{work}.Challenge")
                allowed |= any(in_module(mod, f"SAP.{u}.Defs") or
                               (side == "Challenge" and in_module(mod, f"SAP.{u}.Challenge")) for u in unit_ids)
                require(allowed, f"{work}: {side} import leakage: {mod}")
            else:
                require(not re.match(r"^SAP\.(?:Works\.[^.]+|[^.]+)\.(Challenge|Orig)(?:\.|$)", mod),
                        f"{work}: Solution imports Challenge/Orig: {mod}")
            if mod not in modules:
                if mod.startswith("SAP."):
                    raise Invalid(f"{work}: unresolved or cross-work SAP import: {mod}")
                if mod.startswith("AronowAudit.") or mod == "AronowAudit":
                    # Traverse available project sources; never treat an unknown project
                    # module as an external package. Collected SAP-only snapshots may
                    # supply their base through --base-source instead (see CLI).
                    p = (base_source or source) / (mod.replace(".", "/") + ".lean")
                    require(p.is_file(), f"missing base source for static closure: {mod}")
                    modules[mod] = p.read_text()
                else:
                    require(mod.split(".")[0] in EXTERNAL_ROOTS, f"unknown external module: {mod}")
                    seen.add(mod); return
            active.add(mod)
            for dep in imports(modules[mod]):
                visit(dep)
            active.remove(mod); seen.add(mod)
        visit(root)
        return sorted(seen)
    closures = {side: closure(f"SAP.Works.{work}.{side}", side) for side in ("Defs", "Challenge", "Solution")}
    # Every certified Challenge part must load; no hidden orphan Challenge file.
    wanted = {m for m in modules if any(in_module(m, f"SAP.{u}.Challenge") for u in unit_ids)}
    require(wanted <= set(closures["Challenge"]), f"{work}: unimported Challenge module")
    return closures


def render(formal, site, units, source, source_kind, input_hashes, base_source=None):
    """Return an overlay as relative paths -> bytes. Never writes a source tree."""
    files, inventory = {}, []
    def put(path, value):
        files[path] = json_bytes(value) if not isinstance(value, str) else value.encode()
    for work in sorted(site):
        directory = f"SAP/Works/{work}"
        unit_ids = sorted(u for u, v in units.items() if v["work"] == work)
        meta = formal[work]["work"] if work in formal else site[work]["work"]
        row = {"work_id": work, "title": meta["title"], "citation": meta["citation"],
               "formal_catalog_member": work in formal, "unit_ids": unit_ids,
               "entry_directory": directory, "source_kind": source_kind}
        if work not in formal:
            reason = site[work]["lean"]["reason"]
            row.update({"disposition": "not_applicable_per_site_catalog", "reason": reason,
                        "targets": [], "target_count": 0, "theorem_count": 0, "decisions": {},
                        "challenge_module": None, "solution_module": None, "combined_certificate": None})
            put(directory + "/STATUS.json", row)
            put(directory + "/PROVENANCE.json", {"schema": VERSION, "work_id": work,
                "site_catalog_sha256": input_hashes[f"site/{work}.json"],
                "formal_catalog_member": False, "lean": site[work]["lean"]})
            put(directory + "/README.md", f"# {work}: {meta['title']}\n\n{meta['citation']}\n\n"
                f"The site catalog marks Lean as inapplicable. {reason}\n\n"
                "This work has no targets in the frozen formal catalog. It has no Challenge stubs, Solution, "
                "Comparator config, or certificate. This is a recorded applicability decision, not a proved empty package.\n")
            inventory.append(row); continue
        rows = sorted((r for u in unit_ids for r in units[u]["rows"]), key=lambda r: key(r["target_id"]))
        tids, names = check_manifest(rows, work)
        prefix = f"SAP.Works.{work}"
        for side in ("Defs", "Challenge", "Solution"):
            imps = ([prefix + ".Defs"] if side != "Defs" else []) + [f"SAP.{u}.{side}" for u in unit_ids]
            put(directory + f"/{side}.lean", "".join(f"import {m}\n" for m in imps) +
                "\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n\n" +
                f"-- {work}: compositional {side} entry; all declarations stay in their certified unit modules.\n")
        closures = import_graph(source, unit_ids, work, files, base_source)
        cfg = config(prefix + ".Challenge", prefix + ".Solution", names)
        put(directory + "/comparator.json", cfg)
        put(directory + "/manifest.json", rows)
        mapping = []
        for u in unit_ids:
            for r in units[u]["rows"]:
                item = r.get("theorem") or "OMIT." + r["target_id"]
                mapping.append({"target_id": r["target_id"], "unit_id": u, "decision": r["decision"],
                    "theorem": r.get("theorem"), "restriction": r.get("restriction"),
                    "manifest": f"SAP/{u}/manifest.json", "review_item": item,
                    "review_index": f"SAP/{u}/verification/declaration-review.json",
                    "unit_certificate": f"SAP/{u}/verification/comparator-result.json",
                    "recorded_axioms": r.get("axioms"),
                    "omission_disclosure": {k: r[k] for k in ("restriction", "rows_not_used", "notes", "reason")
                                             if k in r} if r["decision"] == "omitted" else None})
        mapping.sort(key=lambda r: key(r["target_id"]))
        row.update({"disposition": "compositional_entries_pending_combined_replay", "target_count": len(tids),
                    "theorem_count": len(names), "decisions": dict(collections.Counter(r["decision"] for r in rows)),
                    "targets": mapping, "challenge_module": cfg["challenge_module"], "solution_module": cfg["solution_module"],
                    "defs_module": prefix + ".Defs", "combined_certificate": None})
        put(directory + "/TARGET-MAP.json", mapping)
        prov_units = {u: {k: v for k, v in units[u].items() if k not in ("rows", "names")} for u in unit_ids}
        base_files = {}
        for mod in closures["Solution"]:
            if mod == "AronowAudit" or mod.startswith("AronowAudit."):
                rel = mod.replace(".", "/") + ".lean"
                base_files[rel] = sha((base_source or source) / rel)
        put(directory + "/PROVENANCE.json", {"schema": VERSION, "work_id": work, "source_kind": source_kind,
            "units": prov_units, "base_source_sha256": base_files,
            "static_import_closures": closures,
            "frozen_work_catalog_sha256": input_hashes[f"catalog/works/{work}.json"],
            "site_work_sha256": input_hashes[f"site/{work}.json"],
            "declarations_added": [], "declarations_renamed": [],
            "definition_policy": "Shared unit Defs are imported unchanged by both sides; Comparator checks all referenced definitions.",
            "review_scope": "Existing unit evidence is linked byte-for-byte; no new semantic or combined review is claimed."})
        put(directory + "/ASSURANCE.json", {"work_id": work, "source_kind": source_kind,
            "unit_certificate_record_consistency": "passed", "exported_unit_review_evidence_consistency": "passed",
            "full_fw_fingerprint_revalidation": "requires_normal_fresh_collection",
            "static_import_and_target_checks": "passed", "combined_compilation": "not_run",
            "combined_lean_inventory_and_namespace_check": "not_run", "combined_axioms_and_definition_check": "not_run",
            "combined_comparator": "not_run", "combined_certificate": None,
            "independent_adapter_review": "pending", "a3_isolated_dependency_replay": "not_claimed",
            "obligations": ["Fresh complete collected candidate must match the current 81-unit attestation and route plan.",
                "Rebuild all unit modules and three work entries in isolation; inspect both Lean environments.",
                "Exact Challenge theorem/module inventories, per-target standard axioms, statement and definition equality.",
                "Export both complete work roots and obtain all four Comparator acceptance markers.",
                "Independent review of adapter, inventories, controls and any namespace interactions; A1/A2/A3 remain separate."]})
        put(directory + "/README.md", f"# {work}: {meta['title']}\n\n{meta['citation']}\n\n"
            f"This entry covers {len(tids)} catalog targets through {len(unit_ids)} internal unit(s): "
            f"{', '.join(unit_ids)}. It exposes {len(names)} existing proved Solution declarations.\n\n"
            f"Source kind: `{source_kind}`. Counts: `{canonical(row['decisions'])}`. "
            "Restricted statements and omissions retain their original disclosures in manifest.json and TARGET-MAP.json.\n\n"
            f"Use `{prefix}.Defs`, `{prefix}.Challenge`, and `{prefix}.Solution`. Challenge stubs are for statement checking; "
            "import the Solution in proof developments. The roots add no declarations and preserve every existing theorem name. "
            "Challenge and Solution are separate environments.\n\n"
            "Unit certificates and reviews are mapped in PROVENANCE.json. The combined work has not been compiled or "
            "certified; ASSURANCE.json lists its remaining checks. See ../BUILD.md for the executable replay command. "
            "Do not run the unit-only run_comparator.py on this directory.\n")
        inventory.append(row)
    binding = {"schema": VERSION, "source_kind": source_kind, "inputs_sha256": input_hashes,
               "units_sha256": digest(units), "formal_work_ids": sorted(formal), "site_work_ids": sorted(site),
               "unit_ids": sorted(units), "full_dependency_replay_assessed": False}
    put("SAP/Works/SOURCE-BINDING.json", binding)
    inv = {"schema": VERSION, "source_kind": source_kind, "source_binding_sha256": digest(binding),
           "counts": {"formal_works": len(formal), "site_works": len(site), "units": len(units),
                      "targets": sum(x["target_count"] for x in inventory),
                      "theorems": sum(x["theorem_count"] for x in inventory),
                      "decisions": dict(sum((collections.Counter(x["decisions"]) for x in inventory), collections.Counter()))},
           "site_only_work_ids": sorted(set(site)-set(formal)), "works": inventory}
    put("WORK-INVENTORY.json", inv)
    put("SAP/Works/INDEX.json", {w["work_id"]: {k: v for k, v in w.items() if k != "targets"} for w in inventory})
    put("SAP/Works/README.md", "# Work entry index\n\n"
        f"This generated overlay contains {len(formal)} formal work entries and explicit applicability pages for "
        f"{', '.join(sorted(set(site)-set(formal)))}. Source kind: `{source_kind}`.\n\n"
        "Keep this exact overlay separate from the immutable collected SAP/<unit> source root; assemble only in a new parent-owned candidate. Each formal work has separate Defs, Challenge and Solution "
        "roots, a union comparator config, the exact original manifest entries, and evidence maps. No new theorem names "
        "or combined certificates are created. [Build and replay](BUILD.md).\n\n" +
        "\n".join(f"- [{w['work_id']}]({w['work_id']}/README.md): {w['title']} "
                  f"({w['target_count']} targets; {w['disposition']})" for w in inventory) + "\n")
    put("SAP/Works/BUILD.md", BUILD_INSTRUCTIONS)
    return files


BUILD_INSTRUCTIONS = """# Build and replay work entries

The existing unit runner enforces SAP.<unit> module and theorem-name prefixes and allows only that unit's
Defs/Challenge imports. A compositional entry intentionally retains several unit namespaces. Use the scoped
adapter below; do not bypass completeness with the unit runner's --control option.

Run from any directory with the independently reviewed Python runtime and mandatory -I -S -B startup. Source and base trees are read-only; --out must not exist.
The entries directory can remain separate from the collected package. Every SAP module of the selected work
is copied and rebuilt into --out; existing SAP oleans are never selected as a substitute for a missing source.

```sh
python3 -I -S -B tools/palomar/palomar.py --expected-entry-sha256 "$PALOMAR_ENTRY_FROM_INDEPENDENT_CODE_REVIEW" validate \\
  --source /absolute/fresh-collected-package --catalog /absolute/frozen/catalog \\
  --site /absolute/llm-audit/data/works --base-source /absolute/pinned-lean-base \\
  --entries /absolute/work-entry-overlay --kind collected_candidate \\
  --attestation /absolute/current-81-source-attestation.json \\
  --routes /absolute/final-81-route-plan.json \\
  --collection-receipt /absolute/successful-collection/receipt.json \\
  --collected-file-inventory /absolute/successful-collection/collected-file-inventory.json \\
  --admission-root /absolute/archived-approved-admission \\
  --admission-review /absolute/independent-parent-review.json \\
  --expected-admission-pin-sha256 "$EXPECTED_ADMISSION_PIN_FROM_INDEPENDENT_PARENT_RECORD" \\
  --expected-admission-result-sha256 "$EXPECTED_ADMISSION_RESULT_FROM_INDEPENDENT_PARENT_RECORD" \\
  --expected-reviewed-tool-lock-sha256 "$EXPECTED_TOOLS_FROM_INDEPENDENT_PARENT_RECORD" \\
  --expected-admission-review-sha256 "$EXPECTED_FROM_INDEPENDENT_PARENT_RECORD"
python3 -I -S -B tools/palomar/palomar.py --expected-entry-sha256 "$PALOMAR_ENTRY_FROM_INDEPENDENT_CODE_REVIEW" replay \\
  --source /absolute/fresh-collected-package --entries /absolute/work-entry-overlay \\
  --catalog /absolute/frozen/catalog --site /absolute/llm-audit/data/works \\
  --base-source /absolute/pinned-lean-base --kind collected_candidate \\
  --attestation /absolute/current-81-source-attestation.json \\
  --routes /absolute/final-81-route-plan.json \\
  --collection-receipt /absolute/successful-collection/receipt.json \\
  --collected-file-inventory /absolute/successful-collection/collected-file-inventory.json \\
  --admission-root /absolute/archived-approved-admission \\
  --admission-review /absolute/independent-parent-review.json \\
  --expected-admission-pin-sha256 "$EXPECTED_ADMISSION_PIN_FROM_INDEPENDENT_PARENT_RECORD" \\
  --expected-admission-result-sha256 "$EXPECTED_ADMISSION_RESULT_FROM_INDEPENDENT_PARENT_RECORD" \\
  --expected-reviewed-tool-lock-sha256 "$EXPECTED_TOOLS_FROM_INDEPENDENT_PARENT_RECORD" \\
  --expected-admission-review-sha256 "$EXPECTED_FROM_INDEPENDENT_PARENT_RECORD" --work P001 \\
  --lean /home/ubuntu/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \\
  --comparator-lake /home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lake \\
  --primitive-check-file /home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/src/lean/lake/Lake/CLI/Check.lean \\
  --exporter /home/ubuntu/sap/deps/lean4export/.lake/build/bin/lean4export \\
  --lean-path-file /absolute/pinned-lean-path.txt --out /absolute/fresh-replay/P001
```

Run the 50 formal works sequentially (never the two inapplicable works). This may be expensive; it is a
parent-controlled job, not part of structural validation. Output holds snapshot hashes, compilation logs,
Lean inventories, full canonical statement/definition/constructor encodings, per-name axioms, exports and
Comparator logs. A successful new comparator-result.json has scope ordinary_work_comparator_base_reused;
it does not replace unit certificates or constitute A3 dependency replay. Only a real execution can set
accepted=true. The generator always leaves combined assurance pending. The new adapter and Lean inspector
need independent review and live positive/negative controls before their certificates become a release gate.

The dependency LEAN_PATH is explicit and hashed. Mathlib/AronowAudit artifacts are reused, so verify their
complete contents through the separate A3 lock/replay procedure. Compilation uses both autoImplicit options
off and the source token/import scans. Comparator exports include its pinned primitive targets, Quot
builtins and exactly the permitted standard axioms. Empty definition_names does not skip definition equality:
Comparator follows every definition reachable from each target; the inspector also compares project closures.

Every generated SAP/Works/<work> Lean file is at most 300 lines. Existing unit source and file boundaries
are preserved, including inherited files over 300 lines; these are disclosed as source-size exceptions.
All inherited and generated SAP modules still undergo the token scan and applicable import/closure checks.
Lake's defaultTargets in the baseline lists only AronowAudit; a bare lake build is not proof that work entries built.
The replay adapter explicitly compiles all selected SAP modules, then all three work roots.

For baseline fixtures pass --kind baseline_fixture with no attestation/routes and add
--allow-baseline-fixture to replay. Such a run is labeled a fixture and cannot certify the collected candidate.
"""
