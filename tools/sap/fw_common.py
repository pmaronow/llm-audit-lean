#!/usr/bin/env python3
"""fw_common.py: shared definitions for the declaration review (FW), used by fw_prep.py, sap_pipeline.py,
fw_rebind.py and collect_final.py, so that the pipeline and publication apply ONE validator and ONE binding rule
(V-ORCH-SAP2 delta D1-D3).

Binding rule (conservative, D3): a review is valid for the current version of a declaration only if the reviewer was
given exactly the current inputs:
  * the same Defs/Challenge source files of the unit, byte for byte (src_digest: every .lean file, any change to any of
    them invalidates every review of the unit), and
  * the same review packet for that target (packet_digest: canonical claim and its review fields, the work's citation
    and standing assumptions, and the target's full manifest entry).
The review fingerprint is the full sha256 of (src_digest, packet_digest, base identifiers, Lean closure hash)."""
import hashlib, json, pathlib, re

DECL_VERDICTS = {"faithful", "restriction_inaccurate", "label_wrong", "not_faithful", "vacuous", "false",
                 "trivialized", "junk_value"}
OMIT_VERDICTS = {"omission_ok", "omission_questionable", "reason_inaccurate"}
CLEAN = {"faithful", "omission_ok"}
SEVERITIES = {"none", "minor", "major"}
MANIFEST_DROP = ("proof_status", "proof_plan", "axioms")     # proof bookkeeping, not statement meaning


def sha_bytes(b): return hashlib.sha256(b).hexdigest()
def sha_file(p): return sha_bytes(pathlib.Path(p).read_bytes())
def canon(x): return json.dumps(x, sort_keys=True, ensure_ascii=False, default=str, separators=(",", ":"))


def src_files(root, U):
    """Every Defs/Challenge .lean file of unit U under root (a prep dir, review task dir or architect worktree)."""
    root = pathlib.Path(root); base = root / f"SAP/{U}"; out = {}
    for name in ("Defs.lean", "Challenge.lean"):
        if (base / name).exists(): out[f"SAP/{U}/{name}"] = sha_file(base / name)
    for part in ("Defs", "Challenge"):
        if (base / part).is_dir():
            for f in sorted((base / part).rglob("*.lean")): out[str(f.relative_to(root))] = sha_file(f)
    return out


def src_digest(root, U):
    files = src_files(root, U)
    return sha_bytes(canon(sorted(files.items())).encode()) if files else None


def packet(pk, target_entry, manifest_entry, omitted):
    """The review packet for one target, exactly as given to its reviewer."""
    t = {"target_id": target_entry["target_id"], "canonical_claim": target_entry["canonical_claim"]}
    if omitted: t.update({k: target_entry.get(k) for k in ("no_lean", "rows", "coverage_judgments")})
    rec = {k: v for k, v in manifest_entry.items() if k not in MANIFEST_DROP}
    return {"citation": pk.get("citation"), "standing_assumptions": pk.get("standing_assumptions"), "target": t,
            "record": rec}


def packet_digest(p): return sha_bytes(canon(p).encode())


def fingerprint(src_dig, pkt_dig, base, closure_fp):
    return sha_bytes(canon([src_dig, pkt_dig, base, closure_fp]).encode())


def validate_entry(x, key, target_id, given_fp):
    """(ok, clean, reason) for one findings entry for review item `key` (a theorem name, or OMIT.<target>).
    Every field must be present. A clean result (faithful / omission_ok) has severity none and an EMPTY issues list;
    the status of earlier issues goes in the separate optional `resolved` list (briefs/fw-recheck.md)."""
    if not isinstance(x, dict): return False, False, "entry is not an object"
    for k in ("target_id", "theorem", "fingerprint", "verdict", "severity", "issues"):
        if k not in x: return False, False, f"field {k!r} missing"
    if not (isinstance(given_fp, str) and re.fullmatch(r"[0-9a-f]{64}", given_fp)): return False, False, "no valid expected fingerprint"
    omitted = key.startswith("OMIT.")
    if x["target_id"] != target_id: return False, False, f"target_id {x['target_id']!r} != {target_id!r}"
    if omitted:
        if x["theorem"] is not None: return False, False, "omission entry names a theorem"
        verdicts = OMIT_VERDICTS
    else:
        if x["theorem"] != key: return False, False, f"theorem {x['theorem']!r} != {key!r}"
        verdicts = DECL_VERDICTS
    v, sev, iss = x["verdict"], x["severity"], x["issues"]
    if v not in verdicts: return False, False, f"verdict {v!r} not allowed here"
    if sev not in SEVERITIES: return False, False, f"severity {sev!r}"
    if not isinstance(iss, list): return False, False, "issues is not a list"
    if x["fingerprint"] != given_fp: return False, False, "fingerprint not echoed exactly"
    clean = v in CLEAN
    if clean != (sev == "none"): return False, False, f"verdict {v} inconsistent with severity {sev}"
    if clean and iss: return False, False, "clean verdict with a nonempty issues list"
    if not clean and not iss: return False, False, "adverse verdict without issues"
    return True, clean, ""


def index_findings(f, items):
    """Map a findings list to review items. An item named more than once is rejected entirely (never reinstated).
    items: {key: (target_id, given_fp)}. Returns (by_key, problems)."""
    if isinstance(f, dict): f = [f]
    if not isinstance(f, list): return {}, ["findings is not a list"]
    seen, dup, by, problems = {}, set(), {}, []
    for x in f:
        if not isinstance(x, dict): problems.append("non-object entry"); continue
        if "theorem" not in x: problems.append("entry without a theorem field"); continue
        key = x["theorem"] if x["theorem"] is not None else f"OMIT.{x.get('target_id')}"
        if key in seen: dup.add(key)
        seen[key] = x
    for key, x in seen.items():
        if key in dup: problems.append(f"{key}: listed more than once"); continue
        if key not in items: problems.append(f"{key}: not a reviewed item"); continue
        ok, clean, why = validate_entry(x, key, *items[key])
        if not ok: problems.append(f"{key}: {why}"); continue
        by[key] = (x, clean)
    return by, problems


def legacy_bound(*a, **k):
    """Pre-v2 reviews never bind (V-ORCH-SAP2 delta2 D3): they were not given the full packet. Kept for callers."""
    return False, "pre-v2 review (not given the full review packet)"


def task_packets(taskdir):
    """Reconstruct, from a review task dir's actual claims.json and record.json, the packet digest of every item it
    was given ({target_id: digest}), exactly as fw_common.packet built them (V-ORCH-SAP2 delta2 D1)."""
    taskdir = pathlib.Path(taskdir)
    cl = json.load(open(taskdir / "claims.json")); rec = json.load(open(taskdir / "record.json"))
    tl = cl.get("targets"); rl = rec if isinstance(rec, list) else None
    if not isinstance(tl, list) or not isinstance(rl, list): raise ValueError("claims/record are not lists")
    tids = [t.get("target_id") for t in tl]; rids = [r.get("target_id") for r in rl]
    # an ambiguous packet (a target listed twice, or claims and records for different targets) binds nothing
    # (V-ORCH-SAP2 delta3 MAJOR 1)
    if len(set(tids)) != len(tids) or len(set(rids)) != len(rids): raise ValueError("duplicate target in the packet")
    if set(tids) != set(rids): raise ValueError("claims and records cover different targets")
    recs = {r["target_id"]: r for r in rl}
    return {t["target_id"]: packet_digest({"citation": cl.get("citation"), "standing_assumptions": cl.get("standing_assumptions"),
                                           "target": t, "record": recs[t["target_id"]]}) for t in tl}


def review_bound(r, key, target_id, U, cur_src_digest, cur_pkt, cur_base, cur_fp):
    """(bound, clean, reason): a recorded review counts for the current version only if it is v2, its task dir still
    holds exactly the current sources, the packet reconstructed from its actual task files equals both the recorded
    and the current packet, its base equals the current base, and its findings entry revalidates against the
    fingerprint it was given. The fingerprint must also be the current one."""
    if r.get("binding") != "v2": return False, False, "pre-v2 review"
    td = pathlib.Path(r["file"]).parent
    if src_digest(td, U) != cur_src_digest or r.get("src_digest") != cur_src_digest: return False, False, "sources differ"
    try: tp = task_packets(td).get(target_id)
    except Exception as e: return False, False, f"unreadable task packet ({e})"
    if tp is None or tp != r.get("pkt") or tp != cur_pkt: return False, False, "packet differs"
    if r.get("base") != cur_base: return False, False, "dependency base differs"
    if r.get("given_fp") != cur_fp: return False, False, "fingerprint differs"
    try: by, probs = index_findings(json.load(open(r["file"])), {key: (target_id, r["given_fp"])})
    except Exception as e: return False, False, f"unreadable findings ({e})"
    if key not in by: return False, False, "findings entry fails validation: " + "; ".join(probs[:2])
    return True, by[key][1], ""
