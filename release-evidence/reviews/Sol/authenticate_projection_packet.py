"""Bind the final document seal to the projection maps already compared once."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
P = HERE.parent / "final-package-projection-preparation-001"
seal_data = (P / "SEAL.json").read_bytes()
if hashlib.sha256(seal_data).hexdigest() != "7b00008926f17f8c0b444a93ffb755f6fc098edae24c8ad5f8ac2b77d8b78379":
    raise ValueError("Changed final projection preparation seal")
seal = json.loads(seal_data)
if {p.name for p in P.iterdir()} != set(seal["files"]) | {"SEAL.json"}:
    raise ValueError("Projection packet membership differs")
prior = json.loads((HERE / "PROJECTION-JOINS.json").read_bytes())
prior_refs = {v["path"]: v for v in prior["source_refs"].values()}
refs = {}
for name, expected in seal["files"].items():
    path = P / name
    if path.is_symlink() or not path.is_file():
        raise ValueError("Projection packet alias or nonregular member")
    if str(path) in prior_refs:
        if expected["sha256"] != prior_refs[str(path)]["sha256"] or expected["bytes"] != prior_refs[str(path)]["bytes"]:
            raise ValueError("Changed previously compared map")
        refs[name] = dict(prior_refs[str(path)], digest_reused=True)
    else:
        data = path.read_bytes()
        if len(data) != expected["bytes"] or hashlib.sha256(data).hexdigest() != expected["sha256"]:
            raise ValueError("Changed final projection document")
        refs[name] = {"path": str(path), **expected, "digest_reused": False}
future = json.loads((P / "KNOWN-EVIDENCE-AND-FUTURE-REFS.json").read_bytes())
layout = json.loads((P / "FORMAL-BASELINE-AND-LAYOUT.PENDING.json").read_bytes())
if not all(v is None for v in future["required_future"].values()):
    raise ValueError("Invented final package facts")
if layout["formal_repository"]["push_remote"] != "sap" or layout["formal_repository"]["repository"] != "https://github.com/pmaronow/self-audit-palomar.git":
    raise ValueError("Wrong formal publication destination")
out = {
    "schema": "final-sol-projection-preparation-seal-binding-v1",
    "author_seal": {"path": str(P / "SEAL.json"), "sha256": hashlib.sha256(seal_data).hexdigest()},
    "payloads": refs,
    "completed_map_comparisons_reused_not_rerun": True,
    "same_prepared_map_digests": True,
    "future_package_acceptance_facts_still_null": True,
    "formal_destination": layout["formal_repository"],
    "actual_copy_or_publication_approved": False,
}
(HERE / "PROJECTION-PACKET-BINDING.json").write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
print(json.dumps({"payloads": len(refs), "map_comparisons_reused": True, "actual_package_acceptance_issued": False}, sort_keys=True))
