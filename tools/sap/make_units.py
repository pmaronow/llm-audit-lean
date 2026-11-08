#!/usr/bin/env python3
"""make_units.py: split the llm-audit works into packaging units of at most MAX targets (targets kept in catalog order),
writing ~/sap/inputs/units.json: {unit_id: {"work": W, "targets": [...]}}. A work with <= MAX targets is one unit named
by its work id (P022); a larger work becomes P001a, P001b, ... The pilots P010 and P022 keep their single-unit names."""
import json, pathlib, collections, string
H = pathlib.Path.home(); MAX = 20
la = json.load(open(H / "sap/inputs/lean-catalog.json"))
units = {}
for w in la["works"]:
    ts = [t["id"] for t in w["targets"]]
    if len(ts) <= MAX or w["work_id"] in ("P010", "P022"):   # pilots keep their single-unit names
        units[w["work_id"]] = {"work": w["work_id"], "targets": ts}; continue
    k = -(-len(ts) // MAX); size = -(-len(ts) // k)
    for i in range(k):
        units[w["work_id"] + string.ascii_lowercase[i]] = {"work": w["work_id"], "targets": ts[i * size:(i + 1) * size]}
assert sum(len(u["targets"]) for u in units.values()) == 1021
json.dump(units, open(H / "sap/inputs/units.json", "w"), indent=1)
sizes = collections.Counter(len(u["targets"]) for u in units.values())
print(len(units), "units;", "targets per unit:", sorted(sizes.items()))
print([u for u in units if not u[-1].isdigit()])
