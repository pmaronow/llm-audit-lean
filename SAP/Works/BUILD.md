# Build and replay work entries

The existing unit runner enforces SAP.<unit> module and theorem-name prefixes and allows only that unit's
Defs/Challenge imports. A compositional entry intentionally retains several unit namespaces. Use the scoped
adapter below; do not bypass completeness with the unit runner's --control option.

Run from any directory with the independently reviewed Python runtime and mandatory -I -S -B startup. Source and base trees are read-only; --out must not exist.
The entries directory can remain separate from the collected package. Every SAP module of the selected work
is copied and rebuilt into --out; existing SAP oleans are never selected as a substitute for a missing source.

```sh
python3 -I -S -B tools/palomar/palomar.py --expected-entry-sha256 "$PALOMAR_ENTRY_FROM_INDEPENDENT_CODE_REVIEW" validate \
  --source /absolute/fresh-collected-package --catalog /absolute/frozen/catalog \
  --site /absolute/llm-audit/data/works --base-source /absolute/pinned-lean-base \
  --entries /absolute/work-entry-overlay --kind collected_candidate \
  --attestation /absolute/current-81-source-attestation.json \
  --routes /absolute/final-81-route-plan.json \
  --collection-receipt /absolute/successful-collection/receipt.json \
  --collected-file-inventory /absolute/successful-collection/collected-file-inventory.json \
  --admission-root /absolute/archived-approved-admission \
  --admission-review /absolute/independent-parent-review.json \
  --expected-admission-pin-sha256 "$EXPECTED_ADMISSION_PIN_FROM_INDEPENDENT_PARENT_RECORD" \
  --expected-admission-result-sha256 "$EXPECTED_ADMISSION_RESULT_FROM_INDEPENDENT_PARENT_RECORD" \
  --expected-reviewed-tool-lock-sha256 "$EXPECTED_TOOLS_FROM_INDEPENDENT_PARENT_RECORD" \
  --expected-admission-review-sha256 "$EXPECTED_FROM_INDEPENDENT_PARENT_RECORD"
python3 -I -S -B tools/palomar/palomar.py --expected-entry-sha256 "$PALOMAR_ENTRY_FROM_INDEPENDENT_CODE_REVIEW" replay \
  --source /absolute/fresh-collected-package --entries /absolute/work-entry-overlay \
  --catalog /absolute/frozen/catalog --site /absolute/llm-audit/data/works \
  --base-source /absolute/pinned-lean-base --kind collected_candidate \
  --attestation /absolute/current-81-source-attestation.json \
  --routes /absolute/final-81-route-plan.json \
  --collection-receipt /absolute/successful-collection/receipt.json \
  --collected-file-inventory /absolute/successful-collection/collected-file-inventory.json \
  --admission-root /absolute/archived-approved-admission \
  --admission-review /absolute/independent-parent-review.json \
  --expected-admission-pin-sha256 "$EXPECTED_ADMISSION_PIN_FROM_INDEPENDENT_PARENT_RECORD" \
  --expected-admission-result-sha256 "$EXPECTED_ADMISSION_RESULT_FROM_INDEPENDENT_PARENT_RECORD" \
  --expected-reviewed-tool-lock-sha256 "$EXPECTED_TOOLS_FROM_INDEPENDENT_PARENT_RECORD" \
  --expected-admission-review-sha256 "$EXPECTED_FROM_INDEPENDENT_PARENT_RECORD" --work P001 \
  --lean /home/ubuntu/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  --comparator-lake /home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lake \
  --primitive-check-file /home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/src/lean/lake/Lake/CLI/Check.lean \
  --exporter /home/ubuntu/sap/deps/lean4export/.lake/build/bin/lean4export \
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
