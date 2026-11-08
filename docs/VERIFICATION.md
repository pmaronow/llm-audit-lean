# Verification and assumptions

The archive contains 988 proved formal statements for 1,021 targets. The [current index](../package/current-results.json) resolves every statement to its actual declaration file, corresponding proof, definitions and original manifest.

## Routine checks

```sh
python3 scripts/check_repository.py
python3 -m unittest discover -s scripts -p 'test_*.py'
```

Pushes and pull requests run these checks. The source checker verifies mathematical source and retained certificate/evidence bytes, unchanged historical catalog bytes, complete target coverage, matching unit/work outcomes and actual statement/proof locations. A separate content check scans reader documentation and maintained scripts. Solution imports of Challenge files and proof placeholders in SAP proof modules are rejected. These checks preserve the source/evidence bindings; they do not repeat a kernel replay or review paper fidelity.

## Optional fresh proof rebuild

The unchanged proof sources can be rebuilt locally:

```sh
lake exe cache get
python3 scripts/build_current.py
```

To request the same full check in CI, run the workflow manually with `full_rebuild` enabled. It is off by default.

The build command explicitly builds `AronowAudit.All`, then all 50 Challenge and Solution work entries separately. It also runs `#print axioms` for every current Solution theorem and rejects anything except `propext`, `Classical.choice` and `Quot.sound`. A bare `lake build` is not this complete check. `python3 scripts/build_current.py --work P038` checks only one work and is explicitly partial.

Some kernel computations need substantial memory. The optional CI job provides additional swap and removes completed build-setup metadata between phases; proof sources, evidence and compiled proof artifacts remain intact.

Challenge files intentionally contain `sorry` placeholders. The inherited supporting library also contains unused unfinished declarations. Successful compilation permits those declarations; the per-theorem axiom check is therefore essential to establish that a current proof does not rely on `sorryAx`. No source-wide absence of placeholders is claimed.

## Retained evidence

[release-evidence/](../release-evidence/) contains the original replay and review records. Mathematical sources, unit manifests, certificates, reviews and work-entry metadata are unchanged. Historical work-entry pages are labelled, and unused operational launchers are omitted; [the source manifest](../package/source-manifest.json) records these packaging changes separately.

Some retained records describe intermediate or earlier states; the current index reports the collected target outcomes. They are evidence, not fresh executions by this checkout’s metadata checker.

The comparator route uses the Lean 4.34.1 build/export pipeline and the Lean 4.35.0-rc2 comparator with con-ron, NanoDa and the Lean kernel. The checking paths share an exporter, so they are not wholly independent end-to-end implementations. Original tool/dependency bindings and replay limitations remain in the [trust report](../release-evidence/A7/TRUST-REPORT.md).

Paper fidelity and coverage require reading the statement, definitions and hypotheses. The archived supporting library includes conditional results with explicit published-theorem premises. Current target assumptions are stated in each Challenge and its definitions. Restricted results, source/version qualifications and omissions remain disclosed in the per-work guides. The retained evidence is not a blanket claim that every printed paper assertion is proved.
