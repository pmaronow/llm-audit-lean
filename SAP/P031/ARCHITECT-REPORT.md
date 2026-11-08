P031: **8 whole, 1 restricted, 2 refuted, 0 omitted. All 11 exported theorems are proved; 0 open glue tasks.**

This summary reflects the supplied whole versions of T5, T6, and T10 and the round-2 correction to T11. Earlier decisions below are retained as history. All original credited rows remain used, together with the additional existing declarations assembled by the supplied whole versions. No project source or supplied input was edited in this round.

| Targets | Decision | Current exported content |
| --- | --- | --- |
| T1–T4 | whole | HC2/Neyman identity, expectation conservativeness against actual randomization variance, scaled OLS/CE identity, and balanced-design equivalences. |
| T5 | refuted | Exact nonnegative Neyman bias identity and the supplied full-conjunction refutation through HR/HC2 equivalence failure. |
| T6 | refuted | Both OLS/CE variance-error directions and undercoverage, together with the supplied unbalanced standardized-normal counterexample to the Neyman/HC2 coverage contrast. |
| T7 | whole | Every specified four-unit covariance counterexample calculation, including imputed variances 5/2 and original covariance 23/2. |
| T8–T9 | whole | Every link in both corrected proof chains. |
| T10 | whole | All three sign-population families, full assignmentwise shift identities, exact finite-row formulas, deterministic and probability limits, and N=8 comparisons. |
| T11 | restricted | Every mathematical clause of corrected footnote 3; excludes only the bibliographic assertion that Freedman (2008b, p. 190) gives the relation. |

P031-T11 is restricted solely because the literal canonical statement includes that bibliographic assertion. The theorem covers all four deterministic limits, bounded-outcome sufficiency for centered arm-variance consistency, conditional OLS and positive-denominator ratio probability limits, and exact shifts. No mathematical hypothesis, identity, rate, limit, or existence clause of the corrected mathematical relation is dropped. Its sequence, interior allocation, convergent population moments, sample-consistency alternative, and positive leading variance for the ratio are already part of the corrected claim; the usual measure-theoretic conditions are presupposed rather than counted as restrictions. There are no omitted targets.

The route uses shared Mathlib-only definitions and structural bridges. `Defs/Part1.lean` defines finite means, population moments, and regression variance formulas. `Part2.lean` defines populations, uniform finite assignment probabilities, and asymptotic conventions; `Part3.lean` defines the sign families, shifts, and sample conditions. `Part4.lean`, `Part5.lean`, and `WholeW1.lean` define the target propositions. Challenge and Solution import the same compiled SAP definitions. No project declaration is recreated under its original fully qualified name.

The population adapters preserve every field, with inverse identities proved by `rfl`; finite-data, probability, and shift correspondences are definitional. The original bridges apply existing rows, convert existential witnesses, project conjunctions, or assemble the two credited T11 rows. The supplied `WH/W1` modules add the whole T5, T6, and T10 statements through their existing proved leaves and assemblies. Round 2 adds no mathematical proof, definition, hypothesis, or proof dependency.

Standing design conditions protect all arm means, sample-variance divisors, regression inverses, and finite assignment averages. Standardization uses eventual positive actual variance. The T11 ratio is conditional on a positive limiting scaled true variance, making its denominator eventually positive. Relative-error equivalence handles zero reference estimates without a ratio. All expectations are finite real averages, so there is no hidden integrability problem.

The round-2 rebuild compiles every current SAP module in dependency order with `sap-lean`, followed by `#print axioms` for all eleven exported Solution theorems. Every theorem has only `propext`, `Classical.choice`, and `Quot.sound`. Both JSON files parse, list the same eleven theorems, and retain the requested comparator settings. All SAP files retain both implicit-variable options and remain below 300 lines. Detailed validation and logs are recorded in the round-2 section below.

The supplied prior certification record in `SAP/P031/verification/comparator-result.json` reports acceptance of all eleven theorems by the Comparator and all three kernels; its log is `SAP/P031/verification/comparator.log`. That record describes its earlier snapshot. Round 2 preserves theorem statements and all shared definitions, and does not claim a new external-kernel run.

## Declaration review round 1

Finding: `SAP.P031.T5`, `label_wrong`, major, with two issues: the manifest's unqualified `refuted` decision and the Challenge docstring's unqualified assertion that the printed claim is false. See the [T5 entry in the review findings](/home/ubuntu/sap/wt/ARCH-P031/fw/round1/T5/r1g1/findings.json:47) and the [review report](/home/ubuntu/sap/wt/ARCH-P031/fw/round1/T5/r1g1/REPORT.md:1).

Both issues are accepted. I checked the canonical claim's `definitions_needed` field in [work.json](/home/ubuntu/sap/wt/ARCH-P031/work.json:250), the [actual SAP asymptotic definitions](/home/ubuntu/sap/wt/ARCH-P031/SAP/P031/Defs/Part2.lean:53), the [T5 proposition](/home/ubuntu/sap/wt/ARCH-P031/SAP/P031/Defs/Part5.lean:13), and the [credited theorem](/home/ubuntu/sap/wt/ARCH-P031/AronowAudit/P031/Wave1/LargeSampleRefutation.lean:29). The canonical claim explicitly leaves the asymptotic notions and sequence unspecified; the theorem negates the particular definitions in this package. The earlier coverage judgment calling this a full refutation is diagnostic history and cannot override that distinction.

Changed T5 to `restricted`, replaced its opening falsity claim with an interpretation-specific counterexample description, and disclosed all four asymptotic conventions, the lack of a both-arms-growing premise, the omitted nonnegative Neyman bias clause, every positive equivalence/coverage assurance not proved, and the absence of a separate individual coverage refutation. Updated the source-generation draft to match. No finding is disputed, and the other entries in the supplied findings file have no open issues.

All ten SAP Lean modules and the eleven dependency checks were rerun with `sap-lean` in dependency order. The build output is in `scratch/P031Round1Build.log`; the final docstring-only Challenge rebuild is in `scratch/P031Round1ChallengeBuild.log`. Challenge placeholder diagnostics in these saved logs use `[Challenge placeholder]` to respect the token restriction. `scratch/P031Axioms.log` records the fresh dependency output. Every theorem remains proved under the same fully qualified name and has exactly the three permitted dependencies. Both JSON files were parsed and the comparator configuration regenerated and checked; its module names, theorem names, definition list, permitted dependencies, and kernel commands remain identical because the declarations did not change. The validation script and result are in `scratch/validate_p031_round1.py` and `scratch/P031Round1Validation.log`.

No shared definition, theorem type, bridge, or Solution proof was changed. The source fingerprints saved in `scratch/P031Round1Baseline.json` confirm that only `Challenge/Part1.lean` changed among SAP Lean files, and its change is confined to T5's docstring. There are no new mathematical proofs or open glue tasks. The historical decisions after round 1 were 8 whole, 3 restricted, 0 refuted, and 0 omitted.

## Whole versions (new proofs)

P031-T10 (`SAP.P031.T10`) is now whole, with type `SAP.P031.T10WholeStatement` and Solution proof `SAP.P031.WH.W1.T10_whole`. This supersedes the earlier restricted T10 descriptions above. After that switch, the totals were 9 whole, 2 restricted, 0 refuted, and 0 omitted.

Files updated: `SAP/P031/Challenge/Part1.lean` (whole type, supplied docstring, and `SAP.P031.Defs.WholeW1` import; placeholder retained), `SAP/P031/Solution.lean` (whole type, proof term, and `SAP.P031.WH.W1.Proofs.T10` import), and `SAP/P031/manifest.json` (T10 entry only). The supplied whole definition, blueprint, and generated proof remain unchanged in `SAP/P031/Defs/WholeW1.lean`, `SAP/P031/WH/W1/Leaves.lean`, and `SAP/P031/WH/W1/Proofs/T10.lean`.

The old restriction, now removed, was:

> Drops the explicit observed-vector, intercept, treatment-estimate and per-unit residual shift identities in part (a); the exact finite-row N*trueVariance and N*OLS formulas and E[r^2]=3/(N-1) in part (b); and every N=8, M=2, 28-assignment variance, expectation and ratio calculation in part (c). Retains all three explicit families, their fixed allocation and moment identities, scaled true-variance and expected-OLS limits, OLS probability and ratio limits, and universal first-moment and variance shift invariance. Excludes the credited row's additional CE probability limit, which is outside this target.

The whole proof restores the explicit observed-vector, intercept, treatment-estimate, and per-unit residual shift identities in part (a); the finite-row N-times-true-variance and N-times-OLS formulas and E[r²]=3/(N−1) in part (b); and the N=8, M=2, 28-assignment variance, expectation, and ratio calculations in part (c). The CE probability limit remains outside the target. The original credited row is retained in `rows_used`, with the six additional project declarations called by the T10 assembly and its helper proofs.

No other Solution proof uses T10, so no dependent proof repairs were necessary. Every other target's statement, docstring, proof, and manifest entry is unchanged.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P031` rebuilt all 20 P031 modules from scratch and passed its token scan; output is in `scratch/P031WholeRebuild.log`. The scratch file `scratch/P031WholeAxioms.lean` imports `SAP.P031.Solution` and runs `#print axioms SAP.P031.T10`; `scratch/P031WholeAxioms.log` reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Lean processes ran sequentially, and no `lake` command was run. Scope checks confirmed that the only existing source/document files changed are the Challenge, Solution, manifest, and this report; all other SAP files and every other target entry are unchanged. Results are recorded in `switched.json`.

## Whole versions (new proofs)

P031-T5 and P031-T6 now export their whole statements with the `refuted` decisions supplied in `switch.json`. This supersedes their earlier restricted descriptions above. After that switch, the totals were 9 whole, 0 restricted, 2 refuted, and 0 omitted.

P031-T5 (`SAP.P031.T5`): Challenge type `SAP.P031.T5WholeStatement`; Solution proof `SAP.P031.WH.W1.T5_whole`.

Files updated: `SAP/P031/Challenge/Part1.lean` (supplied docstring and whole type, retaining `the Challenge placeholder` and the existing `SAP.P031.Defs.WholeW1` import), `SAP/P031/Solution.lean` (whole type, proof term, and `SAP.P031.WH.W1.Proofs.T5` import), and this target's entry in `SAP/P031/manifest.json`. The supplied definition and proofs are unchanged in `SAP/P031/Defs/WholeW1.lean`, `SAP/P031/WH/W1/Leaves.lean`, and `SAP/P031/WH/W1/Proofs/T5.lean`.

The old restriction, now removed, was:

> Addresses only the interpretation in which large sample means N tends to infinity, normality means CDF convergence to the standard normal after centering at the population effect and standardization by the actual randomization standard deviation with true variance eventually positive, equivalence means relative error in probability against HC2, and conservative coverage means that for every z > 0 and epsilon > 0 coverage is eventually at least 2 Phi(z) - 1 - epsilon. No requirement that both arm sizes grow is imposed; a fixed treatment arm is permitted. Supplies an HR/HC2 counterexample to this interpretation and hence negates its conjunction. Drops the separate nonnegative Neyman bias assertion, omits proofs of the canonical positive HR/HC1/HC3 equivalence and Neyman/HC2/HR/HC1/HC3 coverage assurances, and asserts no separate failure of an individual coverage clause.

P031-T6 (`SAP.P031.T6`): Challenge type `SAP.P031.T6WholeStatement`; Solution proof `SAP.P031.WH.W1.T6_whole`.

Files updated: `SAP/P031/Challenge/Part1.lean` (supplied docstring and whole type, retaining `the Challenge placeholder` and the existing `SAP.P031.Defs.WholeW1` import), `SAP/P031/Solution.lean` (whole type, proof term, and `SAP.P031.WH.W1.Proofs.T6` import), and this target's entry in `SAP/P031/manifest.json`. The supplied definition and proofs are unchanged in `SAP/P031/Defs/WholeW1.lean`, `SAP/P031/WH/W1/Leaves.lean`, and `SAP/P031/WH/W1/Proofs/T6.lean`, with proved leaves in `SAP/P031/WH/W1/P/T6_L1.lean` through `T6_L5.lean`.

The old restriction, now removed, was:

> Drops the contrasting assurance of approximately correct or conservative large-sample coverage for Neyman and HC2 under only the printed assumptions. Retains both directions of OLS/CE error on the N-times-variance scale and the standardized-normal sequence with strict limiting undercoverage for both estimators.

T5's whole proof adds the exact nonnegative Neyman bias identity to the existing full-conjunction refutation. T6's whole proof retains the OLS/CE warning and refutes the Neyman/HC2 contrast with a growing unbalanced standardized-normal sequence whose coverages at z=1 both tend to 1/2, strictly below nominal coverage. Each manifest entry retains its original row and adds the project theorem declarations used by its assembly and proved leaves.

No other Solution proof uses T5 or T6, so no dependent proof repairs were necessary. Every other target statement, docstring, proof, and manifest entry is unchanged.

Validation: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P031` rebuilt all 20 P031 modules from scratch and passed its token scan. The scratch file `/tmp/p031-switch-ae5ir4go/WholeAxioms.lean` imports `SAP.P031.Solution` and runs `#print axioms` for both switched theorems; each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Build and dependency output are saved in `/tmp/p031-switch-ae5ir4go/rebuild.log` and `/tmp/p031-switch-ae5ir4go/axioms.log`. Lean processes ran sequentially, and no `lake` command was run. Scope checks verified the supplied types, docstrings, proof terms, and import boundaries, with every other SAP source and target manifest entry unchanged. Results are recorded in `switched.json`.


## Declaration review round 2

Finding: `SAP.P031.T11`, `label_wrong`, minor: `whole` with no restriction conflicts with the explicit exclusion of the Freedman attribution. See the [finding](/home/ubuntu/sap/wt/ARCH-P031/fw/round2/T11/r4g3/findings.json:9) and [review report](/home/ubuntu/sap/wt/ARCH-P031/fw/round2/T11/r4g3/REPORT.md:5).

Accepted. I checked the literal [canonical statement](/home/ubuntu/sap/wt/ARCH-P031/work.json:596), the [T11 proposition](/home/ubuntu/sap/wt/ARCH-P031/SAP/P031/Defs/Part5.lean:48), and both credited rows in [FootnoteThreeComplete.lean](/home/ubuntu/sap/wt/ARCH-P031/AronowAudit/P031/Wave1/FootnoteThreeComplete.lean:10) and [FootnoteThreeProbability.lean](/home/ubuntu/sap/wt/ARCH-P031/AronowAudit/P031/Wave1/FootnoteThreeProbability.lean:18). The theorem covers every mathematical clause, but does not establish that the relation appears on the cited journal page. The audit-history note in `work.json:599` does not remove that sentence from the canonical claim.

Changed T11's manifest decision to `restricted` with the exact restriction: "States every mathematical clause of the corrected footnote; excludes the bibliographic assertion that Freedman (2008b, p. 190) gives the relation." Made the same exclusion explicit as a restriction in its Challenge docstring. No finding is disputed. T11's statement and Solution proof, all shared definitions, and every other target's declaration and manifest entry are preserved, including the supplied whole versions of T5, T6, and T10. The comparator configuration was regenerated and parsed; its contents remain identical because the exported names and statements are unchanged.

Recompiled all 20 current SAP Lean modules with `sap-lean` in dependency order and reran the eleven checks in `scratch/P031Axioms.lean`. All compiled successfully; the diagnostics were unused-binder and Challenge placeholder warnings and existing tactic-linter warnings in the supplied T6 leaf. The fresh outputs are `scratch/P031Round2Build.log` and `scratch/P031Round2Axioms.log`; placeholder diagnostics in saved build output use `[Challenge placeholder]` to respect the token restriction. Every theorem depends exactly on the three permitted entries.

The source and manifest baseline in `scratch/P031Round2Baseline.json` and the checks in `scratch/validate_p031_round2.py` verify that only T11's docstring changed among Lean source files and only its decision and restriction changed among manifest entries. `scratch/P031Round2Validation.log` records JSON parsing, target/name agreement, import boundaries, options, file-size and token checks, and dependency validation. There are no shared-definition changes, new proofs, or open glue tasks. Final counts: 8 whole, 1 restricted, 2 refuted, 0 omitted; 11 proved.


## 2026-11-05 cited-regime repair proposal

This dated entry discloses a proposed replacement of the earlier P031-T5 and P031-T6
refuted whole versions. The independently certified new Challenge declarations state
the cited finite-population regime with an explicit D > 0 premise, and their manifest
decisions are restricted. The D = 0 coverage case is outside these proofs. The earlier
W1 normality-only counterexamples remain compiled historical helpers and do not earn
credit for the repaired canonical targets. Historical W2/W3 WH groups remain retired;
the current positive W2/W3 proofs are bound by the separate manual-current-route
evidence in the integration transaction. The other nine current declarations retain
their reviewed target meanings. Exact source, claim, certificate and independent FW
bindings are recorded in assure/repair-integration-2026-11-05/plan.json. This entry
preserves the original canonical claims and records independent Sol content acceptance
of the exact corrected claims in work metadata. Site claim-revision events remain draft
and pending. This entry does not declare events accepted, whole-label promotion, A3
replay, or release.
