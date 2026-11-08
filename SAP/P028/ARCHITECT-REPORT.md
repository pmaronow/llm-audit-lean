# P028 Challenge package

Work: “Sharp Bounds for Complier Average Potential Outcomes in Experiments with Noncompliance and Incomplete Reporting,” Statistics and Probability Letters 83 (2013), 677–679; DOI 10.1016/j.spl.2012.11.012.

The package covers exactly P028-T1 through P028-T10 from `work.json`.

| Decision | Count | Targets |
| --- | ---: | --- |
| whole | 3 | T4, T7, T8 |
| restricted | 6 | T1, T2, T5, T6, T9, T10 |
| refuted | 0 | — |
| omitted | 1 | T3 |

All nine listed Solution theorems are proved. There are no open glue tasks.

## Restrictions and omission

- **T1:** Retains the exact 17-atom tables, positive normalized product laws, independence of every latent event and assignment, monotonicity, positive first stage, all observed cells, equal observed laws, the reported respondent and full-population moments, both different complier mean pairs, both Corollary comparisons, and failure of identification from the observed law. It omits the completion formulas and parameters, conditional Bernoulli parameterization, and separately asserted always-taker and never-taker probabilities. The concrete tables replace that construction. Positivity of every respondent, treatment-cell, and respondent-cell denominator used in the formulas is explicitly certified.
- **T2:** Retains the joint-moment identities, mixed available-case identification, sufficient response independence, cell reweighting with empty cells omitted, both sensitivity intervals, and all eight exact source-table calculations. The unrestricted arm-mean equality under response independence is included even without positive pure cells. It omits the counterexample showing that cellwise mean ignorability need not imply respondent-arm mean equality. It also omits attainment of the four sensitivity endpoints and the resulting claim that these source-law bounds cannot be narrowed. Those existence assertions are not replaced by numerical endpoint calculations or by a new conversion of T1's finite laws into causal-response models.
- **T3:** Omitted because this target has no credited Lean rows. The separately credited counterexample for T1 does not supply a credited declaration for this printed empirical passage.
- **T5:** Retains E1–E4, failure of the mixture and corrected systems, all four numerical Proposition 1 endpoints, and existence of a bounded randomized model with input triple `(1/2, 3/4, 3/4)` and complier means `(1,1)`. It omits E5's equalities for the entire feasible coordinate sets. It also omits the specified E6 construction with half never-takers of potential outcome `1/2` and an independent fair assignment coin: the narrower row exports model existence and moments, without these construction properties.
- **T6:** Retains `0 < p ≤ 1`, bounded noncomplier contribution, both mixture equations, its observable product-moment representation, both compliance branches, the positive-event noncomplier mean and bounds, complier formulas permitting empty treatment cells, all interval inequalities, and all four singleton endpoint identities. It omits the existential witness showing that the assumptions permit `p=1`, the optional positive-pure-cell probability-times-mean expression for the contribution, and the separate empty-cell product-moment-zero assertion.
- **T9:** Adds global integrability of each measurable potential outcome through `CausalModel.integrableY`. All four observed cell means being ordinary finite means does not itself bound the unused counterfactual outcome on always-takers or never-takers. The theorem retains arm reconstruction from the four cell moments, both printed complier formulas, the intermediate noncomplier ratio, and positive masses for every conditional event used. Positive treatment-assignment cells implement the existence of the four conditional means in the printed premise.
- **T10:** Adds global integrability of both measurable potential outcomes for the universal population first-stage, reduced-form, and LATE identities. This excludes models with finite observed-arm and complier moments but nonintegrable unused potentials. It also omits the canonical clause about estimating components using sample analogues to population quantities. The existential failure of identification from the three figures is fully retained, with the two bounded randomized models and all their exact moments.

The counterexample targets T5 and T7 are already counterexamples in the canonical claims. They are therefore classified as restricted and whole respectively, rather than as refutations of positive canonical assertions.

## Complete targets

- **T4** includes the mixture/corrected-system equivalence, uniqueness formula for the noncomplier mean, both substitutions, corrected contribution interval, both equivalent lower-endpoint expressions, the treated-interval characterization, both endpoint translations, the exact weaker printed constraint and its redundancy, and a strictness witness.
- **T7** includes the explicit fair two-atom full-compliance law, random assignment, all standing causal and boundedness facts, observed and complier means, null noncomplier and pure-cell events, zero proof denominators and numerators, indeterminacy of the noncomplier mean, and the valid singleton intervals. It does not assign an ordinary mean to a null event.
- **T8** includes validity of both intervals on arbitrary probability spaces, nonemptiness of both intervals for every compatible triple, and attainment of every treated and control interval value by an actual bounded randomized model. Full compliance is included.

## Definitions and bridges

This uses the shared-definition route. `SAP/P028/Defs/Part1.lean` through `Part9.lean`, imported by `Defs.lean`, depend only on Mathlib and earlier SAP definition parts. Challenge and Solution import these same compiled definitions. There are no project imports in the Challenge dependency chain.

`Bridge/Part1.lean`, imported by `Bridge.lean`, provides:

- `toAudit` and `fromAudit`, which preserve every causal-model field, including probability, measurability, integrability, random assignment, positive arms, and the nonzero first stage. The round trip and displayed quantity correspondences are proved by reduction. The existing population theorems consequently transport directly, and existential project models become SAP models without changing any moments.
- `toAuditResponse`, which copies the response variable and its measurability proof. Response events, conditional laws, and response moments agree by reduction.
- `toAuditAtom`, `fromAuditAtom`, `toAuditLaw`, and `fromAuditLaw`, which copy all binary coordinates and rational masses. Finite observed-law and complier-mean correspondences are proved by reduction.
- `lower_law` and `upper_law`, which identify the two SAP tables with the project tables after structural conversion. Their proofs use constructor congruence, function extensionality, and the seventeen index cases, each closed by reduction.
- `lower_mean_domain` and `upper_mean_domain`, which check the remaining conditioning masses by exact rational evaluation of the existing seventeen-entry tables for the finitely many binary cells. These are elementary arithmetic checks, with no inference about response behavior.

All other glue is instantiation, conjunction, extraction of existing conclusions, logical composition, or scalar algebra on exported identities. In particular, control sharpness uses the already exported treated sharpness and endpoint translations; interval nonemptiness comes from the existing numerical compatibility theorem. The corrected-system strictness witness uses the existing reframing equivalence and ground rational arithmetic.

The manifest distinguishes credited rows invoked directly from supporting project declarations used for positivity, probability partition, and scalar transport. Unused credited helper rows are accounted for individually.

## Validation

Every definition part and root, the bridge part and root, the Challenge part and root, and Solution compiled with `/home/ubuntu/sap/tools/sap-lean`, in dependency order. The only expected Challenge diagnostics concern its prescribed proof stubs. No project source or supplied input was changed.

`scratch/P028Axioms.lean` was compiled after the final successful Solution build. Its output, saved in `scratch/P028Axioms.log`, reports exactly `propext`, `Classical.choice`, and `Quot.sound` for each of the nine proved theorems. These match the manifest and permitted list.

Both JSON files parse. The manifest accounts for all ten unit targets and every credited row. The Comparator theorem list is exactly the nine non-omitted Challenge/Solution names. Every SAP file is at most 300 lines; each SAP Lean module sets both required implicit-variable options immediately after imports. The token and import checks pass.

`comparator.json` supplies the requested modules, theorem names, empty explicit definition list, permitted logical principles, and external-kernel commands. The subsequently supplied [Comparator result](SAP/P028/verification/comparator-result.json) records acceptance of all nine theorems on the pre-review snapshot, with all three kernel acceptance markers; the [Comparator log](SAP/P028/verification/comparator.log) confirms them. Every source hash matched that snapshot before this revision. This round changes the T10 docstring and manifest disclosure; the certificate's source hashes refer to the earlier snapshot. No new external-kernel run is claimed for the documentation revision.

## Points requiring care

The canonical text, rather than the coverage summaries, determines completeness. In particular, T1's numerical counterexample does not explicitly restate its Bernoulli construction, and T9's globally integrable model is a stronger domain than finite observed cell means alone. Both differences are disclosed as restrictions even though their selected credited components were reviewed as usable.

No response assumption is asserted for the application data. No numerical completion calculation is presented as endpoint attainment. No quotient value on a zero denominator is described as an existing conditional mean.

## Declaration review round 1

- **T10, reviewer A: `restriction_inaccurate`, minor.** Accepted. The [finding](fw/round1/T10/a/findings.json) correctly identifies the sample-analogue estimation clause in `work.json` at `targets[P028-T10].canonical_claim.statement`. `T10Statement` contains only population identities and population-model witnesses. The historical note excluding estimation does not override that canonical clause. The T10 docstring in [Challenge/Part1.lean](SAP/P028/Challenge/Part1.lean) and its restriction in [manifest.json](SAP/P028/manifest.json) now explicitly disclose that the estimation clause is omitted, in addition to the existing global-integrability restriction. The decision remains `restricted`.
- **T10, reviewer B: `faithful`, none.** Checked the [finding](fw/round1/T10/b/findings.json) against `lateFormulas`, `nonidentificationOfLevels`, `T10Statement`, the causal-model fields, and the Solution proof. Its assessment of the population mathematics, positive conditioning masses, and retained nonidentification witness is consistent with the declarations. No mathematical change was needed; reviewer A's additional disclosure corrects the incomplete description of omitted content.

No shared definition, theorem statement, theorem name, bridge, or Solution proof changed. No new mathematical argument was added. `comparator.json` was regenerated from the nine non-omitted manifest entries and retains exactly the same configuration.

All fifteen SAP Lean modules were recompiled in dependency order with `sap-lean`; the build log is `scratch/P028Round1Build.log`. The nine dependency checks were rerun afterward using `scratch/P028Axioms.lean`, with output in `scratch/P028Round1Axioms.log`. The results remain exactly `propext`, `Classical.choice`, and `Quot.sound` for every theorem. Both JSON files parse, and the theorem-name correspondence, row accounting, implicit-variable settings, token restrictions, and 300-line limits were checked again. There are nine proved theorems and no open glue tasks; the decision counts remain three whole, six restricted, zero refuted, and one omitted.

## Whole versions (new proofs)

The following six targets now use their proved whole statements. This section supersedes their earlier restrictions and the historical decision counts above: there are now nine whole targets and one omitted target. Existing definitions, blueprints, leaves, and generated whole proofs are unchanged.

All six Challenge stubs are in `SAP/P028/Challenge/Part1.lean`; their Solution declarations are in `SAP/P028/Solution.lean`, and their updated decisions and dependencies are in `SAP/P028/manifest.json`.

- **P028-T10** (`SAP.P028.T10`): `SAP.P028.T10WholeStatement` is proved by `SAP.P028.WH.W1.T10_whole`. Files: `SAP/P028/Defs/WholeW1.lean`, `SAP/P028/WH/W1/Leaves.lean`, `SAP/P028/WH/W1/Proofs/T10.lean`, `SAP/P028/WH/W1/P/T10_L1.lean`, `SAP/P028/WH/W1/Late.lean`.

  Removed restriction: Restricted to population first-stage, reduced-form and LATE identities for measurable, globally integrable potential outcomes. This excludes models with finite observed and complier moments but nonintegrable unused potential outcomes. The canonical statement's clause about estimating components using sample analogues is omitted. The existential nonidentification of complier levels from the three reported figures is retained, with explicit bounded randomized models.

- **P028-T1** (`SAP.P028.T1`): `SAP.P028.T1WholeStatement` is proved by `SAP.P028.WH.W1.T1_whole`. Files: `SAP/P028/Defs/WholeW1.lean`, `SAP/P028/WH/W1/Leaves.lean`, `SAP/P028/WH/W1/Proofs/T1.lean`, `SAP/P028/WH/W1/Finite.lean`, `SAP/P028/WH/W1/Donors.lean`.

  Removed restriction: Retains the two exact 17-atom laws, normalized positive product masses, latent-event independence, monotonicity, positive first stage, source cells and moments, both distinct complier means, full-versus-respondent Corollary comparisons, and nonidentification. Omits the completion formulas and parameters, the conditional Bernoulli construction, and separately asserted always-taker and never-taker probabilities. Every finite conditional-mean denominator used in the theorem is explicitly positive.

- **P028-T2** (`SAP.P028.T2`): `SAP.P028.T2WholeStatement` is proved by `SAP.P028.WH.W1.T2_whole`. Files: `SAP/P028/Defs/WholeW1.lean`, `SAP/P028/WH/W1/Leaves.lean`, `SAP/P028/WH/W1/Proofs/T2.lean`, `SAP/P028/WH/W1/P/T2_L1.lean`, `SAP/P028/WH/W1/P/T2_L2.lean`, `SAP/P028/WH/W1/P/T2_L3.lean`, `SAP/P028/WH/W1/P/T2_L4.lean`, `SAP/P028/WH/W1/Finite.lean`, `SAP/P028/WH/W1/Donors.lean`.

  Removed restriction: Retains joint-moment identification, mixed available-case identification, response-independence sufficiency (including arm mean equality without positive pure cells), cell reweighting with empty cells omitted, both sensitivity intervals, and all eight exact worked-table values. Omits the counterexample that cellwise mean ignorability need not give respondent-arm mean equality; also omits attainment of the four sensitivity endpoints and the consequent sharpness assertion for this observed law.

- **P028-T5** (`SAP.P028.T5`): `SAP.P028.T5WholeStatement` is proved by `SAP.P028.WH.W1.T5_whole`. Files: `SAP/P028/Defs/WholeW1.lean`, `SAP/P028/WH/W1/Leaves.lean`, `SAP/P028/WH/W1/Proofs/T5.lean`, `SAP/P028/WH/W1/Elementary.lean`.

  Removed restriction: Retains E1-E4, failure of both the mixture and corrected systems, all four numerical Proposition 1 endpoints, and existence of a bounded randomized model with the given input triple and complier means (1,1). Omits E5, equality of the entire feasible sets for both complier coordinates, and the specified E6 half-never-taker construction with outcome 1/2 and independent fair assignment.

- **P028-T6** (`SAP.P028.T6`): `SAP.P028.T6WholeStatement` is proved by `SAP.P028.WH.W1.T6_whole`. Files: `SAP/P028/Defs/WholeW1.lean`, `SAP/P028/WH/W1/Leaves.lean`, `SAP/P028/WH/W1/Proofs/T6.lean`, `SAP/P028/WH/W1/Elementary.lean`, `SAP/P028/WH/W1/Donors.lean`.

  Removed restriction: Retains positivity and the upper bound on p, bounded contribution and mixture equations, its observable product-moment expression, both compliance branches, the positive noncomplier mean formula and bounds, null-cell-compatible complier formulas, all interval inequalities and singleton endpoints. Omits a witness that the assumptions permit p=1, the optional positive-pure-cell probability-times-mean expression for the contribution, and the separate assertion that an empty treatment-assignment cell has zero product moment.

- **P028-T9** (`SAP.P028.T9`): `SAP.P028.T9WholeStatement` is proved by `SAP.P028.WH.W2.T9_whole`. Files: `SAP/P028/Defs/WholeW2.lean`, `SAP/P028/WH/W2/Leaves.lean`, `SAP/P028/WH/W2/Proofs/T9.lean`, `SAP/P028/WH/W2/P/T9_L1.lean`.

  Removed restriction: Requires measurable, globally integrable Y(0) and Y(1) through the SAP CausalModel fields. The canonical printed premise about ordinary observed cell means does not itself constrain unused counterfactual outcomes. Positive cells represent existence of the four ordinary cell means; both identification formulas, arm reconstruction, and the intermediate noncomplier ratio are retained.

Dependent-proof repairs: none. The unchanged Solution proofs for T4, T7, and T8 do not reference any switched theorem; their statements and proofs remain byte-for-byte unchanged. No other target's manifest entry changed.

Validation of the whole-version switch: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P028` rebuilt all 35 P028 modules from scratch and passed its token scan; output is in `scratch/P028WholeRebuild.log`. The scratch file `scratch/P028WholeAxioms.lean` imports `SAP.P028.Solution` and runs `#print axioms` on all six switched theorems. Each reports exactly `propext`, `Classical.choice`, and `Quot.sound`; output is in `scratch/P028WholeAxioms.log`. No `lake` command was run, and Lean processes ran one at a time.
