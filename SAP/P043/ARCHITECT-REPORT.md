# P043 Challenge package

Counts: **2 whole, 3 restricted, 0 refuted, 1 omitted**. All **5** Challenge theorems have compiled, Comparator-certified Solutions; there are **0 open glue tasks**.

| Target | Decision | Declaration |
| --- | --- | --- |
| P043-T1 | restricted | `SAP.P043.T1` |
| P043-T2 | whole | `SAP.P043.T2` |
| P043-T3 | omitted | none |
| P043-T4 | restricted | `SAP.P043.T4` |
| P043-T5 | restricted | `SAP.P043.T5` |
| P043-T6 | whole | `SAP.P043.T6` |

## Restrictions and omission

- **T1:** Retains both specified randomized mediation witnesses: their finite state masses, response properties, exact numerical contrasts, complete conditional support laws, and assignment independence for every population event. Omits A4's separate statewise observed-support cancellation identity, B1's exact statewise control and treated knowledge formulas, and B3's separate observed-support conditional arm means of 59/25. The three intervention means and the zero reduced form remain stated. Exact finite support sets record the relevant index bounds. The examples refute an unconditional extension of the mediation comparison; neither example satisfies the contextual nonnegative-net-other-channel premise.
- **T3:** Omitted because there are no credited Lean declarations. Its empirical and interpretive prose is not established by the mediation identities or their cancellation examples. It is not labelled refuted.
- **T4:** Retains both IV constructions, their arm means and positive first stages, the zero IV ratio with individual increaser effects equal to one, all exported range and monotone-response facts, the full joint and conditional observable laws for the five-type models, their unequal increaser effects, and the impossibility of a common identifying functional. Omits the universal normalized nonnegative weighted-average assertion in (a3) and the exact increaser probabilities 2/5 and 3/5 in (b3). It proves that both latter probabilities are nonzero, guarding the conditional means. The constructions refute the stated reading of identification under assignment independence, exclusion, consistency and a positive first stage; the docstring makes no blanket assertion that the printed prose is false.
- **T5:** Restricts the population to finitely many types with arbitrary nonnegative weights summing to one. General probability laws, including nonatomic response laws, are outside the credited row's domain. Identification and covariance conclusions retain the aggregate's monotonicity and positive-first-stage hypotheses. Omits signed-crossing value-set membership for arbitrary nonmonotone models, the particular T4 down-type value at margin 9, and the separate nonidentification assertion without monotonicity. Retains both identification equations, the covariance factors and guarded covariance ratio, both monotone unit identities, both expected margin sums, nonnegative normalized weights, the positive-probability conditional-margin formula, general bounded signed telescoping, nonincreaser exclusion, signed membership/equality for the original monotone model, and the general downward-crossing implication.

**T2** states the arbitrary probability-law mediation comparison with exactly the five canonical integrability conditions, the unit identity, both weak and strict sign equivalences, both null inferences, the linear formulas and positive-first-stage ratio, and the sufficient but unnecessary channelwise sign condition. It also includes T1's fixed linear witness to the failure of the null inference without the net sign premise.

**T6** states all corrected-index content: selection of the nonreference coefficient, zero reference offset, the omitted-reference-indicator identity, and equivalence with the stratum-intercept equation. Zero-based `Fin (q+1)` labels cover all positive stratum counts, including the one-stratum case. It does not assert an estimation property or causal interpretation of the treatment coefficient.

## Shared definitions and Bridges

The package uses the shared Mathlib-only definitions route. `SAP/P043/Defs/Part1.lean` through `Part6.lean` define the finite population laws, mediation and IV potentials, their consistent observed outcomes, all numerical/probability quantities, the general-law product assignment model, the crossed-margin formula, and the corrected stratum indicators. Both Challenge and Solution import these exact modules through `SAP.P043.Defs`. No project declaration is recreated under its original fully qualified name.

`SAP/P043/Bridge.lean` supplies three field-preserving adapters:

- `toAuditPopulation` carries across the same probability weights, nonnegativity and normalization certificates.
- `toAuditMediation` carries across the same knowledge and support functions.
- `toAuditIV` carries across the same integer-dose and response functions.

The named correspondences for finite means, reduced forms, general-law reduced forms, integrable potentials, first stages and signed-unit claims are all proved by reflexivity. The fixed mediation statement equality is also reflexive. Concrete witness expressions reduce to the same finite sums even though their containing structures have different SAP and project names.

The five result transports use only these correspondences and existing credited results:

- **T1:** Direct definitional transport of `AronowAudit.P043.mediation_counterexamples`.
- **T2:** Direct transport of `AronowAudit.P043.Wave1.mediation_repair_integrable` with the mediation adapter. The final fixed-witness conjunct is projected from T1, and its positive mediated effect follows by numerical simplification of the exported 3/50 value. The manifest lists both source rows.
- **T4:** Conjunction projections of `AronowAudit.P043.iv_counterexamples`; the model-restricted range assertions are instantiated at each fixed model. If either increaser-event probability were zero, its displayed conditional-effect quotient would be zero, contradicting the exported value 1 or 4/3. This is only a quotient simplification and numerical contradiction.
- **T5:** Conjunction projections of the narrower `AronowAudit.P043.iv_repair`, instantiated with the population and IV adapters. Universally quantified alternate models are passed through `toAuditIV`; all response expressions then agree by reduction.
- **T6:** Direct definitional transport of `AronowAudit.P043.corrected_strata`.

No additional mathematical lemma or generalization of a credited row is introduced. Proof fields of the shared finite probability-law definitions repeat the existing constructions; they do not assert additional paper claims. There are no unused credited rows and no open proof plans.

## Defined quantities and scope checks

- General-law mediation requires a probability measure, an assignment probability strictly between zero and one, and integrability of exactly the five listed potentials. This excludes the nonintegrable-integral and zero/infinite arm-mass branches.
- All finite witnesses use their explicit normalized laws and nondegenerate fair assignment. The linear assignment variance is explicitly 1/4. IV first stages are explicitly positive, and the two five-type increaser conditional means have explicit nonzero event-probability conclusions.
- T5 assumes a positive mean knowledge increase, identifies it with the first stage, and includes conditional margin means only for positive-probability crossings. Its covariance quotient is explicitly guarded by a nonzero first stage.
- The counterexamples concern constructed populations. No theorem asserts a sign for the experiment's net other-channel effect, changes a reported estimate, or proves a GLS sampling claim.

## Validation

All six Defs parts, the Defs root, Bridge, the Challenge part and root, and Solution compiled with `/home/ubuntu/sap/tools/sap-lean` in dependency order. The Challenge diagnostics are limited to the required unfinished stubs. The five Solution declarations all have proofs.

`scratch/Axioms.lean` runs `#print axioms` for every Solution theorem; `scratch/axioms.log` records that each depends only on `propext`, `Classical.choice`, and `Quot.sound`. These lists are recorded in the manifest.

Both JSON files parse. Target IDs match `unit_targets` exactly; the comparator theorem list matches all and only non-omitted targets. Every package source and configuration file is below 300 lines. Every Lean module has both required implicit-variable options immediately after its imports. Challenge imports are restricted to shared Defs and Challenge parts; Solution does not import Challenge. The source-token check passes with the stub exception confined to Challenge.

The supplied certification helper expects writable shared certificate and Git-worktree directories. `scratch/RunComparator.py` redirects certificate output into `scratch/` and replaces only Git-worktree creation with a copied local source snapshot; comparator validation, compilation and kernel commands are unchanged. No existing source or Git metadata is modified. The copied snapshot was checked against all 1,482 existing project Lean modules and all delivered package sources and configuration files.

**Certification accepted:** run `20261104T000001Z`, with five certified theorems and one omitted target. The Comparator checked matching theorem statements and referenced definitions, then accepted the Solution in **con-ron**, **nanoda**, and the **Lean default kernel**. The verified con-ron run accepted 33,042 declarations. All acceptance markers are true.

Evidence: [comparator-result.json](SAP/P043/verification/comparator-result.json) and [comparator.log](SAP/P043/verification/comparator.log). The certificate records the snapshot, configuration, manifest, compiled-module and export hashes; its source/configuration hashes were checked against the delivered files after acceptance. The full successful snapshot and exports are retained under `scratch/cert/P043-20261104T000001Z/`; the copied certification worktree is under `scratch/worktrees/CERT-P043-20261104T000001Z/`.

## Whole versions (new proofs)

This update switches P043-T1 and P043-T4 from restricted to whole, giving **4 whole, 1 restricted, 0 refuted, 1 omitted**. The earlier restriction and transport descriptions above record the previous versions.

- **P043-T1 (`SAP.P043.T1`):** Challenge stub in `SAP/P043/Challenge/Part1.lean`; implementation in `SAP/P043/Solution.lean`; whole statement `SAP.P043.T1WholeStatement` in `SAP/P043/Defs/WholeW1.lean`; proved leaves in `SAP/P043/WH/W1/Leaves.lean`; generated theorem `SAP.P043.WH.W1.T1_whole` in `SAP/P043/WH/W1/Proofs/T1.lean`; updated entry in `SAP/P043/manifest.json`. Removed restriction: Omits A4's statewise observed-support cancellation formula, B1's exact statewise K(0) and K(1) formulas, and B3's separate conditional observed-support arm-mean equalities of 59/25. Retains the intervention means, both complete arm support laws, all other exported numerical facts, and both counterexamples. These refute an unconditional extension; they do not refute the paper's contextual nonnegative-net-other-channel comparison.

- **P043-T4 (`SAP.P043.T4`):** Challenge stub in `SAP/P043/Challenge/Part1.lean`; implementation in `SAP/P043/Solution.lean`; whole statement `SAP.P043.T4WholeStatement` in `SAP/P043/Defs/WholeW1.lean`; proved leaves in `SAP/P043/WH/W1/Leaves.lean`; generated theorem `SAP.P043.WH.W1.T4_whole` in `SAP/P043/WH/W1/Proofs/T4.lean`; updated entry in `SAP/P043/manifest.json`. Removed restriction: Omits the universal normalized nonnegative weighted-average assertion in (a3) and the exact five-type increaser probabilities 2/5 and 3/5 in (b3). Retains nonzero conditioning probabilities, the individual increaser effects, both witnesses, their complete observable laws, and full-law nonidentification. The constructions refute the reading that independent assignment, exclusion, consistency and a positive first stage identify an effect among increasers.

Dependent proof repair: **P043-T2** in `SAP/P043/Solution.lean` now obtains the fixed linear witness from `Bridge.mediationWitnesses`, the proof term previously used for T1, instead of destructuring `SAP.P043.T1` at its old type. T2's statement and docstring are unchanged. Its existing `AronowAudit.P043.mediation_counterexamples` row still accounts for that witness, so its manifest entry is unchanged.

Validation for this switch: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P043` rebuilt all **15** P043 modules from scratch and passed the token scan. `scratch/WholeAxioms.lean` imports only `SAP.P043.Solution` and runs `#print axioms` for T1 and T4; both report exactly `propext`, `Classical.choice`, and `Quot.sound`. Evidence: `scratch/whole-rebuild.log` and `scratch/whole-axioms.log`. Lean compilation ran sequentially through `sap-lean`; no `lake` command was run.
