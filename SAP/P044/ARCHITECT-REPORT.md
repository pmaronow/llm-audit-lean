P044 packages 13 targets: **9 whole, 1 restricted, 1 refuted, 2 omitted**. The whole targets are T1 through T9. All **11 non-omitted Challenge theorems are proved**, with no open glue tasks.

The supplied package already contained the whole versions of T2, T3, T7 and T9, proved by the existing `SAP.P044.WH.W1` declarations. This revision preserves every theorem name, mathematical statement, definition body, proof and decision. It adds no mathematical result or assumption.

| Target | Decision | Restriction or omission |
| --- | --- | --- |
| P044-T10 | restricted | The finite-law consequences assume zero crossing-edge marginals or explicit accepted-graph no-isolate and no-crossing conditions. The statement retains identity-block probability algebra, support consequences, edge counts, shares, both expected ratios and their 3/10 gaps. It does not construct the generator law or derive those law hypotheses from the source-code premise and rejection loop. |
| P044-T11 | omitted | Its sole credited row negates a stronger exact universal conjunction across independent and included-observation regimes. That does not refute the printed approximation assertion or its seed-reused workflow. The row remains valid for its own stronger contract; it is not used to establish this canonical target. |
| P044-T12 | omitted | Its sole credited row refutes an extension that drops zero-support contributions, outside S7's positive-input estimator domain. It also supplies none of the quoted Hajek/WLS consistency or efficiency assertions. The row remains valid for its own extension; it is not used to establish this canonical target. |

T13 is `refuted`: under the supplied ideal Gaussian generator model, the positive printed baseline-law assertion fails at every supplied nonempty loopless Boolean network. Its necessary baseline-law conjunct is negated, without claiming that the multiplier identities or the unspecified degree-correlation prose are false. T1 and T7 state their canonical counterexamples; they are not presented as refutations of the separate printed targets T11 and T12.

The whole T2 statement retains exact-input conservativeness and its surplus, both finite-bank observation laws, the matching family with 10,000 distinct draws and first-row reuse, and the conditional error-transfer result. That last result assumes bounds on errors of estimator expectations and contrast variances. It supplies no propagation theorem from errors of individual marginal or joint probability inputs. The Hajek sentence remains a scope qualification rather than a new finite-sample guarantee.

The whole T3 statement includes the six exposure vectors and positivity for every observed inverse-probability term, so the reported means and biases require no additional positivity hypothesis. T7 includes its base exposure vector, individual joint counts and entries, and exact-joint marginalization identity. T9 includes ordered profile deletion/insertion and the matrix-dimension diagnosis. These were present before this review revision.

Shared SAP definitions are compiled once and imported by both theorem modules. `Defs/Part1.lean` through `Part8.lean` and `Defs/WholeW1.lean` import only Mathlib and earlier SAP definitions. The Challenge imports no project module, and the Solution imports no Challenge module.

The existing bridges provide the following correspondences:

- `Bridge/Part1.lean`: reflexive equalities for generic scalar, network and estimator definitions, an adapter preserving finite-design masses and their certification fields, and the equivalence of the four exposure labels.
- `Bridge/Part2.lean`: transport of label comparisons, finite sums, weights, estimators and the four-case mapping, by unfolding and injectivity or constructor cases.
- `Bridge/Part3.lean`: the same correspondences for the clique, star and cycle data.
- `Bridge/Part4.lean`: function-valued transport and the exposure-count partition, by instantiating Mathlib's finite-fiber cardinality identity.
- `Bridge/Part5.lean`: agreement of optimized exact clique weights with actual marginals, using the existing observation-marginal certificate; integrability transported from existing second moments through measure maps, product-coordinate evaluation and finite linear operations.

Vertices use zero-based indices, corresponding to printed indices by adding one. The finite numerical witnesses use exact rational arithmetic, whose canonical real embedding preserves the relevant sums, guarded divisions and comparisons. Population means and general effects have positive-population guards, exhaustive banks have positive size, exact-input HT claims have their stated support conditions, and arbitrary inverse weights are positive. Gaussian statements include the required finite moments and integrability. Graph-share statements exclude zero edge totals through positive degrees and a nonempty population.

Software provenance remains external. The package does not establish the identity of a historical seeded network, rejection-loop termination, or an error in a published table cell. The matching counterexample at 10,000 draws is a specified finite design, rather than an identification of the chapter's historical numerical example.

## Declaration review round 1

**Finding: SAP.P044.T2, not_faithful/minor.** The reviewer correctly observed that the two docstrings called the transfer assumptions “Probability error bounds” and suggested that those bounds gave the identity. See the [T2 entry in the review findings](fw/round1/T2/r4g1/findings.json) and the [review report](fw/round1/T2/r4g1/REPORT.md).

I checked `W1ErrorTransfer` in [WholeW1.lean](SAP/P044/Defs/WholeW1.lean) and its existing `error_transfer` proof in [Leaves.lean](SAP/P044/WH/W1/Leaves.lean). With the stated design, support and table conditions, the exact transfer identity requires no epsilon bounds. The corrected inequality additionally assumes `|E_J(Vw - V0)| ≤ epsilonV` and `|Var_J(Tw) - Var_P(T0)| ≤ epsilonT`. These concern estimator expectations and contrast variances; they do not bound errors of individual exposure-probability inputs.

**Action:** corrected both copies of the T2 docstring, in `Challenge/Part1.lean` and before `T2WholeStatement` in `Defs/WholeW1.lean`, to say: “An exact transfer identity gives a corrected inequality under bounds on the expected variance-estimate error and the contrast-variance error.” The `whole` decision and all mathematical content are unchanged. There is no disagreement with this finding. The other entries in that findings file report T1, T3, T4 and T5 as faithful and require no correction.

**Formatting and metadata:** four supplied Lean files exceeded the brief's 300-line cap. Blank lines were removed from `Defs/WholeW1.lean` and `WH/W1/Leaves.lean`; blank lines and existing declaration-header line breaks were compacted in `WH/W1/P/T2_L3.lean` and `T2_L8.lean`. Their mathematical tokens are unchanged. Every SAP file now meets the cap. Across all 32 Lean files, removing comments and whitespace gives exactly the pre-review token content; no shared mathematical definition has changed. The manifest records the resolved T2 finding and removes four entries that were listed as both used and unused. Comparator configuration values, including theorem names, permitted axioms and external-kernel commands, are preserved.

**Validation:** all 32 SAP Lean modules were recompiled with `sap-lean` in dependency order, with no more than one Lean compiler running for that rebuild. `#print axioms` was rerun for every one of the 11 proved theorems; only `propext`, `Classical.choice` and `Quot.sound` occur. Separate fully explicit Challenge and Solution theorem-type outputs agree byte for byte. Both JSON files parse, cover exactly this unit's targets and list the same 11 non-omitted theorems. Detailed checks are recorded under `scratch/round1/`.

**Certification provenance:** the supplied [Comparator result](SAP/P044/verification/comparator-result.json) and [kernel log](SAP/P044/verification/comparator.log) record prior acceptance of all 11 theorems by con-ron, nanoda and Lean's default kernel. Its recorded Lean source hashes match the pre-review snapshot saved for this revision. Those historical certificate records are preserved. This round recompiles and checks axioms and type identity; it does not claim a new three-kernel run for the revised source-file hashes.

## Declaration review round 2

**Finding: SAP.P044.T9, not_faithful/minor.** The reviewer correctly identified the same misleading equivalence in the Challenge docstring and the `T9WholeStatement` docstring. The joint subject suggested that both no interference and interference were equivalent to invariance at fixed own treatment. See the [T9 entry in the review findings](fw/round2/T9/r5g2/findings.json) and the [review report](fw/round2/T9/r5g2/REPORT.md).

I checked the universal equality in `w1OrderedNoInterference`, the existential inequality in `w1OrderedInterference`, and the separate equivalences in [WholeW1.lean](SAP/P044/Defs/WholeW1.lean), together with the existing `ordered_interference` and `T9_assembly` proofs in [Leaves.lean](SAP/P044/WH/W1/Leaves.lean). No interference is equivalent to invariance at fixed own treatment. Interference is equivalent to the negation of no interference, and therefore to failure of that invariance.

**Action:** corrected both docstrings, in `Challenge/Part1.lean` and before `T9WholeStatement` in `Defs/WholeW1.lean`, to say: “The corrected interference definition is the negation of no interference. No interference is equivalent to invariance at fixed own treatment.” T9 keeps its `whole` decision and the same fully qualified theorem name, mathematical statement and proof. There is no disagreement with either occurrence of the finding. The same findings file reports T6, T7, T8 and T10 as faithful, with no corrections required.

**Scope and metadata:** only those two Lean docstrings changed. Source outside comments is byte-for-byte unchanged in all 32 Lean modules, so no shared mathematical definition or proof was changed and no hypotheses were added. The manifest records the resolved T9 finding. The Comparator configuration was regenerated with the same theorem list, permitted axioms and external-kernel commands. Counts remain 9 whole, 1 restricted, 1 refuted and 2 omitted; all 11 listed theorems remain proved, with no open glue tasks.

**Validation:** all 32 modules were recompiled with `sap-lean` in dependency order, sequentially. `#print axioms` was rerun for all 11 proved theorems and lists only `propext`, `Classical.choice` and `Quot.sound`. Fully explicit Challenge and Solution theorem-type outputs agree byte for byte. Both JSON files parse, preserve target and theorem coverage, and every SAP file remains within the 300-line limit. The baseline comparison and validation records are under `scratch/round2/`.

The supplied historical Comparator result and kernel log remain untouched. This revision does not claim a fresh three-kernel run for its new source hashes; its formal definitions, statements and proofs are unchanged.
