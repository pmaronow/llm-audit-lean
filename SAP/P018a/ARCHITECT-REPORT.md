P018a packages exactly P018-T1 through P018-T14. P018b and all other targets are outside this package.

| Decision | Count |
| --- | ---: |
| whole | 13 |
| restricted | 1 |
| refuted | 0 |
| omitted | 0 |

All fourteen current Challenge statements have proved Solutions. There are no open glue tasks. Every target except T5 is whole; T5 retains the restriction documented below. The whole-statement modules were supplied before this review revision. The counterexample targets already assert counterexamples in their canonical text, so they are classified as whole or restricted, rather than as refuted positive assertions.

## Earlier package scope (historical)

The following original restriction notes and round-1 evidence describe the earlier snapshot. Ten of these restrictions were subsequently removed using the supplied whole-statement proofs, as recorded under “Whole versions” below; their current manifest entries govern.

**P018-T1 (restricted).** Retains the nonlinear model, bounded ranges, population projection, almost-sure rank for N >= 3, zero conditional covariances and printed meat, exact score-variance decomposition and N = 3 value, positive matrices and determinants, target limit, CLT and sandwich probability limit. Drops the explicit two-row determinant formula; the conditional-mean equality and nonlinearity assertion; separate residual orthogonality and disjoint-score moment assertions; the overlapping-score interpretation of Gamma; the general-N entrywise variance display; the separate scaled-score variance limit and explicit Q-inverse sandwich identity; and both repeated/unit-weight extensions in (f).

**P018-T2 (restricted).** Retains score centering, zero disjoint score moments, the sparse unconditional and conditional-second-moment forms, the omitted-term decomposition with M defined as Var(sum X_d m_d), its positive semidefiniteness and zero-term equivalence, the disjoint conditional remainder, the D H + N(N-1)(N-2) Gamma formula, and the target limit. Drops the explicit identifications M = Var(E[S | X]) and of the full conditional double sum with E[Var(S | X)], the overlapping-score representation of Gamma, the separately displayed rational finite-N formula for V, the separate assertion that projection orthogonality alone is insufficient, and the repeated/weighted score replacements mentioned in the repair text.

**P018-T3 (restricted).** Retains the sign-model mean-step counterexample and surviving consistency, the deterministic missing-N counterexample, the spike example, the three eight-sign covariance values, and the inverse-Gram probability and infinite-moment conclusions. For the inverse design, rank and moment bounds are packaged only for all N above an unspecified threshold at least 3; the exact population determinant identity is dropped. Also drops the general-N fit, exact residual bound and deterministic design-Gram formulas, the unscaled score-variance identity, the arbitrary-array overlap identity, samplewise meat formulas and their unnormalized/normalized mean-difference limits, the explicit scaled-estimator mean limit and fourth-moment/variance formulas, and the general linear-form/general-N covariance identity and six-case classification. The eight-sign covariance formulas are stated directly as finite fair-sign expectations, without an additional OLS-identification assertion.

**P018-T5 (restricted).** Retains the N = 3 covariance matrices and universal parameter mismatch, the fixed-component GLS calculation and variance ratio, and the translation-equivariant intercept variance bound. For that bound, independence of the centered response from the Gaussian unit average, measurability, and both finite second moments are explicit hypotheses; their derivation for design (4) is not asserted. Drops the general-N random-effect covariance derivations, general-N mismatch and binomial(N,3) count, Gaussian average/centered-effect independence, the four displayed numeric lower bounds, and the repeated-observation extension.

**P018-T7 (restricted).** Retains the bounded sign-pair model conditions, Q and beta, projection covariance and limiting target, exact finite-N target, limiting probability of a negative slope variance estimate, absolute sandwich consistency, and the exact N = 8 Gram, determinant, OLS coefficient and negative sandwich value. Drops the sample-rank failure probability and exact residual bound, the separately displayed residual and score moment identities and finite score-variance formula, the explicit inverse-Q display and target-convergence assertion, the N = 8 meat display and positive-probability embedding, the joint second-order weak limit, and the nonnormal studentized-pivot assertion. The latter uses a totalized square root/division in the source and is not asserted as a real statistic on negative-variance samples.

**P018-T8 (restricted).** Retains the possibly singular projection CLT, target and sandwich limits, vanishing probability of nonpositive estimated contrast variance, and confidence-interval coverage for 0 < alpha < 1. The normal-pivot conclusion additionally assumes that, eventually in N, the estimated contrast variance is strictly positive almost surely, so its denominator exists as a positive real square root. Drops the separate degenerate-contrast failure example cited at the end of (iii); T7 supplies negative-estimate facts separately.

**P018-T9 (restricted).** Retains positive bounded weights, the variance lower bound and limit, the uniform positive deviation probability, nonexistence of a common deterministic target, and the repeated-data joint-law transfer. Drops the finite formulas for S_N, W_N, the coefficient array and its sum/first coefficient, the explicit fixed first-eight-sign event and its sharper sandwich bound, the separately asserted coefficient inconsistency and divergent N-scaled variance, the normalized-design limit and coefficient limit, and the explicit population-slope, residual, unweighted-Gram and fitted-residual certificates.

**P018-T10 (restricted).** Retains C1 with the canonical common record-index kernels and overlap-mean condition, weighted consistency for the S9 symmetric single-record dyad model, exact positive scale invariance on nonsingular sample/population designs, and the bounded-weight sign-model obstruction. Does not state weighted consistency for the more general directed-record formulation of S7, or the separate assertion that stacked normal equations alone cannot replace the overlap-mean condition. Scale invariance explicitly uses N >= 2 and ordinary-inverse rank hypotheses.

**P018-T11 (restricted).** Retains N times the intercept estimator variance equal to 4, the literal scalar target 4/D tending to zero, scaled-sandwich consistency for 4, and the missing-sum/restored-sum scalar algebra. Drops the general-N fit and conditional-covariance/single-dyad-meat identifications, exact samplewise and expectation sandwich formulas, explicit convergence of the two differences to 4, the stochastic score-variance formula, and all repeated T > 1 and two-regressor weighted-model calculations in (e)-(f).

**P018-T12 (restricted).** Retains centered total scores, expected normalized Grams, exact covariance interpretations, almost-everywhere nonsingular-sample linearizations for repeated and weighted records, single-record/unit-weight reductions, and the equivalent repeated-target normalization. The linearizations are almost everywhere, rather than on every nonsingular sample. Explicitly requires a positive total repeated observation count wherever it divides by L. The repeated and weighted identity groups additionally assume R.T N d > 0 for every dyad at the chosen size; zero-record dyads are excluded from those groups even when L > 0 and the population Gram is nonsingular. Drops the sparse covariance and uncentered-moment claims in (iii), and both model checks in (vi).

**P018-T13 (restricted).** Retains the binary witness, fitted probabilities and residuals, score, unique maximizer, nonsingular design, exact bread and inverse, both middle factors and covariance matrices, their difference and positive definiteness, neighbor-residual sums and the unit-incidence representation. Drops only the separate assertion that the entire log-likelihood function is strictly concave; uniqueness of its maximizer is still stated.

**Definition route and bridges.** All mathematical vocabulary is declared in the shared Mathlib-only Defs parts in namespace SAP.P018a. Both theorem modules import those same compiled definitions. No project constant occurs in a Challenge or Defs import or statement. The Solution never imports Challenge.

Bridge.toKernel preserves the three fields of the SAP unit model. Bridge.toRepeated preserves all four fields of the SAP repeated-record model, including dependent record indices. The dyad, endpoint, standing-assumption, sample-data, target, conditional-quantity and single-record correspondences are proved by reflexivity (or a conjunction of reflexive equalities). Proof irrelevance handles the finite-set nonemptiness arguments used for minimum/maximum endpoints.

The singleWeighted correspondences remove a singleton Fin 1 record index with Fin.sum_univ_one, then rewrite the resulting Gram, cross-product, coefficient, block-score, variance and target expressions. These are structural finite-array adapters. The existing singleStanding declaration supplies the single-record standing assumptions. They let the reviewed common-directed-kernel weighted consistency theorem apply to the retained symmetric single-record weighted model. All other transports elaborate by definitional equality. The only added consequences are conjunction/projection, strengthening an eventual rank threshold to at least 3, finite matrix arithmetic, and the direct limit consequence of the exported Chebyshev bound.

**Review and scope checks.** Current canonical text takes precedence over historical coverage notes. In particular T10 already contains common record-index kernels and overlap-mean control; these are not new assumptions taken from a suggested repair. T2 is deliberately restricted even though its coverage summary says full: the package does not silently promote equivalent-looking aggregate conditional-expectation identifications or an overlapping-score representation into additional exported clauses. T13 retains unique maximization without asserting global strict concavity.

The narrower inverse-design row is used only with its exported eventual rank, never as a claim of rank for every N >= 3. Both narrower T12 rows retain their almost-everywhere sample quantifier. T8's extra eventual almost-sure positivity protects the real studentized denominator. T7 makes no failed-pivot assertion on samples with negative estimated variance. Probability measures and bounded-data conditions protect the finite integral and probability conversions; the normal quantile appears only at 1-alpha/2 with 0 < alpha < 1. Finite inverse identities use nonsingularity guards, and the repeated finite formulas explicitly require a positive L. Asymptotic sample inverses follow the source's stated total convention on singular samples; the inverse-moment witness is asserted only on its eventual almost-sure rank domain, and its expectation is an extended nonnegative integral rather than a real integral of a nonintegrable quantity.

Some Solutions reuse reviewed components credited elsewhere within this unit: T10 uses the T9 weighted obstruction and the T3 sign-model standing/rank facts; T13 uses T14's logistic incidence identity; T14 uses T13's numerical meat certificate. These names are included in rows_used. Rows_not_used means not called separately by the package, and does not deny their use inside an existing project's proof.

**Validation.** Compile results and final foundation-dependency results are recorded under scratch. Every SAP source has both implicit-parameter options disabled and is at most 300 lines. The manifest and comparator JSON parse, list exactly the fourteen unit targets/theorems, and contain no open proof entries. All fourteen Solutions depend only on propext, Classical.choice and Quot.sound. No baseline project or pilot file was edited.

The orchestrator-supplied [Comparator result](SAP/P018a/verification/comparator-result.json) records acceptance of all fourteen theorems by the Comparator and all three kernels for the prior source snapshot. That artifact is preserved. No new Comparator run was performed here; this revision changes only documentation and metadata.

## Declaration review round 1

Both open findings are accepted and corrected. The decisions remain 3 whole and 11 restricted, with fourteen proved Solutions and no open glue tasks.

- **T7: restriction_inaccurate, minor.** The [review finding](fw/round1/T7/r2g2/findings.json) correctly distinguishes a slope coefficient estimate from its variance estimate. The event in [Defs/Part4.lean](SAP/P018a/Defs/Part4.lean:69) is `(sampleVariance ...) 1 1 < 0`; the same declaration has coefficient zero and slope variance estimate -13/288 in its finite witness. Corrected the Challenge summary to say “negative finite-sample estimates of slope variance” and the restriction to say “negative slope variance estimate”. Updated the manifest restriction and this report to agree.
- **T12: restriction_inaccurate, minor.** The [review finding](fw/round1/T12/r2g3/findings.json) correctly identifies the per-dyad positivity clause in [RepeatedAtSize](SAP/P018a/Defs/Part2.lean:180), used by both principal identity groups in [T12Statement](SAP/P018a/Defs/Part4.lean:178). The Challenge restriction, manifest and report now explicitly disclose R.T N d > 0 for every dyad at the chosen size, excluding zero-record dyads from those groups even when L > 0 and the population Gram is nonsingular. The separate equivalent-normalization group has no added per-dyad positivity requirement.

The metadata generator has the same wording corrections, so regeneration preserves them. No shared definition, theorem type, Bridge or Solution proof was edited; byte hashes in `scratch/round1-before.json` and `scratch/round1-validation.json` verify this. The Comparator configuration was regenerated and revalidated with the same fourteen theorem names, permitted foundations and external-kernel settings. All SAP modules were recompiled in dependency order with sap-lean, and the fourteen dependency checks were rerun. Evidence is in `scratch/round1-compile.log`, `scratch/round1-foundations.log` and `scratch/round1-validation.json`. Every check passed with only the three permitted foundations.

## Whole versions (new proofs)

The ten targets below now use the proved whole statements in `switch.json`. Their Challenge declarations remain proof stubs; the Solution uses the generated whole theorem in each listed Proofs module. The prior restriction notes above describe the earlier source snapshot. The current decisions are 13 whole and 1 restricted (P018-T5), with all fourteen Solutions proved.

### P018-T13

- Whole statement: `SAP.P018a.T13WholeStatement`.
- Solution proof: `SAP.P018a.WH.W1.T13_whole`.
- Files: `SAP/P018a/Challenge/Part2.lean`, `SAP/P018a/Defs/WholeW1.lean`, `SAP/P018a/WH/W1/Leaves.lean`, `SAP/P018a/WH/W1/P/T13_L1.lean`, `SAP/P018a/WH/W1/Proofs/T13.lean`, `SAP/P018a/Solution.lean`.
- Removed restriction: Retains the binary witness, fitted probabilities and residuals, score, unique maximizer, nonsingular design, exact bread and inverse, both middle factors and covariance matrices, their difference and positive definiteness, neighbor-residual sums and the unit-incidence representation. Drops only the separate assertion that the entire log-likelihood function is strictly concave; uniqueness of its maximizer is still stated.

### P018-T8

- Whole statement: `SAP.P018a.T8WholeStatement`.
- Solution proof: `SAP.P018a.WH.W1.T8_whole`.
- Files: `SAP/P018a/Challenge/Part2.lean`, `SAP/P018a/Defs/WholeW1.lean`, `SAP/P018a/WH/W1/Leaves.lean`, `SAP/P018a/WH/W1/Proofs/T8.lean`, `SAP/P018a/Solution.lean`.
- Removed restriction: Retains the possibly singular projection CLT, target and sandwich limits, vanishing probability of nonpositive estimated contrast variance, and confidence-interval coverage for 0 < alpha < 1. The normal-pivot conclusion additionally assumes that, eventually in N, the estimated contrast variance is strictly positive almost surely, so its denominator exists as a positive real square root. Drops the separate degenerate-contrast failure example cited at the end of (iii); T7 supplies negative-estimate facts separately.

### P018-T9

- Whole statement: `SAP.P018a.T9WholeStatement`.
- Solution proof: `SAP.P018a.WH.W1.T9_whole`.
- Files: `SAP/P018a/Challenge/Part2.lean`, `SAP/P018a/Defs/WholeW1.lean`, `SAP/P018a/WH/W1/Leaves.lean`, `SAP/P018a/WH/W1/P/T9_L1.lean`, `SAP/P018a/WH/W1/P/T9_L2.lean`, `SAP/P018a/WH/W1/P/T9_L3.lean`, `SAP/P018a/WH/W1/Proofs/T9.lean`, `SAP/P018a/Solution.lean`.
- Removed restriction: Retains positive bounded weights, the variance lower bound and limit, the uniform positive deviation probability, nonexistence of a common deterministic target, and the repeated-data joint-law transfer. Drops the finite formulas for S_N, W_N, the coefficient array and its sum/first coefficient, the explicit fixed first-eight-sign event and its sharper sandwich bound, the separately asserted coefficient inconsistency and divergent N-scaled variance, the normalized-design limit and coefficient limit, and the explicit population-slope, residual, unweighted-Gram and fitted-residual certificates.

### P018-T10

- Whole statement: `SAP.P018a.T10WholeStatement`.
- Solution proof: `SAP.P018a.WH.W1.T10_whole`.
- Files: `SAP/P018a/Challenge/Part2.lean`, `SAP/P018a/Defs/WholeW1.lean`, `SAP/P018a/WH/W1/Leaves.lean`, `SAP/P018a/WH/W1/P/T10_L1.lean`, `SAP/P018a/WH/W1/P/T10_L2.lean`, `SAP/P018a/WH/W1/P/T10_L3.lean`, `SAP/P018a/WH/W1/P/T10_L4.lean`, `SAP/P018a/WH/W1/P/T10_L5.lean`, `SAP/P018a/WH/W1/P/T10_L6.lean`, `SAP/P018a/WH/W1/P/T10_L7.lean`, `SAP/P018a/WH/W1/Proofs/T10.lean`, `SAP/P018a/Solution.lean`.
- Removed restriction: Retains C1 with the canonical common record-index kernels and overlap-mean condition, weighted consistency for the S9 symmetric single-record dyad model, exact positive scale invariance on nonsingular sample/population designs, and the bounded-weight sign-model obstruction. Does not state weighted consistency for the more general directed-record formulation of S7, or the separate assertion that stacked normal equations alone cannot replace the overlap-mean condition. Scale invariance explicitly uses N >= 2 and ordinary-inverse rank hypotheses.

### P018-T11

- Whole statement: `SAP.P018a.T11WholeStatement`.
- Solution proof: `SAP.P018a.WH.W1.T11_whole`.
- Files: `SAP/P018a/Challenge/Part2.lean`, `SAP/P018a/Defs/WholeW1.lean`, `SAP/P018a/WH/W1/Leaves.lean`, `SAP/P018a/WH/W1/P/T11_L1.lean`, `SAP/P018a/WH/W1/P/T11_L2.lean`, `SAP/P018a/WH/W1/P/T11_L3.lean`, `SAP/P018a/WH/W1/P/T11_L4.lean`, `SAP/P018a/WH/W1/P/T11_L5.lean`, `SAP/P018a/WH/W1/P/T11_L6.lean`, `SAP/P018a/WH/W1/Proofs/T11.lean`, `SAP/P018a/Solution.lean`.
- Removed restriction: Retains N times the intercept estimator variance equal to 4, the literal scalar target 4/D tending to zero, scaled-sandwich consistency for 4, and the missing-sum/restored-sum scalar algebra. Drops the general-N fit and conditional-covariance/single-dyad-meat identifications, exact samplewise and expectation sandwich formulas, explicit convergence of the two differences to 4, the stochastic score-variance formula, and all repeated T > 1 and two-regressor weighted-model calculations in (e)-(f).

### P018-T12

- Whole statement: `SAP.P018a.T12WholeStatement`.
- Solution proof: `SAP.P018a.WH.W2.T12_whole`.
- Files: `SAP/P018a/Challenge/Part2.lean`, `SAP/P018a/Defs/WholeW2.lean`, `SAP/P018a/WH/W2/Leaves.lean`, `SAP/P018a/WH/W2/P/T12_L1.lean`, `SAP/P018a/WH/W2/P/T12_L2.lean`, `SAP/P018a/WH/W2/P/T12_L3.lean`, `SAP/P018a/WH/W2/P/T12_L4.lean`, `SAP/P018a/WH/W2/P/T12_L5.lean`, `SAP/P018a/WH/W2/Proofs/T12.lean`, `SAP/P018a/Solution.lean`.
- Removed restriction: Retains centered total scores, expected normalized Grams, exact covariance interpretations, almost-everywhere nonsingular-sample linearizations for repeated and weighted records, single-record/unit-weight reductions, and the equivalent repeated-target normalization. The linearizations are almost everywhere, rather than on every nonsingular sample. Explicitly requires a positive total repeated observation count wherever it divides by L. The repeated and weighted identity groups additionally assume R.T N d > 0 for every dyad at the chosen size; zero-record dyads are excluded from those groups even when L > 0 and the population Gram is nonsingular. Drops the sparse covariance and uncentered-moment claims in (iii), and both model checks in (vi).

### P018-T1

- Whole statement: `SAP.P018a.T1WholeStatement`.
- Solution proof: `SAP.P018a.WH.W2.T1_whole`.
- Files: `SAP/P018a/Challenge/Part1.lean`, `SAP/P018a/Defs/WholeW2.lean`, `SAP/P018a/WH/W2/Leaves.lean`, `SAP/P018a/WH/W2/P/T1_L1.lean`, `SAP/P018a/WH/W2/P/T1_L2.lean`, `SAP/P018a/WH/W2/Proofs/T1.lean`, `SAP/P018a/Solution.lean`.
- Removed restriction: Retains the nonlinear model, bounded ranges, population projection, almost-sure rank for N >= 3, zero conditional covariances and printed meat, exact score-variance decomposition and N = 3 value, positive matrices and determinants, target limit, CLT and sandwich probability limit. Drops the explicit two-row determinant formula; the conditional-mean equality and nonlinearity assertion; separate residual orthogonality and disjoint-score moment assertions; the overlapping-score interpretation of Gamma; the general-N entrywise variance display; the separate scaled-score variance limit and explicit Q-inverse sandwich identity; and both repeated/unit-weight extensions in (f).

### P018-T3

- Whole statement: `SAP.P018a.T3WholeStatement`.
- Solution proof: `SAP.P018a.WH.W2.T3_whole`.
- Files: `SAP/P018a/Challenge/Part1.lean`, `SAP/P018a/Defs/WholeW2.lean`, `SAP/P018a/WH/W2/Leaves.lean`, `SAP/P018a/WH/W2/P/T3_L1.lean`, `SAP/P018a/WH/W2/P/T3_L2.lean`, `SAP/P018a/WH/W2/P/T3_L3.lean`, `SAP/P018a/WH/W2/P/T3_L4.lean`, `SAP/P018a/WH/W2/P/T3_L5.lean`, `SAP/P018a/WH/W2/P/T3_L6.lean`, `SAP/P018a/WH/W2/P/T3_L7.lean`, `SAP/P018a/WH/W2/Proofs/T3.lean`, `SAP/P018a/Solution.lean`.
- Removed restriction: Retains the sign-model mean-step counterexample and surviving consistency, the deterministic missing-N counterexample, the spike example, the three eight-sign covariance values, and the inverse-Gram probability and infinite-moment conclusions. For the inverse design, rank and moment bounds are packaged only for all N above an unspecified threshold at least 3; the exact population determinant identity is dropped. Also drops the general-N fit, exact residual bound and deterministic design-Gram formulas, the unscaled score-variance identity, the arbitrary-array overlap identity, samplewise meat formulas and their unnormalized/normalized mean-difference limits, the explicit scaled-estimator mean limit and fourth-moment/variance formulas, and the general linear-form/general-N covariance identity and six-case classification. The eight-sign covariance formulas are stated directly as finite fair-sign expectations, without an additional OLS-identification assertion.

### P018-T7

- Whole statement: `SAP.P018a.T7WholeStatement`.
- Solution proof: `SAP.P018a.WH.W2.T7_whole`.
- Files: `SAP/P018a/Challenge/Part1.lean`, `SAP/P018a/Defs/WholeW2.lean`, `SAP/P018a/WH/W2/Leaves.lean`, `SAP/P018a/WH/W2/P/T7_L1.lean`, `SAP/P018a/WH/W2/P/T7_L2.lean`, `SAP/P018a/WH/W2/P/T7_L3.lean`, `SAP/P018a/WH/W2/P/T7_L4.lean`, `SAP/P018a/WH/W2/P/T7_L5.lean`, `SAP/P018a/WH/W2/Proofs/T7.lean`, `SAP/P018a/Solution.lean`.
- Removed restriction: Retains the bounded sign-pair model conditions, Q and beta, projection covariance and limiting target, exact finite-N target, limiting probability of a negative slope variance estimate, absolute sandwich consistency, and the exact N = 8 Gram, determinant, OLS coefficient and negative sandwich value. Drops the sample-rank failure probability and exact residual bound, the separately displayed residual and score moment identities and finite score-variance formula, the explicit inverse-Q display and target-convergence assertion, the N = 8 meat display and positive-probability embedding, the joint second-order weak limit, and the nonnormal studentized-pivot assertion. The latter uses a totalized square root/division in the source and is not asserted as a real statistic on negative-variance samples.

### P018-T2

- Whole statement: `SAP.P018a.T2WholeStatement_W3`.
- Solution proof: `SAP.P018a.WH.W3.T2_whole`.
- Files: `SAP/P018a/Challenge/Part1.lean`, `SAP/P018a/Defs/WholeW3.lean`, `SAP/P018a/WH/W3/Leaves.lean`, `SAP/P018a/WH/W3/P/T2_L1.lean`, `SAP/P018a/WH/W3/P/T2_L2.lean`, `SAP/P018a/WH/W3/P/T2_L3.lean`, `SAP/P018a/WH/W3/P/T2_L4.lean`, `SAP/P018a/WH/W3/Proofs/T2.lean`, `SAP/P018a/Solution.lean`.
- Removed restriction: Retains score centering, zero disjoint score moments, the sparse unconditional and conditional-second-moment forms, the omitted-term decomposition with M defined as Var(sum X_d m_d), its positive semidefiniteness and zero-term equivalence, the disjoint conditional remainder, the D H + N(N-1)(N-2) Gamma formula, and the target limit. Drops the explicit identifications M = Var(E[S | X]) and of the full conditional double sum with E[Var(S | X)], the overlapping-score representation of Gamma, the separately displayed rational finite-N formula for V, the separate assertion that projection orthogonality alone is insufficient, and the repeated/weighted score replacements mentioned in the repair text.

**Dependent proof repairs.** None were required. The unchanged Solution proofs T4, T5, T6 and T14 use their existing library or Bridge terms and do not refer to any switched theorem. Their statements, proofs, Challenge docstrings and manifest entries are unchanged.

**Validation of the whole switches.** `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P018a` rebuilt all 74 unit modules from scratch and passed the forbidden-token scan; see [rebuild log](scratch/p018a-switch-rebuild.log). The [scratch audit](scratch/p018a-switch-axioms.lean) imports `SAP.P018a.Solution` and runs `#print axioms` on all ten switched theorems. Each depends only on `propext`, `Classical.choice` and `Quot.sound`; see [foundation and project-dependency results](scratch/p018a-switch-axioms.log). The manifest retains existing `rows_used` entries and adds the generated whole theorem, assembly, leaf proofs and project theorem dependencies observed by traversing the SAP proof terms. Compilation ran one Lean process at a time; Lake was never run. Source and metadata scope checks confirm that definitions, existing whole proof modules and all four untouched targets remain unchanged.


## Declaration review round 2

**T9: restriction_inaccurate, minor — accepted.** The [review finding](fw/round2/T9/r4g2/findings.json) correctly identifies the domain mismatch in the two docstrings. [W1c](SAP/P018a/Defs/WholeW1.lean:77) divides by W1W N, while the fit and variance identities in [T9WholeStatement](SAP/P018a/Defs/WholeW1.lean:154) quantify over every natural N. At N = 1 there are no dyads, W1W 1 = 0, and these identities use the specified zero completion. The positive-mass formulas and substantive counterexample bounds use N >= 2 or N >= 8; they do not rely on that completion.

Replaced the inaccurate N >= 2 sentence in both the Challenge docstring and the docstring for T9WholeStatement with: “The all-N linear-fit and variance identities include the zero completion when N<2.” Added the same convention as T9's domain_note in the manifest, retaining its whole decision and null restriction. This is a documentation correction, not a new hypothesis or a mathematical restriction. The two edits to Lean files are confined to docstrings: no definition body, theorem statement, proof or fully qualified name was changed. The existing whole-statement proofs are used as supplied; this revision introduces no proofs.

The manifest was compacted without changing other target records. The Comparator configuration was regenerated and revalidated with the same fourteen theorem names, allowed foundations and external-kernel settings. The current counts are 13 whole, 1 restricted, 0 refuted and 0 omitted, with fourteen proved theorems and no open glue tasks. The old packaging generators in scratch predate the whole-statement additions and were not run.

All current SAP modules were recompiled with sap-lean in dependency order, using one Lean process at a time, and all fourteen final dependency checks were rerun. The results are in `scratch/round2-compile.log`, `scratch/round2-foundations.log` and `scratch/round2-validation.json`. The latter also records the source hashes confirming that only the two docstrings changed in Lean source. All checks passed; each theorem uses only propext, Classical.choice and Quot.sound. The existing external certification artifact is preserved; no new external-kernel run is claimed for this revision.


**Pre-existing format note.** Seventeen supplied whole-statement or proof modules exceed the original 300-line file limit. Their organization is preserved in this documentation-only correction; the affected files and line counts are recorded in `scratch/round2-validation.json`. The mathematical declarations are unchanged.
