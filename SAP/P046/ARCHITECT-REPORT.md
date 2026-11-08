# P046 packaging report

Decision counts: whole 2, restricted 7, refuted 1, omitted 0.
All ten listed Solution theorems are proved; there are no open glue tasks.

## Scope decisions

P046-T7 states all three Proposition 2 conclusions, using the canonical common-positivity interpretation of uniformity and the explicit asymptotic variance. P046-T10 states the full unrestricted-class failure of uniform consistency, with a law-specific positive positivity constant. It does not claim a stronger common-constant impossibility theorem.

P046-T6 is the refutation of the positive printed Proposition 3 assertion. Its docstring begins with the required false-claim wording. P046-T1, P046-T2 and P046-T4 are recorded counterexample targets, so their packaged counterexamples are classified relative to those canonical refutations, rather than labelled refuted again. T4 explicitly uses the treated-case weighted-loss reading in the canonical definitions.

Every restricted target is listed below. The restrictions reproduce the Challenge docstrings and manifest. Audit-history notes and finite lemmas add no claim clauses.

### P046-T1

Omits K and S and their category probabilities and joint multinomial law; the sample-statistic reductions to S/65, (S-39)/65 and xiK(K); the equivalence of count-state exclusion tests and the logarithm-indexed mass-sum identity; the total feasible-state count 5151; and the separate coverage-probability and non-strict-tail conclusions. The decimal probability is represented by its exact rational value.

### P046-T2

Retains the valid continuous design, mean, event mass and positivity, xi, radius identity and comparisons, and conditional failure almost everywhere on the event. Omits the pointwise assertions for every covariate/treatment vector that all outcomes and HT vanish and the absolute deviation is 1/2, and the conditional-centre explanation E[HT|W] = muW = 0 distinct from the population mean 1/2.

### P046-T3

Omits corrected-proof assertions (i)–(iv): summand factorization and conditional and iterated means; conditional independence and range; fixed-threshold concentration; random-threshold conditional and unconditional alpha/2 bounds; the regression-value sampling assertions and concentration; and the event inclusion and union-bound display. Does not separately assert sqrt(xi) < delta^(-1), retaining its radius and width consequences. The known-bound alternative states only its final tail inequality; it does not separately assert that Z_i = X_i Y_i / pi(W_i) are i.i.d., lie in [0,b^(-1)] and have mean mu, or its Hoeffding calculation.

### P046-T4

Retains design validity, uniform covariates, empirical optimality almost surely for each sample size and each of the two opposite-fold training sets, convergence, both finite-sample means and variances, fixed-prediction estimator identity, normal limits, variance excess and ratio, weighted-norm formula, and the two displayed risks. Omits the training-loss decomposition, weights and empirical uniqueness characterization; population criterion formula and unique-minimizer characterization; scalar summand table, event probabilities and first/second moments; explicit bounded-i.i.d.-summand assertion; zero's nonmembership and exclusion from weighted closure; Var(Y(1)) = 19/400; and the explicit risk-gap identity and positivity. It does not separately assert empirical optimality for arbitrary training sets or pointwise for every generated sample.

### P046-T5

The family-free direct variant requires a square-integrable deterministic limit and almost-sure square-integrability of each fitted function at every sample size and fold. It excludes fits with infinite L2 error on positive-probability training events whose probabilities vanish. The working-family variant retains the zero-closure alternative and obtains fitted square-integrability from family membership.

### P046-T8

Adds integrability under the full sample law of every evaluated fitted prediction. This excludes cancellation cases in which individual predictions are nonintegrable but the final adjusted estimator is integrable. The declaration states the final unbiasedness equality only; it does not separately assert the printed proof's three-term estimator decomposition, component expectation chains for XY(1)/pi and X*g_hat/pi, conditional factorization E[X*g_hat|W] = E[X|W]*E[g_hat|W], or its conditional-independence and term-cancellation assertions. It permits arbitrary deterministic finite fold assignments, including unequal and empty folds.

### P046-T9

Both parts require almost-sure square-integrability of every finite-sample fit at every sample size and fold. Part (b) uses fixed L2 limits and integrable squared-error expectations tending to zero. Part (d) excludes fits with infinite L2 error on positive-probability training events whose probabilities vanish.

There are no omitted targets.

## Definitions and Bridges

The single shared-definition route is used. Defs/Part1 contains SAP population, sample, estimator, regression, moment, and convergence definitions. Defs/Part2 gives the three explicit continuous laws and the deterministic regression fits. Defs/Part3 and Part4 define the ten theorem propositions. The Challenge imports only the shared Defs; neither Mathlib-only definitions nor Challenge import project modules. The Solution imports the same Defs through Bridge and never imports Challenge.

- Bridge/Part1 adapts SAP Study and CrossFit records to and from the project records. ValidStudy proofs are reconstructed field by field. Statistical functions agree by definitional reduction; record round trips and the concrete studies and fits have reflexive equality proofs.
- Bridge/Part2 transports the two interval counterexamples, corrected coverage and width, and the actual balanced regression counterexample. The T2 radius equality is substitution of the exported xi value followed by rational normalization. The T4 excess and ratio are closed rational arithmetic.
- Bridge/Part3 transports corrected efficiency results. The credited fitted_L2_from_membership theorem derives the family-case prediction moments from empirical membership. Gaussian variance signs follow immediately from the exported variance identity and Mathlib variance_nonneg.
- Bridge/Part4 transports the printed-proposition refutation, HT properties, cross-fit unbiasedness and limits, and observational impossibility. The HT unit-variance identity rewrites Mathlib variance_eq_sub using exported first and second moments. Hahn-bound nonnegativity rewrites the exported fixed-adjusted-variance identity at the true regression; its excess term simplifies to zero.

Shared support for the T9 variance-sign guard: the fixed_adjusted_variance_proof row credited to T5 is reused, together with the existing project helper p4d_regression_L2 in GP046B5.lean. That helper already proves the regression moment condition; no new boundedness or integration argument is supplied here. Manifests account for the rows assigned to each target.

All mathematics is supplied by existing project or Mathlib declarations. New proof terms perform structural transport, instantiation, conjunction/projection, logical contradiction, or the displayed moment rewrites and closed arithmetic. No review-suggested hypothesis, assumption of a concentration theorem, or replacement proof has been introduced.

## Definedness checks

All sample means and confidence statements use positive sample sizes. Confidence levels are strictly between zero and one; lower propensity bounds are positive. ValidStudy supplies probability laws, so all probability-to-real conversions are finite, and binary outcomes ensure population means exist. Cross-fitted unbiasedness explicitly assumes evaluated-prediction integrability. L2 probability statements in the direct and asymptotic clauses require fitted L2 membership at every sample size; in the family clause it follows from membership in the square-integrable family. The concrete deterministic regression fit is bounded. Zero-closure sequences lie in that family, making their norms finite.

SAP NormalLimit records 0 <= variance in addition to the project convergence predicate. Every such sign is proved from an existing variance identity or closed rational arithmetic. This prevents a negative parameter from being silently truncated when converted to a nonnegative real. No nondegeneracy condition is added: variance zero remains allowed.

## Validation

- Compiled Defs parts and root, all Bridge parts and root, Challenge part and root, and Solution with the supplied sap-lean command, in dependency order. No build-manager command was run.
- Ran #print axioms for every Solution theorem in scratch/Axioms.lean. Each depends exactly on propext, Classical.choice and Quot.sound; scratch/axioms.log records the output.
- A supplementary Lean expression check in separately imported Challenge and Solution environments passed: all 10 target statement expressions, 187 SAP declaration types, and 97 SAP definition bodies agree exactly. See scratch/CompareTypes.lean and scratch/type_comparison.log. This is not an external-kernel certification.
- manifest.json and comparator.json parse. The theorem list is exactly SAP.P046.T1 through T10; every unit target and every credited row is accounted for.
- All SAP files are at most 300 lines; the manifest uses one JSON object per target to retain that limit.

The Palomar Comparator configuration is supplied with the requested two external-kernel commands. The Comparator runner and those executables were not available through PATH, and the attempted Comparator tool paths did not exist. External three-kernel certification has not been run or claimed.

## Remaining concerns

The reviews call several aggregate rows full coverage. Here the stricter clause-completeness rule also counts the explicit derivation, count-statistic, and counterexample-detail assertions in canonical statements. T1 through T4 therefore disclose the clauses left unstated, even where the retained theorem already establishes the substantive counterexample or coverage conclusion.

The fitted-function moment restrictions in T5, T8 and T9 are substantive. In particular, real-valued total integrals cannot stand in for infinite L2 error. The statements retain the actual finite-moment restrictions instead of generalizing those existing proofs. The Hahn benchmark is the numerical expression in the canonical definitions; no separate efficiency lower-bound theorem is asserted.

## Open glue tasks

None. Every theorem in comparator.json has a compiled Solution proof.

## Declaration review round 1

- Finding: `SAP.P046.T8` / `P046-T8`, `restriction_inaccurate`, minor. Accepted the [review finding](fw/round1/T8/r1g2/findings.json) and [review explanation](fw/round1/T8/r1g2/REPORT.md). The other entries in the same findings file have no open issues.
- Independent check: `work.json`, `targets[P046-T8].canonical_claim.statement`, explicitly contains the printed proof's component expectation chains and conditional factorization (Appendix A, p. 16 / PDF p. 15). [T8Statement](SAP/P046/Defs/Part4.lean#L56) concludes only the final expectation equality; its credited [project theorem](AronowAudit/P046/Wave1/Gap/GP046B4.lean#L219) likewise concludes that equality with evaluated-prediction integrability. The omission was missing from the earlier disclosure.
- Correction: expanded T8's Challenge docstring and manifest restriction to disclose the omitted three-term decomposition, component expectation chains, conditional factorization, conditional-independence and cancellation assertions. The disclosure also records arbitrary deterministic finite fold assignments, including unequal and empty folds. The existing added-integrability restriction remains explicit, and the decision remains `restricted`.
- Scope: no theorem name, theorem statement, proof, or shared definition was changed. Shared-definition, Bridge and Solution source hashes are recorded in `scratch/round1_baseline.json` for verification. The Comparator theorem list and permitted dependencies remain unchanged; its configuration is regenerated and validated with the manifest.
- Validation: all Defs, Bridge, Challenge and Solution modules are recompiled in dependency order with `sap-lean`. All ten Solution dependency lists are reprinted in `scratch/axioms.log`; the separate-environment expression comparison is rerun in `scratch/type_comparison.log`. Final validation checks JSON parsing, target/row accounting, the 300-line limit, implicit-variable options, and unchanged shared definitions and proofs.


## Declaration review round 2

### P046-T3

Accepted the `restriction_inaccurate` / minor [finding for SAP.P046.T3](fw/round2/T3/r3g1/findings.json); see the [review report](fw/round2/T3/r3g1/REPORT.md). Independent check: the known-bound alternative in `work.json`, `targets[P046-T3].canonical_claim.statement`, explicitly states that the summands Z_i = X_i Y_i / pi(W_i) are i.i.d., belong to [0,b^(-1)], and have mean mu, and invokes Hoeffding's inequality. The known-bound conjunct of [T3Statement](SAP/P046/Defs/Part3.lean#L62) states only the final tail inequality. Expanded the Challenge docstring and manifest restriction to disclose all those omitted assertions and the Hoeffding calculation; the existing exclusions of corrected-proof steps and the separate sqrt(xi) bound remain explicit. The decision remains `restricted`.

### P046-T4

Accepted the `restriction_inaccurate` / minor [finding for SAP.P046.T4](fw/round2/T4/r3g1/findings.json); see the [review report](fw/round2/T4/r3g1/REPORT.md). Independent check: empirical-fit part (a) of `work.json`, `targets[P046-T4].canonical_claim.statement`, asserts optimality for every training set and every generated sample. The retained [T4Statement optimality conjunct](SAP/P046/Defs/Part3.lean#L75) instead quantifies over each sample size and fold, almost every sample, and that fold's specified opposite-fold training set. Corrected the retained-optimality description to include these quantifiers and explicitly disclosed omission of arbitrary-training-set optimality and pointwise optimality for every generated sample. The other previously listed omissions remain explicit, and the decision remains `restricted`.

### Scope and validation

Only the T3 and T4 restriction disclosures and associated report/manifest text were changed. No theorem names, theorem statements, shared definitions, Bridge proofs, or Solution proofs were changed. `scratch/round2_baseline.json` records source hashes and pre-revision metadata; the final checks verify that shared sources are unchanged and that only these two manifest restrictions differ. The Comparator configuration is regenerated with its existing ten theorem names and permitted dependencies.

All Defs, Bridge, Challenge and Solution modules are recompiled with `sap-lean` in dependency order. All ten `#print axioms` outputs are refreshed in `scratch/axioms.log`; each lists only propext, Classical.choice and Quot.sound. The separate-environment expression check is rerun in `scratch/type_comparison.log`. JSON parsing, target/row accounting, all file line limits and both implicit-variable options are rechecked. External three-kernel certification remains unclaimed as described above.


## Whole versions (new proofs)

The seven targets below now use their proved whole statements. Current decisions: whole 9, restricted 0, refuted 1. The earlier restriction disclosures describe the previous packaging. No definitions, whole proof modules, or other target declarations were changed.


### P046-T1

`SAP.P046.T1` now has type `SAP.P046.T1WholeStatement` and Solution proof `SAP.P046.WH.W1.T1_whole`.

Files: [SAP/P046/Challenge/Part1.lean](SAP/P046/Challenge/Part1.lean), [SAP/P046/Solution.lean](SAP/P046/Solution.lean), [SAP/P046/Defs/WholeW1.lean](SAP/P046/Defs/WholeW1.lean), [SAP/P046/WH/W1/Leaves.lean](SAP/P046/WH/W1/Leaves.lean), [SAP/P046/WH/W1/Support.lean](SAP/P046/WH/W1/Support.lean), [SAP/P046/WH/W1/Proofs/T1.lean](SAP/P046/WH/W1/Proofs/T1.lean), [SAP/P046/WH/W1/P/T1_L1.lean](SAP/P046/WH/W1/P/T1_L1.lean), [SAP/P046/WH/W1/P/T1_L2.lean](SAP/P046/WH/W1/P/T1_L2.lean), [SAP/P046/manifest.json](SAP/P046/manifest.json).

Old restriction removed: Omits K and S and their category probabilities and joint multinomial law; the sample-statistic reductions to S/65, (S-39)/65 and xiK(K); the equivalence of count-state exclusion tests and the logarithm-indexed mass-sum identity; the total feasible-state count 5151; and the separate coverage-probability and non-strict-tail conclusions. The decimal probability is represented by its exact rational value.


### P046-T2

`SAP.P046.T2` now has type `SAP.P046.T2WholeStatement` and Solution proof `SAP.P046.WH.W1.T2_whole`.

Files: [SAP/P046/Challenge/Part1.lean](SAP/P046/Challenge/Part1.lean), [SAP/P046/Solution.lean](SAP/P046/Solution.lean), [SAP/P046/Defs/WholeW1.lean](SAP/P046/Defs/WholeW1.lean), [SAP/P046/WH/W1/Leaves.lean](SAP/P046/WH/W1/Leaves.lean), [SAP/P046/WH/W1/Support.lean](SAP/P046/WH/W1/Support.lean), [SAP/P046/WH/W1/Proofs/T2.lean](SAP/P046/WH/W1/Proofs/T2.lean), [SAP/P046/manifest.json](SAP/P046/manifest.json).

Old restriction removed: Retains the valid continuous design, mean, event mass and positivity, xi, radius identity and comparisons, and conditional failure almost everywhere on the event. Omits the pointwise assertions for every covariate/treatment vector that all outcomes and HT vanish and the absolute deviation is 1/2, and the conditional-centre explanation E[HT|W] = muW = 0 distinct from the population mean 1/2.


### P046-T3

`SAP.P046.T3` now has type `SAP.P046.T3WholeStatement` and Solution proof `SAP.P046.WH.W1.T3_whole`.

Files: [SAP/P046/Challenge/Part1.lean](SAP/P046/Challenge/Part1.lean), [SAP/P046/Solution.lean](SAP/P046/Solution.lean), [SAP/P046/Defs/WholeW1.lean](SAP/P046/Defs/WholeW1.lean), [SAP/P046/WH/W1/Leaves.lean](SAP/P046/WH/W1/Leaves.lean), [SAP/P046/WH/W1/Support.lean](SAP/P046/WH/W1/Support.lean), [SAP/P046/WH/W1/Proofs/T3.lean](SAP/P046/WH/W1/Proofs/T3.lean), [SAP/P046/WH/W1/P/T3_L1.lean](SAP/P046/WH/W1/P/T3_L1.lean), [SAP/P046/WH/W1/P/T3_L2.lean](SAP/P046/WH/W1/P/T3_L2.lean), [SAP/P046/WH/W1/P/T3_L3.lean](SAP/P046/WH/W1/P/T3_L3.lean), [SAP/P046/manifest.json](SAP/P046/manifest.json).

Old restriction removed: Omits corrected-proof assertions (i)–(iv): summand factorization and conditional and iterated means; conditional independence and range; fixed-threshold concentration; random-threshold conditional and unconditional alpha/2 bounds; the regression-value sampling assertions and concentration; and the event inclusion and union-bound display. Does not separately assert sqrt(xi) < delta^(-1), retaining its radius and width consequences. The known-bound alternative states only its final tail inequality; it does not separately assert that Z_i = X_i Y_i / pi(W_i) are i.i.d., lie in [0,b^(-1)] and have mean mu, or its Hoeffding calculation.


### P046-T4

`SAP.P046.T4` now has type `SAP.P046.T4WholeStatement` and Solution proof `SAP.P046.WH.W1.T4_whole`.

Files: [SAP/P046/Challenge/Part1.lean](SAP/P046/Challenge/Part1.lean), [SAP/P046/Solution.lean](SAP/P046/Solution.lean), [SAP/P046/Defs/WholeW1.lean](SAP/P046/Defs/WholeW1.lean), [SAP/P046/WH/W1/Leaves.lean](SAP/P046/WH/W1/Leaves.lean), [SAP/P046/WH/W1/Support.lean](SAP/P046/WH/W1/Support.lean), [SAP/P046/WH/W1/Proofs/T4.lean](SAP/P046/WH/W1/Proofs/T4.lean), [SAP/P046/WH/W1/P/T4_L1.lean](SAP/P046/WH/W1/P/T4_L1.lean), [SAP/P046/WH/W1/P/T4_L2.lean](SAP/P046/WH/W1/P/T4_L2.lean), [SAP/P046/WH/W1/P/T4_L3.lean](SAP/P046/WH/W1/P/T4_L3.lean), [SAP/P046/manifest.json](SAP/P046/manifest.json).

Old restriction removed: Retains design validity, uniform covariates, empirical optimality almost surely for each sample size and each of the two opposite-fold training sets, convergence, both finite-sample means and variances, fixed-prediction estimator identity, normal limits, variance excess and ratio, weighted-norm formula, and the two displayed risks. Omits the training-loss decomposition, weights and empirical uniqueness characterization; population criterion formula and unique-minimizer characterization; scalar summand table, event probabilities and first/second moments; explicit bounded-i.i.d.-summand assertion; zero's nonmembership and exclusion from weighted closure; Var(Y(1)) = 19/400; and the explicit risk-gap identity and positivity. It does not separately assert empirical optimality for arbitrary training sets or pointwise for every generated sample.


### P046-T5

`SAP.P046.T5` now has type `SAP.P046.T5WholeStatement` and Solution proof `SAP.P046.WH.W1.T5_whole`.

Files: [SAP/P046/Challenge/Part1.lean](SAP/P046/Challenge/Part1.lean), [SAP/P046/Solution.lean](SAP/P046/Solution.lean), [SAP/P046/Defs/WholeW1.lean](SAP/P046/Defs/WholeW1.lean), [SAP/P046/WH/W1/Leaves.lean](SAP/P046/WH/W1/Leaves.lean), [SAP/P046/WH/W1/Support.lean](SAP/P046/WH/W1/Support.lean), [SAP/P046/WH/W1/Proofs/T5.lean](SAP/P046/WH/W1/Proofs/T5.lean), [SAP/P046/WH/W1/P/T5_L1.lean](SAP/P046/WH/W1/P/T5_L1.lean), [SAP/P046/WH/W1/P/T5_L2.lean](SAP/P046/WH/W1/P/T5_L2.lean), [SAP/P046/WH/W1/P/T5_L3.lean](SAP/P046/WH/W1/P/T5_L3.lean), [SAP/P046/WH/W1/P/T5_L4.lean](SAP/P046/WH/W1/P/T5_L4.lean), [SAP/P046/WH/W1/P/T5_L5.lean](SAP/P046/WH/W1/P/T5_L5.lean), [SAP/P046/manifest.json](SAP/P046/manifest.json).

Old restriction removed: The family-free direct variant requires a square-integrable deterministic limit and almost-sure square-integrability of each fitted function at every sample size and fold. It excludes fits with infinite L2 error on positive-probability training events whose probabilities vanish. The working-family variant retains the zero-closure alternative and obtains fitted square-integrability from family membership.


### P046-T8

`SAP.P046.T8` now has type `SAP.P046.T8WholeStatement` and Solution proof `SAP.P046.WH.W2.T8_whole`.

Files: [SAP/P046/Challenge/Part1.lean](SAP/P046/Challenge/Part1.lean), [SAP/P046/Solution.lean](SAP/P046/Solution.lean), [SAP/P046/Defs/WholeW2.lean](SAP/P046/Defs/WholeW2.lean), [SAP/P046/WH/W2/Leaves.lean](SAP/P046/WH/W2/Leaves.lean), [SAP/P046/WH/W2/Proofs/T8.lean](SAP/P046/WH/W2/Proofs/T8.lean), [SAP/P046/WH/W2/P/T8_L1.lean](SAP/P046/WH/W2/P/T8_L1.lean), [SAP/P046/WH/W2/P/T8_L2.lean](SAP/P046/WH/W2/P/T8_L2.lean), [SAP/P046/WH/W2/P/T8_L3.lean](SAP/P046/WH/W2/P/T8_L3.lean), [SAP/P046/WH/W2/P/T8_L4.lean](SAP/P046/WH/W2/P/T8_L4.lean), [SAP/P046/manifest.json](SAP/P046/manifest.json).

Old restriction removed: Adds integrability under the full sample law of every evaluated fitted prediction. This excludes cancellation cases in which individual predictions are nonintegrable but the final adjusted estimator is integrable. The declaration states the final unbiasedness equality only; it does not separately assert the printed proof's three-term estimator decomposition, component expectation chains for XY(1)/pi and X*g_hat/pi, conditional factorization E[X*g_hat|W] = E[X|W]*E[g_hat|W], or its conditional-independence and term-cancellation assertions. It permits arbitrary deterministic finite fold assignments, including unequal and empty folds.


### P046-T9

`SAP.P046.T9` now has type `SAP.P046.T9WholeStatement` and Solution proof `SAP.P046.WH.W2.T9_whole`.

Files: [SAP/P046/Challenge/Part1.lean](SAP/P046/Challenge/Part1.lean), [SAP/P046/Solution.lean](SAP/P046/Solution.lean), [SAP/P046/Defs/WholeW2.lean](SAP/P046/Defs/WholeW2.lean), [SAP/P046/WH/W2/Leaves.lean](SAP/P046/WH/W2/Leaves.lean), [SAP/P046/WH/W2/Proofs/T9.lean](SAP/P046/WH/W2/Proofs/T9.lean), [SAP/P046/WH/W2/P/T9_L1.lean](SAP/P046/WH/W2/P/T9_L1.lean), [SAP/P046/WH/W2/P/T9_L2.lean](SAP/P046/WH/W2/P/T9_L2.lean), [SAP/P046/WH/W2/P/T9_L3.lean](SAP/P046/WH/W2/P/T9_L3.lean), [SAP/P046/WH/W2/P/T9_L4.lean](SAP/P046/WH/W2/P/T9_L4.lean), [SAP/P046/manifest.json](SAP/P046/manifest.json).

Old restriction removed: Both parts require almost-sure square-integrability of every finite-sample fit at every sample size and fold. Part (b) uses fixed L2 limits and integrable squared-error expectations tending to zero. Part (d) excludes fits with infinite L2 error on positive-probability training events whose probabilities vanish.


Dependent-proof repairs: none. The other Solution proofs use their own Bridge lemmas directly and do not use any switched theorem. P046-T6, P046-T7 and P046-T10, including their manifest entries, remain unchanged.

Validation of the whole versions: `python3 /home/ubuntu/sap/tools/rebuild_sap.py . P046` rebuilt all 46 modules from scratch and reported a clean token scan; see [rebuild log](scratch/P046WholeRebuild.log). [The scratch axiom check](scratch/P046WholeAxioms.lean) imports only `SAP.P046.Solution` and runs `#print axioms` on all seven switched theorems. [Its output](scratch/P046WholeAxioms.log) lists exactly `propext`, `Classical.choice` and `Quot.sound` for each theorem. Lean processes ran sequentially, and no `lake` command was run. [switched.json](switched.json) records the exact Challenge types, Solution proof terms and successful outcomes.
