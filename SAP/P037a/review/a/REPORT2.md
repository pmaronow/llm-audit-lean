# P037a delta review

Reviewed all 15 canonical targets, all nine revised Defs parts, the Challenge declarations and docstrings, `record2.json`, and `architect-report.md` against the saved `reading.md`, `claim-stage.json` and first-round findings.

| Verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 5 |
| omission_ok | 2 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_questionable | 0 |

All 15 severities are `none`. Both earlier findings are fixed; none is partly fixed or unfixed. No new issue was found.

## Earlier findings

| Target | Earlier finding | Status | Revised evidence |
| --- | --- | --- | --- |
| P037-T1 | Missing identification of the design-alone reading refuted by the witness | **Fixed** | The [T1 docstring](/home/ubuntu/sap/tasks/CHFID-P037a-a/SAP/P037a/Challenge/Part1.lean:7) now names randomization, an eligible-composition main effect and marginal average linearity alone. Its next sentence states that the witness violates the preferred qualified response restriction and does not refute that interpretation. |
| P037-T12 | Missing distinction between the exactly-64 reading and the printed upper bound | **Fixed** | The [T12 docstring](/home/ubuntu/sap/tasks/CHFID-P037a-a/SAP/P037a/Challenge/Part1.lean:58) now identifies the exactly-64 reading and explicitly says that the literal upper bound remains true. |

The architect's account of both fixes agrees with the revised docstrings. These changes resolve documentation requirements without changing either mathematical proposition. T1 is now `correct_restricted`; T12 is now `correct_whole`.

## Statement and label comparison

All thirteen theorem declarations retain the names and `TnStatement` types recorded in the blind reading. Direct comparison of their defining propositions and shared SAP definitions with that reading found no mathematical change: objects, hypotheses, quantifier order, conclusions and totalization conventions agree. In particular, neither docstring repair introduces a new hypothesis or removes a canonical clause. The saved first-round mathematical relations remain five narrower statements and eight whole statements.

The decisions and restriction texts in `record2.json` agree with the first record. Each of the five theorem restriction texts is reproduced in its Challenge docstring. There are eight `whole`, five `restricted`, zero `refuted` and two `omitted` decisions. Each label remains appropriate:

| Target | Decision | Coverage checked |
| --- | --- | --- |
| P037-T1 | restricted | Finite clauses (i)–(iv), both outcome schedules, design moments, expected matrices, determinant, unique coefficients and mixture criterion; the repeated-block OLS limit (v) is expressly omitted. The counterexample reading is now disclosed. |
| P037-T2 | restricted | Unconditional product-seed moments, equal-fraction implication, unequal-strata example, response identification, centered and uncentered orthogonality, slope moment, positive-variation identification, augmentation and all witness comparisons. The joint treatment/seed construction, treated-school conditional moments and derivation of (R) remain expressly omitted. (R) remains the canonical explicit premise. |
| P037-T3 | restricted | Incompatibility, bins, both witnesses, comparisons throughout the rational critical-value bracket, and the complete open ratio envelope. Gaussian tails, the actual normal quantile and P-value conclusions remain expressly omitted. No Gaussian bracket is assumed. |
| P037-T4 | restricted | Correct normalized-uniform and constant-density simplex event masses and unequal laws, ratio algebra, uniform area, separate exponential integrals, and WLS scaling/normalization. The normalized-exponential construction, its event probability and combined integral remain expressly omitted. |
| P037-T5 | restricted | One-coordinate logarithmic transformation, factorial gamma integral, unequal normalized-uniform law and WLS invariance. Full simplex support/normalization results, independent normalized-exponential construction, transformed-coordinate independence, Jacobian, joint density and spacings remain disclosed omissions. |
| P037-T6 | whole | All six arithmetic clauses: totals, percentage intervals and exclusion of 30%, rounded-total bounds, per-student comparisons, mixed-basis exclusion and change in the reported percentage. |
| P037-T7 | whole | Both feasible overlap witnesses, distinct labels, both general overlap implications and nonexistence of a function satisfying all printed predicates. These prove the canonical counterexample rather than contradicting it. |
| P037-T8 | whole | Exactly one corrected case for every feasible configuration, with both required witness values. |
| P037-T9 | whole | Indicator moments, independent frequency mean/variance, Chebyshev bound, consistency, last-draw identity and both coding examples. |
| P037-T10 | whole | Uniform-block marginals and pairwise dependence, control-exposure covariance, the general nonuniform fixed-count argument and independent two-block law. These prove the canonical counterexample rather than contradicting it. |
| P037-T11 | whole | All eight canonical parts: oracle unbiasedness and independence, bounds, variance rate, consistency, Lindeberg/Gaussian limit, corresponding contrast results, and fitted-estimator identities and limits under the explicit sufficient conditions. |
| P037-T12 | whole | No ties; bounds, divisibility and monotonicity; cap and interpolation endpoints; all three example counts, the exact 521 threshold and all five shares. The docstring correctly limits its interpretive refutation. |
| P037-T13 | whole | All five arithmetic and interval clauses. The figure-derived control interval remains a hypothesis; the theorem asserts membership of 0.095 and both relative-reduction values, without certifying a precise figure reading. |
| P037-T14 | omitted | The qualified empirical interpretation has no specified universal response condition that can be certified for the application. T1's weaker-reading counterexample and T2's sufficient-model implications do not decide that application. |
| P037-T15 | omitted | The available evidence does not decide either individual empirical significance report. Their incompatibility for one P value is already in T3. |

No `refuted` label is warranted for T1, T7, T10 or T12: their canonical assertions are the counterexample or corrected-rule assertions that the theorems establish. Neither revised docstring says that the printed claim is false. Canonical `statement`, `definitions_needed` and standing assumptions determine these assessments; audit-history `note` and `finite_lemmas` do not add or remove clauses.

## Junk values and nonvacuity

There are no changed mathematical statements requiring replacement instances. The existing nonvacuity examples remain applicable, and the command `/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` was rerun against the refreshed Defs. It completed with exit 0; `scratch/nonvacuity-round2.log` contains tactic-linter warnings only. The file imports Defs and obtains no evidence from Challenge stubs.

For T1, the retained exact rational enumeration gives 454 positive-mass states totaling one, including an assignment of mass 1/1536. It reproduces the Gram, RHS, determinant 31/60000 and regression comparisons. Zero-mass typed states do not create the counterexample. The new wording accurately describes the scope of this unchanged witness.

For T12, subtraction in the interpolation branch is evaluated only when n>200; natural division implements the correct nearest-multiple-of-four rule. The universal no-tie assertion follows by parity. The compiled examples include e(520)=60, e(521)=64 and e(550)=64; the existing exact checks cover the entire interpolation range. Values e(100)=40, e(200)=40 and e(375)=52 establish exactly the distinction now described in the docstring. All five share denominators are positive.

Shared safeguards remain as recorded in the blind reading: normalized design masses exclude empty probability spaces; positive sample totals and the singleton-stratum branch protect seed moments; standard errors and ratio denominators are positive; the ratio-event dimension is at least two; both event measures are explicitly finite before conversion to reals; and the stated integral functions are integrable. T11 retains positive population size, probability and variance guards. Its singular-sample zero coefficient is the canonical explicit convention. The compiled positive-variance growing-block example has two students per block, a nonempty one-dimensional covariate, positive definite Gram and exact positive probabilities, so the asymptotic hypotheses do not rely on empty students, zero variance or zero-dimensional covariates.

`findings2.json` has the same fields as the first-round findings, one object for each of the 15 canonical targets. Its syntax, target coverage, theorem references and verdict counts were checked with Python 3. `scratch/delta-source-checks.json` records the declaration/record checks and hashes of the reviewed source files. The original blind reading and first-round judgments are preserved.
