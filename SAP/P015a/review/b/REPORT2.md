# P015a delta referee report

**12 targets: 8 correct_whole, 4 correct_restricted; no outstanding issues.** All severities are `none`. The revised decisions comprise four complete positive claims, four complete refutations, and four accurately disclosed restrictions. The requested findings schema has no `correct_refuted` verdict, so the four accepted complete refutations retain `correct_whole` as assessments of their canonical counterexample content.

## Earlier findings

Both issues previously recorded for **P015-T6 are fixed**.

| Earlier issue | Status | Revised evidence |
| --- | --- | --- |
| A residual root that is not ML does not refute the printed necessary implication ML implies residual zero. | Fixed by narrowing the claimed result. | The docstring explicitly identifies failure of the converse and disclaims refutation of the necessary implication. It does not claim an actual probit maximizer with a nonzero substituted residual. |
| The record marked T6 whole without disclosing that limitation. | Fixed. | `record2.json` marks T6 `restricted`, and its restriction agrees with `SAP/P015a/Challenge/Part1.lean:69` through the end of that docstring. |

This is a complete fix under the rule permitting a correct, disclosed weaker result. The mathematical witness remains unchanged and still does not establish the stronger refutation; that stronger credit has now been withdrawn. No earlier objection is partly fixed or unfixed. The other eleven targets previously had no adverse findings from this referee.

The architect's response accurately describes this referee's assessments. Its T12 discussion attributes the disputed guard-scope objection to the other referee. My saved `reading.md` already says that both guards precede the entire conjunction, and `REPORT.md` accepted the original restriction. The new grouping and more explicit wording are consistent with that reading.

## Comparison with the saved reading and label audit

I reread every supplied Defs and Challenge module, checked `record2.json` and `architect-report.md`, and compared every target with `reading.md` and its canonical claim. No semantic change to any mathematical proposition was found. T12 adds explicit parentheses around the already-guarded conjunction. The substantive changes elsewhere are descriptions and decisions, rather than hypotheses, quantifier order, numerical data, or conclusions.

| Target | Revised decision | Assessment |
| --- | --- | --- |
| T1 | refuted | Accepted. The positive-overlap family has strictly positive effective profile mass below 4 epsilon for every 0<epsilon<1/2, and its displayed observed-data IPW estimator is unbiased and consistent. This defeats the canonical reading that approximately absent population weight establishes a positivity violation or inability to estimate the representative effect. |
| T2 | refuted | Accepted. Both covariate profiles retain positive effective mass, yet treatment endpoint 1 has zero conditional probability at profile 1. No two distinct endpoints have common support. The observationally identical outcome worlds also show the identification consequence. This addresses the printed pair-specific positivity display for multivalued treatment in the section that drops local linearity. |
| T3 | refuted | Accepted for the canonical reading about estimated sample weights. A positive-probability sample from a positive-overlap population has zero fitted weights on a whole profile and a nonsingular full design. This does not claim that exactly zero population conditional variance is compatible with population endpoint positivity. |
| T13 | whole | Accepted. Every derivative, inverse-logit/log-odds identity, affine Taylor-polynomial form, and evaluation against the printed erroneous fraction remains present. |
| T12 | restricted | Accepted. Clause (iii)'s outside-domain ML dataset is omitted; the real supremum and both guards are disclosed. The wording now expressly states that the guards cover series existence, exact radius, the uniform error estimate, and its vanishing bound. |
| T8 | restricted | Accepted. The additional supported normalized canonical-family and admissibility assumptions are disclosed. The omitted arbitrary-family mean identification, OLS reparameterization/linearization, divided equations, cancellation criteria, and separate discrepancy examples remain disclosed. The canonical claim requests the exact first Taylor polynomial, rather than a quadratic remainder for the actual score. |
| T5 | restricted | Accepted. Its unchanged odds-link residual-root/non-ML example expressly disclaims refuting the printed necessary implication. |
| T6 | restricted | Accepted. The unchanged complete numerical probit witness now carries the precise logical limitation described above. |
| T7 | refuted | Accepted. Two actual locally defined unique maximizing branches have treatment derivatives 120/119 and 1 at the same response mean 1/4. The OLS treatment coefficient is epsilon and the inverse-link derivative at the expansion center is 1. The discrepancy is first order, and the invertible change of basis preserves the treatment coefficient. These facts contradict the canonical mean-only first-order scaling recipe for the claimed general GLM extension. |
| T16 | whole | Accepted. All numerical conversion bounds, the fixed-controls exponential contrast, and the actual four-observation OLS/arithmetic-mean comparison remain present. |
| T4 | whole | Accepted. All positive-mass discrete-cell, finite-second-moment, endpoint, degeneracy, binary, effective-law normalization/reversal, and converse-counterexample clauses remain present. |
| T19 | whole | Accepted. Both the standard conditional-variance identity for general measurable covariates and the a.e. binary propensity formula remain present. |

All four `refuted` docstrings carry the required printed-claim-false prefix and identify the correct witnesses. All four restriction texts agree with their corresponding docstrings after line-wrap normalization. No new hidden assumption, assumed conclusion, missing canonical clause in a `whole` target, or inaccurate scope claim was found. There are no omitted targets.

## Changed-statement safeguards and verification

The explicit-parenthesis change in T12 is checked independently in `scratch/DeltaCheck.lean`. That file reconstructs the original unparenthesized T12 formula and proves equality with the revised `T12Statement` by `rfl`. It also checks the generic implication/conjunction grouping by `rfl` and verifies that T6's proposition retains its original shape. Thus the revision does not move the circle-image guards or change T6's mathematical conclusion.

The earlier `scratch/Check.lean` was recompiled against the refreshed Defs. It still supplies an actual infinite iid uniform sampling law for T2; a measurable fair binary treatment in L2 with an integrable residual weight of mean 1/4 for T4/T19; and a nondegenerate, normalized two-point canonical family with nonempty parameter domain for T8. It also checks the rare-law positive normalizer, actual sample probability, sigmoid smoothness/admissibility, the nontrivial T12 radius inequalities, and equality with Mathlib's conditional variance definition.

The changed labels introduce no new numerical conventions. In particular:

- **T1:** every fixed-law atom is positive; E[w]>0, the propensity denominators are nonzero, and finite-sample bounds require n>=1.
- **T2:** E[w]=5/8 and both effective covariate masses are positive. The endpoint-support failure occurs in represented cells, and the iid sampling hypothesis is inhabited.
- **T3:** the sample has probability 1/256 and the full Gram determinant is 2; the zero fitted weights come from actual residuals rather than a singular inverse.
- **T6:** the quantile set is asserted nonempty and bounded below; the fitted probabilities are 1/4, 1/2, 3/4. The witness has admissible log arguments and full rank, and has not acquired a vacuous hypothesis.
- **T7:** the six atom masses are positive and the allowed models' response probabilities stay strictly between 0 and 1. The admissible base point and nonsingular score Jacobian support the genuine maximizing branches. Branch existence and the treatment derivatives are conclusions, rather than assumptions.
- **T12:** p=1/2, r=1/2, rho=1<pi realizes the real domain restrictions. The unit complex circle is nonempty and compact and avoids the denominator zeros at odd multiples of i pi. Its continuous norm image is bounded, so the extra guards are satisfiable and the supremum is finite. Both rho and 1-r/rho are positive. No empty-set or unbounded-supremum fallback is doing the work.

Both scratch files compiled successfully with the prescribed `sap-lean` wrapper, without `lake` or imports of Challenge proofs. `DeltaCheck.lean` emits only unused-hypothesis-name warnings in the copied original formula. The logs are `scratch/Check2.log` and `scratch/DeltaCheck.log`. The previous independent rational checks remain applicable because the mathematical data are unchanged; no new proof certification is claimed from the architect's account.

`findings2.json` contains one assessment per canonical target in the original order, with the same fields and verdict vocabulary as `findings.json`. Python checks confirm JSON parsing, target coverage, theorem names, schema values, decision counts, restriction agreement, and the refutation prefixes.
