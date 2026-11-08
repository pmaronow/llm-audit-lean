# Palomar statement referee report — P015a

Twelve targets audited: **8 correct_whole, 3 correct_restricted, 1 not_faithful**. Severity: **1 major, 0 minor, 11 none**. No false statements, vacuous targets, or omissions found.

The blind reading was saved in `reading.md` before `claims.json` was opened. The claim comparison was saved in `claim-stage.json` before `record.json` was opened. No step-2 verdict was changed after reading the record. The substantive paper comparisons use the printed passages supplied in `claims.json`; the online [publisher record](https://onlinelibrary.wiley.com/doi/abs/10.1111/ajps.12185) exposed the abstract rather than the full article.

## P015-T6 — not_faithful, major

**The probit example proves failure of the converse of the printed implication.** Its numbers and likelihood calculation appear correct.

Let M(theta) mean that theta maximizes the likelihood, and R(theta)=0 mean that theta solves the substituted residual equation. The quoted Appendix C sentence says an ML estimator solves that equation: **M(theta) implies R(theta)=0**. A refutation therefore needs **M(theta) and R(theta) != 0**.

T6 supplies **R(theta*)=0 and not M(theta*)**. The residual equality is in `SAP/P015a/Defs/Part2.lean:147`; the nonmaximality statement is at lines 152–154. The strict genuine score bound and directional likelihood derivative establish nonmaximality, but do not produce a maximizer violating the substituted equation. This witness disproves sufficiency of the substituted equation, and therefore equivalence with ML, rather than the printed necessary implication.

`record.json` nevertheless declares T6 `whole`, with no restriction, and the Challenge docstring at `SAP/P015a/Challenge/Part1.lean:69` discloses no limit on that refutation role. The same logical problem is explicitly recognized and correctly restricted for T5. T6's finite content matches the validator's numbered example; the failure is in crediting it as a refutation of the printed reading. This objection was already recorded at step 2.

**Fix:** keep the theorem, change T6's record decision to `restricted`, and add this exact restriction to both record and docstring:

> Restriction: Retains the specified 48-observation probit data, the well-defined standard normal quantile, admissible means, full rank, zero substituted residual equation, strictly positive genuine treatment score, likelihood directional derivatives, and nonmaximality at the displayed parameter. This witness proves failure of the converse that every substituted residual root is an ML estimate. It does not refute the printed necessary implication that an ML estimate solves the substituted residual equation; no actual probit ML maximizer with a nonzero substituted residual is asserted.

Alternatively, whole refutation credit requires an actual probit likelihood maximizer with a nonzero substituted residual equation.

## Record decisions accepted

The `whole` decisions for T1, T2, T3, T13, T7, T16, T4, and T19 are supported by the statements. In particular, T19's first identity is definitional, as the paper says: the SAP definition unfolds to Mathlib's `ProbabilityTheory.condVar`. Its separate binary propensity identity remains substantive.

The three declared restrictions accurately describe the retained results and are reproduced in the Challenge docstrings:

- **T5:** retains the complete odds-link residual-root/non-ML example, and explicitly disclaims refuting the printed necessary implication. Correct restricted credit.
- **T8:** discloses the normalized, supported canonical-family assumptions and the omitted arbitrary-family mean identification, OLS reparameterization/linearization, divided equations, cancellation criteria, and separate discrepancy examples. The retained full-score formula is an exact Taylor-polynomial identity, with no nonlinear quadratic remainder claimed.
- **T12:** discloses omission of the outside-domain ML dataset and replacement of the maximum by a guarded supremum without an attainment assertion. Formally the nonemptiness and boundedness guards precede the entire radius/error/convergence conjunction. They are satisfiable; the radius inequalities put the circle before the nearest complex poles. The retained bound applies uniformly to every real point in the stated interval.

There are no omitted targets in this package. The record's references to unused proof declarations were not treated as evidence about statements, and no Solution or Comparator sources were read.

## Verification and nonvacuity

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully with no errors or warnings. It imports only the supplied Defs. It checks positive normalization in the rare-overlap law, the multivalued conditional variance, the actual sample draw probability, agreement with Mathlib conditional variance, and inhabited hypotheses for the measure and likelihood clauses. In particular:

- The T2 sampling hypothesis is realized by the infinite product of the uniform four-point law and coordinate draws; it is not an empty sampling class.
- A fair two-point population has measurable binary treatment in L2, a positive-mass covariate cell, and integrable residual weight with mean 1/4. This realizes the positive-normalization clauses of T4 and the assumptions of T19. Constant treatment realizes the separate degenerate case.
- A two-point canonical family with base measure delta_0+delta_1, cumulant log(1+exp eta), dispersion 1, and full real parameter domain satisfies every `ValidCanonicalFamily` guard.
- Sigmoid smoothness/admissibility and the nontrivial T12 parameter choice p=1/2, r=1/2, rho=1<pi are checked.

`python3 scratch/exact_checks.py` passed independent rational checks of T1's IPW moments, effective masses and actual population OLS; T2's effective probabilities and effects; T3's actual least-squares solution and determinants; T5's residual and score vectors; T6's determinant, cancellation and rational normal-bound certificate; T7's moment matrices, Jacobian, treatment derivative, valid response probabilities and OLS comparison; and T16's exponential enclosures using a rational Taylor tail bound. These checks do not import Challenge theorems. The analytic and probabilistic assertions were also assessed mathematically; the scratch checks are not a new proof of every theorem.

All twelve targets have individual nonvacuity assessments in `findings.json`. Positive cell probabilities, positive weighting normalizers, nonsingular regression matrices, integrable residuals, admissible log arguments, and bounded analytic suprema exclude the relevant totalized-definition pitfalls. JSON parsing, schema values, target coverage, theorem names, and record/docstring restriction agreement were checked with Python.
