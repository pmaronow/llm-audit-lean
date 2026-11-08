# Palomar statement audit: P001a

| Verdict | Count |
| --- | ---: |
| correct_whole | 3 |
| correct_restricted | 16 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |
| **Total targets** | **19** |

All severities are `none`. There are no adverse findings or omitted targets. T2, T3 and T10 receive `correct_whole`; the other sixteen receive `correct_restricted`.

## Order and independence

`reading.md` was saved after reading only the supplied Defs and Challenge sources and following their definitions into Mathlib. `claims.json` was then read and `claim-stage.json` saved with three `whole` and sixteen `narrower` classifications. Only afterward was `record.json` opened. No step-2 classification changed after the record was read.

All nineteen record decisions agree with those independent classifications. All sixteen record restriction texts also match the actual Challenge docstrings exactly after whitespace normalization. No external proof source, Solution, Comparator or excluded proof row was read or credited. Defs and Challenge sources were not modified.

## Material restrictions checked

* T1 retains the actual normalized finite-second-moment zero-direction witness, but does not separately export every support, CDF, finite-bound or abstract differentiability assertion. T2 does contain both the finite-positive-variance CLT and that witness. T3 supplies a genuinely jointly continuous bounded counterexample, not merely a negation of an overbroad contract.
* T4 places even equality on the open set behind an existing coordinate derivative and uses global CEF representatives. T5 supplies a least-squares fit and omits the supplementary square-root-degree endpoint result. T6 exports its sharp finite envelope/probability bounds only on [0,1], while retaining arbitrary-interval cubic-rate stability. These limitations are stated in the docstrings.
* T7 omits the derivative formulas and exact KL gap. T8 requires a finite uniform envelope at every natural sample size, including zero; since the zero-sample log likelihood is zero, it imposes a uniformly bounded population objective. The docstring explicitly discloses this stronger premise. Its consistency clause does not unnecessarily assume finite entropy.
* T9 omits the explicit lower bounds and specified collapse scale; its general positive-sample unboundedness conclusion appears in T10. T11 omits the separate likelihood bound and binomial rewriting while retaining an actual normalized experiment, attained MLE selection, and full-parameter inconsistency.
* T12 also imposes sample-zero uniform log-likelihood and Hessian bounds. Quadratic-mean differentiability is a premise of the entire normality/efficiency clause, rather than only the information bound; local integrability prevents a zero-by-default remainder integral. These restrictions are disclosed and have a nonzero-dimensional compact Bernoulli instance. The competing-estimator regularity definition matches the claim and does not assume the information inequality.
* T13–T16 add per-sample L2 premises and omit the listed design predicates and further inferential conclusions. The fixed design is normalized and nondegenerate, and the L2 premises are satisfiable. T15 only asserts true-score failure and intercept consistency; the estimated-score equality and failure are actually in T16, as disclosed. Neither the hedged empirical assurances nor the reported standard errors are certified.
* T17's 240-observation arithmetic is explicitly population-risk arithmetic, not a constructed finite sample. Its finite-design and asymptotic F/Wald assertions match their claimed meanings. T18 exports the population result, with the stated omission of robust-test asymptotics. T19 uses the exact countable masses reindexed by k+1; positive cells represent complete discrete arm supports, while the explicit rate and chosen violating covariate are omitted as disclosed.

## Nonvacuity and convention checks

Each entry of `findings.json` gives a concrete mathematical instance or explains the unconditional witness. In particular, the instances for T4, T8, T12 and T18 have positive dimensions; none relies on an empty index type. For T6 an iid uniform, zero-outcome model with Legendre basis and degree floor(n^(1/4)) satisfies the Gram premise by the elementary Frobenius second-moment bound. In T13–T16 the score density integrates to one, both Boolean groups have positive probability, the statistics are bounded, and ties between distinct original donors are null; identical bootstrap duplicates have identical outcomes. Thus bounded measurable versions satisfy all additional moment premises.

The real liminf in T5 concerns probabilities bounded in [0,1]. The Gram supremum is over a nonempty compact unit sphere because its finite-bound clause requires positive dimension. All relevant polynomial-square integrals are finite on compact support. KL entropy/cross-entropy and quadratic-mean integrals are protected by explicit integrability premises. Conditional ratios are used on positive cells; shifted natural subtraction is guarded. T17's singular matrix and zero-division conventions disappear eventually almost surely because the limiting moment matrices and residual variances are nondegenerate. The conditional-expectation default cannot make T18's conditional independence automatic: measurability, finite measure and bounded indicators protect its use.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed successfully with exit code 0. This file imports Defs only and has no `sorry` or added axioms. Its kernel checks cover the countable iid product construction, a nonempty mixture restriction, distinct same-law mixture parameters, positive placebo cells and exact risks, positive overlap cells/interior propensities, and the sample-zero uniform-objective bound. Exact rational arithmetic saved in `scratch/exact-arithmetic.json` independently verifies T17's HC0 asymptotic variance, scaled F/Wald constants and risk-based finite arithmetic. At most one Lean process ran at a time; `lake` was never run.

## Confidence and scope

The long local-Poisson matching asymptotics in T13–T16 and the polynomial instability estimate in T5 were checked for statement fidelity, well-definedness and plausible mathematical content, but were not independently re-proved. Confidence is correspondingly lower for those targets; these findings do not certify the supplied proof implementations. The [publisher's book page](https://www.cambridge.org/core/books/foundations-of-agnostic-statistics/684756357E7E9B3DFF0A8157FB2DCECA) was consulted for bibliographic identification; the supplied canonical transcriptions, not inaccessible full chapter text, are the basis of the claim comparisons.
