All five declarations are **faithful**, severity **none**. Each covers its
canonical mathematical claim, and each recorded `whole` decision is correct.
No docstring defect or reliance on a junk value was found.

| Declaration | Basis for the verdict |
| --- | --- |
| `SAP.P037c.T35` | All six clauses are present: own-seed-only outcomes, observed nomination means, the six-point permutation distribution, exact p-value, rejection probability 8/63, and the four-block result with p-value 2/252^4. |
| `SAP.P037c.T36` | The statistic preserves outgoing nomination multiplicity and seed recipients. The exact sharp-null inequality, direct-effect decomposition and reciprocal-pair rejection witness match (a)–(d). The witness violates the global sharp null and does not challenge the test's validity for that null. |
| `SAP.P037c.T27` | Both assignment designs, the twelve-unit potential outcomes and averaging set, both actual WLS fits, normal equations, means and contrast differences are covered. E1 includes the independent joint law. E2 includes the network, percentile rule, complete analysis subpopulation and observation probability 1/640. |
| `SAP.P037c.T28` | The full-rank and positive-weight assumptions match the claim. The general prediction and augmented-mean identities, both residual equations, one-covariate coefficients and equality characterization cover (a)–(e). |
| `SAP.P037c.T33` | The specified abstract 96-state law, marginals, ranks, point fit and residuals are present. The imputation identity holds for every exposure mean at every assignment. Both full-control variances and the collapsed variance match the exact constants and rounding bounds. |

The blind reading in `reading.md` was saved before opening `claims.json`.
`claim-stage.json` was saved before opening `record.json`; no claim-stage
assessment changed afterward. Every dependency listed in `closure.json` was
read, including all 96 distinct generated auxiliary declarations printed in
`scratch/closure-checks.out`. The supplied canonical claims govern the review;
the [paper](https://doi.org/10.1073/pnas.1514483113) was consulted for context.

The three concrete certificates have no hypotheses that could make them
vacuous. Compiled checks establish supported observations and positive masses
or denominators. For T36, a two-state reciprocal-nomination example satisfies
all general hypotheses with distinct assignments and fixed nonconstant
outcomes. For T28, eight units with two distinct covariate values in every
category satisfy both rank requirements, both minimization requirements and
positive within-category sums of squares. These checks use definitions and
Mathlib, without invoking the audited theorem stubs.

The command `/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean` passed.
`python3 scratch/exact-audit.py` also passed: it independently checks all 252
one-block observations, the four-block distribution by convolution, both
twelve-unit WLS fits, the E2 school/seed law, a nonzero T28 example with unequal
weights, and all 96 T33 assignments using exact rational arithmetic.

Zero denominators, out-of-range list defaults and singular matrix inverses
do not supply the asserted values. Positivity and rank hold on the relevant
domains; both square-root inputs are positive. The canonical counterexamples
state their own designs. In particular, T33's certificate does not assert a
school/network realization, and none of these declarations is labelled
`refuted`.

`findings.json` contains exactly the five requested entries, with fingerprints
copied from `closure.json`, and has been parsed and checked with Python.
