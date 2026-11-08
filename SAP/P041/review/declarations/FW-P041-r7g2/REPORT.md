# P041 declaration review

All five declarations are **faithful**, with severity **none**. The record's
`whole` decisions and the declaration docstrings accurately describe the
canonical claims. No correction is needed.

| Declaration | Claim coverage | Verdict |
|---|---|---|
| `SAP.P041.T6` | Rank/own-treatment formula, fixed calendar outcomes, scrutiny direct effects, planned and implemented contrasts, and both numerical instances | faithful |
| `SAP.P041.T7` | Actual binary-data OLS and HC1 calculation, corrected SE, erroneous normal/Student p values, and genuine critical-point comparisons | faithful |
| `SAP.P041.T8` | All rectangles and central approximations, genuine normal critical points, strongest tiers, and the separate nested-cutoff reading | faithful |
| `SAP.P041.T9` | Complement identities, all three regression designs and twelve coefficients, removal exclusion, full six-hour vectors and coding rules | faithful |
| `SAP.P041.T10` | Complete reparameterization, covariance congruence, five reciprocal interpretations, SE/Wald formulas, both star rectangles and exact illustration | faithful |

The blind reading was saved as `reading.md` before opening the canonical
claims. Every closure declaration was read, including all 128 distinct
generated auxiliaries printed in `scratch/BlindProofs.out`. The claim
comparisons were saved in `claim-stage.json` before opening `record.json`.
Reading the record required no change to those conclusions. Audit-history
notes were not used to remove clauses from the canonical assertions.

The definitions use genuine finite uniform averages, matrix OLS/HC1,
Gaussian probabilities, Student(197) density integrals and centered-product
covariances. Matrix invertibility is assumed or derived where needed.
Positive intervals exclude logarithm and reciprocal domain problems.
HC1 alone has the positive degrees-of-freedom guard; the coefficient
identities also cover square full-rank designs. L2 conditions ensure actual
covariances exist. Zero variance is retained for SEs and excluded only for
defined Wald tests. No conclusion relies on a junk value.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` checks explicit
nonvacuity instances independently of the target theorem proofs: the T7
200-row binary dataset; all T9 layouts, twelve binary survivor totals and
extra six-hour study totals; balanced assignments; the rounding rectangles;
and the covariance and SE/Wald domains. The survivor patterns decrease
across horizons, so they are compatible with removal times. The reference
critical points are existential conclusions characterized by actual tail
equalities and uniqueness, rather than assumptions supplying the conclusion.

The five `whole` labels concern corrected claims; none is labelled
`refuted`. In particular, T8 preserves the first three weaker nested levels
and rejects only the fourth nested assertion, while proving all four
strongest-marker corrections.
