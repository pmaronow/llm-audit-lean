# Palomar P001d statement audit

Audited all 19 targets in `claims.json`. Each has a Challenge theorem; none is omitted. The input Lean files and the record were left unchanged.

| Verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 10 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: 18 none, 1 minor, 0 major.

## P001-T65 — restriction_inaccurate (minor)

The theorem `SAP.P001d.T65` has the correct full-rank OLS minimizer and residual identities. Its docstring (`SAP/P001d/Challenge/Part1.lean:41`) and the architect's record say that Gram invertibility is an added restriction and that singular-design residual properties were dropped.

The supplied canonical claim explicitly states in `canonical_claim.note`: “Theorem 4.1.5 inherits the invertibility of $\mathbb{X}^T\mathbb{X}$.” That note also describes the exact formal content for realized samples with invertible Gram matrix. Thus, relative to this canonical target, the theorem is whole; its restriction declaration is inaccurate. Residual identities do extend to singular least-squares designs mathematically, but that extension is outside the canonical reading expressly specified here.

Fix the record to `decision: "whole"`, `restriction: null`. Replace the Challenge restriction sentence with:

> The inverse-Gram OLS coefficient uniquely minimizes the squared criterion and satisfies all three residual identities for nonempty full-rank designs with an intercept, including the inherited Gram-invertibility assumption of Theorem 4.1.5 specified in the canonical claim.

No mathematical change to T65 is needed. The instance n=2, K=0, X=(1,1)^T, y=(0,2)^T has Gram matrix [2], coefficient 1, and residual (-1,1); its hypothesis checks are included in `scratch/Check.lean`.

## Scope and record assessment

The ten accepted restrictions are T58, T61, T64, T66, T68, T69, T70, T73, T74 and T76. Their docstrings and record accurately describe the missing conclusions, strengthened measurability/moment premises, or supplied certificates. In particular:

* T61 asserts the weak-bootstrap limit for the median, not for the regular finite statistic; it adds no external bootstrap theorem as a premise. Its odd-size finite fallback is the appropriate middle order statistic. The local functional identity stays in the linear branch, so the totalized infimum for arbitrary functions does no work.
* T66 retains only the corrected, definitional standard-error diagonal formulas. It expressly drops the covariance-estimator matrix-form equivalences and supplies rather than reconstructs the residuals and variance scale.
* T74 supplies a conditional centered-square certificate and uses a translated-product joint-law premise for the Gaussian branch. Its moment/measurability requirements and omitted pointwise conditional-law conclusion are disclosed.

The eight whole targets are T59, T60, T62, T63, T67, T71, T72 and T75. Some valid generalizations are recorded as `broader` in the claim-stage comparison; they cover every canonical instance and lose no canonical conclusion. For example, T62's conditional moment equivalence does not need marginal asymptotic normality or IID sampling, and T63's weak law also allows zero coordinate variance.

T72's zero-scale assertion is explicitly about the *totalized algebraic formula*: it is not claimed to be a density of a degenerate Gaussian or an evaluation of the printed partial expression. All actual density and first-moment claims require positive scale. Its explicitly named zero extension has mass zero and is excluded as a probability density. T75 computes the entire fixed-covariate two-point PMF mean, as requested by the canonical formal content.

## Evidence and ordering

1. `reading.md` was saved after reading the Defs, Challenge and relevant Mathlib definitions, before opening either JSON input.
2. `claim-stage.json` was saved and parsed before opening `record.json`. It contains 19 independent comparisons: 3 whole, 10 narrower, 6 broader.
3. The record was then compared with those saved readings. No step-2 verdict was changed after reading the record. In particular, the T65 discrepancy was already identified in its saved step-2 reason.

`scratch/Check.lean` imports only the supplied Defs and uses no Challenge theorem or admissions. It checks kernel integrability and a concrete admissible rectangular kernel; measurability and probability normalization of the heavy law and existence of a genuinely IID coordinate realization; the finite counterexample; a full-rank intercept design with strictly positive selected covariance diagonals; probability bounds protecting real limsup; an elementary event-integral conditional-mean certificate; and the explicitly totalized zero-scale formula. It was compiled with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. No `lake` command was used and at most one Lean process was run at a time.

The asymptotic bootstrap statements were assessed mathematically rather than independently reproved. Their confidence is marked medium-high; the remaining findings are high confidence. Each target's concrete nonvacuity instance or unconditional example appears in `findings.json`. Both JSON deliverables were parsed and their target coverage and required fields checked with Python 3.
