# P026b statement audit

All twelve targets are accounted for. There are no adverse findings.

| Verdict | Count |
|---|---:|
| correct_whole | 11 |
| correct_restricted | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: none 12; minor 0; major 0. No target is omitted.

The architect's eight `whole`, three `refuted`, and one `restricted`
decisions are upheld. The three faithful refutations count as
`correct_whole` in the requested findings vocabulary. No claim-stage verdict
changed after reading the record.

## Restricted target

**P026-T21 / SAP.P026b.T21** is `correct_restricted`.
`Defs/Part5.lean:38` adds to clause (b) that every positive-probability
assignment treats exactly m clusters. The canonical formal-content clause
(b) states only the partition, equal marginals and 0<m<M. Independent fair
assignment of two singleton clusters meets those conditions, while treating
zero or two clusters each has probability 1/4. Thus the extra hypothesis is
not implied by that formal-content clause. The printed introductory prose
does describe fixed-count assignment, but it does not erase the stronger
formal-content assertion included in the canonical claim.

`Challenge/Part1.lean:53` discloses precisely this added condition:

> Restricted: clause (b) requires exactly m treated clusters on every supported assignment;
> the canonical formal-content paragraph lists only the partition and marginal probabilities.

The record's restriction is accurate and complete. Clauses (a)–(c) are
retained, with no further material narrowing found. The extra condition is
unnecessary mathematically for the fixed-denominator identity, but a
correctly disclosed restriction is permitted. No correction is required.

## Refutations and interpretation

**T17** contradicts the canonical printed support/conservativeness and
sharp-null assertions. Its asymmetric example is a valid probability
design with positive marginals and positive same-arm joints. With constant
potential outcomes, the true variance is 27/8 and the expected variance
estimate is 23/8. Its directed cross joints are 0 and 1/3, despite positive
disagreement. This also validates the separate footnote-9 refutation.

**T18** contradicts the canonical rule explicitly formulated with pairwise
independence. Each input is independent of the focal assignment, but their
XOR equals that assignment and has covariance 1/4 with its indicator. This
does not challenge the valid single-input composition argument or actual
independent-block fitting. The docstring's claim of a false printed general
rule is justified by the canonical formal content.

**T19** refutes the asserted conjunction of table moments. It suffices that
one selected moment fails; the theorem does not claim every entry fails.
The FE denominator is positive on all 90 allocations, with minimum
2710/993. Its expectation is approximately -0.0139874263, outside the
printed -0.012 rounding interval. Independently, the Linear variance is
38307/634880, approximately 0.0603373866, outside the printed 0.026 interval.

**T15** is correctly classified `whole`, as the canonical target is the
specified package counterexample. Its docstring describes the actual bias
example without declaring the printed package guidance itself false.

## Definitions, truth checks, and nonvacuity

The blind expansion was saved in [reading.md](reading.md) before opening
either JSON source. [claim-stage.json](claim-stage.json) was saved before
opening `record.json`. No Solution or Comparator source was inspected.

All generalized universal unit statements quantify over arbitrary finite
binary assignment laws, with nonempty unit sets and positive treatment and
control marginals. These ensure N>0 and nonzero marginal denominators.
The natural subtractions in T21 are positive by its inequalities. All
expectations are finite sums. No integrability, infinite-limit, empty-type,
or conclusion-as-hypothesis mechanism was found. The pair estimator's
regularization at zero joint probability is the stated epsilon convention.
T24's off-diagonal covariance sum includes zero cross joints and therefore
does not require directed cross support.

OLS fitted responses use the ordinary Euclidean orthogonal projection onto
the real column space, including rank-deficient designs. The logistic fits
maximize the ordinary finite-coefficient unpenalized likelihood; their
existence and uniqueness are conclusions. Both blocks have full-rank
intercept/covariate designs and no nonzero weak separating direction, so
the fallback coefficients do not supply the result. For finite real
coefficients the sigmoid and its complement are strictly positive, so
Mathlib's extended logarithm conventions are not used.

The Table 1 data and Section 7.1 specification were checked against the
[paper, pp. 147–149](https://www.degruyterbrill.com/document/doi/10.1515/jci-2012-0009/html).
In particular, opposite-block predictions are intentional and match both
T14's canonical claim and the paper.

The following independent checks were completed:

- `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` exited successfully.
  It imports only the supplied Defs and constructs an explicit two-unit
  UnitExperiment, positive marginals, fixed supported treatment count,
  a surjective two-cluster experiment with positive disagreement, and
  checks the asymmetric support and XOR covariance examples. It does not
  import the Challenge stubs or assume any target statement.
- `python3 scratch/audit_checks.py` passed. Exact rational calculations
  check the three-unit OLS example, asymmetric variance discrepancy, XOR
  independence cells, unequal-cluster bias, all FE denominators, both
  cross-block OLS lines, and Linear variance.
- The same script recomputes the logistic maxima and moments using
  60-digit Decimal arithmetic. It gives ATE variance approximately
  0.0610543332119005, ATE SD 0.247091750594593, and variance-estimator SD
  0.0125667023899652, agreeing with T14. This numerical check corroborates
  the intervals; it is not a formal interval certificate. Exact
  unbiasedness follows from the fixed residuals, positive pair support,
  and sharp-null equality, rather than numerical near-equality.

Detailed instances are recorded per target in [findings.json](findings.json).
Reproducible numerical output is in
[scratch/check-results.json](scratch/check-results.json).
Both required audit JSON files and the scratch result JSON were parsed
with Python; required fields, allowed verdicts and severities, unique
target coverage, and theorem correspondence were checked.

## Items requiring correction

None. There are no non-`correct_*` or `omission_ok` items to enumerate.
