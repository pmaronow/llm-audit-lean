# P026b delta review

All 12 revised targets were checked against the saved blind expansion in
`reading.md`, their canonical `statement`, `definitions_needed`, standing
assumptions, and `record2.json`. The architect's account in
`architect-report.md` agrees with the changes observed. Claim notes and
proof provenance were not used to change the canonical scope.

| Verdict | Count |
| --- | ---: |
| correct_whole | 11 |
| correct_restricted | 1 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity: 12 none, 0 minor, 0 major. No new or outstanding adverse finding.

## Earlier finding: fixed

My sole earlier adverse finding was the missing interpretation disclosure
in T15's docstring. It is **fixed**, with no residual issue. The revised
`SAP/P026b/Challenge/Part1.lean:18–19` now states:

> This refutes the reading of the package help that estate() with HT=TRUE
> remains unbiased when covariates X are supplied.

This is exactly the reading identified in the canonical claim and my
earlier requested fix. The docstring does not call the canonical
counterexample false. `record2.json` correctly retains `whole` for T15.
Its full three-unit fitted-vector, covariance, estimator, expectation,
ATE and bias assertions remain present. Its verdict therefore changes
from `not_faithful` (minor documentation defect) to `correct_whole`.

Earlier adverse findings: 1 fixed, 0 partly fixed, 0 not fixed. All earlier
accepted mathematical assessments remain accepted.

## Change and clause review

The only detected change from the original review is the T15 docstring
addition. Expanding all revised statement definitions and their supporting
SAP definitions gives the same mathematical content recorded in
`reading.md`: no changed quantifier, hypothesis, conclusion, numerical
constant, prediction rule, or population was found. `record2.json` is
also equal to the original `record.json` as parsed JSON. This comparison
uses the saved mathematical reading; it does not claim a byte comparison
against an unavailable archived source tree.

| Target | Revised decision | Clause and label check |
| --- | --- | --- |
| T13 | whole | Both arm-total covariance identities and the ATE bias identity remain, for arbitrary assignment-dependent predictions. |
| T14 | whole | Both unique finite logistic maxima, coefficient bounds, corrected moment intervals, all ten rounded entries, both RMSEs and all six printed-entry failures remain. |
| T15 | whole | Complete canonical OLS counterexample remains; the interpretation it refutes is now explicitly disclosed. |
| T16 | whole | Fixed predictions, all-unit OLS without a rank hypothesis, residual identities, covariance bias, biased example, zero-covariance condition and sharp-null condition remain. |
| T17 | refuted | The support assertion and sharp-null unbiasedness assertion are assertions made in the canonical printed claim. The supported two-unit example contradicts them. |
| T18 | refuted | The canonical general rule explicitly permits fitting multiple individually independent inputs. The XOR example satisfies those premises and has nonzero focal covariance. |
| T19 | refuted | Negating a necessary conjunction of printed moments refutes their asserted joint correctness. Positive FE residual norms and unique logistic maxima remain asserted. |
| T20 | whole | Observed/potential masking, both unbiased arm totals and unbiased ATE under arbitrary treatment dependence remain. |
| T21 | restricted | All three clauses remain; clause (b) adds exactly m treated clusters on every positive-weight assignment, precisely as disclosed. |
| T22 | whole | Both unbiased generalized totals, unbiased ATE, fixed predictions and the allocationwise adjustment identity remain. |
| T23 | whole | Exact affine formula, balance equivalence, supported failure example and identically transformed generalized estimator remain. |
| T24 | whole | Both residual identities, the fixed-prediction variance formula, both cluster arm variances and all three covariance forms remain, without directed cross-support. |

The `refuted` decisions for T17–T19 are correct: each theorem contradicts
an assertion of its canonical claim, rather than merely an alternative
interpretation of guidance. T18 does not claim to disprove the valid
single-input independence implication in footnote 5. T19 does not assert
that every selected table entry is individually false. The findings
schema has no `correct_refuted` verdict, so these three accepted
refutations use `correct_whole`, as in the first review.

T21's restriction remains accurate and complete in both the record and
the Challenge docstring at lines 55–56. Equal marginal probabilities
alone permit independent fair assignments on two clusters with positive
probability of zero or two treated clusters. Requiring exactly one
treated cluster is therefore a proper restriction of the canonical
formal-content clause, even though the preceding printed quotation
already describes fixed-count sampling. No clause is silently dropped.

## Junk values and nonvacuity

No mathematical statement changed, so no new junk-value convention or
antecedent was introduced. The changed T15 documentation still describes
the actual three-unit, three-allocation model: weights `1/3`, marginals
`1/3` and `2/3`, population denominator `3`, OLS Gram determinant `6`,
adjusted estimates `(1/4,1,1/4)`, expectation `1/2`, and ATE `1`. Its
assertions are closed facts, not consequences of an impossible premise.

The existing nonvacuity examples remain applicable: the fair singleton
experiment, independent two-cluster experiment, complete one-of-two
experiment, and supported unequal-cluster example. Positive marginals
protect inverse weights; nonempty populations protect ATE denominators;
strict count bounds protect natural subtraction. The printed variance
formula retains its stated epsilon correction. The finite logistic
maximizer assertions exclude the fallback branch, sigmoid probabilities
keep likelihood logarithms positive, and the FE residual-norm assertion
excludes division by zero. These conclusions were not converted into
extra hypotheses.

Validation checks the revised theorem headers, all 12 target mappings,
the interpretation disclosure, and the three printed-refutation prefixes.
Current-source fingerprints and the comparison basis are saved in
`scratch/delta-review-evidence.json`. The finite-example checks in
`scratch/Check.lean` compiled successfully against the refreshed definitions
with exit code 0; the log is `scratch/delta-review-check.log`. These checks
import only `SAP.P026b.Defs`. JSON parsing, schema and exact target
coverage passed with Python. No `lake` command or new external
proof-certification run is involved in this review.
