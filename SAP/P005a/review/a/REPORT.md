The audit covers all 14 targets in `claims.json` and all 13 Challenge
theorems. There are **2 correct whole statements, 11 correct restricted
statements, and 1 acceptable omission**. There are **0 adverse findings**.

| Verdict | Count |
| --- | ---: |
| correct_whole | 2 |
| correct_restricted | 11 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

No target requires an adverse-item explanation or a corrected statement or
docstring. The architect's decisions agree with the independent claim-stage
assessment. Each declared restriction also matches the corresponding
Challenge docstring, including its added hypotheses. No claim-stage verdict
was changed after reading the record.

| Target | Record assessment |
| --- | --- |
| T1 | Restricted correctly: numerical counterexample retained; product mean, decomposition, gap and location/centering comparisons disclosed as omitted. |
| T2 | Restricted correctly: both-arm expectation and centered bound retained; separately asserted proof steps (a)–(d) disclosed as omitted. |
| T3 | Restricted correctly: admissible leverage counterexample and both failed bounds retained; detailed moments, category law, gaps and later comparisons disclosed as omitted. |
| T4 | Restricted correctly: finite variance chain and actual variance orders retained; intermediate moments, numerical-RHS order, allocation bounds and sequence-domain requirements disclosed. |
| T5 | Restricted correctly: actual and printed opposite signs retained; the separate moments, coefficients and component values are disclosed as omitted. |
| T6 | Whole correctly: both third moments, both signed components and their difference match the canonical hypotheses and formulas. |
| T7 | Restricted correctly: an actual regular sequence refutes the printed remainder; grid/formula/intermediate/probability/numerical details and the normalization domain are disclosed. |
| T8 | Omission acceptable: the visible record identifies an unproved, noncanonical proposition required by its only credited expansion proof. |
| T9 | Restricted correctly: only the logarithm inequalities and equivalence/implication clauses remain; the complete estimator expansion and remainder are expressly dropped. |
| T10 | Restricted correctly: the wrong and corrected expectation values remain; assignment, leverage, gap and scaling details are disclosed as omitted. |
| T11 | Restricted correctly: cancellation, expectation formulas, weights and stochastic order remain; alternative weight form, leverage range, control size restriction and sequence requirements are disclosed. |
| T12 | Restricted correctly: scalar OLS gives the three actual expectations and wrong-inverse mismatch; component identification and auxiliary identities are disclosed as omitted. |
| T13 | Whole correctly: the corrected control inverse, expectation chain, components and coefficient identities are all present. |
| T14 | Restricted correctly: corrected algebra, bias decomposition and observed-data factorization remain; the missing wrong-set counterassertion and added hypotheses are disclosed. |

The blind reading was saved in [reading.md](reading.md) before opening
`claims.json` or `record.json`. The subsequent independent comparison is in
[claim-stage.json](claim-stage.json); the final per-target results and
nonvacuity instances are in [findings.json](findings.json).

The definitions correctly implement finite complete randomization, covariance
with the actual arm-size divisor, fixed potential outcomes, standardized
covariates and finite-population leverage. Every substantive denominator is
protected by the size or invertibility hypotheses. Leverage suprema are maxima
of finite nonempty ranges wherever used substantively. The asymptotic
predicates quantify over genuine nonempty assignment spaces eventually.
The index subtraction in the spike grid is guarded by its nonzero-index
branch. The one-coordinate counterexample uses the ordinary equality
log(1)=0 and a positive remainder rate. Empty dimensions, singular total
inverses and initial total-function values do not establish the retained claims.

Independent exact rational enumeration in
[scratch/audit_checks.py](scratch/audit_checks.py), with results in
[scratch/exact-checks.json](scratch/exact-checks.json), recovered all retained
counterexample numbers. It checked every assignment for the six-unit examples
and all 12,870 assignments for T3, with strictly positive arm variances. It
also checked the finite expectation, centered-bound, third-moment,
control-bias and pooled-bias formulas on two nonconstant scalar populations
through all allocations, and spike populations at n=6,7,8,10,12.

[scratch/Check.lean](scratch/Check.lean) compiled successfully using exactly
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It imports only Defs
and independently proves a positive-dimensional population's standardization,
the assignment count, signed third-moment coefficients, positive-variance
assignment and size conditions. It uses no Challenge theorem or `sorry`.
No `lake` command was run.

For asymptotic nonvacuity, take d=1, m=floor(n/2), zero outcomes and
x_i=(i−(n−1)/2)/sqrt((n²−1)/12), for n≥3. This has M(x)=0,
M(x²)=1 and κ=3(n−1)/(n(n+1)); K=1 and allocation constants
1/4,3/4 suffice. Its covariates are distinct, and both arms are regular for
n≥4. Thus the sequence assumptions and the repaired logarithm conditions
have positive-dimensional instances. For T7, the explicit spike formula gives
κ→1 and the all-assignment remainder bound along even n negates the stated
O_p order. Finite enumeration supports these formulas; universal and
asymptotic judgments additionally use the mathematical identities and bounds
recorded in the reading and claim-stage reasons.

The original journal article was consulted only after the blind reading.
Its Lemma A.1, Theorem 4.1 and Appendix B displays agree with the printed
formulas relevant to the retained refutations. See the
[journal article PDF](https://joelmidd.github.io/papers/ChangeMiddletonAronow_ExactBiasCorrection.pdf),
printed pp. 1509–1511 and 1517–1519. The supplied canonical text remains
the comparison standard.

The T8 omission assessment is limited to the supplied record's account of
the unavailable unconditional proof. The external formalization was not
inspected. The record identifies `Tropp2011RowSampling` as an unproved
dependency and correctly avoids adding it to the canonical hypotheses;
T9's docstring accurately limits its separate retained result to logarithms.
Both JSON outputs were parsed and checked with Python 3 for target coverage,
unique theorem mappings and permitted verdict values.
