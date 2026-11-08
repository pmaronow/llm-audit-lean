All 12 targets are correct within their declared scope: 6 cover the whole
canonical claim and 6 have accurate, disclosed restrictions. There are no
adverse findings and no omitted targets.

| Verdict | Count |
| --- | ---: |
| correct_whole | 6 |
| correct_restricted | 6 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 12; minor 0; major 0.

The blind reading was saved as `reading.md` before `claims.json` was opened.
The independent comparison was saved as `claim-stage.json` before
`record.json` was opened. No step-2 reading was revised after reading the
record. The three `broader` comparisons in that file (T3, T10, T12) retain
every canonical assertion and add valid generalizations: equality of
cluster totals suffices for T3's sharp-null equalities; T10's partition
identity also holds without separated cluster indicators; and T12 also
gives the same-arm covariance formulas. Their final `correct_whole`
verdicts record complete canonical coverage.

The architect's six whole decisions (T2, T3, T8, T10, T11, T12) are right.
All six declared restrictions match the theorem docstrings verbatim and
accurately describe the mathematical omissions:

| Target | Accurate restriction |
| --- | --- |
| T1 | Keeps both counterexamples; omits the listed exact marginal/support details and selected pointwise statistics. Diagnoses literal [34]'s zero denominator and A's zero numerator; numerical covariance assertions explicitly concern the zero-omitted continuation. |
| T4 | Keeps the six-unit and both three-unit fits, joint-cell facts, nonzero covariances and specified estimates/expectations. Omits exact full fitting sets, the explicit independence-failure cell comparison, three-unit exact marginals, and B(i)'s pointwise zero estimate. |
| T5 | Keeps both independence premises for the local fitting conclusions, the composition and additive results, and both design examples. Unbiased totals and ATE use only assignment-vector independence for every unit; the observed-outcome-vector and mixed-premise versions are omitted. |
| T6 | Gives the numerical formulas, residuals, moments, denominator positivity and rounding refutations. Their identification as OLS fits or regression solutions is omitted. |
| T7 | Gives the specified-formula versions of the corrected linear/FE entries and RMSE comparison, plus selected HT/prior moments and variance rounding. Omits OLS identification and the blanket unchanged-column assertion, including the stated IPW/FE and HT/prior variance-estimator SE/RMSE entries. |
| T9 | Keeps the six printed-display values, expectation −42, covariance bound and covariance −28, [34] expectation −28 and true treatment-total variance 28. Omits exact marginals, [34]'s six pointwise values and the population arm-variance-bound equality to 28. |

Definitions were followed to ordinary finite sums and products over finite
types. UnitLaw bundles nonnegative normalized weights and strictly positive
marginals; ClusterLaw uses a fixed surjective partition. The separation
premise in the general cluster results is already in the standing
assumptions. Positive marginals and nonempty populations protect all
marginal and population-size denominators. Zero joint probabilities are
guarded or explicitly corrected; the unguarded equation [31] is asserted
under its same-arm support premise, and the equation [34] continuation is
used as the literal statistic only under directed support. Ordered pairs,
the covariance diagonal, and unavailable-pair product terms have the
required indices and signs. Finite test-function factorization is genuine
independence here. No integrability, limit, empty-index, or circular-premise
defect was found.

The numerical population and estimator descriptions were also checked
against Table 1, Section 7.1 and Table 2 of the
[paper](https://doi.org/10.1515/jci-2012-0009). The Lean data match those
printed values and specifications within the stated restrictions.

`scratch/Check.lean` imports only the definitions and compiled successfully
with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`. It constructs a
real law of two independent fair assignments and a four-unit/two-cluster
partition, and proves probability, positive-marginal, separation, joint-cell
and nonempty-fitting-vector independence facts. Thus the general support
and fitting hypotheses have concrete nontrivial instances.

`python3 scratch/audit.py` completed successfully. Its independent rational
enumeration, saved in `scratch/audit-results.json`, checks the two support
counterexamples, the strict six-cluster repair witness, all XOR fits, the
literal Appendix E display, the 90-state table moments and rounding
intervals, and the support minima. It also checks the general bias formulas
on 57 nonuniform finite laws with signed outcomes. These sampled checks
supplement the algebraic statement review; they are not universal Lean
proofs. The FE centered-covariate squared norm is 331/10 and its minimum
treatment-residual squared norm over all 90 allocations is 2710/993, so
the numerical coefficient uses genuine positive denominators.

Both required JSON files were parsed and checked with Python 3 for target
coverage, permitted verdicts and the required fields. Every target has
exactly one finding.
