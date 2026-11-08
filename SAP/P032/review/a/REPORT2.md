# P032 delta statement review

All 12 targets are accounted for: **9 correct_whole, 3 correct_restricted**.
Both earlier individual issues are fixed. There are no partly fixed or
unfixed issues, no new adverse findings, and no omitted targets.

| Verdict | Count |
| --- | ---: |
| correct_whole | 9 |
| correct_restricted | 3 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

All 12 severities are `none`.

The earlier findings are resolved as follows:

| Earlier finding | Status | Evidence |
| --- | --- | --- |
| T5: incorrect `refuted` decision | **Fixed** | The T5 entry in [record2.json](/home/ubuntu/sap/tasks/CHFID-P032-a/record2.json) is now `whole`, with no restriction. The canonical statement itself concludes that the four universal forms are false, and T5 establishes exactly that assertion. |
| T5: blanket “The printed claim is false” docstring | **Fixed** | The [revised docstring](/home/ubuntu/sap/tasks/CHFID-P032-a/SAP/P032/Challenge/Part1.lean:30) identifies the validators' unrestricted weak and strict population, residual-estimator expectation, and relative probability-limit readings. It says those four readings fail and no longer makes the blanket printed-claim assertion. |

The architect's Revision 2 account accurately describes these two fixes.
The revised record differs from the original record only in T5's decision.
The canonical statement, definitions needed and standing assumptions remain
the basis of judgment; historical notes do not change their scope.

I compared every current theorem and its supporting SAP definitions with
[reading.md](/home/ubuntu/sap/tasks/CHFID-P032-a/reading.md). I found no change
in mathematical content, quantifiers, hypotheses, data, masks, integrals or
limits. The identified theorem change is T5's docstring. Its mathematical
payload remains the conjunction of the same four negations in
[T5Statement](/home/ubuntu/sap/tasks/CHFID-P032-a/SAP/P032/Defs/Part7.lean:163).
Rechecking the four underlying universal propositions found no added premise,
weakened refutation or claim to refute an empirical expectation or possibility.

The target-by-target scope check is:

| Targets | Revised decision | Delta result |
| --- | --- | --- |
| T1, T2 | whole | All six constructions and their limits, and the arbitrary-probability-space OLS comparison, remain present. |
| T3, T4 | whole | The full Cox example, decomposition, exhaustive coefficients and id/scaling discrepancies remain present. |
| T5 | whole | Same four refutations; corrected label and interpretation-specific docstring. |
| T6, T7 | whole | The fitted indefinite OLS covariance and the generic and concrete spectral-clipping assertions remain present. |
| T8 | restricted | The two direct ordered-pair equalities remain omitted; the record and docstring disclose precisely that omission. |
| T9 | restricted | The coefficient formula retains the nonzero guards on every member-cluster denominator, the dyad denominator and record denominator; all three guards are disclosed. |
| T10 | whole | Integer recovery, both thresholds and all neighboring table counts remain present. |
| T11 | restricted | The OLS matrix identity remains; the separate pointwise identity, conventional multiway equivalence, software computability, square-root rule and clipping assertion remain explicitly omitted. |
| T12 | whole | The finite-variance identities and all strict and equality sign cases remain present. |

No new junk-value or nonvacuity problem arises from the T5 revision. Its
population counterexample has two nonempty disjoint dyads, a full-rank
intercept design and a realizable positive definite covariance: the dyadic
value is 1/2 and the true variance 1/4. The four-record example gives expected
residual variance 7/32 above true variance 3/16, and its IID replication has
relative probability limit 5/3. Errors are bounded; the expectation integrals
are finite; the limiting sampling-variance denominator is eventually positive.
The refutations therefore use genuine probability models.

I recompiled both existing nonvacuity files against the refreshed definitions
with `/home/ubuntu/sap/tools/sap-lean`: [Check.lean](/home/ubuntu/sap/tasks/CHFID-P032-a/scratch/Check.lean)
and [IID.lean](/home/ubuntu/sap/tasks/CHFID-P032-a/scratch/IID.lean) both exited
successfully with linter warnings only. They establish nonempty random,
design and factor instances and actual infinite IID realizations of both
block laws. The IID proof again reports only `propext`, `Classical.choice`
and `Quot.sound`. The earlier 80 exact rational checks remain applicable to
the retained finite data and formulas. This review concerns statements and
labels; Solution/Comparator proof certification is separate.

[findings2.json](/home/ubuntu/sap/tasks/CHFID-P032-a/findings2.json) contains
one object per canonical target with the original schema, updated verdicts
and nonvacuity evidence. JSON parsing and exact target coverage were checked.
