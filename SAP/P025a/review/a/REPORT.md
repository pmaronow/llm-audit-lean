# P025a statement audit

All 11 targets were reviewed in the required order. `reading.md` was saved before
`claims.json` was opened; `claim-stage.json` was saved before `record.json` was opened.
No claim-stage verdict was changed after reading the record.

| Verdict | Count |
| --- | ---: |
| `correct_whole` | 4 |
| `correct_restricted` | 7 |
| `restriction_inaccurate` | 0 |
| `not_faithful` | 0 |
| `vacuous` | 0 |
| `false` | 0 |
| `omission_ok` | 0 |
| `omission_questionable` | 0 |

Severity counts: none 11; minor 0; major 0.

There are no adverse findings and no omitted targets. The four `correct_whole`
verdicts comprise the affirmative T6 and T9 results and the faithful T7 and T8
refutations. Both refutations apply to admissible finite sampling instances.

The architect's decisions agree with the independent scope comparison. All seven
restriction declarations match their theorem docstrings, allowing for line wrapping,
and accurately disclose the following omissions.

| Target | Verdict | Scope assessment |
| --- | --- | --- |
| P025-T1 | `correct_restricted` | Discloses the omitted numerical residual decompositions, general mean residual and coordinate-change identities, and explicit independence assertion. |
| P025-T2 | `correct_restricted` | Discloses the omitted design/replication, singleton-class calibration, upper first cut, residual equalities, and general weighted diagnosis. |
| P025-T3 | `correct_restricted` | Discloses omission of continuity on the optimizer segment; segment attainment and all other canonical certificates are present. |
| P025-T4 | `correct_restricted` | Discloses omission of last-cut inequalities, weighted increments, and explicit feasibility/value/optimality assertions for prescribed vectors; attained extrema are present. |
| P025-T5 | `correct_restricted` | Discloses omission of the joint independent design, its population linkage, and the statements about every joint draw; the seven separate quota laws are present. |
| P025-T6 | `correct_whole` | Covers the overlap criterion, numerical thresholds, reweighted-odds/product identities, counterexamples to individual-ratio necessity, and common-cap consequence. |
| P025-T7 | `correct_whole` | Refutes the printed lower rule and interval assertion with the original inequality direction, and retains the valid upper half. |
| P025-T8 | `correct_whole` | Refutes the printed class optimizer/formula conjunction and retains the valid upper half. The canonical target separately excludes the asymptotic sharpness sentence. |
| P025-T9 | `correct_whole` | Covers every-cut partition, the corrected endpoint conditional, both duplicated classes and their exact discrepancy, and undefined indices. |
| P025-T10 | `correct_restricted` | Discloses exactly the omitted residual equality and uniqueness assertion; the finite design and numerical minimum counterexample remain. |
| P025-T11 | `correct_restricted` | Discloses the omitted original-scale identities, endpoint and first-cut identifications, global threshold maximum, and finite-population calibration. Normalized stationarity and pair comparisons remain. |

The definitions agree with the stated reading conventions: cuts count prefix entries,
the printed lower inequality is preserved in the refutations, and the printed
one-based tail index k−1 becomes zero-based k−2 only when 2≤k≤J. Invalid
indices are represented by `None`. Positive masses, nonempty index sets and
positive bounds exclude zero denominators. Attainable sets are nonempty and
bounded, so the real infimum/supremum fallback values do no work. The binary
and pair-objective denominators are positive under their hypotheses. No hidden
extra assumptions or conclusion-assuming hypotheses were found.

Validation: `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with
exit status 0 and an empty `scratch/check.log`. The scratch file imports only
`SAP.P025a.Defs` and contains no `sorry`. It checks concrete nonconstant and
boundary instances, the two-unit finite design and separation condition,
nonempty quota sets, counterexample feasibility and failed leastness, and
general denominator positivity and nonempty bounded attainable sets. Exact
Python rational/combinatorial calculations also checked the numerical threshold
brackets, counterexample values, seven quota marginals and four-state design.
The JSON files were parsed and their target coverage and counts checked with Python.
