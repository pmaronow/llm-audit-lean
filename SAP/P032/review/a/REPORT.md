# P032 statement audit

All 12 canonical targets have a Challenge theorem. The audit found 8 correct
whole statements, 3 correct disclosed restrictions, and 1 issue with the
certification decision and docstring. No mathematical statement was found
false or vacuous, and there are no omitted targets.

| Verdict | Count |
| --- | ---: |
| correct_whole | 8 |
| correct_restricted | 3 |
| restriction_inaccurate | 0 |
| not_faithful | 1 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

Severity counts: none 11, minor 0, major 1.

**P032-T5 — not_faithful, major; SAP.P032.T5.** The mathematical payload is
correct and covers the canonical claim. The problem is its certification
scope. The canonical statement already concludes that all four universal
lower-bound readings are false. The Lean theorem asserts precisely those
negations, so it establishes the canonical assertion. The record's
`decision: refuted` reverses that relationship and violates the supplied rule
for labeling a refutation of a reading.

The docstring at `SAP/P032/Challenge/Part1.lean:30` additionally begins
“The printed claim is false.” The theorem addresses four universal
mathematical readings. This does not establish falsity of every quoted
expectation, possibility or empirical description. The printed passages
include an expectation and a possibility alongside the lower-bound language;
these are visible on pp. 191 and 196 of the
[published paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/521F1378ED4F8411B2A4AB0E8FA172A0/S1047198723000268a.pdf/dyadic_clustering_in_international_relations.pdf).

Set T5's decision to `whole`, retain its theorem type, and replace its
docstring with:

```lean
/-- P032-T5; pp. 187, 191 and 196, formal universal lower-bound readings.
Refutes the weak and strict population, residual-expectation, and relative
probability-limit universal lower-bound readings described in the canonical
claim. These are the validators' mathematical interpretations of the printed
passages. -/
```

The three declared restrictions are accurate and complete. T8 omits the two
completed-data equalities to direct ordered-pair sums. T9 adds the three
nonzero-denominator guards for the asylike coefficient formula. T11 retains
the OLS matrix decomposition and explicitly omits the separate pointwise
identity and the other listed assertions. These omissions are disclosed in
both the record and the theorem docstrings.

The blind expansion was saved as `reading.md` before either JSON source was
opened. `claim-stage.json` was saved before `record.json` was opened. No
step-2 mathematical comparison was changed after reading the record: T5
remains mathematically whole; its final adverse verdict concerns the later
checked label and its docstring.

Verification used Mathlib's actual definitions of matrix inverse,
positive semidefiniteness, spectral decomposition, Bochner integrals,
variance, covariance, square integrability, independence and convergence
in measure. `scratch/arithmetic.py` passed 80 exact rational checks; its
individual results are saved in `scratch/arithmetic-results.json`.
`scratch/Check.lean` compiled nonempty random/design/factor instances using
only the definitions. `scratch/IID.lean` compiled genuine infinite IID
realizations for both block laws; its generic proof depends only on
`propext`, `Classical.choice`, and `Quot.sound`. These scratch files contain
no `sorry` and do not import Challenge theorems. This is a statement audit,
not a replacement for the Solution/Comparator proof certification.
