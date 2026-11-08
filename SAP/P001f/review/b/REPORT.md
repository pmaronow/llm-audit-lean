# Statement-referee report

19 targets: 18 theorem stubs and one omission.

| Verdict | Count |
| --- | ---: |
| correct_whole | 9 |
| correct_restricted | 8 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity: 18 none, 1 minor, 0 major.

## P001-T113 — restriction_inaccurate, minor

The Lean theorem appears correct. The discrepancy is its description relative
to the supplied canonical claim. The record says it **adds** integrability of
`m ∘ X` ([record.json:229](record.json#L229)); the Challenge docstring presents
this as a restriction excluding correct-propensity cases with integrable scores
but nonintegrable regressions ([Challenge/Part1.lean:130–133](SAP/P001f/Challenge/Part1.lean#L130)).
However, the canonical note explicitly says that regression integrability is
**implicit in case (ii)** ([claims.json:274](claims.json#L274)). In the correct-regression
branch, population integrability already follows from restricted-law
integrability and uniform positive response propensity. Consequently this is
not an additional restriction of the supplied target. Integrable-score-only
examples belong to a larger class already excluded by the canonical note.

Fix: retain the Lean statement, classify this target as whole, and replace the
restriction paragraph with: “Integrability of the nuisance regression m(X),
implicit in the canonical claim, is explicit in both branches; correctness and
overlap are interpreted up to null sets.” The complete replacement docstring
is in `findings.json`.

## Other scope decisions

T97, T98, T101, T103, T104, T107 and T114 disclose the conclusions they omit
or the stronger pointwise premises they use. Those descriptions match the
actual types. T102's refutation stays within the joint-density class; an
explicit disconnected-support example with distinct actual derivatives is
given in `findings.json`. The mixture and overlap negations likewise have
concrete witnesses with legitimate denominators and convergent sums.

T111's conservative restriction label is accepted: its text accurately says
that population integrability is retained as a premise rather than derived.
That premise is mathematically redundant under uniform positive response:
restricted-law integrability of m(X) bounds its population absolute integral
by the respondent absolute integral divided by the positive lower bound.
The text does not assert that a new class of otherwise admissible models is
excluded.

T105's omission is reasonable on the supplied evidence. The book and canonical
note leave informational completeness undefined, and no corresponding
predicate is supplied. A refutation on a larger domain without binary
treatment or the informational premise would not suffice. The credited row
and credit-status files were not supplied for independent inspection; this
acceptance does not authenticate the record's description of their contents.

## Procedure and checks

`reading.md` was saved before opening `claims.json`; `claim-stage.json` was
saved before opening `record.json`. No step-2 verdict was changed after the
record was opened. Its whole readings of T111 and T113 are retained: T111's
explicit-premise disclosure is accepted conservatively, while T113's claim
of an added restriction conflicts with the canonical note.

The independent scratch file imports only `SAP.P001f.Defs`. Running
`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` succeeded with exit code 0.
It checks a nonempty positive cell-mass instance, finite-law normalization,
the six-unit estimator arithmetic, an actual propensity conditional-mean
premise with positive probability of both response arms, pointwise overlap,
and the eventwise conditional-independence definition for a constant variable.
Exact Python rational arithmetic additionally checked T96's estimator values
and gap, and T114's sample endpoints. Nonvacuity instances for all targets are
recorded individually in `findings.json`; analytic witnesses not compiled are
identified as mathematical checks. No Solution or Comparator was read, and no
Challenge `sorry` was used as evidence.
