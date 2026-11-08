# Palomar statement audit — P037b

Audited 15 targets and 13 theorem statements. The retained mathematical
statements appear true and nonvacuous. One restriction description needs a
minor wording correction.

| Verdict | Count |
| --- | ---: |
| correct_whole | 2 |
| correct_restricted | 10 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 2 |
| omission_questionable | 0 |
| **Total** | **15** |

Severity: 14 none, 1 minor, 0 major.

## P037-T29 — restriction_inaccurate, minor

The restriction in
[Challenge/Part1.lean:50](/home/ubuntu/sap/tasks/CHFID-P037b-b/SAP/P037b/Challenge/Part1.lean:50)
and [record.json:106](/home/ubuntu/sap/tasks/CHFID-P037b-b/record.json:106)
calls the omitted branch assertions “r=0/r≥1 error equalities.” Canonical
T29(iii) gives an equality for r=0 and a lower bound for r≥1:

\[
|r/10000-p|\ge 1/10000-p>p,\qquad p=1/127008.
\]

Replace “the separate r=0/r≥1 error equalities” with “the separate r=0
exact-error equality and r≥1 error lower-bound assertions.” The complete
corrected restriction is in `findings.json`. The theorem's retained
probabilities, error floor, moments and probability bounds are sound; the
other declared omissions are accurate.

## Scope and omissions

T25 and T30 cover their canonical mathematical claims. The restrictions for
T18–T24, T26, T31 and T32 accurately disclose their retained conclusions and
omissions. In particular, the conditional scalar or algebraic results are
not credited with establishing the omitted actual-design, full-analysis-set,
regression-identification or released-code conclusions.

T16 and T17 are reasonably omitted: their canonical assertions report
empirical table/procedure information and an empirical treatment-effect
estimate. Mathematical facts about an interpreted weight law or arithmetic
on printed numbers would certify separate, narrower assertions. Audit notes
were not treated as new clauses requiring a Dirichlet-law refutation or a
new empirical-effect theorem.

The nomination/union counterexample is assessed relative to its canonical
ambiguity witness. Its theorem and docstring compare the two concrete matrix
readings and do not call the publication's unspecified adjacency assertion
false.

## Audit sequence and verification

[reading.md](/home/ubuntu/sap/tasks/CHFID-P037b-b/reading.md) was saved before
opening the claims or record. It expands every theorem's objects,
hypotheses, quantifiers and conclusions, including the underlying Mathlib
semantics. [claim-stage.json](/home/ubuntu/sap/tasks/CHFID-P037b-b/claim-stage.json)
was saved before opening the record: 2 whole and 11 narrower. No step-2
scope verdict was changed after reading the record.

The checks addressed singular matrix inversion, Bochner-integral
well-definedness, positive assignment support, actual subset laws, natural
subtraction, empty dimensions and all relevant denominators. T19's zero-block
totalized ratio is immaterial to its limit; positive block counts give a
strictly positive denominator. T22's four mutually exclusive positive
exposures imply upper bounds below one even with a fifth direct category.
T30's subset sizes and sample bounds prevent truncated subtraction or zero
binomial denominators from changing its sampling formula.

The independent script
[referee_exact.py](/home/ubuntu/sap/tasks/CHFID-P037b-b/scratch/referee_exact.py)
passed 39 checks of the finite certificates, using rational arithmetic,
enumeration and exact integer comparisons for the rare zero-hit bounds.
Results are saved in
[referee-exact-results.json](/home/ubuntu/sap/tasks/CHFID-P037b-b/scratch/referee-exact-results.json).

[RefereeCheck.lean](/home/ubuntu/sap/tasks/CHFID-P037b-b/scratch/RefereeCheck.lean)
compiled successfully with
`/home/ubuntu/sap/tools/sap-lean scratch/RefereeCheck.lean`. It imports only
the Defs and verifies a positive finite probability design, a nonempty
four-positive-exposure population, a full-rank matrix, genuine blocked and
rare assignments, and integrable mean-zero/unit-second-moment multipliers
on a normalized two-atom measure. Further substantive instances are given
per target in `findings.json`. These scratch checks validate examples and
hypotheses; the audit's judgments concern the Challenge statements.

Both required JSON files were parsed and checked with Python, including
complete target coverage and unique theorem mappings.
