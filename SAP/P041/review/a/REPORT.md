# P041 statement audit

Thirteen targets were reviewed: twelve theorem statements and one omission.

| Verdict | Count |
| --- | ---: |
| correct_whole | 5 |
| correct_restricted | 6 |
| restriction_inaccurate | 1 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 1 |
| omission_questionable | 0 |

Severity: 12 none, 1 minor, 0 major. No Lean proposition was found false or vacuous.

## P041-T12: restriction_inaccurate, minor

The opening of the docstring at `SAP/P041/Challenge/Part1.lean:69` says **“The printed claim is false.”** This is not an acceptable description of what `SAP.P041.T12` establishes relative to its canonical claim.

Canonical T12 explicitly asserts that the symmetric percentages and directions are correct (P1/P3), and that all three directional roundings are false (P2). `T12Statement` retains P1/P3 and proves only the negation of the conjunction of the directional rounding assertions. It is a weaker part of that canonical claim; it does not contradict it. The record correctly chooses `restricted`, and the detailed restriction correctly lists the omitted exact directional values and omitted individual negations. The error is the docstring's unqualified falsity label, which the audit instructions expressly prohibit for a refuted reading.

Replace the opening with: “Under the reference-risk reading of ‘x% more likely ... than’, the conjunction of the three printed directional rounding assertions is false. The symmetric percentage differences round to the printed values and the three directions are correct.” Retain the explicit restriction and `restricted` decision. A complete replacement docstring is supplied in `findings.json`.

The mathematical proposition itself is true: the directional values are 575/13, 100/3 and 375/4, and each fails its corresponding printed rounding. The symmetric values round to 36, 29 and 64 as asserted. This is a documentation defect, so severity is minor.

## Scope and record assessment

The five whole statements are T1, T3, T4, T5 and T6. The accepted restricted statements are T2, T7, T8, T9, T10 and T11. Their disclosed restrictions match the omitted content or added hypotheses. In particular, the canonical central/finer numerical bounds were counted as clauses even where audit-history notes called them optional or “for the reader.” T7 does not certify the omitted reference-distribution or significance conclusions. T9's k<n condition gates its entire general complementation block; the P/C/F formulas are conditional on sufficient statistics. T10 excludes zero variance. T11 does not claim the central living-subgroup p value rounds to .70.

T13's omission is acceptable in context: it is marked `no_lean`, has no separately credited declaration, and the explicit mathematical reading of its empirical assurance is already covered by the T5 countermodel and T6 sufficient condition. This does not mean that its validator-specified implication lacks a mathematical definition. No assertion about bias of the actual study is certified by that coverage.

No step-2 reading was changed after consulting the record. The record's whole/restricted choices agree with `claim-stage.json`; the remaining T12 defect is the Challenge docstring.

## Checks and audit order

`reading.md` was saved before opening `claims.json`. `claim-stage.json` was saved and parsed before opening `record.json`. Definitions were expanded through the relevant Mathlib finite-set, real-function, Gaussian-CDF and matrix-inverse definitions. No Solution or outside formalization was read.

`/home/ubuntu/sap/tools/sap-lean scratch/AuditNonvacuity.lean` completed with exit code 0. It imports only the supplied Defs, uses no Challenge theorem and contains no `sorry`. It checks the rounding-domain witnesses, positive cardinality of every balanced sample space, an actual intercept/full-rank/n>k design, nonsingularity of all three stipulated Gram matrices, and witnesses for the strict domain and positive-variance hypotheses. No `lake` command was run.

`python3 scratch/audit_arithmetic.py` passed. Exact rational checks cover the supplied risk arithmetic, countermodel contrasts, probability support, reciprocal bounds, the four-cell OLS/HC1 calculation and explicit binary datasets realizing all three regression designs. Exact finite enumeration checks the small balanced scrutiny examples and the independent-assignment boundary; binomial arithmetic checks the size-50 K distribution. The general balanced-expectation identity also follows directly from each rank's citation probability 1/2.

Gaussian-tail and logarithm checks in `scratch/arithmetic-checks.json` are numerical diagnostics, not replacement formal proofs. Their corner extrema apply because each rectangle stays on one side of 1/e, where -h log h is monotone, and every s is positive. The CDF is Mathlib's actual standard Gaussian probability CDF. No zero-denominator, singular-inverse, empty-index, nonintegrability or limsup convention was found doing the mathematical work.

Both requested JSON outputs were parsed with Python and checked against all target/theorem identifiers.
