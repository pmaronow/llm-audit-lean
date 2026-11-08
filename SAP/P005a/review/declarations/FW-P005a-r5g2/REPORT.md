# Palomar P005a declaration review

All five declarations are **faithful**, with severity **none**. Each states the
whole canonical claim; the record's five `whole` decisions are correct.

| Declaration | Result of independent comparison |
| --- | --- |
| `SAP.P005a.T6` | Both third moments, both signed components, and the corrected difference have the exact hypotheses and signs. |
| `SAP.P005a.T7` | The complete spike counterexample includes every canonical clause and satisfies every condition of the printed expansion it disproves. |
| `SAP.P005a.T9` | The actual repaired expansion, all logarithmic comparisons, and the intermittent dimension-one equivalence are present. |
| `SAP.P005a.T10` | The entire specified finite counterexample is present, including positive arm variances, exact expectations, covariance and scaling identities. |
| `SAP.P005a.T11` | Both arm cancellations, expectation formulas, corrected weights, coefficient identity and uniqueness, printed-weight bias, and both asymptotic orders are present. |

The docstrings accurately describe the final statements. T7 and T10 prove their
canonical counterexample claims; neither is mislabeled as refuting that
canonical counterexample. Their references to false *printed* claims are
justified by witnesses satisfying all printed conditions. Unused-source notes
in the record do not remove conjuncts from the final statements.

All dependency-closure entries were read, including compiler-generated
declarations. No substantive conclusion relies on division by zero, a singular
inverse default, an empty supremum, or a square root/logarithm outside its
intended domain. Finite randomization makes the usual measure-theoretic
conditions automatic.

`reading.md` was saved before opening the claims, and `claim-stage.json` before
opening the record. No claim-stage classification changed. `checks.md` gives
the clause comparisons, condition-by-condition witness audits, and explicit
joint nonvacuity constructions. The variable-size normalized-grid construction
for T9/T11 is justified analytically; it is not represented as a fully compiled
infinite-sequence instance.

Validation uses Lean scratch instances in `scratch/Check.lean` and
`scratch/FiniteRegularity.lean`, and independent exact rational enumeration in
`scratch/exact_checks.py`. The enumeration reproduces both spike minima and
T10's expectations `4913/1200` and `20/3`, checks all relevant finite arm
variances, and checks T6 and T11 through singleton allocations. Detailed output
is saved in `scratch/exact-results.json`.
