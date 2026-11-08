# Declaration review

All five declarations are **faithful**, with severity **none**. Each was
reviewed independently with every declaration listed in its elaborated
statement closure, including the generated numeral and finite-index proofs.

| Declaration | Verdict | Main comparison |
| --- | --- | --- |
| `SAP.P014.T1` | faithful | The exact six-row witness, printed and intended local conditions, unweighted and conditional means, zero estimator, and 1/18 bias are all present. |
| `SAP.P014.T9` | faithful | The comparison witness establishes the printed target -1/9, conditional target -1/12, control-minus-treatment average 1/12, both sign inequalities, and 1/36 bias. |
| `SAP.P014.T5` | faithful | The full-vector clauses hold while the local arrangements are nonuniform; the unequal propensities and no-interference discrepancy 1/6 versus 1/3 are stated. |
| `SAP.P014.T10` | faithful | All conditional-average identities, the reversed direct-effect sign, the estimator identity under the canonical count and propensity hypotheses, and the unweighted failure example are included. |
| `SAP.P014.T6` | faithful | All corrected local-law consequences, both directions of the full-score reconstruction result, and the independent outside example are included. |

The definitions count distinct supported treatment vectors once in the
printed average and use probability weights in the conditional average.
They preserve the threshold at zero, closed window endpoints, fixed outcome
schedules on every binary assignment, and the canonical distinct-subject
no-ties convention. No definition encodes the conclusion or substitutes a
placeholder notion.

All displayed arm means and estimators have positive denominators wherever
the statements use them. T6 uses a probability measure, so `ENNReal.toReal`
never acts on infinite mass; its natural subtraction `(n-1)` is guarded by
`n≥2`. The usual measure-theoretic conditions are assumed as authorized in
the task. No substantive additional restriction or non-measurable witness
is involved. A finite law on binary assignment vectors in T10 represents
every possible law of the canonical finite-population random vector.

Independent scratch checks import the definitions and Mathlib, without
using the Challenge proofs:

* `scratch/FiniteAudit.lean` verifies the finite-law masses, positive arms,
  the three numerical discrepancies, the no-interference property, and a
  two-subject instance satisfying every T10 estimator hypothesis.
* `scratch/LocalAudit.lean` verifies every printed-local hypothesis for each
  of the three finite witnesses, their six full-score support points, the
  local arrangement probabilities, and the outside example's normalization
  and marginal probabilities.
* `scratch/MeasureAudit.lean` constructs an actual two-state probability
  measure satisfying every T6 general hypothesis, its discreteness and
  full-atom mass premises, and its outside-function premise.

The construction of T6's twelve-state example is the product of six masses
1/6 with outside masses 1/3 and 2/3. Distinct local rows and outside signs
give twelve full vectors, with masses 1/18 and 1/9; the product weights
establish the claimed independence.

`reading.md` was saved before opening the canonical claims.
`claim-stage.json` was saved before opening the architect's record. No
claim-stage conclusion changed afterward. The record's five `whole`
decisions and null restrictions are correct, and the reviewed docstrings
accurately describe their declarations. In particular, the forward
implication of T6(d) is present in `Defs/WholeW1.lean:133`, not omitted.
The counterexample declarations prove the canonical witness assertions;
they are correctly labelled `whole`, rather than `refuted` relative to
those assertions.

Validation: all three audit files above compiled successfully with
`/home/ubuntu/sap/tools/sap-lean` (exit 0). Python parsed both JSON outputs
and checked the five unique targets, required fields, copied fingerprints,
and verdict/severity/issue-list consistency.
