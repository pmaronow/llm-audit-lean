All five declarations are **faithful**, with severity **none**. The record's
`whole` decisions are justified; no restriction or docstring correction is
needed. The comparison against the record required no change to the saved
claim-stage conclusions.

| Declaration | Result | Main fidelity check |
| --- | --- | --- |
| `SAP.P009a.T1` | faithful / none | All canonical counterexample clauses (a)–(h), including the rate conditions, half coverage, and vanishing normalized variance, are stated. |
| `SAP.P009a.T2` | faithful / none | Every part of the corrected coverage result is present, including unbiasedness, the finite event inclusion, Definition 10, and the positive normalized-variance floor. |
| `SAP.P009a.T3` | faithful / none | All three specified finite witnesses meet their respective design and moment conditions and strictly violate the signed weighting bounds. |
| `SAP.P009a.T4` | faithful / none | The general identity, observed-moment-only bound, and every corrected A9/A22/A23/A25 comparison are present, including diagonal mixing and infinite-order endpoints. |
| `SAP.P009a.T5` | faithful / none | The regular cluster family has the exact claimed graphs, density, parity gaps, positive limsup, and finite threshold set. |

The counterexamples target the canonical assertions themselves: the
variance-to-plug-in-coverage implication, the finite signed weighting steps,
and the limsup selection step. Their conclusions do not assert that the
associated final propositions or lemma rates are false. In T5, fair Bernoulli
assignment is permitted by the canonical claim's illustrative design clause.

Every closure entry was inspected, including all 33 generated helper
declarations. The substantive definitions match the paper's notions. Positive
sizes and treatment probabilities protect the divisions; integrability
protects the general variance calculations; probability sequences are bounded;
and the mixing convention at zero is explicit. The unused size-zero cluster
density does not enter any assertion.

Both nonvacuity files compiled successfully with `sap-lean`, without using the
target stubs as proofs. They check all-order regularity and genuine finite
counterexample calculations, a probability-space witness with every generic
T2 hypothesis and a positive variance floor, and nonconstant L2 variables plus
finite/infinite-order experiment witnesses for T4. The identity-outcome family
also establishes joint satisfiability of T2's HT-specific hypotheses by direct
calculation, recorded in the detailed audit.

The staged evidence is in [reading.md](/home/ubuntu/sap/tasks/FW-P009a-r4g1/reading.md),
[claim-stage.json](/home/ubuntu/sap/tasks/FW-P009a-r4g1/claim-stage.json), and
[claim-audit.md](/home/ubuntu/sap/tasks/FW-P009a-r4g1/claim-audit.md).
Compiled checks are in
[Nonvacuity.lean](/home/ubuntu/sap/tasks/FW-P009a-r4g1/scratch/Nonvacuity.lean) and
[MeasureNonvacuity.lean](/home/ubuntu/sap/tasks/FW-P009a-r4g1/scratch/MeasureNonvacuity.lean).
The required verdicts and fingerprints are in
[findings.json](/home/ubuntu/sap/tasks/FW-P009a-r4g1/findings.json).
