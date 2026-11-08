All four reviewed declarations are faithful. Their definitions render the finite randomization and sampling notions correctly; no vacuity, hidden substantive restriction, or unintended junk value was found.

| Declaration | Record decision | Verdict | Severity |
|---|---|---|---|
| `SAP.P013a.T11` | whole | faithful | none |
| `SAP.P013a.T12` | refuted | faithful | none |
| `SAP.P013a.T13` | whole | faithful | none |
| `SAP.P013a.T14` | whole | faithful | none |

T11 contains every counting, ratio and numerical implication in the corrected claim. Its assumptions protect the natural subtractions and probability denominators. T13 contains both expectation identities, both variance identities and the covariance expansion, with the printed positivity and distinct-exposure conditions.

T12 genuinely refutes the printed assertion. Two units with exposure probabilities `(1/3,2/3)` and potential outcomes `(2,-1)` have total 1. One independent replicate gives expected estimated total `2/9`, hence relative bias `7/9`, exceeding the printed bound `4/9`. Target `b=2/3` satisfies the logarithmic rule (threshold zero), yet is also exceeded. The witness satisfies Conditions 1 and 2, all positivity and independence requirements, and uses defined quantities throughout. The printed reading and complete condition checklist are in [claim-stage.md](claim-stage.md). The step-2 relation `different` records the theorem's negation of the positive canonical assertion; it does not identify a defective refutation.

T14 covers the exposure claims and every general sampling result included in `definitions_needed`: the bias identity, conjugate-power correction and quadratic corollary. Its missing-pair convention agrees with the paper's zero-over-zero convention. The general branch permits certainty units, zero-weight atoms and outcomes of either sign. The docstrings accurately describe all four declarations, and the record required no change to the claim-stage conclusions.

[reading.md](reading.md) was saved before opening the claims; [claim-stage.json](claim-stage.json) was saved before opening the record. Every listed closure declaration was inspected, including the generated auxiliaries printed by [scratch/BlindChecks.lean](scratch/BlindChecks.lean). [scratch/AuditChecks.lean](scratch/AuditChecks.lean) compiled successfully with `/home/ubuntu/sap/tools/sap-lean`, with no errors or warnings. Its examples construct satisfying hypotheses for every target, directly refute both T12 universals without invoking T12, and check T14 with missing joints, positive joints, nonquadratic conjugate exponents, certainty inclusion and a zero-weight atom. The findings and stage JSON files were parsed and checked for the required four targets and fingerprints.
