# P039 declaration review

All five declarations are **faithful**, with severity **none**. The architect's `whole` decisions and the Challenge docstrings accurately describe their statements. No step-2 conclusion changed after reading the record.

The blind reading of every declaration and every listed dependency was saved in `reading.md` before opening `claims.json`. The claim comparisons were saved in `claim-stage.json` before opening `record.json`. Generated dependency declarations were also printed and read; they contain numeral/index proofs and an exhaustive finite matcher, without additional statistical assumptions.

| Declaration | Assessment |
|---|---|
| `SAP.P039.T1` | All four canonical clauses are present: quarter-one independence, the two missing terms, and both exact witnesses. The reversed sum indices implement precisely Q2–16 and Q1–16. Both witness decays are strictly inside (0,1), with positive denominators. |
| `SAP.P039.T2` | The corrected definition, positive normalization, independence, growth difference, equality characterization, and both endpoint cases are complete. The election-quarter factor remains 1/3 at decay one. |
| `SAP.P039.T3` | Both genuine OLS counterexamples, conventional errors and degrees of freedom, disagreement at 5%, all tail formulas and intermediate bounds, and the Gaussian scaled-t3 law and finite moments are included. The analytic tails are identified with actual Student probability tails, rather than merely named as probabilities. |
| `SAP.P039.T4` | All formal clauses (a)–(f) are included, with the precise structural and positive-SSE guards. The full Gaussian Student law is a conclusion. Only the residual-line law requires orthogonality. Degrees of freedom one and two remain included. Clause (g) expressly excludes itself from the canonical formal content. |
| `SAP.P039.T5` | Both voter-centered magnitude counterexamples, all five exact positive signed maxima, and the negative signed-maximum worked product are stated. Every one of the 64 deposited values and all five election domains match the canonical definitions. |

T1, T3, and T5 prove the canonical counterexample assertions; they are appropriately labelled `whole`, rather than `refuted`. The printed readings, their conditions, and witness checks are recorded separately in `scratch/claim_checks.md`. T3 concerns the inferential procedure, without asserting that the paper's literal .26 calculation is false. T5 distinguishes the signed-order reading from the implemented magnitude rule.

No conclusion relies on a junk value. Real normalization denominators and relevant Gram determinants are nonzero. Deterministic t identities require positive full-model SSE; Gaussian zero-SSE inputs have probability zero. The squared moments in T3 have explicit integrability conclusions. Covariance uses finite first and second moments. All probability maps are measurable; tail measures are finite, so conversion from extended nonnegative reals is ordinary. Out-of-domain score placeholders are excluded from every comparison.

Validation completed successfully with `/home/ubuntu/sap/tools/sap-lean`:

- `scratch/ClosurePrint.lean`: all 135 generated dependency declarations inspected.
- `scratch/BlindScope.lean`: Gaussian conjunction/implication scope checked by definitional equality.
- `scratch/Check.lean`: income witnesses, admissible endpoint data, all OLS rank conditions, baseline residual, complete Gaussian input hypotheses, and an independent proof of the entire finite T5 statement.
- `scratch/CovarianceCheck.lean`: integrable coordinates and products, zero means, and identity covariance for independent standard Gaussian coordinates.
- `scratch/EdgeCheck.lean`: complete structural/Gaussian inputs and orthogonality at residual degrees of freedom one and two.

`scratch/exact_audit.py` independently checks the 64-value table, domains, maxima, gaps, products, quarter weights, and all four OLS fits using rational arithmetic. Its decimal p-value evaluations are numerical corroboration only; the certified declaration supplies the exact probability bounds. `findings.json` and `claim-stage.json` were parsed and checked for exactly one entry per reviewed declaration and matching identifiers/fingerprints.
