All five declarations are **faithful**, with severity **none**. The record's five `whole` decisions are justified. No correction to a statement, definition or docstring is needed.

| Declaration | Review result |
| --- | --- |
| `SAP.P026a.T6` | The exact printed population, design and actual OLS estimators support the canonical numerical refutation. All required moments, approximations and rounding exclusions are included. |
| `SAP.P026a.T7` | All clauses of the corrected statement are covered, including the complete unchanged columns without X. The clustered HC1 convention is explicit and reproduces the IPW/FE entries. |
| `SAP.P026a.T8` | The covariance expansion, lower bound, exact gap, corrected statistic's unbiasedness, and equality characterization all match. Directed support is required in the appropriate clauses. |
| `SAP.P026a.T9` | The genuine finite counterexample contradicts the literal display's canonical unbiasedness assertion. It satisfies positive marginals, distinct indicators, all joint-support conditions and the sharp null. |
| `SAP.P026a.T10` | Every intermediate regrouping equality, both arm totals and the ATE contrast are present. The result also correctly permits nonmaximal fixed partitions. |

`reading.md` was saved before opening the claims or record. Every closure entry was read, including all 22 generated auxiliary declarations. `claim-stage.json` preserves the pre-record comparison; its `broader` classification for T10 records a valid generalization that entails the whole claim. Reading the record required no change to those conclusions. The printed population, estimator specifications, table and appendix formulas were also checked against the [paper](https://doi.org/10.1515/jci-2012-0009).

Both `scratch/Check.lean` and `scratch/PaperCheck.lean` compiled successfully using `sap-lean`, importing only the definitions and using no Challenge theorem. They establish concrete nonvacuity instances, nontrivial partition grouping, valid counterexample values, probability/support conditions and projection guards. The T8 instance has a strictly positive squared-difference gap, so equality is not forced by its hypotheses.

`scratch/enumerate.py` independently enumerates all ninety assignments using exact rational arithmetic, solves the full OLS/WLS systems, computes the sandwich estimates and moments, and verifies all fifty entries of the five complete columns using exact interval inequalities. It also checks the six-allocation Appendix E witness. Results are saved in `scratch/enumeration.json`. Printed readings and witness-condition checks for both refutations, and clause-by-clause comparisons for all five targets, are in `scratch/claim-audit.md`.

All relevant divisions and matrix inverses have nonzero denominators; square-root arguments are nonnegative finite moments. Zero-joint omission conventions are inactive wherever a literal printed statistic is asserted. No placeholder, encoded conclusion, vacuous premise or material junk-value dependence was found.
