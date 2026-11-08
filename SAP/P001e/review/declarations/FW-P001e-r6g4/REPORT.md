# Palomar declaration review

All four declarations are faithful to their canonical claims. The record's decisions are correct: T92 refutes the specified printed-table equality; T93, T94 and T95 cover their whole claims. No changes to the statements, definitions or docstrings are required.

| Declaration | Record decision | Verdict | Severity |
|---|---|---|---|
| SAP.P001e.T92 | refuted | faithful | none |
| SAP.P001e.T93 | whole | faithful | none |
| SAP.P001e.T94 | whole | faithful | none |
| SAP.P001e.T95 | whole | faithful | none |

The blind expansion is in [reading.md](reading.md), saved before reading the claims. It covers every closure declaration, including all 66 distinct generated auxiliaries printed in [scratch/ClosurePrint.out](scratch/ClosurePrint.out). A subsequent scratch check clarified that `Fin` numeral literals wrap modulo their size; all audited literal indices are in range, so this changed no mathematical reading or finding. [claim-stage.json](claim-stage.json) was saved before opening the record. No claim-stage conclusion changed after reading it.

For **T92**, the printed reading is: fit OLS to the six original observations with unit 3's first covariate equal to 10, execute both printed imputation tables with that covariate equal to 9, and assert that the two completed-column differences of means agree. The witness meets each condition:

- The original outcome, treatment and covariate vectors are exactly those in the canonical statement.
- The original Gram determinant is 7311, and its OLS coefficients are `(13563,6178,-759,-1778)/2437`.
- Both predictions use the printed 9; the missing-only routine retains observed outcomes, while the all-imputed routine replaces them.
- Both estimates average over all six units. Their values are `12103/4874` and `6178/2437`, with nonzero difference `-253/4874`.

Consequently this is a refutation of the canonical statement's own explicitly specified printed equality. It does not refute the consistent-data identity. An i.i.d. strongly ignorable population can realize the table with positive probability, so the witness does not depend on violating the setting's sampling or causal conditions.

For **T93**, the corrected tables, coefficients, normal equations, filtered residual correction and both imputation formulas are present. The population clause includes exactly the canonical uniform overlap, conditional independence and exact linear observed CEF. It gives the conditional effect almost everywhere and the marginal ATE; the fitted contrast holds everywhere. It adds no rank, uniqueness, separate covariate-moment, asymptotic or computational-cost assertion. A nonzero-effect finite sample and randomized population satisfy every input hypothesis.

For **T94**, the density predicate specifies the actual conditional law, not an assumed identity for its mean. Both potential means, their population and density-integral displays, equal-observable-law identification, the observed-covariate estimator, the free-covariate collapse and the ATE formula are included. Uniform overlap is already in the canonical definition of strong ignorability. A fully constructed treatment-coin times uniform-outcome model satisfies every population and density premise; an attained ML fit satisfies every estimator premise.

For **T95**, all eight opposite-arm distances, all six unique donors, the second-nearest donor and its 0.02 gap, both completed columns and the 7/6 estimate match. The donor map permits replacement and is certified against nonempty opposite-arm candidate sets. The fixed score table can be realized with actual treatment propensities under strong ignorability.

[Scratch checks](scratch/Check.lean) compile with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean`; [the output](scratch/Check.out) records the named witness proofs' axioms. The checks use no target theorem or `sorryAx`. Independent rational elimination also verifies the OLS fit and determinant. No undefined integral, zero denominator, singular-inverse fallback, negative-density truncation or empty-index convention changes an audited assertion. Only review artifacts and scratch files were written; no unit source was edited and `lake` was never run.
