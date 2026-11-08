All three reviewed declarations are **faithful**, with severity **none**. Their recorded `whole` decisions are correct, and their docstrings accurately describe their statements. No step-2 conclusion changed after reading the record.

The blind reading of each full closure, including generated declarations, was saved in `reading.md` before opening the claims. `claim-stage.json` was saved before opening the record.

- **T12:** The printed reading asserts that the displayed control expression containing the treated inverse is unbiased for the expected control nuisance product. Its conditions are fixed real finite-population arrays, uniform complete randomization, nonempty complementary arms, standardization, bounded second moments, allocation bounded away from zero and one, and invertibility under every assignment. The specified six-unit witness satisfies each condition. The statement includes every canonical numerical and structural clause. Its nuisance and corrected-estimator expectations are both 31085815448171/17062566567774, while the printed estimator has expectation 12010469/846720. This refutes the printed unbiasedness assertion under its own reading. The recorded `whole` label covers the canonical counterexample target.
- **T13:** The statement includes the complete corrected expectation chain, all three component identities, the expected covariance, and both coefficient equalities, under exactly the stated finite-size and control-invertibility hypotheses. Its definitions use the control inverse and the correct sign for the third component. Positive-dimensional four-unit and nonconstant-leverage six-unit instances satisfy every hypothesis.
- **T14:** The statement includes every corrected expansion, inverse cancellation, the residual identity for arbitrary vectors, centered arm-mean identities, and the actual bias decomposition. Its four-unit witness gives 1/3 for the printed treated-set control sum and 1 for the control residual mean. The final observing function is quantified before the potential outcomes and works without standardization. An explicit function using only the assignment, covariates and observed outcomes was independently constructed and checked.

All dependent statistical definitions are ordinary finite sums, real covariances and finite-dimensional matrix operations. Relevant denominators are positive and inverses are nonsingular under their stated conditions. The square root has positive input. Natural subtraction in `NCCC` agrees with ordinary subtraction because m<n. Finite assignment spaces ensure the usual measurability and expectation-existence conditions automatically.

Successful scratch checks, using `/home/ubuntu/sap/tools/sap-lean`:

- `scratch/Nonvacuity.lean`: standardization, every-assignment regularity, full hypothesis instances, T12 moment/allocation conditions, and T14's actual witness values.
- `scratch/WitnessArithmetic.lean`: exact rational-coordinate values of T12's fitted, printed and corrected expectations and their inequality.
- `scratch/Observability.lean`: explicit uniform observations-only function for T14.

Independent exact rational enumeration of all 15 T12 assignments is saved in `scratch/T12-exact-check.json`. `findings.json` and `claim-stage.json` parse successfully; target coverage and copied fingerprints were checked against `closure.json`.
