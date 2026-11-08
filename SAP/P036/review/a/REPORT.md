# P036 statement audit

Two targets audited. Both are `correct_whole`, with severity `none`.

| Verdict | Count |
| --- | ---: |
| correct_whole | 2 |
| correct_restricted | 0 |
| restriction_inaccurate | 0 |
| not_faithful | 0 |
| vacuous | 0 |
| false | 0 |
| omission_ok | 0 |
| omission_questionable | 0 |

There are no adverse findings and no omitted targets.

`reading.md` was saved before opening `claims.json`. It expands every clause of both theorem types and follows the SAP definitions to the relevant Mathlib definitions. `claim-stage.json` was then saved before opening `record.json`. Reading the record required no revision of either claim-stage verdict.

For **P036-T1**, the theorem covers the corrected symbol roles, both conditional-mean consequences, existence and uniqueness of the unadjusted OLS minimizer, its identification with the two arm means, and both exact and rounded table calculations. The measurability assumptions express the usual random-variable requirements. The model hypotheses imply integrability of the response. The generated sigma-algebras are genuine sub-sigma-algebras, so conditional expectation is not exploiting its default-zero convention. Positive arm probabilities and cardinalities make the relevant mean denominators nonzero. The OLS conclusion is substantive: it quantifies over all competing coefficient pairs, and is not merely an equality with a definition called OLS. Its standard justification is the RSS decomposition into within-arm sums of squares plus n0(b0-mean0)^2+n1(b0+b1-mean1)^2.

For **P036-T2**, the statement includes all parts (a)-(e) of the canonical correction. The entrywise definitions implement the HC2 sandwich, and the theorem certifies both inverse products and the regression-coefficient identity. The assignment average is the uniform distribution on all fixed-size treatment subsets, with fixed potential outcomes. The size hypotheses force a nonempty assignment space, N >= 4, nonzero sample-variance denominators, and leverages strictly below one. The expected sample variances give the expected HC2 value, and the exact randomization variance yields the gap S_tau^2/N. Its vanishing is equivalent to a single constant effect shared by every unit. The theorem asserts precisely the corrected variance conservativeness in expectation; it asserts no property of adjusted regressions, expected square-root standard errors, or assignment-wise domination of the true variance. It does not claim that the printed hedged sentence is false.

The architect records `whole` for both targets and declares no additional restrictions. Both decisions are correct relative to the canonical corrected claims. T2's scope to unadjusted specifications, complete randomization, fixed potential outcomes, and at least two units per arm already belongs to its canonical target and is accurately stated in the Challenge docstring. The unused rows are helper results or conclusions outside the targets; none supplies a missing canonical conclusion.

Nonvacuity was checked by compiling `scratch/Check.lean` with `/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` (exit 0, no errors or warnings). It imports only the supplied Defs, constructs positive-probability conditional models, realizes both finite arm-size regimes, proves the six-element small assignment support is nonempty, permits nonconstant treatment effects, and realizes both response-count tables on an actual 189-element type. It also checks both coefficient pairs and both variance fractions directly in Lean.

`python3 scratch/numerical_check.py` passed independent exact-rational checks of both matrix inverse products, the regression coefficients, leverages, the full HC2 sandwich, all randomization identities, the constant-effect equality criterion, and the table arithmetic. The randomization checks cover all 256 binary potential-outcome pairs with N=4 and two units per arm, plus six further populations including unequal arms, signed and rational outcomes, and constant effects. Both standard-error rounding claims were checked through exact squared rational endpoints. Results are saved in `scratch/check-results.json`. These finite checks support the statement review; they are not a proof of the universal theorems, and this audit does not certify the Solution or Comparator proofs.
