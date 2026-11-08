All five declarations are **faithful**, with severity **none**. Each was
reviewed independently with its entire statement dependency closure, including
the generated proof declarations. The audited Lean sources were left intact.

The blind mathematical readings and junk-value checks were saved in
[reading.md](/home/ubuntu/sap/tasks/FW-P026b-r3g1/reading.md) before opening the
claims. The comparison in
[claim-stage.json](/home/ubuntu/sap/tasks/FW-P026b-r3g1/claim-stage.json) was saved
before opening the record.

- **T13:** Both arm-total identities and the complete covariance-difference
  bias formula match the corrected claim for arbitrary assignment-dependent
  predictions. `UnitExperiment` supplies exactly the finite assignment law and
  positive marginals required by the standing assumptions.
- **T14:** The population, design, opposite-block logistic fits, maximizers,
  coefficient tolerances, exact unbiasedness statements, numerical intervals,
  ten corrected entries, and six failed printed entries all match. The apparent
  reversal of the Boolean block index implements the required opposite-block
  fitting. The data and fitting direction also agree with Table 1 and Section
  7.1 of the [paper](https://doi.org/10.1515/jci-2012-0009).
- **T15:** The exact three-unit OLS example matches every canonical quantity.
  Its generalized estimator equals the package branch's observed-outcome
  residual contrast. The docstring correctly identifies the help-text reading
  being refuted; the record correctly labels the canonical counterexample
  `whole`.
- **T16:** The fixed-prediction branch, all-unit intercept-inclusive OLS branch,
  covariance bias, biased example, and both sufficient conditions are covered.
  Orthogonal projection defines actual OLS fitted responses at deficient rank.
  Fixed pretreatment residualization is covered by substituting both residual
  potential-outcome vectors into the universal statements.
- **T17:** The explicit law meets every printed condition, including positive
  same-arm joints on and off the diagonal. With singleton clusters and
  sharp-null outcomes one, its expected variance estimate is `23/8`, while the
  true variance is `27/8`; one directed cross-arm joint is zero. This refutes
  the printed assertion itself and supports the record's `refuted` label.
  [The witness checklist](/home/ubuntu/sap/tasks/FW-P026b-r3g1/scratch/refutation-check.txt)
  states the printed reading and checks each condition. Step 2's `different`
  classification records the deliberate reversal of polarity, not a fidelity
  defect; no step-2 mathematical conclusion changed after reading the record.

[scratch/Check.lean](/home/ubuntu/sap/tasks/FW-P026b-r3g1/scratch/Check.lean)
compiled successfully using `sap-lean`, importing only Defs. It constructs an
admissible experiment, verifies the fixed laws, certifies the three displayed
OLS fits, evaluates the package residual contrast, and checks T17's exact
moments. The independent Python enumeration checks all 90 T14 assignments and
corroborates SE `0.2470917506`, variance `0.06105433321`, and SD of the variance
estimator `0.01256670239`; these floating-point checks supplement the supplied
formal certificate. Finite-dimensional strict concavity and the displayed
nonseparation conditions ensure genuine finite logistic maximizers.

No definition encodes its conclusion, and no claim depends on a junk value.
All estimator denominators are nonzero under the relevant laws; the explicit
epsilon convention handles zero joint probabilities. The final
[findings.json](/home/ubuntu/sap/tasks/FW-P026b-r3g1/findings.json) contains one
entry per requested declaration with its original fingerprint.
