# Declaration review

All five declarations are faithful to their recorded scope. T11 is correctly
labelled restricted; T12–T15 correctly cover their whole canonical claims.
There are no current issues.

The blind statement and junk-value analysis is in `reading.md`, saved before
opening the claims, earlier review, architect report, or record. Every entry
of each supplied dependency closure was read, including generated auxiliaries
printed in `scratch/Inspect.lean`. `claim-stage.json` records the claim
comparison made before opening `record.json`; no conclusion changed at the
record stage. The canonical statement, definitions and standing assumptions
determine coverage; audit-history notes were not used to add or remove clauses.

- **T11:** Equation (7) covers finite-support laws only. This is narrower than
  canonical clause (a), accurately disclosed in both the Challenge docstring
  and record. Clause (b)'s exact cluster-design expectation and bias are complete.
  Both earlier issues are resolved by disclosure and relabelling; the general
  probability-law identity remains omitted.
- **T12:** The total and ATE unbiasedness, affine identity, conditional
  non-invariance and genuine existential counterexample are all present.
  The transformation correctly shifts each cluster total by its individual
  count times the location shift. On each selected arm the corresponding
  potential total is the observed total under the standing observation rule.
- **T13:** Both sets of total/ATE unbiasedness equations and the centering
  calculation are present. The expectation in (22) averages the selected
  cluster or arm mean, as used in the estimator sums. No fixed-label
  expectation is incorrectly declared zero or used as a refutation.
  All coefficients and covariates are fixed; zero variances and zero
  covariates remain admissible.
- **T14:** The expansions, actual first and second derivatives, complete
  coefficient rearrangements, unique optima and efficiency comparisons
  are stated. The coefficient fractions and unique stationary minima use
  nonzero size variance, matching the domain of the printed fractions and
  positive-second-derivative optimization step in the canonical statement.
  Unconditional expansions remain available at zero variance, and the
  theorem explicitly handles equal cluster sizes. This assessment does
  not rely on the historical note supplying an extra hypothesis.
- **T15:** Clauses (a)–(f) are covered with the divisor-M population moments
  and the selected-arm sample variance statistics. Two clusters per arm
  are required precisely where sample denominators need them. The block
  law is uniform over the entire Cartesian product, ensuring the printed
  independent-block setting. The plug-in theorem assumes blockwise bounds
  and proves their global consequence.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` succeeds with no errors
or warnings; `scratch/Check.log` is empty. The checks import definitions only,
never Challenge stubs. They construct valid unequal-size and equal-size
populations, evaluate a nonzero ratio covariance and design bias, construct
T12's existential witness, check fixed covariate adjustments, verify a strict
variance reduction, and satisfy every blockwise conservativeness premise.
All expected values are computed independently by finite sums. Positive
denominators or explicit domain guards prevent each relevant junk value.
Arbitrary real cluster totals or fixed covariate totals lose no individual-level
generality: each can be distributed constantly over its positive-sized cluster.

No source declaration was changed, no web search was needed, no `lake` command
was run, and Lean processes ran one at a time. `findings.json` contains exactly
the five requested fingerprints and records a separate resolution for each
earlier T11 issue.
