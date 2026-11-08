# Review of P002-T26–T30

All five declarations are faithful to their recorded scope: T26 and T27 are
whole, T28 is explicitly restricted, and T29 and T30 genuinely refute the
printed exact-limit assertions. No step-2 comparison was changed after reading
the record. In particular, the step-2 `different` entries distinguish a repaired
algorithm or a negation from the positive canonical statement; they do not by
themselves establish an inaccurately described declaration.

The blind reading is in `reading.md`, saved before accessing the claims or
record. Every declaration in each supplied closure was inspected, including
the generated helpers printed by `scratch/ClosureChecks.lean`.

## T26

`T26WholeStatement` contains all of the algebraic clauses, including the two
interacted treatment coefficients, the IV product identity without an added
nonzero-receipt hypothesis, and the conditional Wald equality. It also supplies
the finite-union assertion on the ordinary-inverse domain and a genuine
noninterval example. Defining the interacted coefficient through the invertible
change of arm-intercept coordinates is a correct representation of that
regression coefficient, not a definition of the desired contrast identity.

The full-rank and IV assumptions are jointly satisfiable. The compiled
six-unit, one-covariate instance in `scratch/Nonvacuity.lean` has centered,
distinct covariates, full rank for every assignment, a receipt contrast of 1,
and both IV determinants nonzero. Independent exact rational enumeration of
the eight-unit witness checks all 70 assignments: −12 and 10 are accepted,
while −7 is rejected. Every arm Gram determinant is at least 5. The computations
are in `scratch/WitnessChecks.py` and `scratch/witness-checks.json`.

## T27

All four Lemma 1 conclusions are present, including both one-sided infinite
endpoint cases. Function equality in the crossing definition correctly excludes
identical curves. Strictly positive denominator polynomials are the printed
Assumption 6; nonnegative numerators follow from their squared-contrast
construction. The empirical quantile uses the correct weak-rank threshold and
retains all tied indices.

The compiled checks construct both a raw family with genuine crossings and an
adjusted, positive-dimensional family satisfying every premise. The latter
also checks a nonempty crossing-free interval, so the universal interval
assertion is not resting on inconsistent inputs.

## T28

The record's **restricted** decision is essential. The theorem includes the
printed Algorithms 1/3 and no-intersection behavior, and additionally treats
completed **corrected** Algorithms 2/4. Its Challenge docstring expressly says
“using the corrected interval-index pairs”
(`SAP/P002b/Challenge/Part1.lean:91`), and the restriction identifies the
corrected runs, adjusted rank domain, and omission of arbitrary-policy
termination (`SAP/P002b/Challenge/Part1.lean:93`). These accurately describe
`T28Statement` and its run predicates.

This does **not** establish correctness of a literal shifted-index reading of
printed Step 5. The four-unit example gives crossings −4 and −1 and Step-4
indices 1,0,1. At effect 0 the observed squared statistic is 10, the empirical
critical squared value is 18/13, and the shifted printed comparison accepts
the point that the empirical set rejects. The exact checks verify the dataset,
positive denominators, complete crossing list, and quantile choices. This
distinction remains in `claim-stage.json`; it is accepted only because the
reviewed declaration explicitly limits its scope to corrected pairs. The
canonical audit note was not used to turn the printed algorithm into a whole
positive claim.

Run existence, complete crossing-list existence, and arbitrary no-intersection
quantile selections are actually asserted. Correctness is not merely assumed
inside the definitions. Both raw and adjusted premises have compiled instances.

## T29

The negation is exactly a refutation of the printed universal exact nominal
limit. With `δ=0`, `r=1/4`, `A=1/2`, and `α=1/2`, the fourth-moment bound
forces both adjusted potential-response variances to zero for every admitted
model. The LATE identity makes the two constant responses equal. All assignments
then have coverage 1. The classes are inhabited for every `n≥2`, so their
coverage infimum is 1, not 1/2. The printed zero-over-zero convention expressly
permits these models.

`scratch/RefutationChecks.lean` constructs such a model for every `n≥2`, proves
all `Theta` conditions, and proves coverage 1. The complete printed-reading
condition check and the argument about **every** model in the infimum appear
in `scratch/RefutationAudit.md`.

## T30

The adjusted negation also contradicts the canonical assertion itself. For
`(k,δ,e,A,B,r,α)=(1,0,1/4,4,1/2,1/4,1/2)`, the moment bound forces zero
population regression residuals. The adjusted contrast is then zero whenever
the observed arm designs have full rank. The balance, eigenvalue and fourth
moment bounds give a uniform probability of rank failure tending to zero.
Consequently the worst coverage tends to 1, not 1/2.

Centered distinct-grid covariates and zero potential outcomes give inhabited
classes at every sufficiently large size, with all assignment-arm regressions
full rank. A concrete grid instance satisfying every `Xi` condition is compiled
in `scratch/RefutationChecks.lean`. `scratch/RefutationAudit.md` checks each
printed condition and gives an explicit uniform bound. The refutation is
independent of the chosen singular-arm least-squares minimizer and does not use
an empty-model infimum or an undefined statistic.

## Validation

The following completed successfully, with no `sorry` or Challenge theorem
used in the scratch proofs:

* `/home/ubuntu/sap/tools/sap-lean scratch/ClosureChecks.lean`
* `/home/ubuntu/sap/tools/sap-lean scratch/Nonvacuity.lean`
* `/home/ubuntu/sap/tools/sap-lean scratch/RefutationChecks.lean`
* `python3 scratch/WitnessChecks.py`

The scratch Lean checks have only auxiliary-declaration, deprecation or style
warnings. The asymptotic counterexample arguments are written mathematical
checks, not new formal proofs of T29 or T30. `findings.json` and
`claim-stage.json` were parsed and checked for exactly the five requested
declarations and matching closure fingerprints.
