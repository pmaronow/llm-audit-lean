# Review of SAP.P013b.T15–T19

All five declarations are faithful. T15, T16, T17 and T19 cover their canonical
claims in full. T18 faithfully refutes the universal assertion under the
**printed** Condition 5. The recorded decisions and the five docstrings agree
with these scopes. No correction is required.

`reading.md` was saved before reading the canonical claims. `claim-stage.json`
was saved before reading the architect's record. The record required no revision
of the claim-stage assessment. Every declaration in all five supplied closures
was read, including structure fields, constructors, projections and generated
numeral proofs. The review used the supplied statements and definitions; the
certified Solution and external source formalization were not inspected.

| Declaration | Canonical clauses checked | Verdict |
|---|---|---|
| T15 | Both covariance conservativeness results, the equality case, and effect-variance conservativeness | faithful / none |
| T16 | Fixed-prediction unbiasedness and residual identity, unbiased count, zero-convention Hájek bias bound | faithful / none |
| T17 | Literal misspecification condition, weighted total expectation, weighted contrast expectation | faithful / none |
| T18 | Negation of coverage guarantee for nested populations under Conditions 3, printed 5 and 6 | faithful / none |
| T19 | HT effect consistency under uniform Condition 3 and the pair-count Condition 4 | faithful / none |

For T15, the four conjuncts in `Defs/Part5.lean:16` preserve the different
hypotheses of Propositions 5.3–5.6. The off-diagonal positivity assumption applies
only to the first two conjuncts. The adjustment in `Defs/Part1.lean:92` includes
diagonal zero-joint pairs and all required off-diagonal zero-joint pairs, with
the correct negative sign. The effect-variance definition includes both A2
corrections and subtracts twice that adjusted covariance. Finite weighted
covariance and variance are the actual randomization moments. The compiled
two-unit signed-outcome instance satisfies even the equality-case hypotheses.

For T16, the explicit “Statements to formalize” clause of the canonical
**statement** selects (a1), (b1) and (b2). This selection is present without
using the audit note to remove a clause. `Defs/Part5.lean:28` supplies all three,
including the assignmentwise residual identity. Fixed predictions impose the
specified scope. At zero count the HT numerator also vanishes; the selected
zero ratio therefore preserves the product identity behind the bias bound.
The compiled example has a genuine zero-count assignment and nonzero bias:
the expected ratio is −3/8 and the target is −1/2.

For T17, `Defs/Part1.lean:115` is exactly Condition 7. The separate randomization
outcome array is unrestricted by the unused exposure-specific outcome field.
The conditional weight in `Defs/Part1.lean:123` uses the exposure induced by its
assignment, so each of the two contrast sums has its own correct denominator.
The compiled witness has two positive-probability assignments with the same
exposure for a unit and different randomization outcomes for that unit.

For T18, the printed reading is: every nested finite-population sequence
satisfying consistency, exposure sufficiency, positivity and Conditions 3,
printed 5 and 6 has limiting lower Wald coverage at least 1−α at every
0<α<1. The independently constructed witness in
`scratch/CoverageWitness.lean` was checked against each condition:

* The support is a fair two-point law, with positive weights summing to one.
* Every unit receives that common coin's exposure; both marginal probabilities
  are 1/2 and the selected exposures are distinct.
* Fixed potentials are y_i(1)=√(i+1)−√i and y_i(0)=0, indexed from zero.
  Identity exposure labels and the same infinite potential array establish
  nesting, exposure sufficiency and consistency.
* The potential increments lie in [0,1], so Condition 3 holds with constants
  c1=1 and c2=2 for the entire sequence.
* The diagonal dependency matrix has row count 1. The literal four-clause
  `PrintedNoEdge` predicate forces both tested disjoint sets empty, which
  verifies printed Condition 5. This is exactly the printed predicate in the
  canonical assumptions, including its diagonal convention.
* The compiled identity N·Var(HT effect)=1 verifies Condition 6 with c=1.
* The target is 1/√N. On the coin-0 assignment the estimator and estimated
  variance are zero, so its interval misses the positive target. Coverage is
  at most 1/2 for every N, contradicting the 3/4 requirement at α=1/4.
* Estimated variances are nonnegative on both assignments. Thus every interval
  in this witness is defined, and the negative-variance noncoverage convention
  has no effect on its refutation.

This establishes a refutation of the canonical assertion itself under its
printed conditions. The docstring's observation about a paired source witness
is provenance; the independent witness above verifies that undefined intervals
are unnecessary for the failure. No conclusion about a corrected dependency
condition is inferred from this particular witness.

For T19, categorical joint-probability factorization is exactly pairwise
independence. `Defs/Part2.lean:90` permits potentially dependent pairs to be
marked and requires their count divided by N² to vanish. Constants in Condition
3 are uniform over all populations, units and exposures. The conclusion uses
the correct population effect and each population's own randomization law.
The compiled sequence has independent fair binary exposures, fixed nonzero
potentials, and a diagonal dependency indicator with count N.

The junk-value audit found no defect: marginal and size denominators are
positive; zero-joint terms implement the paper's omitted-pair convention;
the Hájek zero convention is explicitly selected; the Gaussian quantile has a
nonempty set bounded below for the permitted levels; coverage lies in [0,1],
so its real liminf is the ordinary bounded liminf. Finite supports make the
usual measurability and moment conditions automatic. No conclusion relies on
nonintegrable integrals, infinity conversion, or a default value of an
unbounded extremum.

Validation used `/home/ubuntu/sap/tools/sap-lean` on `scratch/Blind.lean`,
`scratch/AsymHelpers.lean`, `scratch/Nonvacuity.lean`,
`scratch/CoverageWitness.lean` and `scratch/ConsistencyWitness.lean`. The
nonvacuity and counterexample checks import only `SAP.P013b.Defs` and do not
invoke the audited theorem stubs. Both output JSON files were parsed and their
five-entry coverage was checked against `closure.json`.
