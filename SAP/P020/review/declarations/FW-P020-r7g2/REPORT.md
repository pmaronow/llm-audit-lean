# Review of P020 T6–T10

All five declarations are **faithful**, with severity **none**. Every `whole`
decision in `record.json` is justified, and each Challenge docstring accurately
describes its statement. No step-2 conclusion changed after reading the record.

`reading.md` was saved before opening either claims or record; `claim-stage.json`
was saved before opening the record. I inspected all 77 distinct declarations
in the five closures, including all 19 generated auxiliary proofs. No external
review or solution files were used.

| Declaration | Clause coverage |
| --- | --- |
| T6 | All specified population values, fitted slopes, arm size means, adjusted estimates, expectation, bias, and both covariances, including the corrected bias identity. |
| T7 | Individual aggregation, both transformed potential identities, and every substantive equality in the corrected estimator chain for arbitrary affine parameters and admissible assignments. The initial observed-arm expression follows by unfolding the estimator. |
| T8 | Both arm variance expansions by specialization of one universal vector identity, mean preservation, and all seven corrected covariance-chain lines. |
| T9 | Both specified counterexamples, assignment admissibility, and the bracket expression at both clusters. |
| T10 | Individual and total sharp-null identities, both variance identities and the covariance identity, actual design variance, and the exact observed-total formula. |

T8 was classified `broader` at step 2 because its algebra also permits arbitrary
real size vectors and M=1. This true generalization contains every canonical
instance and supports the record's `whole` decision. T7's aggregation identity
also correctly includes the empty vector. T10's substituted observed-variance
middle display follows by rewriting its general variance formula with its
explicit moment equalities; equality of observed variance across assignments
follows from equality to the same fixed potential variance.

## Checks of the printed readings and witnesses

For T6, the printed reading is: equation (31) asserts expectation equal to Delta
for a coefficient estimated from the experiment, because its identical
covariance terms cancel. Every condition is met:

- Fixed individual potential outcomes realize totals (0,0,0) and (0,0,3).
- M=3, mt=1, mc=2, sizes (1,2,3), N=6 satisfy the design assumptions.
- Complete randomization is uniform over exactly the three singleton assignments.
- The coefficient is OLS on observed cluster totals against sizes, with an
  intercept and no treatment indicator; size variance is 2/3, so it is defined.
- Both adjusted arms use the same estimated coefficient, as the canonical
  counterexample requires. Mean 1/8 differs from Delta=1/2 and bias is -3/8.

For T9(a), the printed reading is: the transformed estimator equals the
intermediate expression that uses treatment potentials in the control sum.
Every condition is met:

- M=2, mt=mc=1, positive sizes (1,2), N=3 and treated set {0} are admissible.
- Control totals (0,0) and treatment totals (1,2) are realized by individual
  control outcomes zero and treatment outcomes one.
- The fixed parameters k=0, b0=0, b1=1 give the prescribed identity transform.
- The actual estimate is 2/3 and the printed intermediate expression is -2/3.

For T9(b), the printed reading is: covariance equals the expression whose
second factor lies outside the cluster-average expectation bracket.
Every condition is met:

- M=2, mt=mc=1 and sizes (1,2) satisfy the same design assumptions.
- Both potential-total vectors are (0,2), realized by identical individual
  potentials: zero in the first cluster and one for both individuals in the second.
- k=0 is fixed, and the expectation is the uniform average over clusters,
  with divisor-M variance and covariance.
- Covariance is 1, but the displayed expression is -1 at the first cluster
  and 1 at the second. All quantities are finite and defined.

These results establish the canonical counterexample targets themselves.
Their record label `whole` is therefore appropriate.

## Definitions, nonvacuity, and validation

Population moments use divisor M; randomization moments use normalized uniform
weights over assignments. Aggregation, observed outcomes, HT, Des Raj,
centering, and affine transformation agree with the canonical definitions.
No definition encodes the conclusion or replaces the intended quantity by a
placeholder. All population denominators are positive; the sole inverted size
variance in these witnesses is explicitly 2/3. No junk value or inconsistent
hypothesis affects any declaration.

`/home/ubuntu/sap/tools/sap-lean scratch/Check.lean` completed with exit code 0.
It imports only Defs and independently proves the complete T6 and T9 witness
statements. It also checks a nonzero-shift T7 instance, nonconstant T8 vectors,
and a T10 individual sharp-null instance with unequal sizes, observed total
variance 1, and both actual HT variance and the observed formula equal to 16/9.
These checks use no Challenge theorem stubs. `scratch/ClosureProofs.lean` also
compiled successfully and printed every generated closure proof.

`findings.json` contains exactly the five requested declarations and their
unchanged fingerprints. Both JSON output files were parsed and checked with
Python.
