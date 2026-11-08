# Review of SAP.P037a.T11–T13

All three declarations are **faithful**, severity **none**. Their recorded
`whole` decisions are justified. No statement, definition, or docstring fix
is needed.

The blind reading was saved in `reading.md` before opening `claims.json`.
The independent claim assessment was saved in `claim-stage.json` before
opening `record.json`; none of its conclusions changed after reading the
record. Every closure entry was read, including generated constructors,
projections, and auxiliary proofs (`scratch/ClosureCheck.out`).

## SAP.P037a.T11

The sixteen conjuncts in `SAP/P037a/Defs/Part9.lean:111` cover all eight
numbered mathematical clauses of the canonical claim. They include finite
unbiasedness, product-law independence, variance identities and bounds,
Chebyshev consistency, centered bounds, the Lindeberg condition and Gaussian
limits, their contrast counterparts, both fitted-estimator subtraction
identities, coefficient consistency, asymptotic equivalence, and fitted
consistency and normality.

The product law in `Defs/Part1.lean:77` preserves independence of blocks,
while allowing arbitrary dependence inside each block. Abstract finite
assignment spaces include the hierarchical four-school design as a special
case; unused restrictions such as π<1 can be imposed when specializing.
Finite Monte Carlo randomness can be included in the assignment spaces
without changing exposure marginals. Fixed-dimensional coordinate bounds
give the canonical bounded-norm condition. Indexing rows by B+1 covers every
positive block count.

The substantive regularity assumptions in `Defs/Part3.lean:85` and
`Defs/Part9.lean:53` are present in the canonical mathematical statement.
The zero coefficient on singular empirical Gram matrices is explicitly
canonical, so Mathlib's totalized matrix inverse correctly implements it.
Strict variance lower bounds protect all normalizing square roots. A zero
unnormalized Lindeberg numerator implies the canonical normalized sum is
zero. Gaussian probabilities are finite, so `toReal` introduces no artifact.
The docstring at `Challenge/Part1.lean:90` accurately summarizes the result.

The compiled nonvacuity sequence has N=2(B+1), block variance 4, contrast
variance 16, and a genuine one-dimensional positive definite Gram limit.
The same sequence satisfies every fitted-limit premise with exact
probabilities and g=xβ*=0. Thus the limit hypotheses are jointly satisfiable,
including the positive-variance branches; the example does not rely on an
empty coefficient space.

## SAP.P037a.T12

`Defs/Part1.lean:105` correctly implements nearest-multiple-of-four
interpolation with the stated endpoints. In the interior branch natural
subtraction is not truncated, and integer division has positive denominator
350. The no-tie equation has opposite parity on its two sides. All five
canonical clauses appear in `Defs/Part6.lean:113`–137, including the rounded
cap threshold 521 and every listed share. Extending the count function to
n=0 is harmless.

The literal printed reading is an upper bound of 64 below size 550, together
with the stated interpolation rule. Its conditions are positive integer
school size and the piecewise rounded rule. Sizes 100, 200 and 375 meet those
conditions and have counts 40, 40 and 52: they satisfy that upper bound.
They refute only the interpretation assigning *exactly* 64 at every size
below 550. The docstring at `Challenge/Part1.lean:94` expressly makes this
distinction, and the record correctly uses `whole`, not `refuted`.

## SAP.P037a.T13

The arithmetic and interval implications in `Defs/Part6.lean:139`–164 match
canonical clauses (i)–(v). The figure-derived control interval is a premise.
The predicted level excludes the entire 0.08 rounding bin; 0.095 is asserted
only to belong to the resulting interval. The reduction interval contains
both 57% and 60%, so the theorem does not refute 60%. The separate exact
60% calculation uses control 0.20 as intended. All variable denominators
are bounded away from zero. The docstring at `Challenge/Part1.lean:99`
describes these conditional arithmetic results accurately.

`scratch/Nonvacuity.lean` supplies a joint interior instance for all three
coefficient/control premises and compiles successfully. Exact rational
checks also recover all three sharp interval ranges.

## Validation

Both scratch Lean files were compiled using the supplied `sap-lean` runner;
the nonvacuity file imports only `SAP.P037a.Defs` and uses no target theorem.
`findings.json` and `claim-stage.json` were parsed and checked for exactly
the three requested declarations; fingerprints were checked against
`closure.json`. The unit's sources were not changed.
