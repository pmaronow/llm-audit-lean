# Review of T34–T38

All five declarations are **faithful**, with severity **none**. Every declaration in
each supplied dependency closure was read, including the generated proof constants
printed by Lean. `reading.md` was saved before opening the claims, and
`claim-stage.json` before opening the record. No step-2 assessment was changed after
reading the record. The source statements were not edited.

**T34 — the `refuted` decision is correct.** The printed reading is: under the Section 2
setting and Assumptions 2 and 3, the probability that the absolute error of the
n-scaled auxiliary oracle is **less than** any positive tolerance tends to zero.
This is the canonical assertion P4 itself, rather than a repaired consistency claim.
The literal auxiliary formula is at `Defs/WholeW1.lean:29`, and the counterexample
statement is at `Defs/WholeW1.lean:119`.

The witness meets every condition:

| Condition | Check |
|---|---|
| Joint outcomes and dependency graph | Uniform over all Boolean vectors gives independent fair real signs; the graph is empty. This is not one common repeated sign. |
| LUE and target | Unit weights, beta equal to zero, and n times the variance equal to one. |
| Scaling | Sizes k+1; bounds (1,1,1,2); full and observed empty graphs nest. |
| Homoskedasticity and constraints | Every coordinate variance is one; take empty known graphs and zero caps. |
| Auxiliary coefficients | Every coefficient array works because every adjacency entry is zero, including any admissible correlation interpretation. |

On the support, n times the auxiliary estimate is `1-betaHat²`, and
`E[betaHat²]=1/n`. Markov's inequality therefore makes the P4 probability tend to
one, contradicting its printed zero limit. Refuting this conjunct suffices; the
declaration does not need to repair the undefined correlations or assert that
Proposition 2 is false.

**T35 — the `refuted` decision is correct.** The printed formal reading is: under
Assumption 2, valid graph constraints, and a correctly specified OLS mean model,
the maximizing general variance estimator is n-scaled conservative and its Wald
interval has at least nominal asymptotic coverage. The statement at
`Defs/WholeW2.lean:37` contradicts the variance conjunct, which suffices to refute
this combined assertion. It correctly uses the canonical divisor-n formula;
neither a separate coverage counterexample nor realized vignette errors are claimed.

An independent reconstruction verifies the witness conditions. Use `n=3(k+1)` and
disjoint three-vertex paths, with all true edges known and caps equal to their
degrees. In every triple put `delta=(1,-2,1)`, design rows `(1,delta_i)`, weights
one, and `Y_i=delta_i+U_i`. The noises are independent, with mass `31/90` at each
of `-1,1` and `7/45` at each of `-2,2`.

| Condition | Check |
|---|---|
| OLS specification | True coefficients `(0,1)`; Gram matrix `diag(n,2n)` is invertible; the first scaled OLS row is one. |
| Scaling | Target zero; outcomes bounded by 4, hence by 6; degrees at most 2; weights below 2; n times the variance is exactly 29/15. |
| Dependency and nesting | All raw outcomes are independent, so these path graphs are valid dependency graphs; adding disjoint paths nests the full graphs. |
| Valid constraints and actual maximization | The known graph equals the true graph, and the degree caps force it to be the unique feasible graph for every outcome. |
| Failure of the asserted limit | n times V1 converges in probability to 19/15, below the true 29/15. The underestimation probability at tolerance 1/3 tends to one. |

For the last row, a triple's mean quadratic contribution is `-2`, its expected
noise contribution is `3*(29/15)`, and independent bounded block averages converge
to their expectations. Replacing target-centering by sample-centering adds terms
that vanish in probability. This witness uses finite-support measurable variables
and defined finite moments throughout.

**T36 — the `whole` decision is correct.** The universal conjunct at
`Defs/WholeW2.lean:58` states the exact one-sided n-scaled oracle limit with no
equality-of-means assumption. The existential conjunct includes the introductory
nonconsistency assertion in the explicitly disclosed n-scaled/relative sense.
For example, take independent fair signs plus balanced alternating means `+1,-1`,
unit weights, empty graphs, and even growing sample sizes. The constants are
`(2,1,1,2)`, individual variances are one, and n times the true variance is one;
the sample variance, hence n times V2, converges to two. This is a genuine scaled
nonconsistency witness. No failure of ordinary unscaled absolute consistency is
asserted. The broader rowwise universal scope covers the printed full-graph setting.

**T37 — the `whole` decision is correct.** Both canonical conservativeness limits
are present at `Defs/WholeW2.lean:79–80`, with valid constraints, weighted
homoskedasticity, the correct maximization objective, and the exact
`min(d_i,n-1)` truncation. Supplied degree caps are not additionally bounded.
An arbitrary maximizing selector has the same value as a finite maximum of fixed
continuous graph objectives, so its value is measurable even if its tie choices
are not. Positive sample sizes make the natural subtraction in the truncation safe.

**T38 — the `whole` decision is correct.** `Defs/WholeW1.lean:45–49` gives the
standard normal cdf limit at every real threshold, equivalent to the claimed
convergence in distribution because the limiting cdf is continuous. It also
concludes eventual strictly positive variance. All Assumption 2 conditions are
present; individual means may differ. Arbitrary growing size sequences and
rowwise dependency graphs include the printed setting.

Across all five closures, the coordinate bounds imply genuine finite moments:
even before identifying beta as its ordinary integral, it is a finite real
constant, so boundedness around beta implies integrability of the measurable
weighted coordinates. Probability laws exclude infinite-mass `toReal` defaults.
Positive sizes exclude zero sample-size division, T35 excludes singular matrix
inversion, and T38's eventual positivity removes zero-variance standardization
from the limit. No conclusion is manufactured by a junk value or an encoded
conclusion in a definition.

Validation: `scratch/Blind.lean` and `scratch/Nonvacuity.lean` compile using the
specified `sap-lean` command. The latter imports only Defs modules and constructs
all hypotheses of the universal statements, including T37's maximizing selector,
and all T34 witness-data clauses independently of the Challenge theorems. It also
checks T35's finite OLS and mean-quadratic identities and T36's alternating-mean
identity. The full T35 and T36 asymptotic witnesses above are justified analytically,
not claimed as separately re-proved Lean existentials. `scratch/Counterexamples.py`
passes exact rational moment and finite-support checks. Both output JSON lists
were parsed and the findings were checked against all five closure fingerprints.
