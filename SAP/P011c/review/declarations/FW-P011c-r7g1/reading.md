# Blind reading

This file was written and saved before opening `claims.json`, `record.json`,
`earlier.json`, or `architect-report.md`. It uses the current Challenge docstrings,
every entry of the five closures in `closure.json`, the corresponding unit source
declarations, Mathlib definitions, and `scratch/BlindCheck.lean`.

The auxiliary closure entries were inspected with `#print`. `T29Statement._proof_1`,
`edgeProgramVariance._proof_1`, and `normalQuantile._proof_1` merely supply the
`AtLeastTwo` instance for the numeral 2. `Scaling._proof_1` supplies the ordinary
outer-measure instance of a measure. None introduces an assumption or substantive
mathematical definition. Structure constructors and all listed projections were
read through their structure declarations and printed constructors.

## SAP.P011c.T29

Source: `Challenge/Part1.lean:8–12`, `Defs/Part3.lean:14–24`.

The theorem is the conjunction of two universally quantified assertions.

First, choose any natural numbers n and p, assume n > 0, then choose:

- a probability measure μ on R^n, with its ordinary product Borel sigma algebra;
- fixed real weights θ_i, two simple undirected graphs G and R on `Fin n`, and
  natural-number degree caps d_i (these are fields of `Model n`, unused here);
- a real n-by-p matrix D and a vector b in R^p.

A graph is a Boolean matrix a with a_ij = a_ji and a_ii = false. `Model.mk` simply
packages μ, a proof that μ has mass one, the weights, the two graphs and caps; it
does not itself assume independence, moments, graph compatibility, or a mean model.
Require det(D^T D) != 0, and require that each coordinate Y_i is integrable under μ
and E_μ Y_i = sum_j D_ij b_j. Put L = (D^T D)^(-1)D^T. The two conclusions are:

1. For every coefficient index j in `Fin p` and every y in R^n,
   `((D^T D)^(-1)(D^T y))_j = (sum_i (n L_ji)y_i)/n`.
2. For every such j, the ordinary Bochner integral of that OLS coefficient is b_j.

All sums are finite. Matrix products are their ordinary coordinate sums, matrix
transpose exchanges the indices, and the inverse is Mathlib's nonsingular matrix
inverse. `olsTheta D` is n times L. The representation conclusion is pointwise,
not merely almost sure. The quantifier order makes D and b fixed for the outcome
law, rather than outcome-dependent designs.

Second, choose any natural n > 0 and any `Model n` as above. Assume each raw
coordinate Y_i belongs to Mathlib `MemLp ... 2 μ`, i.e. is a.e. strongly measurable
with finite L2 seminorm. Define

`B(y) = (sum_i θ_i y_i)/n`.

The conclusion is

`integral (B(y) - integral B dμ)^2 dμ
 = (sum_i sum_j θ_i θ_j [integral Y_i Y_j dμ
                          - (integral Y_i dμ)(integral Y_j dμ)])/n^2`.

Thus `var` is a centered second moment and `covOf` is the raw product moment minus
the product of means. `weighted` is the vector (θ_i y_i), `average` is sum/n,
`betaHat` is its average, and `expectation` is the real Bochner integral. No
dependency, homoskedasticity, or graph constraints enter either assertion. The
two conjuncts have separate quantifiers and assumptions; the L2 requirement is
not attached to the first, integrable-mean assertion.

Junk-value and degeneracy audit:

- Division by n and n^2 uses total real division, with inverse of zero equal to
  zero. n > 0 in both conjuncts excludes this convention.
- Matrix inversion returns zero for singular real square matrices. The determinant
  assumption excludes this branch in the first assertion.
- A real Bochner integral is zero for a nonintegrable function. Coordinate
  integrability in the first assertion implies integrability of every OLS
  coefficient. L2 coordinates and the probability law in the second imply
  integrability of coordinates, their products, and the required squared linear
  combination. No asserted statistical quantity uses the nonintegrable branch.
- p = 0 is allowed. Its Gram matrix has determinant 1, and both coefficient
  conclusions are empty-index universal statements. This is a legitimate empty
  coefficient problem; p = n = 1 also permits ordinary nonempty instances.
- `Fin n` is nonempty because n > 0. All natural-to-real casts preserve their
  values; exponents are the natural number 2. There is no truncated subtraction,
  logarithm, square root, real power, extended-real conversion, infimum, supremum,
  limit inferior, or partial-function default in this closure.

The docstring describes an integrable linear mean model with invertible Gram
matrix and the variance formula under finite second moments and positive size.
This matches the two displayed mathematical assertions as read blindly.

## SAP.P011c.T30

Source: `Challenge/Part1.lean:14–21`, `Defs/Part5.lean:14–46`.

Choose any natural n, assume n > 0, and then choose a finite set F of mandatory
edges, natural caps d_i for i in `Fin n`, a real data vector x, and a finite
candidate edge set S. An edge is a pair (i,j) with i,j in `Fin n` and i < j. Thus
each unordered pair appears once, there are no loops, and a `Finset` cannot repeat
an edge. All unordered pairs are available as candidates.

Let xbar = (sum_i x_i)/n, z_i = x_i - xbar, and define

`p(S) = sum_(i,j in S) z_i z_j`,

`v(S) = [sum_i z_i^2 + 2 p(S)]/n^2`.

Define the degree of i in S as the cardinality of the subset of S whose first or
second endpoint is i. `DegreeFeasible F d S` says F is a subset of S and each of
these cardinalities is at most d_i. `IncidenceFeasible F d S` says F is a subset
of S and, for every i, the sum over edges in S of the natural-number indicator
of endpoint incidence is at most d_i. These are ordinary cardinality and
finite-indicator-sum formulations of the same constraints.

For every choice of the above objects, the theorem states the equivalence:

`[S is degree-feasible and every degree-feasible T satisfies v(T) <= v(S)]`

if and only if

`[S is incidence-feasible and every incidence-feasible T satisfies p(T) <= p(S)]`.

The quantification over T includes every finite subset of unordered pairs. Profits
can be negative, positive, or zero. The common feasibility condition includes
mandatory edges even when their profit is negative. The optimization is over a
finite set; however, the theorem does not assert existence of a feasible set for
arbitrary F and d. It says that any proposed S has the same maximizing status in
the two formulations. All maximizers, including ties, are covered.

This is a finite 0/1 item encoding: an edge is one binary item consuming one unit
of capacity at each endpoint. It asserts no polynomial-time algorithm, reduction
from arbitrary knapsack, hardness, approximation guarantee, or variable-count
formula. The docstring explicitly limits the scope to this optimization encoding.

Junk-value and degeneracy audit:

- `average` and the variance objective divide by n or n^2. n > 0 excludes zero
  division and makes the affine slope 2/n^2 strictly positive.
- n = 1 is allowed and its edge type is empty. Only the empty edge set exists;
  both objectives and all degrees are zero. n >= 2 permits nonempty edge types.
- Empty S and empty F use ordinary empty sums and cardinalities, both zero.
  Incompatible F and d make both maximizing predicates false, rather than
  assigning a junk optimal value. There is no infimum or maximum-of-empty-set
  operation in the statement.
- Natural degree caps and incidence sums involve no subtraction. Their use is
  integral capacity counting, not real rounding or truncation. The natural-to-real
  cast of n is exact. No integral, extended-real conversion, root, logarithm,
  real power, limit, or partial-function default occurs.
- `edgeProgramVariance._proof_1` is only a numeral instance, as noted above.

## SAP.P011c.T31

Source: `Challenge/Part1.lean:23–26`, `Defs/Part3.lean:26–29`.

The assertion is the negation of a universal consistency implication. Its
classical existential reading is: there exist a `Family` F and four real
constants c1,c2,c3,c4 satisfying `Scaling`, for which the scaled general oracle
variance estimate does not converge in probability to the scaled true variance.
Equivalently, for some positive real ε the error-event probabilities below do
not tend to zero. It does not assert that every scaling family is inconsistent.

Here is the entire family/scaling vocabulary unfolded. A family consists of:

- natural sample sizes n_k > 0 for all natural k, with n_k tending to infinity;
- for each k, a probability measure μ_k on R^(n_k), real weights θ_ki, simple
  undirected graphs G_k and R_k, and natural caps d_ki.

There is no common probability space or relation between row laws. Set

`X_ki(y) = θ_ki y_i`, `B_k(y) = (sum_i X_ki(y))/n_k`,

`b_k = integral B_k dμ_k`, `s_k^2 = integral (B_k - b_k)^2 dμ_k`.

`Scaling F c1 c2 c3 c4` is precisely the conjunction of:

1. `Nested F`: n_k is nondecreasing, and for each k there is an injective map
   e_k from `Fin n_k` to `Fin n_(k+1)` preserving both edges and nonedges of G.
   This is induced nesting of the observed graphs, with no required coherence
   among the successive injections and no nesting of R or caps.
2. Each of c1,c2,c3,c4 is strictly positive.
3. For every k, G_k is a dependency graph for the raw coordinates Y_i: for every
   two disjoint finite vertex sets S,T with no G edge between them, the random
   vectors (Y_i)_(i in S) and (Y_j)_(j in T) are `IndepFun` under μ_k. These are
   vectors indexed by the corresponding subtypes, with product measurable spaces.
   Independence means their joint measurable events have product probabilities.
   It is independence of sets of coordinates, not merely pairwise independence.
4. For every k, for μ_k-almost every y, simultaneously for all i,
   `|X_ki(y) - b_k| <= c1`.
5. For every k,i, the natural degree of i in G_k, cast to R, is at most c2.
   Degree counts true Boolean entries in the graph's adjacency row.
6. The sequence n_k s_k^2 tends to c3.
7. For every k,i, `|θ_ki| < c4` (strict inequality).

Neither equal individual means nor equal variances are imposed. The bound is
around b_k, the expected average, rather than around each coordinate's own mean.
The `Nested` documentation explicitly calls its observed-graph requirement an
additional strengthening of the printed full-graph nesting condition.

For a graph A with Boolean adjacency a, its real adjacency matrix has entry 1
when a_ij is true and 0 otherwise. For a vector x of length n, set xbar = sum x/n,
z_i = x_i - xbar, and

`V1(A,x) = [sum_i z_i^2 + sum_i sum_j a_ij z_i z_j]/n^2`,

where the double sum is over ordered pairs (so each undirected edge contributes
twice). Thus the oracle uses the true observed graph G_k and the weighted data
X_k. `scaledOracle F k y = n_k V1(G_k,X_k(y))` and
`scaledTrue F k = n_k s_k^2`.

`InProbability` means that, for every ε > 0,

`(μ_k {y : |n_k V1(G_k,X_k(y)) - n_k s_k^2| > ε}).toReal -> 0`.

All quantifiers F,c1,c2,c3,c4 lie inside the negation; for a counterexample all
the scaling conditions above must hold together. R_k and d_ki are present in
the model but unused here. No valid-constraints assumption occurs.

Junk-value and degeneracy audit:

- Positive sample sizes exclude zero denominators, empty observed index types,
  and truncation at n = 0. The graphs can have no edges.
- `expectation` is a total Bochner integral. Although b_k is defined before
  integrability is asserted, the almost-sure bound on all X_ki around its finite
  real value implies each weighted coordinate is essentially bounded and hence
  integrable and square-integrable on the probability space. It also makes B_k
  and its square integrable. Thus the hypothesis itself excludes the junk-value
  branch for all moments used in this assertion. A raw Y_i with zero weight need
  not have finite moments, but no raw-coordinate moment is used here.
- `probability` is μ.real, namely `(μ E).toReal`; infinity would map to zero.
  The probability-measure field guarantees μ E <= 1 for every E, so infinity
  cannot occur. Each probability lies in [0,1]. The displayed error event is
  Borel measurable, since it is given by finite polynomial operations in y.
- The limit is ordinary `Filter.Tendsto` along natural-number `atTop`, not a
  conditionally complete-lattice liminf or an asserted value at infinity.
- No root, logarithm, real exponent, truncated subtraction, infimum, supremum,
  matrix inverse, or partial-function default occurs. The generated scaling
  proof is just the measure instance, not a probabilistic assumption.

The Challenge docstring calls this a refutation of universal n-scaled oracle
consistency under printed assumptions. Its actual logical content is existence
of failure even with the explicitly stronger observed-graph nesting.

## SAP.P011c.T32

Source: `Challenge/Part1.lean:28–32`, `Defs/Part3.lean:31–39`.

The theorem negates a universal implication. Its variables, in order, are a
family F, four real constants, a proof of `Scaling F c1 c2 c3 c4`, a proof of
`Valid F`, a graph-valued outcome function A, and a proof that A maximizes the
general variance estimate for every row and every outcome. The conclusion being
negated is C and (H implies C), where C is scaled conservativeness of this
maximized estimator and H is rowwise homoskedasticity. Logically the conjunction
is equivalent to C. Therefore the negation supplies some instance with failure
of C; it does not supply a homoskedastic counterexample.

Fully expanded objects and assumptions: F supplies n_k > 0 tending to infinity,
probability measures μ_k on product Borel R^(n_k), fixed weights θ_ki, simple
undirected graphs G_k,R_k, and natural caps d_ki. Let X_ki = θ_ki Y_i,
B_k = sum_i X_ki/n_k, b_k = integral B_k dμ_k, and
s_k^2 = integral (B_k-b_k)^2 dμ_k. Scaling requires all seven clauses listed in
the T31 section: nondecreasing sizes and induced embeddings of successive G_k;
c1,c2,c3,c4 > 0; independence of every two disjoint G-unconnected collections of
raw coordinates; the a.s. bound |X_ki-b_k| <= c1; true G degrees <= c2;
n_k s_k^2 -> c3; and |θ_ki| < c4. It imposes no individual-mean equality.

`Valid F` says, for each row, R_k is contained in G_k and degree(G_k,i) <= d_ki.
For each k and every y in R^(n_k), A_k(y) is a simple undirected graph of that
row size. It is required to contain every edge in R_k and satisfy all degree
caps. In addition, for every other such graph B,

`V1(B,X_k(y)) <= V1(A_k(y),X_k(y))`.

Here, writing z_i = X_ki(y) - sum_j X_kj(y)/n_k,

`V1(B,X_k(y)) = [sum_i z_i^2 + sum_i sum_j 1_(B_ij) z_i z_j]/n_k^2`.

The selector A is universally quantified after F and the constants. Its
maximization premise holds for all y, including null outcomes. No measurability
of the graph-valued selector is explicitly required, but the chosen objective
value is the maximum of finitely many polynomial functions on a fixed nonempty
feasible set, so the real-valued statistic is measurable independently of tie
choices. `Valid` supplies at least the feasible graph G_k.

`Conservative`, the proposition C above, means: for every real ε > 0,

`(μ_k {y : n_k [s_k^2 - V1(A_k(y),X_k(y))] > ε}).toReal -> 0`.

This is a one-sided n-scaled probability assertion, not expectation bias,
pointwise domination, or absolute consistency. Its failure means that some
positive ε has probabilities that do not tend to zero.

For completeness, H says that for each k and all i,j,

`integral (X_ki - integral X_ki dμ_k)^2 dμ_k
 = integral (X_kj - integral X_kj dμ_k)^2 dμ_k`.

This is exactly `Homoskedastic`: diagonal equality of `covariance`, whose general
(i,j) entry is the integral of the product of the individually mean-centered
weighted coordinates. It requires equal variances, not equal means or equal
distributions. The theorem negates the combined contract rather than asserting
failure under H, as its Challenge docstring explicitly explains.

Junk-value and degeneracy audit:

- n_k > 0 excludes zero divisions and empty vertex types. Natural-to-real casts
  are exact. There is no natural subtraction or cap truncation in this closure.
- The scaling bound implies finite first and second moments of weighted
  coordinates and the sample average, so `expectation`, `var`, and every entry
  of `covariance` used here are genuine integrals rather than zero defaults.
- Measures are probability measures; `toReal infinity = 0` never applies to an
  event. All required event probabilities are in [0,1]. Maximization values are
  measurable for the reason above, even for arbitrary tie selectors.
- Feasible sets are finite and nonempty under `Valid`; `Maximizes` itself uses
  universal comparisons and no default maximum or infimum.
- There are no roots, logarithms, real powers, liminfs, sInf/sSup, singular
  inverses, or defaults of partial functions in this statement.

## SAP.P011c.T33

Source: `Challenge/Part1.lean:34–40`, `Defs/Part3.lean:41–48`,
`Defs/Part2.lean:63–66,76–83`.

This is again a negated universal implication. Quantifiers and hypotheses occur
in this order: choose F and four real constants; assume `Scaling` and `Valid`;
choose the rowwise outcome-dependent graph selector A; assume it maximizes V1
over all compatible graphs at every outcome; then assert conservative printed
coverage at every real level α with 0 < α < 1. The theorem negates this entire
assertion. Classically it says there exist such F, constants and a maximizing A,
and some α in (0,1), for which the limiting inferior coverage is strictly below
1-α. It need not fail at every α.

All objects are the following concrete ones. F has n_k > 0 tending to infinity,
probability laws μ_k on product Borel R^(n_k), real weights θ_ki, simple symmetric
loopless Boolean graphs G_k,R_k, and natural degree caps d_ki. Set

`X_ki(y) = θ_ki y_i`, `B_k(y) = sum_i X_ki(y)/n_k`,

`b_k = integral B_k dμ_k`, `s_k^2 = integral (B_k-b_k)^2 dμ_k`.

Scaling means: the sizes are nondecreasing and successive observed G_k have
induced embeddings; all four constants are positive; every two disjoint
G_k-unconnected collections of raw coordinates are independent; a.s. for all i,
|X_ki-b_k| <= c1; true G_k degrees <= c2; n_k s_k^2 -> c3; and |θ_ki| < c4.
There is no homoskedasticity or equality-of-means condition.

Validity means R_k is a subgraph of G_k and degree(G_k,i) <= d_ki. A_k(y)
contains R_k, has degree at most d_ki, and maximizes, over every graph B with those
constraints, the quantity

`V_k(y) = [sum_i (X_ki(y)-B_k(y))^2
           + sum_i sum_j 1_(A_k(y)_ij)
               (X_ki(y)-B_k(y))(X_kj(y)-B_k(y))]/n_k^2`.

`Phi t` is the cdf of Mathlib's real Gaussian measure with mean 0 and variance
parameter 1: equivalently the probability of (-infinity,t]. Define

`q_α = inf {t in R : 1-α/2 <= Phi(t)}`.

At each row the specified coverage is

`p_k(α) = (μ_k {y : 0 <= V_k(y) and
                         |B_k(y)-b_k| <= q_α sqrt(V_k(y))}).toReal`.

The universal contract being negated is

`for every 0 < α < 1, 1-α <= liminf_(k -> infinity) p_k(α)`.

The limiting inferior is the real `Filter.liminf`, i.e. the supremum of all
eventual real lower bounds of the coverage sequence. It is not an asserted
ordinary limit. The coverage event deliberately excludes every realization
with negative V_k, even if the numerator is zero. It is an explicit convention
for a partially defined real-square-root interval, as the docstring states.
The theorem does not assert undercoverage for a family with V_k >= 0 a.s., or
for any alternative treatment of negative estimates.

Junk-value and degeneracy audit:

- All n_k are positive, so the averages and V1 denominator are genuine. All
  moment integrals are well-defined by the a.s. bounded weighted coordinates
  under probability laws, as in T31 and T32.
- `Measure.real` maps infinity to zero in general, but all these event measures
  lie in [0,1], so that convention cannot affect the result.
- For 0 < α < 1, 1-α/2 lies strictly between 1/2 and 1. The normal cdf is
  continuous, strictly increasing, and has limits 0 and 1. The quantile set is
  nonempty and bounded below, and q_α is the ordinary positive finite normal
  critical value. The undefined/default cases of real `sInf` on empty or
  unbounded-below sets cannot occur at an asserted level. The globally defined
  quantile can have uninformative values for other α, which are never used.
- Mathlib's `Real.sqrt` is total, with sqrt(t)=0 for t < 0. The explicit conjunct
  0 <= V_k(y) makes coverage false on that branch regardless of the root value.
  Thus there is no reliance on a negative-input square-root junk value, but
  there is a substantive choice to count undefined intervals as misses.
- The coverage sequence is in [0,1]. Its eventual-lower-bound set contains 0
  and is bounded above by 1; real `liminf` has its usual bounded-sequence
  meaning, without an unbounded/empty-set default.
- The selected maximizing value is measurable as a finite maximum of continuous
  quadratic functions with a nonempty feasible set. Hence coverage events are
  measurable even if the selector's tie choices are arbitrary.
- No empty observed type, logarithm, real power, natural subtraction, matrix
  inverse, or partial-function default otherwise occurs. Quantile division by
  2 is ordinary division by a fixed nonzero real numeral.
