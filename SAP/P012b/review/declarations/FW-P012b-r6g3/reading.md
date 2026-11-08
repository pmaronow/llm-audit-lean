# Blind reading

This file was saved before opening `claims.json` or `record.json`. The source
docstring, the declaration, and every declaration listed in `closure.json` were
read. Generated structure declarations and `hNumerator._proof_1` were also
inspected by compiling `scratch/Check.lean` with `sap-lean`.

## SAP.P012b.T24

Location: `SAP/P012b/Challenge/Part2.lean:6` (docstring), line 10 (theorem).
Fingerprint: `ff088b90741b5d0ece1c9df4fe1b92092b9d0bf1961c8413e9dfd5bd3364b801`.

### Objects and definitions, unfolded

The vertex label type is the disjoint union of the natural numbers and pairs of
natural numbers, `ℕ ⊕ (ℕ × ℕ)` (`Vertex`, Part1:13). No role is imposed on either
summand by this theorem. A `State` (Part1:27) consists of a finite set V of these
labels, a finite set E of finite sets of these labels, and a total function
t from labels to the two Boolean values. `State.mk` constructs this triple;
`State.vertices`, `State.edges`, and `State.trait` return its respective fields.
There are no validity conditions built into the structure.

`Simple H` (Part1:56) means that every e in E has exactly two distinct members
and is a subset of V. Thus, under this hypothesis, E is the edge set of a finite
undirected graph without loops or parallel edges. Isolated vertices are allowed.

For any label v, let d(v) be the natural number of elements e of E containing v
(`graphDegree`, Part1:39). It counts incident edges, not neighbors with any
multiplicity. Let m be the natural number of elements of E. All occurrences of
d(v) and m in real arithmetic use their exact casts to the real numbers.
The adjacency number a(v,w) is 1 if v differs from w and the unordered pair
{v,w} belongs to E, and is 0 otherwise (`adjacency`, Part1:70). Let z(v) be 1
when t(v) is true, and 0 when it is false (`z`, Part1:73).

The two real finite double sums are

N(H) = Σ(v in V) Σ(w in V) (a(v,w) - d(v)d(w)/(2m)) z(v)z(w),

Q(H) = Σ(v in V) Σ(w in V) (1[v=w]d(v) - d(v)d(w)/(2m)) z(v)z(w).

They are `hNumerator` (Part1:75) and `hDenominator` (Part1:80), respectively.
`hValue H` (Part1:86) is the real quotient N(H)/Q(H).
`HomophilyDefined H` (Part1:88) is the conjunction m > 0 and Q(H) ≠ 0.
`homophily H` (Part1:90) returns `some (N(H)/Q(H))` when that conjunction holds,
and returns `none` otherwise. Its return type is `Option ℝ`, so `none` denotes
absence, not a real zero.

For b equal to false or true, `traitDegree H b` (Part1:119) is the natural
number D_b = Σ(v in V with t(v)=b) d(v). These are degree totals over all
vertices, not vertex counts or totals over any sampled subset.

`annealingObjective ε h p` (Part6:8–9) is the real number
f_ε(h,p) = 1/(1+ε+h), for three real arguments ε,h,p. The argument p is ignored.
`squareObjectiveValues ε` (Part6:11–14) is the set of real r for which there
exist real h and p, each between -1 and 1 inclusive, such that
r = 1/(1+ε+h). No graph, data, compatibility, or attainability by a graph is
required for membership.

`hNumerator._proof_1`, a generated auxiliary declaration at Part1:0, proves
the natural-number fact `(1+1).AtLeastTwo` using
`Nat.instAtLeastTwoHAddOfNat 1`. It supports the numeral 2; it imposes no
assumption on H or on a denominator and contains no additional graph notion.

This accounts for all 20 declarations in the supplied dependency closure,
including the State constructor and three projections. `T24Statement` itself
is unfolded immediately below. Other definitions appearing in Part1 are not
dependencies of this statement.

### Quantifiers, hypotheses, and conclusion

`T24` asserts `T24Statement` (Part6:16–26). For every real ε, if ε > 0, the
following four assertions hold together:

1. For every real h with -1 ≤ h ≤ 1, and then every real p with -1 ≤ p ≤ 1,
   0 < 1/(1+ε+h) ≤ 1/ε.
2. 1/ε is a greatest element of the set of scalar square values defined above.
   In Mathlib, `IsGreatest S a` means both a ∈ S and
   ∀ r ∈ S, r ≤ a. In particular there exist h,p in the square with
   1/ε = 1/(1+ε+h); this is an attained scalar maximum, not merely a supremum.
3. f_ε(-1,0) = 1/ε. This supplies one specific square maximizer. There is no
   uniqueness assertion; p is inactive.
4. For every State H, if Simple H, then if D_false > 0, then if D_true > 0,
   all of the following hold: m > 0; Q(H) ≠ 0;
   homophily H = some (N(H)/Q(H)); -1 ≤ N(H)/Q(H) ≤ 1;
   and 0 < 1/(1+ε+N(H)/Q(H)) ≤ 1/ε. The p argument is fixed to zero here.

The order is ε, its positivity assumption, the conjunction of assertions,
and within the graph assertion H followed by the three graph hypotheses.
There is no data set, compatible graph space, Markov chain, proposal law,
cooling schedule, convergence quantifier, communication depth, preferential
recruitment statistic, or maximizer in a compatible graph space in this
statement. Positive degree totals in both trait classes are substantive graph
hypotheses and exclude trait classes consisting only of isolated vertices.

### Docstring as read blindly

The docstring describes positivity, the attained scalar square maximum 1/ε,
and the bound at ordinary binary graph correlations. Its restriction sentence
explicitly limits the graph result to finite simple binary-trait graphs with
positive all-vertex degree totals in both classes, takes the second coordinate
to be zero, and disclaims any defined preferential statistic or compatible
graph attaining 1/ε. It explicitly omits annealing convergence, certification
of proposals and the cooling schedule, communication-depth assertions, maxima
on arbitrary compatible spaces, the cited convergence implication, and a
divergence assertion. Assessment against the canonical claim is deferred.

### Totalization and junk-value audit

- Real division is total in Lean: x/0 = 0. Consequently the bare objective
  has value 0 at a zero denominator. In the square assertion, however,
  1+ε+h ≥ ε > 0. Its bound 1/ε is also well-defined because ε > 0.
  The explicit square maximizer has denominator ε.
- In an arbitrary State, m can be zero and Q(H) can be zero. The terms involving
  2m and the final quotient are still real numbers by totalized division.
  The `Option` guard returns none if m=0 or Q(H)=0. In the theorem's graph
  branch, simplicity and the positive degree totals rule these cases out:
  D_false + D_true = 2m, and
  Q(H) = D_true - D_true²/(2m) = D_false D_true/(2m) > 0.
  Thus neither homophily nor the stated graph objective relies on division
  by zero. The asserted homophily range makes the graph objective's denominator
  at least ε > 0 as well.
- Finset sums over empty sets are 0; cards of empty sets are 0. The square
  value set is nonempty (h=-1,p=0). The positive graph degree totals exclude
  an empty vertex set, an empty edge set, and either trait class having no
  positive-degree vertex. Other isolated vertices are harmless.
- Natural-number cards and degree sums are cast exactly into ℝ. There is no
  natural-number subtraction or division in this closure and no truncation
  issue. The `2 * (card : ℝ)` denominator is real multiplication.
- Boolean if-then-else and the total trait function introduce no partial
  lookup or default value. Although traits exist for all labels, the finite
  sums use V, and simplicity puts every edge endpoint in V. Out-of-V traits
  do not affect the graph branch.
- There are no logarithms, square roots, real powers, integrals, expectations,
  conditional laws, extended reals, `toReal`, infima, suprema, liminf/limsup,
  or defaults of partial functions in this dependency closure. In particular,
  the greatest-element assertion uses membership and upper bounds directly,
  so it does not depend on the conventions for `sSup` of an empty or
  unbounded set.

The graph hypotheses have a straightforward candidate model: two distinct
vertices joined by one edge, with opposite traits. Its two degree totals are
1, N=-1/2, Q=1/2, and homophily=-1. A kernel-checked construction is deferred
to the claim-comparison stage.
