# Blind reading

This file was saved before opening `claims.json` or `record.json`. The source
docstrings and statements, all declarations listed in `closure.json`, and their
generated Lean auxiliaries have been read. `scratch/Closure.lean` prints all 105
distinct closure declarations; its successful output is `scratch/Closure.txt`.
The generated constructors, projections, recursors, pattern-match functions,
deciders, and proofs that numeric denominators are at least two have their usual
structural meanings. None adds a mathematical hypothesis.

Throughout, a big-O assertion for real-valued functions means that there is a
real constant C such that eventually |f| <= C |g|. For `atTop` on the naturals,
eventually means for every n beyond some natural threshold. For `atTop` on
natural pairs, there are thresholds N and M and the inequality holds for all
n >= N and K >= M. Constants may depend on parameters quantified before the
big-O assertion, but not on the indices inside it.

## SAP.P003b.T36

Location: `SAP/P003b/Challenge/Part1.lean:135-144`; its proposition is
`T36WholeStatement`, defined at `SAP/P003b/Defs/WholeW2.lean:304`.

### Objects and complete expansion of the definitions

A count vector is an ordered quadruple v=(a,b,c,d) of natural numbers,
advertised as counts of the binary potential-outcome types (11,10,01,00).
Its total is a+b+c+d, a natural number; its effect numerator is the integer
b-c. There is no positive-total or positive-arm restriction on a count vector.

Fix observed counts o=(A,B,C,D), and put n=A+B+C+D. The list P(o) of possible
vectors is constructed by the nested loops

* i=0,...,A;
* h=0,...,B;
* k=0,...,C;
* l=0,...,D;

with output (i+k, A-i+l, C-k+h, B+D-h-l). These loops are in that order;
outputs are retained with multiplicity. `Possible o v` means list membership
v in P(o). These are precisely the missing-outcome completions represented by
these four integer choices, rather than an independently assumed predicate.

The candidate-numerator list X(o) is

    [A-C-(A+B)+s : s=0,...,n],

with the subtraction performed in the integers. Thus it runs from -B-C to
A+D in steps of one and has n+1 entries.

For integer x and natural j, G(o,x,j) is the sublist of P(o) satisfying b-c=x
and a+b=j. `minimumB` returns `none` on the empty list; on a nonempty list it
selects a vector with the least b, with the earlier entry winning a tie.
`firstOnLine o x j` is that selection from G(o,x,j). This selection is defined
by exhaustive enumeration, without a hypothesis asserting feasibility.

Write all the following bounds in the integers:

    L(o,x,j) = max(0, x, j-A-C, A+C+x-j),
    U(o,x,j) = min(j, A+D, B+C+x, n+x-j).

The four guards are x+C<=j, A<=j, j+B<=n, and j<=A+x+B+C.
The fast selector is `none` unless all four guards hold and L<=U. Otherwise
it returns

    (j-b, b, max(b-x,0), max(n-j-b+x,0)),   b=max(L,0),

where the first subtraction is natural truncated subtraction and the other
two displayed maxima are integer-to-natural conversions. This is exactly the
definition using `lineVector` and `Int.toNat`, not yet a claim that truncation
cannot occur. The bounds in the successful branch include L>=0 and U<=j.

For any vector v and natural k, its reuse vector is

    R(v,k)=(max(v.a-k,0), v.b+k, v.c+k, max(v.d-k,0)).

The exhaustive reuse list H(o,v) contains, in increasing order, the integers
k=1,...,n satisfying k<=v.a, k<=v.d, and R(v,k) in P(o). Its length is a
natural number. The fast reuse list for (o,x,j,v) is the increasing list

    [1,..., max(max(U(o,x,j),0)-v.b,0)].

This last definition is meaningful for arbitrary data; the equality to legal
reuse is asserted only when v is the selected feasible minimum.

There is a Boolean parameter full. For each x, form the list of pairs (j,v)
for j=0,...,n whose fast selector returns `some v`. When full=true, retain
the entire list; when full=false, retain only its first pair. Call the result
B_full(o,x). Define the following natural counts for every natural K:

    draws_full(o,K) = sum over x in X(o) of K * length(B_full(o,x));
    updates_full(o,K) = sum over x in X(o), (j,v) in B_full(o,x)
                         of K * length(fast reuse list(o,x,j,v)).

For real coefficients c0,c1,c2, the real arithmetic charge is

    C_full(o,K) = c0*(n+1)^2 + 2*c1*n*draws_full(o,K)
                              + 2*c2*updates_full(o,K).

All natural counts are cast exactly to the reals in this expression. The
real envelope is

    E(n,K)=(n+1)^2 * (c0+2*(c1+c2)*K*n).

These are specified arithmetic charges. The definition does not measure the
running time of Lean's enumeration of `possibleTables` or `filterMap`.
The docstring explicitly describes constant-cost estimand/statistic
evaluation, linear-cost fresh drawing and scanning, constant-cost reuse,
bookkeeping and insertion, rather than bit complexity.

### Full proposition, including quantifier order

The proposition is the conjunction of these four assertions:

1. For every count quadruple o, every integer x, and every natural j, the
   fast selector equals the exhaustive minimum-b selector as options.
2. For every o and v, then every integer x and natural j, if the exhaustive
   selector returns `some v`, the fast reuse list equals H(o,v) as lists.
3. For every Boolean full, count quadruple o, natural K, and real c0,c1,c2,
   if c0,c1,c2 are all nonnegative, all of the following hold:
   draws_full<=(n+1)^2*K; updates_full<=(n+1)^2*n*K;
   0<=C_full<=E(n,K); and, if in addition 1<=n and 1<=K,

       C_full(o,K) <= 4*(c0+2*(c1+c2))*K*n^3.

   The last two positivity conditions apply only to the last inequality.
4. For every full and every fixed real c0,c1,c2, assuming their
   nonnegativity, both of these hold:
   * for every family o:Nat x Nat -> Counts with total(o(n,K))=n for every
     pair, C_full(o(n,K),K)=O(K*n^3) as both indices tend to infinity;
   * for every family o:Nat->Counts and every K:Nat->Nat, if total(o(n))=n
     for every n and K(n)>=1 eventually, then
     C_full(o(n),K(n))=O(K(n)*n^3) as n tends to infinity.

There is no hypothesis about treatment balance, arm positivity, a significance
level, a statistic or estimand function, a randomization distribution, or
independence. Such objects are not arguments to this deterministic cost
statement. The coefficients are fixed outside each big-O, so the result does
not allow a coefficient increasing with n. Both schedule choices and every
eventually positive sequence K(n), including a constant positive K, are
covered.

### Junk-value and boundary audit

* Every natural subtraction is truncated at zero. In P(o), the loop ranges
  imply i<=A, k<=C, and h+l<=B+D, so all the subtractions agree with
  nonnegative integer subtraction. The candidate effects and L,U,guards use
  signed integers and preserve negative effects.
* `lineVector` truncates j-b and maps negative integer coordinates to zero.
  In the fast selector's successful branch, the lower and upper bounds ensure
  b>=0, b<=j, b>=x, and b<=n+x-j, preventing these conversions from
  silently altering a feasible vector. On arbitrary standalone arguments
  `lineVector` can represent a clipped vector; no such standalone semantic
  identity is asserted here.
* `reuseVector` truncates v.a-k and v.d-k. H(o,v) explicitly imposes the two
  inequalities preventing this. Equality of the fast reuse list with H is
  conditional on a genuinely selected base. The fast list's `.toNat` and
  subsequent natural subtraction produce an empty list when the upper bound
  is negative or below v.b; the theorem does not interpret this arbitrary
  case as a legal nonempty interval.
* Empty feasible groups return `none`. Empty base lists, empty reuse lists,
  and `take 1 []` contribute zero to the counts. There is no hidden default
  vector. Ties in minimum-b selection are resolved by the list's order;
  duplicate completions do not create extra selected bases per (x,j).
* n=0 and K=0 are permitted in the finite envelope assertions. In particular,
  the overhead c0*(n+1)^2 need not vanish for K=0. The Kn^3 comparison excludes
  these cases, and the asymptotic assertions eventually have n,K>=1.
* Casts Nat->Int and Nat->Real are exact, with no machine overflow or
  unsigned subtraction used for effect numerators.
* There is no division, logarithm, square root, real power, integral, extended
  real value, infimum/supremum, limit superior/inferior, or partial indexing
  in the substantive T36 definitions. The named `_proof` auxiliaries merely
  discharge numeral instances; they do not introduce such operations.
* `atTop` on Nat and on Nat x Nat is nontrivial; the asymptotic statements
  are not made true by an empty filter. Total-n families exist, including
  (0,0,0,n), so their total constraints are not contradictory.

## SAP.P003b.T18

Location: `SAP/P003b/Challenge/Part1.lean:146-152`; its proposition is
`T18WholeStatement`, defined at `SAP/P003b/Defs/WholeW1.lean:111`.

### Complete expansion of finite objects, algorithms and costs

Here again a Counts object is an arbitrary quadruple of naturals. For
o=(A,B,C,D), n=A+B+C+D, its completion list is

    P(o)=[(i+k,A-i+l,C-k+h,B+D-h-l) :
           0<=i<=A, 0<=h<=B, 0<=k<=C, 0<=l<=D]

in the displayed nested-loop order, retaining duplicates. Its candidate
numerators are X(o)=[-B-C,...,A+D]. On a line (x,j), retain the completion
vectors v with integer v.b-v.c=x and v.a+v.b=j; return `none` if there are
none, otherwise the first vector with minimum v.b. Denote this optional
selection by F(o,x,j). This unfolds `Possible`, `possibleTables`,
`lineGroup`, `minimumB`, `firstOnLine`, `Counts.total`, and `Counts.effect`.

For a vector v, R(v,k)=(v.a-k,v.b+k,v.c+k,v.d-k), where the first and last
subtractions are natural truncated subtraction. H(o,v) is the ascending list
of k=1,...,n with k<=v.a, k<=v.d and R(v,k) in P(o).

The full-line draw count D_g(o,K) is K times the number of pairs
(x,j), x in X(o), j=0,...,n, at which F(o,x,j) is `some`. The full-line
update count U_g(o,K) sums K*length(H(o,v)) over these selected bases.
For the literal schedule, at each x take only the first feasible j in the
ascending scan; no selected j gives no base. D_l(o,K) charges K for each
selected base, and U_l(o,K) charges K*length(H(o,v)). The two real operation
charges, for s=g or l, are

    C_s(o,K)=c0*(n+1)^2+2*c1*n*D_s(o,K)+2*c2*U_s(o,K).

The general envelope is E(n,K)=(n+1)^2*(c0+2*(c1+c2)*K*n).
These definitions count abstract operations, without charging the runtime
of their exhaustive Lean list implementations.

For the remaining definitions, write log for Mathlib's real natural log,
L2(n)=log(n)/log(2), and define

    K_e(n) = natural ceiling of log(4*n*L2(n)/e)/(2*e^2),
    B_e,c(n) = 4*c*K_e(n)*n^2*L2(n),
    D(n) = (n+1)*(Nat.log2(n+1)+3).

The natural ceiling is clipped at zero. `Nat.log2` is the integer binary
logarithm, whereas L2 is a real quotient of real logarithms.

An assignment of size m in n labels is a finite subset z of {0,...,n-1}
whose cardinality equals m. No probability law is built into this type.
A pool is a function

    {0,...,2*D(n)} x {0,...,K-1} -> {assignments of size n/2 in n labels}.

The probability of an event on any finite type Omega is its number of
elements divided by |Omega|, with the division in the reals. When applied to
this entire function type of pools, this is the uniform product law: all
coordinates are independent uniform assignments, with replacement.

The canonical labeled binary table of v places its a copies of (1,1)
first, then b copies of (1,0), then c copies of (0,1), followed by (0,0).
More precisely the comparisons are i<a, i<a+b, i<a+b+c, with the last
case returning (0,0), including indices beyond total(v). For a finite subset
z of n labels, its observation has coordinates: treated labels with first
outcome one; treated labels with first outcome zero; untreated labels with
second outcome one; untreated labels with second outcome zero. These are
finite-set cardinalities, with no stochastic assumption.

For any v,o and natural m, define the integer

    Q(v,o,m)=N*((N-m)*o.a-m*o.c)-m*(N-m)*(v.b-v.c), N=total(v).

The subtractions in this formula are signed integer subtraction. At batch
number idx, take the pool coordinate idx modulo (2*D(n)+1). The rational
Monte Carlo mean for candidate v and observed o is

    (1/K) * sum over i<K of
      1{|Q(v, canonical observation(v,pool[idx,i]), A+B)|
                                             >= |Q(v,o,A+B)|}.

The absolute values in the implementation are integer `natAbs`, so the
comparison is exact. Reject the candidate when this mean (cast to a real)
plus epsilon is strictly less than alpha.

The candidate-test list at an integer x is built by scanning j=0,...,n.
Skip a `none` selection F(o,x,j). For a selected v, usually append [v].
If v.b=v.c=0, v.a>=1, v.d>=1 and (v.a-1,1,1,v.d-1) is possible, append
[v,(v.a-1,1,1,v.d-1)] instead. On each candidate list, test in order,
incrementing idx for every performed test, and stop at the first
non-rejection. Return a Boolean saying whether such a non-rejection was
found, the next idx, and the list of performed (vector,rejection) pairs.
The empty list returns false, the old idx, and the empty trace. This unfolds
the three fields and constructor of `QueryResult` and `runTests`.

The upper search defines k1=2*(A-C), k2=A-C+(A+B). In corrected mode its
initial bracket is (k1-1,k2+1) and fuel is n+3. At each call, if b<=a+1,
return `some a` and an empty new trace. Otherwise, if fuel is zero, return
`none` and the empty trace. Otherwise set c=(a+b)/2 using integer division,
test the candidate list at c, replace a by c when the query is compatible,
or replace b by c otherwise, and recurse with fuel reduced by one and the
returned idx. Concatenate the query and recursive traces. `EndpointResult`
consists of this optional integer value and the trace.

For completeness the same `adaptiveSearch` definition has an uncorrected
branch: it starts at (k1,k2); after a midpoint update giving b'=a'+1 it
returns a' for an interior bracket, otherwise additionally tests k1 or k2
when that bound is reached, returning that bound if compatible and its
predecessor otherwise. If no such branch applies it returns `none`.
This branch is not used by the shuffle-cost statements.

For a balanced pool and the corrected upper search just defined, its full
shuffle charge is

    S(alpha,epsilon,o,pool) = trace length * K * (n-1),

with natural subtraction in n-1. This charges n-1 shuffle steps for each
of the K draws in every performed test. Its expected cost F(alpha,epsilon,
n,K,o) is the real sum of S over every pool divided by the number of pools.
It is conditional on fixed o and counts only the upper endpoint search.
It does not add the lower endpoint, observation randomization, or other
arithmetic work. The counterexample family is n=2^r, m=n/2,
o=(0,n/2,0,n/2), alpha=1/2, epsilon=1/8.

### Full proposition, including quantifier order

`T18WholeStatement` is a conjunction of all the following assertions:

1. For every real alpha,epsilon,c satisfying 0<alpha<1, 0<epsilon<alpha,
   c>=0, every tests:Nat->Nat, and every operations:Nat->Real, if operations
   is nonnegative for every n, tests(n)<=4*n*L2(n) eventually, and
   operations(n)<=tests(n)*K_epsilon(n)*(c*n) eventually, then
   operations(n)=O(n^2*(log n)^2). The premises supply, rather than derive,
   the relation of this arbitrary operation sequence to the test count.
2. For every natural r,K with r>=4 and K>0, for the dyadic family above,
   the event S >= (n/4+1)*K*(n-1) has strictly positive probability under
   the uniform law on all pools. In addition, if r>=6 and the real cast of
   K is at least 32*log(32*n*L2(n)), then

       F(1/2,1/8,n,K,o) >= (n/4+1)*K*(n-1)/2.

3. For every real c>=0, with K=K_(1/8)(n) on that dyadic family, the
   expected-cost function of r is NOT O(n*(log n)^c), as r tends to infinity.
4. For every natural n>=15, L2(n)<=(log n)^2.
5. For every natural n,K,t and real c,O, assuming c>=0,
   t<=4*n*L2(n) and O<=t*K*(c*n), all these hold:

       t*K <= 4*K*n*L2(n),
       O <= 4*c*K*n^2*L2(n),
       (4*n*L2(n))*K*(c*n) = 4*c*K*n^2*L2(n).

   O need not be nonnegative in this finite algebraic assertion.
6. For every fixed real epsilon>0 and every tests:Nat->Nat satisfying
   tests(n)<=4*n*L2(n) eventually,
   tests(n)*K_epsilon(n)=O(n*(log n)^2).
   Also, for every fixed epsilon>0 and c>=0, B_epsilon,c is both
   O(n^2*(log n)^2) and

       O(n^2*log(n)/epsilon^2 * log(n*log(n)/epsilon)).

   Epsilon is fixed outside each big-O; these are not uniform two-variable
   assertions as epsilon tends to zero.
7. For every o,K and real c0,c1,c2, if the coefficients are nonnegative,
   D_g<=(n+1)^2*K, U_g<=(n+1)^2*n*K, C_g<=E(n,K), and, when n,K>=1,
   C_g<=4*(c0+2*(c1+c2))*K*n^3. In addition, for every fixed set of
   nonnegative coefficients, and every o:Nat x Nat->Counts with total
   o(n,K)=n for all pairs and with both A+B>0 and C+D>0 eventually in the
   product filter, C_g(o(n,K),K)=O(K*n^3) jointly in n and K.
8. For every o,K,c0,c1,c2 with nonnegative coefficients and n,K>=1,
   D_l<=D_g, U_l<=U_g, C_l<=C_g, and
   C_l<=4*(c0+2*(c1+c2))*K*n^3.
9. For every natural n>=15 and every real epsilon>0,

       log(4*n*L2(n)/epsilon)/(2*epsilon^2)
          <= log(4*n*(log n)^2/epsilon)/(2*epsilon^2),

   and K_epsilon(n) is at most the natural ceiling of the right-hand side.
   The real inequality does not say that the unrounded number is already
   a natural sample size.
10. For EVERY real q, including negative q, the dyadic expected-cost
    function in item 3 is NOT O(n*(log n)^q). This final conjunct strengthens
    item 3's restriction c>=0.

The general finite bounds of item 7 are unrestricted by balance or positive
arms. Their product-filter order bound includes a positive-arm hypothesis.
The finite bounds already give a pointwise constant valid for every positive
K, including fixed K. The balanced upper assertions use arbitrary test and
cost sequences subject to the displayed premises; they do not themselves
identify such sequences with the actual search trace. The full-shuffle
lower statements do identify their charge with that trace. No refutation
label or assertion that the canonical printed claim is false appears in
this theorem's docstring.

### Junk-value and boundary audit

* The completion list's natural subtractions are safe by its loop ranges.
  H(o,v) guards the two subtractions in R(v,k). The exceptional second
  candidate has explicit v.a,v.d>=1 guards. Signed effect numerators and
  deviation numerators use integers, with no natural truncation there.
* `Nat.log2(0)=0`; its use is at n+1>=1. The natural divisions n/2,n/4
  are floor divisions. For the lower-bound family r>=4 (or r>=6), n=2^r
  is divisible by both 2 and 4, and n-1 is ordinary positive subtraction.
  In the unrestricted cost definition n=0 gives n-1=0, but none of the
  asserted lower bounds uses that value.
* Mathlib has log(0)=0 and log(-x)=log(x). Thus L2(0)=L2(1)=0, and
  K_epsilon(0)=K_epsilon(1)=0. Division in reals or rationals at zero
  returns zero. K_0(n) is consequently a defined junk value, not a valid
  positive-tolerance budget. All substantive epsilon assertions assume
  epsilon>0 or use epsilon=1/8. For fixed positive epsilon the logarithm
  arguments are positive eventually; for the finite budget comparison
  n>=15 already ensures positivity. The natural ceiling of a nonpositive
  real is zero, so a very large epsilon can give K_epsilon(n)=0 at small
  n; the asymptotic statements do not require positive K there.
* The denominator log(2) is positive. The denominators 2*epsilon^2 are
  positive under the stated epsilon hypotheses. The denominator K in
  `monteMean` would give zero for K=0; every finite probabilistic lower bound
  assumes K>0. On the asymptotic family with epsilon=1/8, the prescribed
  K is positive eventually.
* Empty finite probability spaces would give cardinality/0=0 in
  `uniformProb` and in the finite mean. Here the assignments have size
  n/2<=n, so they exist, and their finite function spaces of pools are
  nonempty. In particular the dyadic family is a genuine probability space.
  `Fin 0` can appear at K=0, in which case a function with that argument
  has no draws; that case is excluded from the finite lower assertions.
* Pool indexing uses modulo 2*D(n)+1, always a positive integer. It is not
  a partial read. It would reuse batches if the trace exceeded the pool
  length; independence of successive performed tests therefore needs a
  bound on the number of tests. The corrected balanced search has a finite
  midpoint depth and at most two tests per j at any query, so this issue
  must be checked rather than assuming that modulo indexing is fresh.
* `canonicalPair` defaults to (0,0) outside the first three blocks. When
  ambient n=total(v), this is the intended d block. The lower-bound family
  has total(o)=n, and the search's candidate tables are selected from
  completions of o; there is no intended table-length mismatch.
* Integer midpoint division is Euclidean division by the positive integer
  2 (rounding down), even for negative midpoints. Fuel exhaustion gives
  `none`, rather than a default endpoint. The shuffle charge counts a trace
  even if the optional endpoint is `none`; it does not divide by that
  endpoint or use a default integer. Lower-bound family brackets are valid.
* Empty candidate lists and searches with no tests have zero trace length.
  Their fresh-draw charge is zero. The `head?` used by the literal schedule
  returns `none` on an empty list, not a default count vector.
* Real powers occur only as (log n)^q in the asymptotic comparison. The
  dyadic n is eventually >1, so its base is positive and this is the usual
  real power, even for negative q. At n=1, Mathlib's 0^0=1 and 0^q=0 for
  nonzero real q only affect an initial index. No asserted asymptotic
  obstruction uses those conventions.
* All sums and means here are finite. There are no Bochner integrals,
  nonintegrable expectations, infinities, `toReal`, `sInf`/`sSup`, square
  roots, `limsup`/`liminf`, or default partial-array reads in this closure.
  The real mean of the bounded finite shuffle charge is well-defined.
  Nat/Int/Real/Rat casts preserve the counted values exactly.
