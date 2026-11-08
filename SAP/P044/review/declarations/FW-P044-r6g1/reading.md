# Blind reading of P044-T1 through P044-T5

Saved at step 1, before opening either `claims.json` or `record.json`.
I read all source definitions in the five closures, and printed the generated
recursors, matchers, projections, and auxiliary declaration types in
`scratch/closure-print.log`. There are 133 distinct closure entries. Generated
proofs certify numeral bounds, finite-index bounds, or the derived equality
decision procedure; the matchers have the ordinary four-constructor behavior.

The following notation is an explicit mathematical expansion of the shared
definitions, and applies wherever it is used in each section below. No
probability or sampling assumptions are implicit in this notation.

* A size-N assignment is a function `{0,...,N-1} → {false,true}`. An adjacency
  matrix is an arbitrary Boolean function on two such indices; symmetry and a
  zero diagonal are imposed only where explicitly stated. The peer count is
  `c_i(z)=Σ_j 1{A(i,j)=true and z(j)=true}` (a natural number). The four-element
  exposure type has distinct values 11,10,01,00. Its exposure map is the pair
  `(z(i),1{c_i(z)>0})`, with the pair encoded by the corresponding value.
* A finite design on a finite type Ω is a real function p with `p(ω)≥0` for
  every ω and `Σ_ω p(ω)=1`. Plain weight functions in rational formulas are not
  automatically designs. `E_p t=Σ_ω p(ω)t(ω)` and
  `Var_p(t)=Σ_ω p(ω)t(ω)^2-(Σ_ω p(ω)t(ω))^2`.
* For a map `f:Ω→{0,...,N-1}→D` into a type with decidable equality and a
  schedule `y:{0,...,N-1}→D→K`, define
  `p_i(d)=Σ_ω 1{f(ω,i)=d}p(ω)` and
  `p_ij(d,e)=Σ_ω 1{f(ω,i)=d and f(ω,j)=e}p(ω)`.
  Write `I_i^d(ω)=1{f(ω,i)=d}`. Given numeric tables w and q, the HT term
  is `y_i(d)/w_i(d)` when `f(ω,i)=d`, and 0 otherwise. Thus
  `H_d(ω)=N^(-1)Σ_i I_i^d(ω)y_i(d)/w_i(d)`,
  `T(ω)=H_a(ω)-H_b(ω)`, and
  `τ(y,a,b)=N^(-1)Σ_i(y_i(a)-y_i(b))`.
* The within-exposure total used for variance is the following sum over
  **ordered** pairs i,j:
  `U_d(ω)=Σ_{i,j:q_ij(d,d)>0} I_i^d I_j^d y_i(d)y_j(d)
  (1/(w_i(d)w_j(d))-1/q_ij(d,d))
  +Σ_{i≠j:q_ij(d,d)=0}(I_i^d y_i(d)^2/(2w_i(d))
  +I_j^d y_j(d)^2/(2w_j(d)))`.
  The cross total is
  `C_ab(ω)=Σ_{i,j:q_ij(a,b)>0} I_i^a I_j^b y_i(a)y_j(b)
  (1/(w_i(a)w_j(b))-1/q_ij(a,b))
  -Σ_{i,j:q_ij(a,b)=0}(I_i^a y_i(a)^2/(2w_i(a))
  +I_j^b y_j(b)^2/(2w_j(b)))`.
  The variance estimate is `V(ω)=(U_a(ω)+U_b(ω)-2C_ab(ω))/N^2`.
  These formulas mean conditional branches, so a q-denominator is evaluated
  in a contributing branch only when q>0. If q<0 neither branch contributes.
* For a bank `g:{0,...,R-1}→{0,...,N-1}→D`, let
  `C_i(d)=#{r:g(r,i)=d}` and
  `C_ij(d,e)=#{r:g(r,i)=d and g(r,j)=e}`.
  Smoothed weights are `(C_i(d)+1)/(R+1)`. Smoothed joints are
  `(C_ij(d,d)+1{i=j})/(R+1)` if d=e, and `C_ij(d,e)/R` otherwise.

## SAP.P044.T1

This is a closed conjunction of rational identities and inequalities, with no
outer assumptions. The data are twelve vertices indexed 0 through 11, split
into cliques `{0,1,2,3}`, `{4,5,6,7}`, `{8,9,10,11}`. An edge joins distinct
vertices with equal integer quotient by 4. The 66 assignment indices enumerate
all unordered pairs `(u,v)` with `u<v` in lexicographic order; exactly u and v
are treated. The exposure function is explicitly: treated vertices have 11
when u,v are in one clique and 10 otherwise; untreated vertices have 01 when
their clique contains u or v and 00 otherwise. Every potential outcome is 1.
The design mass is 1/66.

For a deleted index t, the bank consists of all 65 assignments except t,
enumerated using the order-preserving skip map from 65 indices into 66.
The counts for every vertex under the full bank are
`c(11)=3,c(10)=8,c(01)=27,c(00)=28`. The hard-coded full joint table has
diagonal `1{d=e}c(d)` and, off diagonal, entries
`c_ij(01,01)=17` in one clique and 9 between cliques,
`c_ij(00,00)=28` in one clique and 6 between cliques, and
`c_ij(01,00)=c_ij(00,01)=0` in one clique and 15 between cliques.
Other entries are computed as actual counts. For the bank missing t,
`w_i^t(d)=(c(d)-1{f(t,i)=d}+1)/66`, and, writing
`c=c_ij(d,e)-1{f(t,i)=d,f(t,j)=e}`,
`q_ij^t(d,e)=(c+1{i=j})/66` if d=e and `c/65` otherwise.
Here the subtractions in c and w occur in the natural numbers.
Let `T(t,z)` and `V(t,z)` be the expanded HT contrast and variance estimate
above for exposures a=01,b=00 with these tables.

The theorem asserts all of the following.

1. The explicit f equals the adjacency-based exposure map. The assignments
   are injective and exhaust exactly all two-treated profiles. The graph is
   symmetric, loopless, and has no isolates. For each vertex, exact
   probabilities are `p_i(01)=9/22,p_i(00)=14/33`. Each retained assignment
   list is injective and avoids its deleted assignment. Both relevant
   smoothed weights are positive. The target τ is zero.
2. With the exact marginal and joint tables, the contrast expectation is 0,
   its variance is `6050/11907`, and the variance estimate has expectation
   `6050/11907`.
3. On pairs (t,z), the `included=false` mass is `1/4356` everywhere.
   The `included=true` mass is 0 when t=z and `1/4290` otherwise. Thus in the
   former law the deleted assignment and observation are independent uniform
   indices; in the latter the observation is uniform among the retained
   rows. These definitions do not generate independent draws within a bank.
   In the former law, the mean, variance, expected variance estimate, and
   their last-two difference are, respectively,
   `-67/53592`, `113448938731/232640299584`,
   `1040129476423/2326402995840`, `-953130413/23499020160`.
   In the latter they are
   `-67/52780`, `11375808887/23342482800`,
   `4673362763/10414338480`, `-20161943/522324075`.
   For **each** Boolean choice, expected V is strictly below the variance
   of T and strictly below `6050/11907`.
4. For fixed t=0 the variance and expected V over uniform z are
   `2810528137/5767941312` and `267260522663/634473544320`.
   For t=3 they are `937589375/1922647104` and
   `4830430961/10574559072`. More generally, every t in the same-clique case
   has the first pair and gap `-1551761941/23499020160`, and every other t
   has the second pair and gap `-72513467/2349902016`; each gap is negative.
5. All the individual 01 and 00 counts and the three joint-count formulas
   above hold for actual counted exposures. An assignment in one clique has
   two 01 and eight 00 vertices; one in different cliques has six 01 and
   four 00 vertices. There are 18 assignments of the first kind and 48 of
   the second. With exact marginals, T is `-220/189` in the first kind and
   `55/126` in the second.
6. For every deleted t and vertex, the displayed w tables for 01,00 equal
   the smoothed weights of its actual retained bank. For every t,i,j and
   d,e in {01,00}, the q tables equal its smoothed joints.
   For every t there exists a vertex permutation preserving adjacency and
   sending the assignment t, by precomposition, to assignment 0 if its
   treated pair shares a clique and to assignment 3 otherwise.

The docstring calls these finite-input expected-variance shortfalls a
refutation of exact dominance for finite simulated inputs.

Junk conventions: rational division by 0 is 0, but N=12,R=65 and all literal
denominators are nonzero. Relevant marginal and smoothed weights are positive.
Zero q values are handled by the explicit adjustment branch rather than
division by 0. Natural subtraction truncates at 0, but full counts count the
very row being subtracted, so truncation does not change these tables.
Natural quotient by 4 is ordinary floor division; its denominator is nonzero.
Finite sums and arrays have nonempty, statically bounded index types.
There are no integrals, logarithms, square roots, real powers, extrema,
limits, infinities, or partial-function defaults in this statement.

## SAP.P044.T2

The statement is `T2Statement` (at base universes), a matching-family
conjunction for **every natural n**, the two size equalities for n=4998,
and a general error-transfer theorem. Nothing is assumed at the outer level.

The first universal part ranges, in order, over finite types Ω, arbitrary D
with decidable equality, N>0, a real finite design P on Ω, any f and real y,
then distinct a,b, then strictly positive exact marginals for a and b at
**every vertex**. It asserts
`E_P V_exact - Var_P T_exact = S ≥ 0`, where the inequality is separately
stated as `Var_P T_exact ≤ E_P V_exact`, and the equality uses

`S=N^(-2)[Σ_{i≠j:p_ij(a,a)=0}(y_i(a)+y_j(a))^2/2
+Σ_{i≠j:p_ij(b,b)=0}(y_i(b)+y_j(b))^2/2
+Σ_{i,j:p_ij(a,b)=0}(y_i(a)-y_j(b))^2]`.

V and T are the formulas in the introduction, with `w=p_i,q=p_ij`.
The same `T2Statement` also asserts the two strict clique shortfalls from T1,
with exactly its graph, schedules, rational bank tables, and two pair masses.

For each n≥0 the matching family has `N=2(n+3)` vertices, in n+3 disjoint
edges `{2k,2k+1}`. The distinguished edge is k=0. The design has
`R=2(n+2)` assignments, indexed by `(b,r)∈{0,1}×{0,...,n+1}` using the
standard finite-product bijection. It treats the distinguished edge iff b=1,
and always treats precisely ordinary edge r+1. Other ordinary edges are
untreated. Outcomes at the two distinguished vertices are 1 for **every**
exposure; outcomes elsewhere are 0 for every exposure. A bank indexed by a
permutation e of all R indices is the entire exhaustive list in order e.
Its w and q are the smoothed count tables from the introduction. Its T,V
use a=11,b=00. Uniform mass on any finite type is the rational
`1/card(type)`. The independent joint mass on `(e,s)` is the product of
the uniform permutation mass and uniform assignment mass. The included
observation is specifically s=e(0).

For **every n**, the following are conclusions, not assumptions:

* The graph is symmetric, loopless, and nonisolated; the assignments are
  injective; exposure is 11 at treated vertices and 00 elsewhere; τ=0.
* Exact marginals at a distinguished vertex are 1/2 for 11 and 00.
  At ordinary vertices they are `1/(n+2)` for 11 and `(n+1)/(n+2)` for 00.
  They are zero for 10 and 01, and strictly positive for 11 and 00.
* All w entries (for every e,i,d) are strictly positive; all q entries are
  nonnegative; `q_ii(d,d)=w_i(d)`. At distinguished vertices and d in
  {11,00}, `w=(n+3)/(2n+5)`. For two distinguished vertices and relevant
  exposures, q is w on the equal-vertex equal-exposure diagonal,
  `q=(n+2)/(2n+5)` on unequal vertices with equal exposure, and 0 for
  unequal exposures. For each distinguished/ordinary pair in either order,
  all four relevant q entries are strictly positive.
* Every bank lists distinct assignment profiles and exhausts the design.
  All uniform assignment masses, uniform permutation masses, and independent
  pair masses are positive and sum to 1. The independent observation
  marginal is uniform, and the distribution of e(0) under uniform e is
  uniform. There is **no assertion that the R bank rows are independent**.
* With the abbreviations N,w,q above, under the product law, T has mean 0,
  variance `4/(N^2 w^2)`, and V has mean
  `(4/w^2+2/w-2/q)/N^2`. Under uniform e with observation e(0), these
  three values are exactly the same. Under **each** law,
  `E V-Var T=-2(2n+5)/((n+2)(n+3)N^2)<0`.

At n=4998 it additionally states R=10000 and N=10002.

Finally the error-transfer part universally quantifies finite types Ω,B,
arbitrary D with decidable equality, N>0, finite designs P on Ω and J on
B×Ω, and the hypothesis `Σ_t J(t,ω)=P(ω)` for each ω. It then quantifies
f,y,distinct a,b and strictly positive exact a,b marginals, followed by
arbitrary bank tables w(t),q(t). Extra hypotheses are `w(t,i,d)>0` for all
entries, `q(t,i,j,d,e)≥0` for all entries, and
`q(t,i,i,d,d)=w(t,i,d)` for all diagonal entries. No other consistency
or sampling property of those tables is imposed. With exact-input functions
V₀,T₀, input-table functions Vw,Tw on B×Ω, and the exact S displayed above,
it states

`E_J Vw-Var_J Tw = S+E_J(Vw-V₀∘projection)-(Var_J Tw-Var_P T₀)`.

For every pair of **nonnegative real** εV,εT, if the absolute expected
V-error is at most εV and the absolute variance error is at most εT, then
`Var_J Tw ≤ E_J Vw+εV+εT`. Dependence between t and ω is allowed.

The docstring describes exact-input conservativeness, finite-input failures,
an error correction, and a Hajek scope qualification. There is no Hajek
statistic or Hajek identity in the elaborated statement.

Junk conventions: the exact-input hypotheses ensure the only used marginal
denominators are positive; q division occurs only for q>0. N>0 is explicit.
A finite design forces Ω nonempty and, for J, B×Ω nonempty. The matching
sizes R≥4,N≥6 ensure nonempty assignment and permutation types and nonzero
uniform denominators. Its w,q closed formulas have positive denominators.
The clique portion has the T1 conventions. The transfer part requires all
w positive. Its error hypotheses allow arbitrarily large but finite errors;
they do not independently assert they are small. All expectations here are
finite sums of finite real/rational values. No integral, infinity, limit,
extremum, sqrt, log, or rpow junk value occurs.

## SAP.P044.T3

This is a closed conjunction. The graph is the four-vertex star with center
0: i,j are adjacent iff i≠j and (i=0 or j=0). The six profiles are, in order,
`0011,0101,0110,1001,1010,1100` with 1 meaning treated; their masses are 1/6.
Schedule A is 1 at every vertex/exposure. Schedule B is also 1 except at
vertex 0, exposure 00, where it is 5. Their values are rational, with real
casts in the statistic impossibility assertion.

It asserts that the graph is symmetric, loopless, nonisolated, of degree
vector `(3,1,1,1)`, and that these profiles are injective and exhaust exactly
the two-treated profiles. Exact marginal probabilities at the center, in
order 11,10,01,00, are `(1/2,0,1/2,0)`; at each leaf they are
`(1/6,1/3,1/3,1/6)`. Every observed outcome under A and B is 1. The effects
`τ(A,11,00)=0` and `τ(B,11,00)=-1` differ.

For **every** real-valued function T taking an assignment vector, an exposure
vector and an observed real outcome vector as arguments, its expected value
under A equals its expected value under B, and it cannot simultaneously have
expectation 0 under A and -1 under B. The quantifier permits any such function;
on the finite observation support all restrictions are automatically measurable.

The exact exposure vectors in profile order are
`(01,00,10,10)`, `(01,10,00,10)`, `(01,10,10,00)`,
`(11,01,01,11)`, `(11,01,11,01)`, `(11,11,01,01)`.
Every actually observed vertex/exposure has a positive exact marginal.
For both schedules, HT mean at 11 has expectation 1, HT mean at 00 has
expectation 3/4, and their contrast has expectation 1/4. Its bias is 1/4
for A and 5/4 for B. The inner `T3Statement` first phrases this last result
conditionally on observed-term positivity, but the enclosing whole statement
proves the positivity and repeats the result without that assumption.
For every one of the four exposures there exists at least one vertex having
strictly positive marginal for it.

Junk conventions: N=4 and all sampling masses have nonzero denominators.
Two center marginals are 0, but those exposures are never observed there.
The HT term is an `if`, returning 0 at such unobserved terms; no contributing
inverse uses a zero denominator. Consequently the mean and bias computations
do not rely on the numerical value assigned to division by zero. The absent
potential outcome is still a legitimate schedule value and contributes to τ.
There are no integrals, extrema, infinities, limits, sqrt, log, rpow, natural
subtraction, or out-of-range vector accesses.

## SAP.P044.T4

This conjunction has seven groups, with independent universal quantifiers.

1. For every finite Ω, arbitrary D with decidable equality, N>0, real finite
   design P, f,y,distinct a,b, and strictly positive exact a,b marginals at
   every vertex, each a and each b HT term has expectation its respective
   potential outcome; each HT mean has expectation its respective population
   mean; and the contrast has expectation τ. Everything uses exact marginals.
2. For every such Ω,D,N>0,P, but now arbitrary assignment function z, exposure
   function f and real schedule y, distinct a,b, a vertex j with
   `p_j(a)=0`, any real δ≠0, and **every** statistic T of assignment,
   exposure and observed outcome vectors, put
   `y'_i(d)=y_i(d)+δ` at (j,a) and `y_i(d)` elsewhere. On every sample point
   with positive mass, all observed outcomes agree. T has equal expectations
   under these two schedules, their targets differ by δ/N, and T cannot be
   unbiased under both. Neither f nor z must be injective or tied to a graph.
3. For every finite Ω,D,N,P,f,y and distinct a,b, let
   `S={i:p_i(a)>0 and p_i(b)>0}`. If S is nonempty, the expectation of
   `|S|^(-1)Σ_{i∈S}(I_i^a y_i(a)/p_i(a)-I_i^b y_i(b)/p_i(b))`
   equals `|S|^(-1)Σ_{i∈S}(y_i(a)-y_i(b))`. Nonempty S implies N>0.
4. For the four-vertex star, schedules A,B, and uniform six-profile law from
   T3, with a=11,b=00, S is exactly `{1,2,3}`. Both the S-target and the
   S-restricted HT contrast expectation are 0 for either schedule.
5. For every natural N,M, N>0, `1≤M≤N-1`, symmetric Boolean adjacency A
   with false diagonal, and vertex i, let k be its number of neighbors.
   Uniform complete randomization means all M-element subsets of N vertices,
   with probability of an exposure equal to its number of such subsets
   divided by the total number of subsets. It asserts
   `p_i(10)=binom(N-1-k,M-1)/binom(N,M)`,
   `p_i(00)=binom(N-1-k,M)/binom(N,M)`,
   `p_i(11)=M/N-p_i(10)`, `p_i(01)=(N-M)/N-p_i(00)`, and
   `[all four p_i(d)>0] ↔ [2≤M and 1≤k and k≤N-M-1]`.
6. For every symmetric loopless Boolean adjacency on 1000 vertices and every
   vertex, all four probabilities with M=100 are positive iff `1≤k≤899`.
7. For the star, the center's exact 00 and 10 probabilities are zero, even
   though no vertex is isolated and the center's degree is 3.

The statement proves the missing-a impossibility for a contrast; the missing-b
case follows by swapping a,b. The docstring describes support, corrected
common-support estimands, and complete-randomization formulas/criteria.

Junk conventions: general HT denominators are positive by hypothesis, or by
membership in S. N and |S| are nonzero where used. Finite designs exclude an
empty sample space. `completeProfiles` is the finite powerset of cardinality
M, and is empty if M>N; its count ratio would then be 0/0=0 in ℚ. That case
is excluded here by the treatment bounds. All natural differences in the
binomial formulas are truncated subtraction. The false diagonal gives
`k≤N-1`; M≥1 gives M-1≥0; M≤N-1 prevents truncation of N-M-1. Thus the
formulas coincide with ordinary nonnegative integer counting, including
binomial coefficients 0 when the lower argument is too large. Rational
denominators `binom(N,M)` and N are positive. Star calculations have the
same protected zero-support convention as T3. No continuous-measure or limit
junk values occur.

## SAP.P044.T5

This closed conjunction uses both real computations and actual Mathlib
Gaussian measures. For any Boolean adjacency on N vertices define
`d_i=Σ_j 1{A(i,j)=true}` and
`h_i=#{j:j≠i and there exists k with A(i,k)=true and A(k,j)=true}`.
This counts distinct endpoints of length-two walks other than i, including
endpoints that may already be neighbors; it does not count paths with
multiplicity. Put `a_i=d_i+h_i+d_i h_i` (a natural number). For real a,g,e,
`B_a(g,e)=a|g|+e`. The dilation schedule takes values
`(2B, (3/2)B, (5/4)B, B)` in exposure order 11,10,01,00.

The probability space is the product of a real Gaussian of mean 0 and
variance 1 with a real Gaussian of mean 1 and variance 1/16. Thus g,e are
independent, with e's standard deviation 1/4. `baselineLaw(a)` is the
pushforward of this product measure by B_a. `halfNormalLaw` is the
pushforward of the standard Gaussian by absolute value. Φ is the Mathlib
CDF of the standard Gaussian, equivalently its probability of `(-∞,x]`.

The theorem asserts:

1. On the loopless complete three-vertex triangle, every d_i and h_i is 2
   and every a_i is 8. For g-vector `(1/64,1,-1/2)` and e-vector
   `(-3/4,1,5/4)`, the baseline vector is `(-5/8,9,21/4)`, whose first
   component is negative. The number of two-step walks from i to j is 2
   if i=j and 1 otherwise, both as a product of adjacency entries and as
   a direct count. The four dilation vectors are
   `(-5/4,18,21/2)`, `(-15/16,27/2,63/8)`,
   `(-25/32,45/4,105/16)`, and `(-5/8,9,21/4)`.
2. For **every real a≥0**, the product-Gaussian probability of
   `|g|<1/(4(a+1)) and -1<e<-1/2` is strictly positive, and **every point**
   in this rectangle has `B_a(g,e)<-1/4`. Also the law of B_a gives
   positive probability to negative reals, the absolute-standard-Gaussian
   law gives that set probability 0, and the two laws differ.
3. The real-valued measure of
   `(-1/32,1/32)×(-1,-1/2)` equals the strictly positive number
   `(Φ(1/32)-Φ(-1/32))(Φ(-6)-Φ(-8))`. At **every** g,e in these two
   respective intervals, `B_8(g,e)<-1/4`.
4. The mean of |g| under the standard Gaussian is `sqrt(2/π)`, its variance
   is `1-2/π`, and its second raw moment is 1. For **every a≥0**, the
   mean of B_a is `a sqrt(2/π)+1`, and its variance is
   `a^2(1-2/π)+1/16`.
5. At a=8 these are `8sqrt(2/π)+1` and `64(1-2/π)+1/16`.
   Relative to |g| the mean shift is `7sqrt(2/π)+1>0`, and variance
   shift is `63(1-2/π)+1/16>0`.
6. For **every N**, arbitrary adjacency A with `d_i≥1` at every vertex,
   and every vertex i, the mean of `B_{a_i}` exceeds the half-normal mean
   by at least 1. No symmetry or zero-diagonal condition is imposed on A.
7. For **every real a**, B_a belongs to L² of the product Gaussian; |g|
   belongs to L² of the standard Gaussian. For **every a≥1**, the exact
   mean difference from |g| is `(a-1)sqrt(2/π)+1`.

The docstring identifies this as a refutation within the supplied ideal
Gaussian generator model, and explicitly leaves the connection to a staged
generator as external provenance. No program, program execution, seeded
randomness, or law of such an execution occurs in the statement.

Junk conventions: real/rational division has 0/0=0, but all displayed
constant denominators and π are nonzero. In the variable rectangle a≥0
makes a+1 strictly positive. `Real.sqrt` is total and equals 0 on negative
arguments, but 2/π is positive here. GaussianReal uses a nonnegative-real
**variance**, not a standard deviation; both variances are strictly positive
and hence neither is a Dirac fallback. A Bochner integral is 0 when its
integrand is nonintegrable; Mathlib's real variance takes `toReal` of an
extended nonnegative variance, giving 0 for infinite variance. Here explicit
L² conclusions and the finite Gaussian moments ensure these are genuine
integrals and finite variances. `Measure.real` also maps infinite mass to 0,
but all sets are under probability measures. A nonmeasurable pushforward
can use a default in Mathlib, but absolute value and B_a are continuous and
measurable, so these are actual distribution laws. For N=0 the universally
quantified vertex i does not exist; this harmless empty graph case does not
make the triangle or real-a assertions empty. Natural-to-real casts are
ordinary nonnegative casts; degree sums and counts do not use subtraction.
There are no logarithms, rpow, limits, extrema, or partial-function defaults
in any contributing expression.
