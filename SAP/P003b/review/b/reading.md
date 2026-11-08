# Blind mathematical reading

This file was written before opening `claims.json` or `record.json`. It reads the
17 stubs in `SAP/P003b/Challenge/Part1.lean`, expanding their propositions in
`Defs/Part4.lean` and `Defs/Part5.lean` and their dependencies in Parts 1–3.
The Challenge imports Defs, whose only external import is Mathlib. No Solution
or Comparator was inspected.

## Common objects and exact conventions

Write a count vector as `v=(a,b,c,d)`, with all four entries in the nonnegative
integers. There is no positivity or fixed-total condition in the type itself.
Its total is `N(v)=a+b+c+d`, its integer effect numerator is `e(v)=b-c`, and
`tau(v)=(b-c)/N(v)`, calculated in the rationals and then embedded in the reals.
For an observed vector `o=(A,B,C,D)`, write `m=A+B`, `h=C+D`, `N=m+h` and
`T(o)=A/m-C/h`, again calculated rationally before embedding in the reals.

All natural-number subtraction in the actual definitions is truncated at zero.
All rational/real divisions are totalized with division by zero equal to zero.
Integer subtraction is ordinary subtraction. Integer division by the positive
integer 2 is floor division, including on negative integers. `Int.toNat` replaces
a negative integer by zero. These conventions are part of the literal reading;
where bounds make them ordinary arithmetic, that will be clear below.

For `v` and a natural `m`, `Q(v,m)` is the ordered list of vectors `q=(a',b',c',d')`
with `0<=a'<=min(a,m)`, `0<=b'<=min(b,m-a')`,
`0<=c'<=min(c,m-a'-b')`, and `d'=m-a'-b'-c'<=d`. Thus it enumerates once each
componentwise subvector of `v` of total `m`. `binomial(n,k)` is
`Nat.fast_choose n k`, which equals the usual `Nat.choose n k`, including zero
for `k>n` (Mathlib `Data/Nat/Choose/Basic.lean:303–306`). Define

* `M(v,q)=choose(a,a') choose(b,b') choose(c,c') choose(d,d')`;
* `O(v,q)=(a'+b',c'+d',a-a'+c-c',b-b'+d-d')`, with the displayed natural
  subtractions evaluated in their source's left-associated order;
* `P(v,m;E)=sum(q in Q(v,m), M(v,q) 1_E(q))/choose(N(v),m)`;
* `E(v,m;f)=sum(q in Q(v,m), M(v,q) f(q))/choose(N(v),m)`.

The last two expressions are finite real sums, not measure integrals. When
`m<=N(v)`, they are the probabilities/expectations obtained by choosing an
`m`-subset uniformly among `N(v)` labeled units partitioned into four types.

The integer comparison used for two-sided tails is
`Delta(v,o,m)=N(v)((N(v)-m) A-m C)-m(N(v)-m)e(v)`.
In this formula every subtraction is in the integers. The rational p-value is

`p(v,o)=sum(q in Q(v,m), M(v,q) 1_{|Delta(v,O(v,q),m)|>=|Delta(v,o,m)|}) / choose(N(v),m)`,

where `m=A+B`. The absolute values in the implementation are integer `natAbs`.
When `N(v)=N(o)` and both observed arms are positive, this is exactly the
randomization probability of a deviation from `tau(v)` at least as large as
`|T(o)-tau(v)|`. The function is also defined on incompatible vectors.

`V(o)` is the list, possibly with repeated vectors, formed by all
`0<=i<=A`, `0<=j<=B`, `0<=k<=C`, `0<=l<=D` in that order, returning
`(i+k,A-i+l,C-k+j,B+D-j-l)`. `Possible(o,v)` means membership in this list.
It is the completion of missing binary potential outcomes, with observed
treatment/control and success/failure cells held fixed. Every vector in it has
total `N`. Define the finite real set

`S_alpha(o)={tau(v): v in V(o), alpha<=p(v,o)}`.

Acceptance uses **weak** inequality, including ties. The interval `I_alpha(o)`
is `{t: there exist l,u in S_alpha(o) with l<=t<=u}`. It is empty if the accepted
set is empty, and otherwise is its closed real interval hull. `L_alpha(o)` and
`U_alpha(o)` are respectively the real infimum and supremum of that finite set;
when it is nonempty these are its minimum and maximum. Real conditional
completeness gives totalized values on an empty set; they are not automatically
meaningful endpoints without nonemptiness.

For rational alpha, `levelAccepted` computes the same comparison by clearing
the positive rational denominator and the integer binomial denominator. If the
binomial denominator is zero it returns the truth value of `alpha<=0`.
`acceptedEffectsQ` removes duplicate vectors from `V(o)`, filters by this test,
and lists their integer effect numerators (different vectors can still give the
same numerator). `intervalQ` returns `none` if this list is empty, and otherwise
`some(minimum numerator/N, maximum numerator/N)` as a rational pair.

A labeled table on `n` units is any function `w:{0,...,n-1}->{0,1}^2`.
`tableCounts(w)` counts `(1,1),(1,0),(0,1),(0,0)`. `bit` embeds a Boolean as
the real 0 or 1. For a treatment subset `z`,

`tau(w)=sum_i(w_i(1)-w_i(0))/n`,
`T(w,z)=sum_{i in z}w_i(1)/|z| - sum_{i notin z}w_i(0)/(n-|z|)`.

Here `n-|z|` is natural subtraction, but `z` is a subset of `Fin n`.
`Assignment(n,m)` is the finite type of all `m`-subsets of these `n` indices.
`canonicalPair(v,i)` lists first `a` units of type 11, then `b` of type 10,
then `c` of type 01, and all remaining indices of type 00. In its uses with
`n=N(v)`, the last block has exactly `d` entries. `canonicalObserved(v,z)` counts
successes/failures from the first coordinate in treatment and from the second
coordinate in control. `treatedCounts(v,z)` counts the four canonical types
within `z`.

`C(o)` is the integer list `A-C-m+k` for `k=0,...,N`.
The candidate lattice is `Lambda(o)={x/N:x in C(o)}`. The list has `N+1`
entries even when `N=0`. `lineVector(n,j,b,x)` is
`(j-b,b,max(b-x,0),max(n-j-b+x,0))`, with natural `j-b`.
`lineGroup(o,x,j)` filters `V(o)` by `e(v)=x` and `v.a+v.b=j`.
`firstOnLine(o,x,j)` is `none` if that list is empty and otherwise selects
a vector of minimum second coordinate. The recursive tie rule prefers the
earlier vector. `reuseVector(v,k)=(a-k,b+k,c+k,d-k)` uses natural subtraction.

`logTwo(x)=ln(x)/ln(2)`, using Mathlib's total real logarithm. Natural `log2`
in the integer budget is the integer floor logarithm. Real square root is
Mathlib's nonnegative square root, zero on nonpositive inputs
(`Analysis/Real/Sqrt.lean:112,142`). `Real.rpow` is real exponentiation;
all logarithms used as bases in the eventual rates are positive eventually.
Natural ceiling is the nonnegative integer ceiling (clamped at zero).

## The search and Monte Carlo definitions

For an integer query `x`, `candidates(o,x)` loops over **all** `j=0,...,N`.
For each existing `firstOnLine(o,x,j)=v`, it lists `v`; if `b=c=0`, `a,d>=1`,
and `(a-1,1,1,d-1)` is possible, it also lists that second vector immediately
after `v`.

An oracle is any Boolean function `reject(v,idx)` of a vector and an absolute
test index. `runTests` scans this candidate list, increments the index for each
call, records `(v,reject(v,idx))`, and stops at the first `false`. It reports
compatibility exactly if it encountered a `false`; an empty list is incompatible.
A trace's Boolean is therefore **rejection**, not acceptance.

For `upperRun(corrected,o,reject,idx=0)`, put
`k1=2(A-C)`, `k2=A-C+m`. The starting bracket is `(k1-1,k2+1)` when corrected
and `(k1,k2)` otherwise. It has fuel `N+3`. A corrected run returns `some(a)`
immediately whenever the current bracket `(a,b)` has `b<=a+1`.
Otherwise, if fuel is zero it returns `none`. With fuel available it queries
`c=floor((a+b)/2)` by `runTests(candidates(o,c))`. Compatibility replaces `a`
by `c`; incompatibility replaces `b` by `c`. The next query starts at the updated
index, and traces concatenate.

For an uncorrected run, a newly adjacent bracket returns its lower end if both
ends are strictly inside the initial interval. If its lower end is `k1`, it
additionally queries `k1` and returns `k1` if compatible and `k1-1` otherwise.
Otherwise if its upper end is `k2`, it additionally queries `k2` and returns
`k2` if compatible and `k2-1` otherwise. The `k1` case has priority. If neither
case applies it returns `none`. Other brackets recurse with one fewer fuel.

`complementObserved(o)=(B,A,D,C)` flips both observed outcome labels.
`exactUpperRun(alpha,o)` is the corrected run with rejection `p(v,o)<alpha`.
`exactRejectQ` is the rational equivalent.

The separate `printedExecution` used in T27 acts on any integer Boolean `f`.
At each step it queries `c=floor((a+b)/2)`, changing `(a,b)` to `(a,c)` when
`f(c)=true` and to `(c,b)` otherwise. It checks adjacency **after** the query.
For adjacent ends it returns the lower end with count 1 if both are interior;
otherwise it checks `k1` first, returning `k1-1` when `f(k1)` and `k1` otherwise,
with count 2; otherwise it checks `k2`, returning `k2-1` when `f(k2)` and `k2`
otherwise, with count 2. It returns `none` if none of these apply. Nonadjacent
steps recurse and add 1 to the eventual evaluation count. Zero fuel is `none`.

Let `D_N=(N+1)(floor(log2(N+1))+3)` and `B_N=2D_N+1`.
`uniformProb(E)` on any finite type Omega is `#{omega:E(omega)}/#Omega` in the
reals. It would be zero on an empty type; relevant assignment types below are
nonempty under the stated design hypotheses. Uniform functions from finite
index types give mutually independent uniform coordinates.

`MonteSpace(n,m,K)` is the product of an observed assignment and a pool of
`B_n` batches, each of `K` independent assignments in `Assignment(n,m)`.
The batch for absolute index `idx` is the batch at `idx mod B_n`.
For candidate `v`, observed `o`, and batch `z_i`, its Monte Carlo mean is
the rational average of the K indicators
`|Delta(v,canonicalObserved(v,z_i),A+B)| >= |Delta(v,o,A+B)|`.
The approximate oracle rejects exactly when this mean plus epsilon is strictly
less than alpha. An upper run starts at index zero, and the reflected lower run
starts at the length of the upper trace, using the same pool. The resulting
`MC(corrected,alpha,epsilon,o,pool)` is `[-lo/N,hi/N]` if both runs returned
integer values, and empty otherwise. If the two endpoints are reversed, the
closed interval is also empty.

`traceProbabilityQ(o,trace)` is the product over its entries `(v,r)` of
`1-p(v,o)` if `r=true`, and `p(v,o)` otherwise.
`firstMismatch(a,b)` looks only at the rejection Booleans of the zipped traces
and returns the first differing index, or `a.length` if none differs (including
when one trace is a proper agreeing prefix). Out-of-range list access with `!`
uses the inhabited default, rather than asserting an index is in range.

`upperShuffleCost(alpha,epsilon,o,pool)` is by definition the corrected upper
trace length times `K*(n-1)`, with natural subtraction. Its expected value is
the finite uniform average over all batch pools of assignments of size `n/2`.
It measures a stipulated full-shuffle cost per draw, not the actual Lean runtime.

## Missingness, Wald, strata, and general reuse definitions

`missingMasks(o)` lists every componentwise bounded vector `0<=r<=o`.
The two completions are
`plus(o,r)=(A+r.b,B-r.b,C-r.c,D+r.c)` and
`minus(o,r)=(A-r.a,B+r.a,C+r.d,D-r.d)`.
The missing interval has lower endpoint `min(L_alpha(minus),T(minus))` if the
minus accepted set is nonempty, and `T(minus)` otherwise; its upper endpoint is
`max(U_alpha(plus),T(plus))` if the plus accepted set is nonempty, and `T(plus)`
otherwise. `IsMissingLaw(v,m,mu)` (not a theorem premise here) says weights are
nonnegative on these finite masks and that for each `q` their sum is
`M(v,q)/choose(N(v),m)`. `missingProb` sums such weights over the indicated event.

For natural `m,k`, the explicit Wald formulas are
`T_mk=(2k-m)/m`, `V_mk=(2m/(2m-2))*2k(m-k)/m^3`,
`W_zmk=2z sqrt(V_mk)`, and `J_zmk=[T_mk-z sqrt(V_mk),T_mk+z sqrt(V_mk)]`.
The source's `2*m` is first formed naturally and then cast to the rationals;
the denominator `2m-2` and difference `m-k` are rational subtraction, as also
confirmed by Lean's pretty-printed definition in `scratch/Check.lean`.
`waldCoverageQ(m,l,u)` is
`sum_{k=0}^m 1_{l<=k<=u} choose(m,k)^2 / choose(2m,m)`.
The median of a finite nonempty list of reals is obtained by sorting in increasing
order and averaging entries at zero-based indices `floor((length-1)/2)` and
`floor(length/2)`; it is defined to be zero for the empty list.
`IsWaldMedian(L,m,d)` means that under masses
`choose(m,k)^2/choose(2m,m)`, `k=0,...,m`, both `Pr(L(k)<=d)>=1/2` and
`Pr(d<=L(k))>=1/2`. It asserts a median, not uniqueness.

`allCounts(n)` enumerates all nonnegative four-vectors of total n.
`stratifiedCounts(N0,N1)` is the Cartesian product `allCounts(N0) x allCounts(N1)`.

For reuse, set `c0=(s0 mod d < d-q.d)` and
`c1=(s1 mod a < a-q.a)` and return
`update(v,q,s0,s1)=(if c1 then q.a else q.a-1,
if c1 then q.b else q.b+1, if c0 then q.c else q.c+1,
if c0 then q.d else q.d-1)`.
Seeds below are uniform integers in `[0,n!-1]`. At time zero the reused sample
is `treatedCounts(v,initial_i)`; at time `t+1` it is the update at population
`reuseVector(v,t)` with that time's independent seed pair. For `t>=n` the
definition supplies zero seeds instead; accepted reuse indices below have
`k<=n` and `k<=v.a,v.d`.

`GeneralSpace(n,m,K)` consists of an observed assignment, an independent initial
batch of K assignments for each `(i,j) in {0,...,n}^2`, and an independent pair
of factorial seeds for every such pair, every `t<n`, and every sample index.
For an arbitrary real statistic `R(o,v)`, the rank value of a sample list is
`[1+sum_i 1_{|R(O(v,q_i),v)|>=|R(o,v)|}]/(K+1)`.

`G(alpha,theta,R,o,initial,seeds)` contains exactly those real t for which
there exist, in this order, `(i,j) in {0,...,n}^2`, a vector v with
`firstOnLine(o,reverse(C(o))[i],j)=some(v)`, and a natural `k<=n` with
`k<=v.a`, `k<=v.d`, `Possible(o,reuseVector(v,k))`,
`t=theta(reuseVector(v,k))`, and rank value **strictly greater** than alpha
using the actual reused samples at k. The list access defaults to zero if out
of range, but in theorem uses `N(o)=n` so `i<n+1` is in range.

For each existing first vector on a line, `reuseLine` lists k from 1 to N with
`k<=v.a,v.d` and possible reused vector. Let F be K times the number of
nonempty `(x,j)` lines, for `x in C(o), j=0,...,N`, and let H be the sum of
`K*length(reuseLine)` over those lines. Then
`generalDrawCount=F`, `generalUpdateCount=H`, and
`generalOperations=c0*(N+1)^2+2*c1*N*F+2*c2*H`.
`generalEnvelope(n,K,c0,c1,c2)=(n+1)^2*(c0+2*(c1+c2)*K*n)`.
`recommendedK(epsilon,n)` is the nonnegative ceiling of
`ln(4*n*logTwo(n)/epsilon)/(2*epsilon^2)` and
`balancedEnvelope(epsilon,c,n)=4*c*recommendedK(epsilon,n)*n^2*logTwo(n)`.

In all following Big-O assertions, Mathlib `IsBigO` means that there exists a
real constant C such that eventually `|f|<=C*|g|`; see
`Analysis/Asymptotics/Defs.lean:73–97`. On naturals, eventually means for all
sufficiently large indices. On `N x N` with its product order, it means
uniformly for all n and K past fixed thresholds, not an iterated limit;
see `Order/Filter/AtTopBot/Prod.lean:24–27,70–77`.

## SAP.P003b.T24

For every natural n, every labeled binary table w on n units, and every natural
m, if `m>0` and `n=2m`, then all of the following hold:

1. For every treatment subset z, if `|z|=m`, then `|z^c|=m`,
   `T(w,z)+T(w,z^c)=sum_i(w_i(1)-w_i(0))/m`, and this last expression equals
   `2*tau(w)`.
2. The exact design expectation of `T(O(tableCounts(w),q))` is `tau(w)`.
3. For every real t, the exact point probabilities at `tau(w)-t` and
   `tau(w)+t` agree.

The expectation and point probabilities are the finite weighted design sums
defined above. There is no hypothesis on the pattern of outcomes.

## SAP.P003b.T25

The assertion is the conjunction of a universal result and fixed numerical
facts. For every natural count vector o and real alpha, assuming
`0<m=h` and `0<alpha<1`,

* `S_alpha(o)=I_alpha(o) intersect Lambda(o)`;
* `[T(o),(A-C+m)/N] intersect S_alpha(o)
  = [T(o),U_alpha(o)] intersect Lambda(o)`.

Independently, for `o=(0,2,0,2)` and rational alpha `1/2`, the set of accepted
integer numerators is `{-1,0,1}`, `intervalQ=some(-1/4,1/4)`, the incompatible
vector `(1,0,2,1)` has p-value `2/3`, and it is not possible. The rational
number `1/8` lies between `-1/4` and `1/4`, but there is no integer
`d in C(o)` with `d/4=1/8`.

## SAP.P003b.T8

For **every real z**, if
`1.95996398454005<z<1.95996398454006`, all the following hold, with no normal
distribution or quantile occurring in the proposition:

1. For every natural `k<=25`, `0 in J_z,25,k` iff `10<=k<=15`; whenever it
   covers zero, `W_z,25,k>0.55`.
2. For every nonempty list of integers `k in {0,...,25}`, if the fraction
   whose intervals cover zero is at least `0.925`, the median of its widths
   exceeds `0.55`.
3. `waldCoverageQ(25,10,15)=14399081696900/15801325804719`,
   `W_z,25,11=2z sqrt(77/3750)`,
   `sum_{k=12}^{13} choose(25,k)^2/choose(50,25)<1/2`, and
   `sum_{k=11}^{14} choose(25,k)^2/choose(50,25)>1/2`.
4. `waldCoverageQ(50,21,29)=3816125510529753382833452/4109292299835622081085553`
   and `W_z,50,23=2z sqrt(621/61250)`.
5. For every nonempty list of `k in {0,...,25}`, if strictly more than half
   its intervals cover zero, its median width is at least `2z sqrt(1/50)`.
6. For every natural `k<=25`, put `V0=2k(25-k)/15625` and `T=T_25,k`.
   The interval `[T-z sqrt(V0),T+z sqrt(V0)]` covers zero iff `10<=k<=15`,
   and in that range its width exceeds `0.54`.
7. `2z sqrt(77/3750)` is a design median of the m=25 widths;
   for every natural `k<=50`, `0 in J_z,50,k` iff `21<=k<=29`;
   and `2z sqrt(621/61250)` is a design median of the m=50 widths.
8. These two medians lie respectively in the open decimal intervals
   `(0.56170,0.56171)` and `(0.39470,0.39471)`.

All decimal constants are exact rationals embedded in the reals. All universal
list conditions concern arbitrary finite lists, allowing repeated k values.

## SAP.P003b.T19

For every pair of natural stratum totals N0,N1:

1. Every pair `(v0,v1)` in their product composition set has those totals.
2. Its cardinality is `choose(N0+3,3)*choose(N1+3,3)` and, as a real number,
   is at most `(N0+N1+3)^6/36`.
3. `#allCounts(N0+N1)=choose(N0+N1+3,3)`.
4. `sum_{r=0}^{N0+N1} choose(r+3,3)*choose(N0+N1-r+3,3)
   =choose(N0+N1+7,7)`.

Additionally `#stratifiedCounts(2,2)=100`, `choose(11,7)=330`, and the pair
`((3,0,0,0),(1,0,0,0))` has summed total 4 but first total unequal to 2.
There are no positivity premises, covariates, or labeled-table assertions here.

## SAP.P003b.T20

This is the conjunction of three independent universally quantified blocks:

1. For every natural n, natural m with `0<m<n`, and labeled tables w,w' on n
   with equal four-type counts, for every real t the fractions of assignments
   with `T(w,z)=t` and `T(w',z)=t` agree.
2. For every natural vector v with `a>=1,d>=1`, all four integer coordinates
   of `reuseVector(v,1)` equal `(a-1,b+1,c+1,d-1)`.
3. For every integer tuple `n,n11,n10,n01,j,b,x,u11,u10,u01,u00`, assuming
   `u11+u10+u01+u00=n` and `u10-u01=x`, the following four equivalences hold:
   `j-b-n01<=j-b` iff `0<=n01`;
   `j-b-n01<=n11` iff `j-n11-n01<=b`;
   `j-b-n01<=j-x-n01` iff `x<=b`;
   `j-b-n01<=n-b-n10-n01` iff `j+n10<=n`.
   Also `(u11+u10-b,b,b-x,n-(u11+u10)-b+x)` equals
   `(u11+(u10-b),u10-(u10-b),u01-(u10-b),u00+(u10-b))`.
   Finally, for every pair of integers a,d, if `(a+2+d) mod 2=0`, then
   `d mod 2=a mod 2`.

The parity implication is syntactically within the third block. No count
nonnegativity or minimum-line-choice assumption is present in that block.

## SAP.P003b.T26

This is a closed conjunction, with no external hypotheses. Let `v=(11,0,3,6)`
and let `r(q)=(0,0,1,0)` if `q=(0,0,3,0)` and zero otherwise. Then
`N(v)=20`, `0<3<N(v)`, `0<109/500<1`, and `tau(v)=-3/20`. For every
`q in Q(v,3)`, the mask r(q) is componentwise bounded by O(v,q), and the accepted
sets at alpha `109/500` of **both** completions are nonempty. The exact design
probability that the missing interval contains tau(v) is `297/380`, and
`297/380<1-109/500`. This is a specific coverage counterexample for the exact
missing-interval construction above, including its Neyman-estimate enlargement.

## SAP.P003b.T27

It is **not** the case that for every integers k1,k2,r and Boolean integer
function f, the following implication holds: if `0<k1<k2`,
`k1-1<=r<=k2`, and for every integer `k1<=x<=k2`,
`f(x)=false` iff `x<=r`, then there exist natural fuel and evaluation count
such that `printedExecution(fuel,k1,k2,f,k1,k2)=some(r,count)` and
`count<=floor(logTwo(k2-k1+1)+2)`.

This negates a universal correctness-and-budget assertion for the literal
procedure. It does not assert failure of a corrected sentinel procedure or
failure of a final statistical coverage theorem.

## SAP.P003b.T30

For every count vector o and real alpha, assuming `0<m=h` and `0<alpha<1`,
`T(o) in S_alpha(o)`, `T(o) in I_alpha(o)`, and
`L_alpha(o)<=T(o)<=U_alpha(o)`. No particular completion witness is specified.

## SAP.P003b.T31

For every count vector o and real alpha, if `m>0`, `h>0`, `0<alpha<1`, and
`S_alpha(o)` is nonempty, then

`U_alpha(o)-L_alpha(o) <= sqrt((4/alpha)*(N/(N-1))*(N/(m*h)))`.

The source uses natural `N-1`, which is positive since `m,h>0` imply `N>=2`.
This theorem expressly requires nonemptiness, with no balanced-design premise.

## SAP.P003b.T33

For every count vectors o and v, if o has equal positive arm sizes,
`N(v)=N(o)`, `min(v.b,v.c)>=1`, and `max(v.b,v.c)>=2`, then
`p((v.a+1,v.b-1,v.c-1,v.d+1),o)>=p(v,o)`.
Here the two subtractions are ordinary on the admitted inputs. v need not be
possible for o. The excluded case `v.b=v.c=1` is not covered.

## SAP.P003b.T7

Conjunction of two blocks:

1. For every count vector o and every index-dependent rejection oracle,
   if o has positive balanced arm sizes, its corrected upper run returns
   an integer and makes at most `D_N` individual vector tests.
2. For every count vector v, naturals m,K and reals alpha,epsilon, assuming
   `m>0`, `N(v)=2m`, `K>0`, `0<alpha<1`, and `0<epsilon<alpha`, the uniform
   joint probability over the observed assignment and all batches that
   `I_alpha(o)` is a subset of `MC(true,alpha,epsilon,o,pool)` is at least
   `1-2D_N exp(-2K epsilon^2)`. In addition, **if** `alpha-2epsilon>0`,
   the joint probability of the reverse containment into
   `I_(alpha-2epsilon)(o)` is at least the same bound.

In the second block `o=canonicalObserved(v,observed assignment)`. No theorem
about conditional test histories is assumed or separately concluded.

## SAP.P003b.T32

For every count vector o and real alpha, if `0<m=h`, `N>=15`, and
`0<alpha<1`, the corrected exact upper run returns a numerator whose quotient
by N is `U_alpha(o)`; the run on `(B,A,D,C)` returns a numerator whose negative
quotient by N is `L_alpha(o)`; and the sum of both trace lengths is at most
`4N logTwo(N)`. The Option equalities assert existence of the returned values.
There is no claim here about the uncorrected search.

## SAP.P003b.T34

For every count vector v, naturals m,K and reals alpha,epsilon, if `m>0`,
`N(v)=2m`, `N(v)>=15`, `K>0`, `0<alpha<1`, and `0<epsilon<alpha`, then:

1. **If** `K>=ln(4N logTwo(N)/epsilon)/(2epsilon^2)`, the joint probability
   over the observed assignment and batch pool that tau(v) belongs to
   `MC(true,alpha-epsilon,epsilon,o,pool)` is at least `1-alpha`.
2. **If** `epsilon<alpha/3`, the joint probability that that Monte Carlo
   interval is a subset of `I_(alpha-3epsilon)(o)` is at least
   `1-4N logTwo(N) exp(-2K epsilon^2)`.

The K lower bound is a premise only of conclusion 1. Conclusion 2 has its own
additional epsilon premise and no such K lower bound.

## SAP.P003b.T6

This is a closed conjunction, with the following bindings and subclaims.
Let `o=(2,13,1,14)`.

1. `N=30`, `m=15`, `T(o)=1/15`, `0<1/200<1/20<1`.
   Under population `(3,0,0,27)` with m=15 the exact probability of this
   observed o is `45/116>0`. For every Boolean s,
   `(1 if s else 0)+1/200>=1/20` iff `s=true`.
2. At rational alpha `1/20` and `1/25`, `intervalQ(o)=some(-1/5,1/3)`.
   Let a and a' be the uncorrected exact runs at those respective levels.
   Let bA use `reject(v,i)=(i!=0)`, bB use `(i=0)`, and bD use `(i<2)`.
   Both a,a' return 10, and a has trace length 16. bA returns 9, its first
   rejection bit is false whereas a's is true, and its trace-product
   probability is positive. bB returns 16, its first rejection bit is true
   whereas a's prime trace has first bit false, and its product probability
   is positive. bD returns 16, its first bit equals a's, its second is true
   whereas a's second is false, and its product probability is positive.
3. For a uniform pool of batches of **one** assignment, let b be the
   uncorrected approximate run at level `1/20` and epsilon `1/200`.
   The probability it returns a value below 10 differs from the probability
   that its first Boolean mismatch J with a satisfies `J<a.length` and its
   bit at J is true. The probability it returns a value above 10 differs
   from the probability that its first mismatch J with a' satisfies
   `J<a'.length` and its bit at J is false. Here mismatch uses the precise
   zip/default convention specified above.
4. For a uniform pool of batches of **5000** assignments, take the
   uncorrected approximate run at level `1/20` and epsilon `1/50`.
   The event that its trace has at least two entries and the second rejects
   has probability at least
   `4693104776190294207/5012394999999664375`, which exceeds `9/10`.
   Also `16 exp(-4)<48/103<9/10`.

All runs and probabilities are exactly the explicit definitions above.

## SAP.P003b.T35

Conjunction of two universal assertions:

1. For every count vector v, naturals m,K, real alpha, and arbitrary
   real-valued functions theta on vectors and R on pairs of vectors, if
   `0<m<N(v)`, `K>0`, and `0<alpha<1`, then over the uniform
   `GeneralSpace(N(v),m,K)`, the probability that theta(v) belongs to the
   full-j-loop set G is at least `1-alpha`. The observed o and all initial
   draws/seeds come from that product space; no validity assumption on R,
   theta or the output set is a premise.
2. For every vector v and natural m with `0<m<N(v)`, `v.a>0`, `v.d>0`,
   and every vector q', the probability that one update of a uniform
   treated-count draw for v, using two independent uniform factorial seeds,
   equals q' is exactly `P(reuseVector(v,1),m; q=q')`.

This set uses plus-one ranks, correlated reuse within each line, all line
indices j, and strict rank acceptance. It is not an interval hull.

## SAP.P003b.T36

Conjunction of a finite assertion and an asymptotic assertion:

1. For every count vector o, natural K, and reals c0,c1,c2, if all costs are
   nonnegative then `F<= (N+1)^2 K` and `H<= (N+1)^2 N K`. Moreover if
   `N>=1` and `K>=1`, the explicit operation polynomial is at most
   `4*(c0+2*(c1+c2))*K*N^3`.
2. For every triple of nonnegative real costs and every function
   `o:N x N -> Counts`, if **for all** pairs p its total is `p.1` and if
   eventually in the product order both observed arm sizes are positive,
   then `generalOperations(o(n,K),K,c0,c1,c2)=O(K*n^3)` jointly as n,K
   tend to infinity. The Big-O constant is allowed to depend on the fixed
   costs and chosen function o; the first clause supplies a uniform bound.

The counts and operation polynomial are the stipulated definitions F,H above.
No runtime theorem for enumerating the finite lists is asserted.

## SAP.P003b.T18

Conjunction of four assertions:

1. For every real alpha,epsilon,c with `0<alpha<1`, `0<epsilon<alpha`,
   `c>=0`, every natural-valued function tests and real-valued operations,
   if operations is nonnegative at **every** n, eventually
   `tests(n)<=4n logTwo(n)`, and eventually
   `operations(n)<=tests(n)*recommendedK(epsilon,n)*(c*n)`, then
   `operations(n)=O(n^2*(ln n)^2)`. Alpha and epsilon are fixed before
   the functions; no actual search is bound to tests in this clause.
2. For every natural `r>=4` and `K>0`, put `n=2^r` and
   `o=(0,n/2,0,n/2)`. Under a uniform batch pool for balanced assignments,
   the event `upperShuffleCost(1/2,1/8,o,pool)>=(n/4+1)*K*(n-1)` has
   strictly positive probability. Furthermore **if** `r>=6` and
   `K>=32 ln(32n logTwo(n))`, its expected cost is at least
   `(n/4+1)*K*(n-1)/2`.
3. For every nonnegative **real** exponent c, the function of natural r
   equal to the expected full-shuffle upper cost for `n=2^r`,
   `K=recommendedK(1/8,n)`, `o=(0,n/2,0,n/2)`, is **not**
   `O(n*(ln n)^c)` as r tends to infinity.
4. For every natural `n>=15`, `logTwo(n)<=(ln n)^2`.

The lower-bound clauses concern the defined corrected upper run. Clause 1 is
a conditional cost implication, not a claim that every implementation meets
its test-count and draw-cost premises.
