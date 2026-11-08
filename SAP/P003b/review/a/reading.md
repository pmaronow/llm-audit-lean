# Blind mathematical reading

This file was written from `SAP/P003b/Defs*.lean`, `SAP/P003b/Defs/*.lean`, and
`SAP/P003b/Challenge*.lean`, with Mathlib definitions checked as needed, before
opening either `claims.json` or `record.json`. The Challenge has 17 theorems. Each
theorem asserts a proposition named `T…Statement`; the readings below expand
those propositions. No theorem has an additional hypothesis outside its alias.

## Common definitions and conventions

* A count vector is an arbitrary quadruple of natural numbers
  `v=(a,b,c,d)`, in potential-outcome order `(11,10,01,00)` when used as a
  population. Set `N(v)=a+b+c+d`, `e(v)=b-c` (an **integer**), and
  `tau(v)=(b-c)/N(v)` (first calculated in the rationals, then embedded in the
  reals). For an observed vector `o=(A,B,C,D)`, put `m=A+B`, `l=C+D`,
  `n=N(o)`, and `hat(o)=A/m-C/l`, also calculated rationally first.
* `randomStates(v,m)` enumerates each nonnegative quadruple `q` with
  `q<=v` coordinatewise and `N(q)=m`, once. Its weight is
  `W(v,q)=choose(a,q.a)choose(b,q.b)choose(c,q.c)choose(d,q.d)`.
  `binomial` is Mathlib `Nat.fast_choose`, which equals ordinary `Nat.choose`
  (`Data/Nat/Choose/Basic.lean`, `choose_eq_fast_choose`). The observed vector is
  `O(v,q)=(q.a+q.b,q.c+q.d,a-q.a+c-q.c,b-q.b+d-q.d)`.
  `designProb(v,m,E)` is `sum_q W(v,q)1_E(q)/choose(N(v),m)`;
  `designMean(v,m,f)` is the corresponding weighted sum of `f`.
* Define the integer
  `Delta(v,o,m)=N(v)((N(v)-m)A-m C)-m(N(v)-m)e(v)`.
  `p(v,o)` is the sum of `W(v,q)` over the above random states with
  `|Delta(v,O(v,q),m)| >= |Delta(v,o,m)|`, divided by `choose(N(v),m)`,
  where `m=A+B`. Thus the tail includes equality. When `N(v)=N(o)` and both
  arms are positive it is exactly the two-sided randomization tail for
  `|hat-tau(v)|`. The integer absolute value is `Int.natAbs`.
* `possibleTables(o)` is the list of
  `(i+k,A-i+h,C-k+j,B+D-j-h)` for `0<=i<=A`, `0<=j<=B`,
  `0<=k<=C`, `0<=h<=D`. `Possible(o,v)` means membership in that list.
  Let `S_alpha(o)={tau(v):Possible(o,v), p(v,o)>=alpha}`. This is the
  finite set `accepted`. Its interval `I_alpha(o)` is
  `{t: exists L,U in S_alpha(o), L<=t<=U}`; it is empty when the set is
  empty, otherwise the closed interval between its minimum and maximum.
  `lower` and `upper` separately mean real `sInf` and `sSup` of that finite
  set; identifying them with endpoints requires nonemptiness.
* For rational `alpha`, `levelAccepted` tests the same weak inequality by
  clearing the positive rational denominator. If the binomial denominator is
  zero it instead tests `alpha<=0`. `acceptedEffectsQ` deduplicates possible
  vectors, filters by that test, and returns their integer effects (possibly
  repeated). `intervalQ` is `none` for an empty list, otherwise `some` of its
  smallest and largest effects divided by `N(o)`.
* The candidate numerator list is
  `A-C-m, A-C-m+1, ..., A-C-m+n`. Its real lattice `L(o)` consists of
  these integers divided by `n`. `lineGroup(o,x,j)` is the list of possible
  vectors with `e(v)=x` and `v.a+v.b=j`. `firstOnLine` returns a vector in that
  list with minimal second coordinate, or `none`. Ties favor the earlier list
  element. `lineVector(n,j,b,x)` is
  `(j-b,b,max(b-x,0),max(n-j-b+x,0))`, with the first difference also
  natural truncated subtraction. `reuseVector(v,k)` is
  `(a-k,b+k,c+k,d-k)`, again with natural truncated differences.
* A potential table of size `n` is a function from `{0,...,n-1}` to two
  Booleans. Booleans have numerical values 0 and 1. `tableCounts` counts its
  four types; `tableTau` is the average of first minus second potential
  outcomes. `tableEstimator(w,z)` is the average first outcome over the
  treated finite subset `z`, minus the average second outcome over its
  complement. `Assignment(n,m)` is the finite type of all subsets of
  `{0,...,n-1}` of cardinality `m`.
* `canonicalPair(v,i)` labels the first `a` indices `(1,1)`, next `b`
  `(1,0)`, next `c` `(0,1)`, and all remaining indices `(0,0)`.
  `canonicalObserved(v,z)` counts treated first outcomes and control second
  outcomes for that labeling. When its ambient index size is `N(v)` this is
  the intended population, with exactly `d` final indices.
* `uniformProb(E)` on a finite type `Omega` means `#E/#Omega` in the reals.
  On a nonempty finite product it is the usual independent uniform law on
  the coordinates; on an empty type its definition instead returns zero.
  No measure-theoretic integral, conditional expectation, or limsup occurs.
* All Lean natural subtractions truncate at zero. All rational/real divisions
  are totalized with division by zero equal to zero. Integer division by 2 in
  the searches is Euclidean division, hence the mathematical floor of the
  half-sum, including for negative endpoints. `Real.sqrt(x)` is the
  nonnegative square root of `max(x,0)`; `Real.log(0)=0` and
  `Real.log(-x)=Real.log(x)`. Here `logTwo(x)=Real.log(x)/Real.log(2)`.
  `Nat.log2(n)` is floor base-two log for `n>0`, with value zero at zero
  (`Data/Nat/Log.lean`, `log2_eq_log_two`). Natural ceiling is rounded up and
  clamped below by zero. `=O[atTop]` means an eventual uniform bound on
  absolute values by a real constant times the comparison absolute value
  (`Analysis/Asymptotics/Defs.lean`). On `N x N`, `atTop` sends **both**
  coordinates to infinity with one bound on the resulting quadrant.

## Exact search and Monte Carlo definitions

For observed `o`, define `k1=2(A-C)` and `k2=A-C+m`.
`candidates(o,x)` scans every `j=0,...,n`; for each nonempty line it lists its
`firstOnLine` vector. If that vector has `b=c=0`, `a,d>=1`, and
`(a-1,1,1,d-1)` is possible, it lists that vector as well, immediately after
the first. An indexed rejection oracle returns a Boolean on a vector and a
natural test index. `runTests` queries candidates in order until the first
false (acceptance), recording every `(vector,rejection Boolean)` and advancing
the index after each test. It reports compatibility exactly when there was an
acceptance, including reporting false on an empty list.

`upperRun(corrected,o,reject,idx)` calls a fueled binary search with fuel `n+3`.
The corrected version starts at `(k1-1,k2+1)`, returns its left endpoint as
soon as the endpoints are adjacent (before consuming another unit of fuel),
and otherwise queries compatibility at the midpoint. Compatibility replaces
the left endpoint; incompatibility replaces the right endpoint. Fuel
exhaustion returns `none`. The uncorrected version starts at `(k1,k2)`, takes
a midpoint step before checking adjacency, and at adjacency returns the left
endpoint if both bounds are internal, otherwise retests `k1` or `k2` and
returns that endpoint when compatible and one less when incompatible (with
the `k1` branch having priority). The trace concatenates every vector test.
`exactUpperRun(alpha,o)` is the corrected run rejecting iff `p(v,o)<alpha`.
Outcome complementation replaces `o` by `bar(o)=(B,A,D,C)`.

Let `D(n)=(n+1)(floor(log2(n+1))+3)` and `B(n)=2D(n)+1`. A Monte pool
has `B(n)` batches, each with `K` assignments of size `m` in `n` units. Test
index `idx` uses batch `idx mod B(n)`. `monteMean(v,o,batch)` is the fraction
of its `K` assignments satisfying the same weak absolute-Delta tail test,
using `canonicalObserved` at those assignments. The approximate oracle
rejects iff `monteMean+epsilon<alpha`.

`monteEndpoints` first runs the upper search on `o`, starting at index zero,
then the upper search on `bar(o)`, starting at the first trace's length. If
both runs return integers `lo,hi`, `monteInterval` is
`[-lo/N(o),hi/N(o)]`; otherwise it is empty. Its `corrected` flag is passed to
both searches. `MonteSpace(n,m,K)` is the product of one observed assignment
and one Monte pool, with the uniform product law in the statements.

`printedExecution(fuel,k1,k2,f,a,b)` is the separate literal Boolean search:
query `f(floor((a+b)/2))`, replacing `b` if true and `a` if false. After that
step, on adjacency, return the left endpoint if interior, or query the
corresponding original boundary and return it minus one when true and itself
when false. The left-boundary branch has priority. The returned pair also
counts one evaluation for each midpoint and one for each boundary query.
Otherwise recurse, returning `none` when fuel is exhausted.

## SAP.P003b.T24

For every natural `n`, every potential table `w` of size `n`, and then every
natural `m`, if `m>0` and `n=2m`, all the following hold:

1. For every finite subset `z` with `|z|=m`, its complement has size `m`,
   `hat(w,z)+hat(w,z^c)=sum_i(Y_i(1)-Y_i(0))/m`, and this last expression
   equals `2 tableTau(w)`.
2. The weighted design mean at count vector `tableCounts(w)` and treated
   size `m` of `hat(O(tableCounts(w),q))` equals `tableTau(w)`.
3. For every real `t`, the design probabilities of that estimate equaling
   `tableTau(w)-t` and `tableTau(w)+t` are equal.

## SAP.P003b.T25

The conjunction of a universal balanced assertion and fixed numerical facts:

* For every observed count vector `o`, then every real `alpha`, under
  `m>0`, `m=l`, and `0<alpha<1`,
  `S_alpha(o)=I_alpha(o) intersect L(o)`, and
  `[hat(o),(A-C+m)/n] intersect S_alpha(o)` equals
  `[hat(o),upper(alpha,o)] intersect L(o)`.
* At `alpha=1/2`, `o=(0,2,0,2)`, the rationally computed accepted integer
  effects form the set `{-1,0,1}`; `intervalQ=some(-1/4,1/4)`;
  `p((1,0,2,1),o)=2/3` although this vector is not possible;
  `-1/4<=1/8<=1/4`; and there is no integer in the candidate numerator list
  whose quotient by 4 is `1/8`.

## SAP.P003b.T8

Here `m` is half the population size and `k` a natural number. Write
`T_mk=(2k-m)/m`,
`V_mk=(2m)/(2m-2) * 2k(m-k)/m^3`,
`W_mk(z)=2z sqrt(V_mk)`, and
`J_mk(z)=[T_mk-z sqrt(V_mk),T_mk+z sqrt(V_mk)]`.
The subtraction `2m-2` is natural; `m-k` in the numerator is rational.
`waldCoverageQ(m,lo,hi)` is
`sum_{0<=k<=m,lo<=k<=hi} choose(m,k)^2 / choose(2m,m)`.
The median of a nonempty finite list is the average of its two central order
statistics (the same element twice at odd length); the empty-list median is
defined to be zero. A design median `d` means separately
`P(W<=d)>=1/2` and `P(W>=d)>=1/2` under weights
`choose(m,k)^2/choose(2m,m)`; uniqueness is not asserted.

For **every real** `z` satisfying the strict bounds
`1.95996398454005<z<1.95996398454006`, the theorem asserts all of:

* For every natural `k<=25`, `0 in J_25,k` iff `10<=k<=15`; inclusion
  implies `W_25,k>0.55`.
* For every list `runs` of indices in `{0,...,25}`, if nonempty and at least
  `0.925` of its entries have intervals containing zero, its empirical
  median width is strictly greater than `0.55`.
* `waldCoverageQ(25,10,15)=14399081696900/15801325804719`;
  `W_25,11=2z sqrt(77/3750)`;
  the total design weight of `k=12,13` is less than `1/2`, whereas that of
  `k=11,...,14` is greater than `1/2`.
* `waldCoverageQ(50,21,29)=3816125510529753382833452/4109292299835622081085553`;
  `W_50,23=2z sqrt(621/61250)`.
* For every nonempty list of indices in `{0,...,25}`, if strictly more than
  half contain zero, its empirical median width is at least
  `2z sqrt(1/50)`.
* For every natural `k<=25`, let `V0=2k(25-k)/15625` (real arithmetic).
  The interval `T_25,k +/- z sqrt(V0)` contains zero iff `10<=k<=15`,
  and in that range its width is strictly greater than `0.54`.
* `2z sqrt(77/3750)` is a design median at `m=25`; for every `k<=50`,
  `0 in J_50,k` iff `21<=k<=29`; and `2z sqrt(621/61250)` is a design
  median at `m=50`.
* These two median values lie, respectively, strictly between
  `0.56170,0.56171` and strictly between `0.39470,0.39471`.

There is no assertion identifying `z` as a normal quantile or connecting these
one-index formulas to a labeled assignment distribution.

## SAP.P003b.T19

`allCounts(N)` is exactly the finite set of nonnegative quadruples summing to
`N`; `stratifiedCounts(N0,N1)` is the product of those two sets. For every
natural `N0,N1`, every member has those two prescribed totals, its cardinality
is `choose(N0+3,3)choose(N1+3,3)`, and its real cardinality is at most
`(N0+N1+3)^6/36`. Also `#allCounts(N0+N1)=choose(N0+N1+3,3)`, and
`sum_{r=0}^{N0+N1} choose(r+3,3)choose(N0+N1-r+3,3)=choose(N0+N1+7,7)`.
Finally `#stratifiedCounts(2,2)=100`, `choose(11,7)=330`, and the two vectors
`(3,0,0,0),(1,0,0,0)` have combined total 4 but the first has total unequal
to 2. No labeled-table equivalence is asserted.

## SAP.P003b.T20

This is a conjunction of three independently universally quantified clauses:

1. For every natural `n`, then `m` with `0<m<n`, then tables `w,w'` of
   size `n` with identical four type counts, for every real `t` the uniform
   assignment probabilities `P(hat(w,z)=t)` and `P(hat(w',z)=t)` agree.
2. For every count vector `v` with `a,d>=1`, the four coordinates of
   `reuseVector(v,1)`, interpreted as integers, are exactly
   `(a-1,b+1,c+1,d-1)`.
3. For all **integers** `n,n11,n10,n01,j,b,x,u11,u10,u01,u00`, if
   `u11+u10+u01+u00=n` and `u10-u01=x`, then all four equivalences hold:
   `j-b-n01<=j-b iff 0<=n01`;
   `j-b-n01<=n11 iff j-n11-n01<=b`;
   `j-b-n01<=j-x-n01 iff x<=b`;
   `j-b-n01<=n-b-n10-n01 iff j+n10<=n`.
   Also
   `(u11+u10-b,b,b-x,n-(u11+u10)-b+x)` equals
   `(u11+(u10-b),u10-(u10-b),u01-(u10-b),u00+(u10-b))`.
   Under those same hypotheses, for every integer `a,d`, if
   `(a+2+d) mod 2=0`, then `d mod 2=a mod 2`.

## SAP.P003b.T26

For `v=(11,0,3,6)`, `N(v)=20`, `0<3<N(v)`, `0<109/500<1`, and
`tau(v)=-3/20`. For each possible treated-type vector `q` at `m=3`, let
`r(q)=(0,0,1,0)` when `q=(0,0,3,0)`, and `(0,0,0,0)` otherwise.
The theorem asserts this mask is coordinatewise at most `O(v,q)` and that
both completed observed tables below have nonempty accepted sets at
`alpha=109/500`.

For arbitrary observed `o=(A,B,C,D)` and mask `r`,
`oPlus=(A+r.b,B-r.b,C-r.c,D+r.c)` and
`oMinus=(A-r.a,B+r.a,C+r.d,D-r.d)`.
The missing interval is the closed interval with lower endpoint
`min(lower(alpha,oMinus),hat(oMinus))` when that accepted set is nonempty,
otherwise `hat(oMinus)`, and analogous upper endpoint
`max(upper(alpha,oPlus),hat(oPlus))`, otherwise `hat(oPlus)`.
The design probability, over `q` at this fixed `v,m`, that this missing
interval contains `tau(v)` is exactly `297/380`, and
`297/380<1-109/500`. There is no additional assumption about a missingness
distribution. (The separately defined `IsMissingLaw` and `missingProb` are
not used in any Challenge theorem.)

## SAP.P003b.T27

It is **not** the case that for all integers `k1,k2,r` and then every Boolean
function `f:Z->Bool`, if `0<k1<k2`, `k1-1<=r<=k2`, and, for every integer
`x` in `[k1,k2]`, `f(x)=false iff x<=r`, there exist natural fuel `steps`
and evaluation count `evaluations` for which the literal `printedExecution`
starting at `(k1,k2)` returns exactly `(r,evaluations)` and
`evaluations<=floor(log2(k2-k1+1)+2)`.
Thus a counterexample may fail endpoint correctness, termination, or this
evaluation bound. The negation is not restricted to one exhibited witness.

## SAP.P003b.T30

For every observed vector `o`, then real `alpha`, if `m>0`, `m=l` and
`0<alpha<1`, `hat(o)` belongs to both `S_alpha(o)` and `I_alpha(o)`, and
`lower(alpha,o)<=hat(o)<=upper(alpha,o)`. No explicit vector attaining that
effect or attaining p-value one is part of this theorem.

## SAP.P003b.T31

For every observed vector `o`, then real `alpha`, if `m,l>0`,
`0<alpha<1`, and `S_alpha(o)` is nonempty, then
`upper(alpha,o)-lower(alpha,o) <= sqrt((4/alpha)*n/(n-1)*n/(m*l))`.
The written `n-1` is natural subtraction, but the positive arms force `n>=2`.
Nonemptiness is an explicit additional premise.

## SAP.P003b.T33

For every observed vector `o`, then population count vector `v`, if `m>0`,
`m=l`, `N(v)=N(o)`, `min(b,c)>=1`, and `max(b,c)>=2`, then
`p((a+1,b-1,c-1,d+1),o)>=p(v,o)`. Possibility of either vector is not
assumed. The subtractions here are exact because `b,c>=1`.

## SAP.P003b.T7

Two independent universal assertions:

1. For every observed `o`, then every indexed Boolean rejection oracle,
   under `m>0,m=l`, the corrected upper search returns an integer and its
   trace has at most `D(n)` vector tests, for **every** oracle behavior.
2. For every population `v`, then natural `m,K`, then real `alpha,epsilon`,
   if `m>0`, `N(v)=2m`, `K>0`, `0<alpha<1`, and `0<epsilon<alpha`,
   under the joint uniform law on `MonteSpace(N(v),m,K)` (write `o` for
   its observed vector and `pool` for its pool),
   `P(I_alpha(o) subset monteInterval(true,alpha,epsilon,o,pool))`
   is at least `1-2D(N(v))exp(-2K epsilon^2)`. If in addition
   `alpha-2epsilon>0`, then
   `P(monteInterval(true,alpha,epsilon,o,pool) subset I_(alpha-2epsilon)(o))`
   has the same lower bound. These are separate probability assertions,
   not a simultaneous-event probability bound.

## SAP.P003b.T32

For every observed `o`, then real `alpha`, if `m>0`, `m=l`, `n>=15`,
`0<alpha<1`, the corrected exact upper run, with its returned integer
divided by `n`, is `some(upper(alpha,o))`; the corrected exact upper run on
`bar(o)`, with the negative of its returned integer divided by `n`, is
`some(lower(alpha,o))`; and the sum of the two trace lengths is at most
`4n log2(n)`. There is no assertion about the literal uncorrected search.

## SAP.P003b.T34

For every population `v`, then natural `m,K`, then real `alpha,epsilon`, if
`m>0`, `N(v)=2m>=15`, `K>0`, `0<alpha<1`, and `0<epsilon<alpha`, both
implications hold under the joint uniform observed-assignment/pool law:

* If `K>=log(4N(v)log2(N(v))/epsilon)/(2epsilon^2)`,
  `P(tau(v) in monteInterval(true,alpha-epsilon,epsilon,o,pool))>=1-alpha`.
* If `epsilon<alpha/3`,
  `P(monteInterval(true,alpha-epsilon,epsilon,o,pool)
     subset I_(alpha-3epsilon)(o))`
  is at least `1-4N(v)log2(N(v))exp(-2K epsilon^2)`.

The sample-size premise is required only by the first implication.

## SAP.P003b.T6

This is an unconditional conjunction of four finite-example assertions.
Let `o=(2,13,1,14)`. A trace entry's Boolean is **rejection**. For any trace
`t`, let `PTrace(t)=product_{(v,b) in t}(if b then 1-p(v,o) else p(v,o))`.
Let `a` and `aPrime` be the uncorrected exact upper-search traces/runs at
levels `1/20` and `1/25`. Let `bA,bB,bD` be uncorrected upper runs whose
rejection oracles are respectively `idx!=0`, `idx=0`, `idx<2`.

1. `N(o)=30`, `m=15`, `hat(o)=1/15`, `0<1/200<1/20<1`;
   for population `(3,0,0,27)` at `m=15` the probability of observing `o`
   is `45/116>0`; and, for every Boolean `s`,
   `(1_s+1/200>=1/20) iff s=true`.
2. Both exact rational intervals (`intervalQ`) at those two levels are
   `some(-1/5,1/3)`. Both `a` and `aPrime` return 10; `a` has trace length
   16. `bA` returns 9, has first Boolean false while `a` has true, and has
   `PTrace>0`. `bB` returns 16, has first Boolean true while `aPrime` has
   false, and has `PTrace>0`. `bD` returns 16, its first Boolean agrees
   with `a`, its second Boolean is true while `a`'s is false, and it has
   `PTrace>0`.
3. On a uniform Monte pool with `n=30,m=15,K=1`, let `b` be the
   uncorrected approximate upper run at `alpha=1/20,epsilon=1/200`.
   `firstMismatch(t,u)` is the first index of unequal Booleans in their
   zip, or the length of `t` if no such index exists (including a short
   common prefix). Default out-of-range list entries are the inhabited
   values. Then
   `P(b returns x<10) != P(J<length(a.trace) and b.trace[J].bool=true)`,
   where `J=firstMismatch(a.trace,b.trace)`; and
   `P(b returns x>10) != P(J<length(aPrime.trace) and b.trace[J].bool=false)`,
   with `J` now formed from `aPrime`. Only the pool is random here.
4. On a uniform pool with `K=5000`, at `alpha=1/20,epsilon=1/50`, let
   `E` mean that the uncorrected approximate upper run has at least two
   trace entries and its second Boolean is true. Then
   `P(E)>=4693104776190294207/5012394999999664375>9/10`, and
   `16 exp(-4)<48/103<9/10`.

## General procedure and cost definitions

`treatedCounts(v,z)` counts the four canonical types in `z`.
For seeds `s0,s1`, put `control0=(s0 mod d < d-q.d)` and
`control1=(s1 mod a < a-q.a)`. `updateTreated(v,q,s0,s1)` returns
`(if control1 then q.a else q.a-1,
  if control1 then q.b else q.b+1,
  if control0 then q.c else q.c+1,
  if control0 then q.d else q.d-1)`.
`reusedSamples(v,initial,seeds,0,i)` is the treated count of initial draw
`i`. At time `t+1` it applies this update at population `reuseVector(v,t)`
to the preceding count, using seed pair `(t,i)` if `t<n`, otherwise zeros.
Each provided seed lies in `{0,...,n!-1}`. No claim treats successive reused
vectors as independent.

For any real-valued function `R(observed,population)`, define
`rankValue(R,o,v,samples)=(1+sum_{i<K}1_{|R(O(v,samples_i),v)|>=|R(o,v)|})/(K+1)`.
`GeneralSpace(n,m,K)` is the finite product of an observed assignment,
an independent array of initial assignments indexed by
`(i,j) in {0,...,n}^2` and draw `iDraw<K`, and an independent array of pairs
of factorial seeds indexed by that pair, time `<n`, and draw `<K`.

`generalSet(alpha,theta,R,o,initial,seeds)` contains the real `t` exactly when
there exist `(i,j) in {0,...,n}^2`, a vector `v` returned by
`firstOnLine(o, reverse(candidateNumerators(o))[i],j)`, and a natural `k`
with `k<=n`, `k<=v.a`, `k<=v.d`, and `Possible(o,reuseVector(v,k))`, such
that `t=theta(reuseVector(v,k))` and its rank value at time `k` from that
line's reused samples is strictly greater than `alpha`. The reverse-list
lookup has a default zero when out of range, but for `N(o)=n` every
`i<=n` is in range.

Let `G(o,K)` be `K` times the number of nonempty `(candidate numerator,j)`
lines, with `0<=j<=N(o)`. Let `U(o,K)` be the sum over those lines of
`K` times the number of `k=1,...,N(o)` with `k<=v.a,v.d` and possible
`reuseVector(v,k)`, starting at their `firstOnLine` vector. Then
`Ops(o,K,c0,c1,c2)=c0(N(o)+1)^2+2c1 N(o)G(o,K)+2c2 U(o,K)`.
The additionally defined `generalEnvelope` is
`(n+1)^2(c0+2(c1+c2)Kn)`. The ceiling budget is
`Krec(epsilon,n)=ceil_nat(log(4n log2(n)/epsilon)/(2epsilon^2))`.
`balancedEnvelope(epsilon,c,n)=4c Krec(epsilon,n)n^2 log2(n)`.

`upperShuffleCost(alpha,epsilon,o,pool)` is the corrected upper run's trace
length times `K(n-1)`, for assignments of size `floor(n/2)` in ambient size
`n`. Its expected value is the arithmetic mean over all such pools, and
does not average over observed data.

## SAP.P003b.T35

The conjunction of:

1. For every population `v`, then naturals `m,K`, real `alpha`, real-valued
   functions `theta:Counts->R` and `R:Counts->Counts->R`, if
   `0<m<N(v)`, `K>0`, and `0<alpha<1`, the uniform probability on
   `GeneralSpace(N(v),m,K)` that `theta(v)` belongs to the general set
   constructed from its observed vector, initial samples and seeds is at
   least `1-alpha`.
2. For every `v`, then `m`, with `0<m<N(v)`, `a>0`, `d>0`, then every
   count vector `qPrime`, the probability that one update of the treated
   count of a uniform assignment, using two independent uniform seeds in
   `{0,...,N(v)!-1}`, equals `qPrime`, is
   `designProb(reuseVector(v,1),m,q=qPrime)`.

## SAP.P003b.T36

The conjunction of:

1. For every observed vector `o`, natural `K`, real `c0,c1,c2`, if all
   three constants are nonnegative, then
   `G(o,K)<=(N(o)+1)^2 K` and
   `U(o,K)<=(N(o)+1)^2 N(o)K`; and, if additionally `N(o)>=1,K>=1`,
   `Ops(o,K,c0,c1,c2)<=4(c0+2(c1+c2))K N(o)^3`.
2. For every triple of nonnegative real constants, every count-vector-valued
   function `o(n,K)` whose total is `n` for **every** pair, if its treated
   and control arms are eventually positive on the joint `atTop` filter,
   `Ops(o(n,K),K,c0,c1,c2)=O(K n^3)` on that same filter.

These are statements about the defined arithmetic cost, which does not charge
for enumerating possible tables to construct `firstOnLine`.

## SAP.P003b.T18

Four independently universally quantified clauses:

1. For every real `alpha,epsilon,c` with `0<alpha<1`,
   `0<epsilon<alpha`, `c>=0`, then every natural-valued `tests(n)` and
   real-valued `operations(n)`, if `operations(n)>=0` for every `n`,
   eventually `tests(n)<=4n log2(n)`, and eventually
   `operations(n)<=tests(n) Krec(epsilon,n) c n`, then
   `operations(n)=O(n^2(log n)^2)` as `n` tends to infinity.
2. For every natural `r>=4`, then natural `K>0`, put `n=2^r` and
   `o=(0,n/2,0,n/2)`. The uniform pool probability that the corrected upper
   shuffle cost at `alpha=1/2,epsilon=1/8` is at least
   `(n/4+1)K(n-1)` is strictly positive. If also `r>=6` and
   `K>=32 log(32n log2(n))`, its expectation is at least
   `(n/4+1)K(n-1)/2`.
3. For every real `c>=0`, the expected upper shuffle cost on that dyadic
   family, with `K=Krec(1/8,n)`, is **not** `O(n (log n)^c)` as natural
   `r` tends to infinity. The real exponent uses Mathlib `Real.rpow`.
4. For every natural `n>=15`, `log2(n)<=(log n)^2`.

The cost upper bound in clause 1 is conditional on the two stated eventually
valid bounds; it does not itself prove them for the implemented search.
