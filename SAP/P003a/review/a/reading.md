# Blind mathematical reading

This file was written and saved after reading all supplied Defs and Challenge files, before opening either `claims.json` or `record.json`. The Challenge declarations are stubs; this reading concerns their types, not their proofs. All names below are in `SAP.P003a`.

## Common definitions, expanded

`Counts` is a quadruple `(a,b,c,d)` of natural numbers. Its total is `n=a+b+c+d`, its signed effect numerator is the **integer** `b-c`, and its effect is the rational `(b-c)/n`, embedded in the reals when called `tau`. For population counts the cells denote potential outcomes `(1,1),(1,0),(0,1),(0,0)`. For observed counts they denote `(treated,success),(treated,failure),(control,success),(control,failure)`. The observed estimator is the rational `a/(a+b)-c/(c+d)`, again embedded into the reals as needed. Division is field division (zero denominator gives zero in Lean); the experiment hypotheses in the coverage statements and the numerical witnesses provide positive denominators.

For population `v` and treated size `m`, `randomStates v m` enumerates quadruples `q` with `0≤q_i≤v_i` and `sum q_i=m`: it loops over `a≤min(v.a,m)`, `b≤min(v.b,m-a)`, `c≤min(v.c,m-a-b)` and sets `d=m-a-b-c`, keeping it if `d≤v.d`. Subtractions here are natural truncated subtractions, but the preceding bounds prevent truncation from changing any intended residual. The weight of `q` is `W(v,q)=choose(v.a,q.a) choose(v.b,q.b) choose(v.c,q.c) choose(v.d,q.d)`. SAP's `binomial` is Mathlib's `Nat.fast_choose`, defined by a descending factorial divided by a factorial and equal to `Nat.choose` (`Mathlib/Data/Nat/Choose/Basic.lean`, `choose_eq_fast_choose`).

The observed table for state `q` is `(q.a+q.b, q.c+q.d, v.a-q.a+v.c-q.c, v.b-q.b+v.d-q.d)`. Its natural subtractions agree with ordinary subtraction on admissible states. `designProb v m E` is the finite weighted sum of `1_E(q) W(v,q)` divided by `choose(n,m)`, as a real. Thus for `0<m<n` it is the uniform law on the labeled size-`m` assignments, compressed by potential-outcome type.

For an observed table `o`, write `m=o.a+o.b`. Define the integer

`A(v,o,m)=n((n-m)o.a-m o.c)-m(n-m)(v.b-v.c)`.

`tailCount v o` sums `W(v,q)` over states with `|A(v,observed(v,q),m)|≥|A(v,o,m)|`. `pValue v o` is this count divided by `choose(n,m)` as a rational. If `n=o.total` and both observed arms are positive, this is precisely the two-sided randomization tail `P_v(|estimate(O)-tau(v)|≥|estimate(o)-tau(v)|)`, **including ties**. At rational level `alpha`, `levelAccepted` tests `alpha≤pValue` by cross multiplication; its zero-denominator branch instead tests `alpha≤0`. The uses with positive valid arms have positive denominators.

`possibleTables o` enumerates, for `0≤i≤o.a`, `0≤j≤o.b`, `0≤k≤o.c`, `0≤l≤o.d`, the vectors

`(i+k, o.a-i+l, o.c-k+j, o.b+o.d-j-l)`.

These are population counts with some unit-level potential-outcome completion consistent with the observed cells. `Possible o v` is membership in this list. `accepted alpha o` is the finite set of real `tau(v)` for such possible tables satisfying `alpha≤pValue(v,o)`. `exactInterval alpha o` consists of all real `t` with accepted effects `l,u` such that `l≤t≤u`. It is the closed interval between the minimum and maximum accepted effects if any exist, and is empty otherwise. `lower` and `upper` are Mathlib real `sInf` and `sSup` of that finite set; they are its extrema when nonempty. `acceptedEffectsQ` lists accepted **integer effect numerators**, removing duplicate population tables before testing. `intervalQ` is `none` if that list is empty, and otherwise returns its minimum and maximum divided by `o.total`. No formula asserting `sInf` or `sSup` of an empty set is used to define the empty interval.

A missing mask `r` is a quadruple with `0≤r_i≤o_i`, enumerated once by `missingMasks o`; its cells count missing outcomes in the corresponding complete-data cells. Extremal imputation gives

* plus: `(o.a+r.b, o.b-r.b, o.c-r.c, o.d+r.c)`;
* minus: `(o.a-r.a, o.b+r.a, o.c+r.d, o.d-r.d)`.

All count completions are `(o.a-r.a+t, o.b-r.b+r.a+r.b-t, o.c-r.c+s, o.d-r.d+r.c+r.d-s)` for `0≤t≤r.a+r.b` and `0≤s≤r.c+r.d`, with the parentheses of the Lean definition understood. For valid masks no subtraction is truncated improperly. `completionUnion` is the union of the exact intervals of these completions; `completionHull` is its existential closed interval hull and is empty for an empty union.

`missingInterval alpha o r` is the closed interval with lower endpoint `min(lower(alpha,minus), estimate(minus))` if the minus accepted set is nonempty, and `estimate(minus)` otherwise, and upper endpoint `max(upper(alpha,plus),estimate(plus))` if the plus accepted set is nonempty, and `estimate(plus)` otherwise. `missingIntervalQ` uses the same guarded definition via `intervalQ`.

`IsMissingLaw v m mu` requires, for every admissible state `q` and every valid mask `r` for `observed(v,q)`, `mu(q,r)≥0`, and, for every such `q`, the sum of these masses over all its valid masks to equal `W(v,q)/choose(n,m)`. Values off these finite supports are unrestricted and unused. `missingProb` is the finite sum of `mu(q,r)` over the supported pairs satisfying its event. It permits arbitrary dependence of missingness on the assignment state.

`PotentialTable n` is a function from the `n` labels `Fin n` into Boolean potential-outcome pairs `(Y(1),Y(0))`. `bit` embeds false and true as real 0 and 1. `tableCounts` counts the four pairs; `tableTau` is `sum_i(Y_i(1)-Y_i(0))/n`. `Assignment n m` is the finite type of `m`-element subsets of `Fin n`. `tableEstimator w z` is the treated potential-outcome average minus the control potential-outcome average, with denominators `|z|` and `n-|z|`. `unitOutcomes w z` selects the treatment potential outcome on `z`, control elsewhere. `PossibleTable y z w` means this selected outcome function equals `y`. `outcomeEstimator y z` uses the observed Boolean outcomes with those same averages. `unitObserved` counts the four assignment/outcome cells. `uniformProb E` is `|{omega:E(omega)}|/|Omega|` for a finite type `Omega`; an empty type would give zero, but valid assignment sizes below avoid this.

`unitPlus y z r` sets outcomes in the missing label set `r` to 1 on `z` and 0 off `z`, keeping `y` elsewhere. `coupledPlus w yPlus z` replaces only the potential outcome observed under `z` by `yPlus`, preserving the other potential outcome. `unitPValue w y z` is the uniform probability over `q:Assignment n |z|` of `|tableEstimator(w,q)-tableTau(w)|≥|outcomeEstimator(y,z)-tableTau(w)|`.

`SDShape f c2` means `f(c2-i)=f(i)` for every integer `i`, and `f(j)≤f(i)` whenever the integers satisfy `c2≤2i` and `i≤j`. Thus the center is `c2/2`, allowed to be a half integer, and masses decrease away from it. `IsPMF f` requires nonnegative masses on the integers, `Summable f`, and `sum_i f(i)=1`. `IsMass f` additionally requires `Summable(i↦i f(i))`. `IsSD f` means `IsMass f` and existence of an integer `c2` with mean `sum_i i f(i)=c2/2` and `SDShape f c2`.

Here Mathlib `Summable` means existence of the unconditional limit of finite partial sums (`Topology/Algebra/InfiniteSum/Defs.lean`); for real families it is equivalent to absolute summability (`summable_abs_iff`, `Topology/Algebra/InfiniteSum/Order.lean`). Its `tsum` would default to zero for a nonsummable family; `IsMass` explicitly rules out using this convention for the first moments in these statements. `fairMass` puts mass 1/2 at 0 and 1; `dependentSumMass` puts mass 1/2 at 0 and 2; `zeroMass` puts mass 1 at 0. `smoothMass f(i)=(f(i)+f(i-1))/2`. `paritySmooth f p(i)=f((i-p)/2)/2`, with Euclidean integer division (floor for positive divisor 2). Thus both `p+2k` and `p+2k+1` have mass `f(k)/2`. `PrintedDecrease f` means nonincreasing on **the whole integer line**: every `i<j` has `f(j)≤f(i)`. `latticeMean k g=sum_j (j/k)g(j)` uses the physical coordinates `j/k`.

For the search definitions, all bounds and queried indices are integers; `(a+b)/2` uses integer floor division. `searchStep f a b` queries the midpoint `c` and returns `(a,c)` if `f(c)=true` (rejection), `(c,b)` otherwise. `printedReturn k1 k2 a b f` returns only when `b=a+1`: it gives `a` if `a>k1` and `b<k2`; otherwise, if `a=k1`, it gives `k1-1` or `k1` according as `f(k1)` is true or false; otherwise, if `b=k2`, it gives `k2-1` or `k2` according as `f(k2)` is true or false; otherwise none. `printedSearch` performs the step first, then tries this return rule, recursively using one fuel unit per iteration; zero fuel returns none. `sentinelSearch` instead returns `(a,[])` immediately if zero fuel or `b≤a+1`; otherwise it queries the midpoint, recurses on the indicated bracket, and prepends the query to its trace. `logTwo x=Real.log(x)/Real.log(2)`.

For table searches `candidateNumerators o` lists `o.a-o.c-(o.a+o.b)+k`, for natural `k=0,...,o.total`, as **integers**. `lineGroup o x j` filters the possible population tables to those with effect numerator `x` and treatment-potential-success total `v.a+v.b=j`. `firstOnLine` is none for an empty group, otherwise a table with minimum `v.b`, ties chosen by list order. `reuseVector v k=(v.a-k,v.b+k,v.c+k,v.d-k)` uses natural subtraction; the explicit bounds `k≤v.a,v.d` in T22 make it ordinary subtraction.

`candidates o x` visits `j=0,...,o.total`, taking the first table on each nonempty line; if it has `b=c=0`, positive `a,d`, and `(a-1,1,1,d-1)` is possible, it also tests that second table. `runTests` tests the ordered list until a table is not rejected; it increments a test index on every test, returns whether there was such a table, and records all tested tables and decisions. `adaptiveSearch` tests these candidates at the midpoint and follows the compatibility decision. With `corrected=false` it uses the same printed boundary return rule, re-testing boundary candidates and using the first matching boundary case; fuel exhaustion yields none. `upperRun false o reject` starts with `k1=2(o.a-o.c)`, `k2=o.a-o.c+(o.a+o.b)`, bracket `(k1,k2)`, test index 0 and fuel `o.total+3`. `exactRejectQ alpha o v idx` ignores the index and rejects precisely when the rational acceptance test fails.

## SAP.P003a.T29

For every natural count vector `v`, natural `m`, and real `alpha`, if `0<m<v.total` and `0<alpha<1`, then the design probability that `tau(v)` belongs to `exactInterval alpha (observed v q)` is at least `1-alpha`. The ordering is `forall v, forall m, forall alpha`, followed by these two hypotheses and the conclusion. No missingness or balance is assumed.

## SAP.P003a.T1

A conjunction of numerical and mask facts, with no external hypothesis. Let `v=(11,0,3,6)`, `alpha=109/500`, `o=(0,3,11,6)`, `oPlus=(0,3,10,7)`, and `r=(0,0,1,0)`. Then `n=20`, `choose(20,3)=1140`, `0<3<20`, `0<alpha<1`, and `tau(v)=-3/20`. The exact rational intervals for `o` and `oPlus` are respectively `[-7/10,-3/20]` and `[-13/20,-1/5]`; the guarded two-extreme interval for `(o,r)` is `[-7/10,-1/5]`.

Define `badMask(q)=r` if `q=(0,0,3,0)` and zero otherwise. Define `badCoverage` as the sum of the assignment weights for states whose guarded missing interval contains `tau(v)`, divided by 1140. Then `badCoverage=297/380<1-alpha`; all state weights sum to 1140; and **for every count vector q**, `badMask(q)` is a valid mask for `observed(v,q)` (including vectors not in the randomization support). Moreover, the p-values of `v` at both displayed observed tables are `83/380>alpha`; `v` is possible for `o` and impossible for `oPlus`; and the two observed estimates are `-11/17` and `-10/17`.

## SAP.P003a.T2

Three universally quantified assertions are conjoined.

1. For every `v,m,alpha`, if `m>0`, `v.total=2m` and `0<alpha<1`, then for every joint mass function `mu` satisfying `IsMissingLaw v m mu`, its probability that `tau(v)` belongs to the guarded two-extreme missing interval is at least `1-alpha`.
2. For every `o,r,alpha`, if `0<alpha<1`, `0<o.a+o.b=o.c+o.d`, and `r` is a valid mask, then `completionUnion alpha o r` is a subset of `missingInterval alpha o r`.
3. For every natural `n,m` with `m>0,n=2m`, Boolean outcome functions `y,y'` on `Fin n`, label sets `z,r` with `|z|=m`, and potential table `w`, assume `y'=y` outside `r` and `w` is possible for `(y',z)`. For every real `alpha` with `0<alpha<1`, additionally assume `alpha≤unitPValue(w,y',z)` and `outcomeEstimator(unitPlus(y,z,r),z)<tableTau(w)`. Put `yPlus=unitPlus(y,z,r)`, `D={i:y'(i)≠yPlus(i)}`, `d=|D|`, `wPlus=coupledPlus(w,yPlus,z)`. Then `wPlus` is possible for `(yPlus,z)`, its effect is `tableTau(w)+d/n`, and the plus observed estimator is the previous estimator plus `2d/n`. For every size-`m` assignment `q`, put `N=|{i in D:(i in q iff i in z)}|`; then `N≤d`, the coupled estimator is the old estimator plus `2N/n`, and the absolute difference between the two centered estimators is at most `d/n`. The absolute observed deviation decreases by exactly `d/n` (real, not truncated subtraction). Also `unitPValue(w,y',z)≤unitPValue(wPlus,yPlus,z)`, the latter is at least `alpha`, and `upper(alpha,unitObserved(yPlus,z))≥tableTau(wPlus)≥tableTau(w)`.

## SAP.P003a.T3

The following six assertions are conjoined.

1. For every `v,m,alpha` with `0<m<v.total`, `0<alpha<1`, and then every `mu` satisfying `IsMissingLaw v m mu`, both the completion union and its closed hull cover `tau(v)` with joint probability at least `1-alpha`.
2. For every real `alpha` and counts `o,r`, if both arms of `o` are positive and the mask is valid, `exactInterval alpha o` is contained in `completionUnion alpha o r`.
3. For every such `alpha,o,r` with the same hypotheses, the union is contained in its hull.
4. For every `o,r` with a valid mask, `o` occurs among the completions, this completion list has no duplicates, and its length is `(r.a+r.b+1)(r.c+r.d+1)`.
5. The complete-data coverage assertion of T29 holds, with the same quantifiers and hypotheses.
6. For `alpha=109/500`, `o=(0,3,11,6)`, `r=(0,0,1,0)`, the rational completion hull is `[-7/10,-3/20]`. Under T1's population, randomization, and mask function, its exact coverage is `892/1140`, which is at least `391/500`.

## SAP.P003a.T4

Two sets of counterexample facts are conjoined. First `0<1<2` in the integers. On the integer domain `[1,2]`, the constant-false decision satisfies `f(x)=false iff x≤2`, and the constant-true decision satisfies `f(x)=false iff x≤0`. The one-fuel printed search on bounds and bracket `(1,2)` with constant false returns `some 1`, and does not return `some 2`. A step on `(1,2)` with constant true yields `(1,1)`. For **every natural fuel**, the constant-true printed search returns none both from bracket `(1,1)` and from `(1,2)` (with bounds 1 and 2).

Second, let `o=(7,1,0,8)`. Its estimate is `7/8`; populations `(0,14,0,2)` and `(0,15,0,1)` are possible and both have p-value 1; the rational exact interval at `alpha=1/20` is `[1/2,15/16]`; and the executed `upperRun false` with exact rejection at that level returns integer numerator 14. The execution is the finite-fuel, ordered-candidate algorithm expanded above.

## SAP.P003a.T5

First, for every integer `k1,k2,r` and Boolean decision function `f`, if `k1≤k2`, `k1-1≤r≤k2`, and every integer `x` in `[k1,k2]` satisfies `f(x)=false iff x≤r`, put `d=k2-k1+1` as a natural and run `s=sentinelSearch(d+1,f,k1-1,k2+1)`. Its result is `r`; its trace has no duplicates; every queried integer lies in `[k1,k2]`; and its length is at most `floor(log_2 d)+1` (comparison in the reals after casts).

Second, for every `k1,k2,f` with only `k1≤k2`, the very same run has a duplicate-free trace within `[k1,k2]`, the same logarithmic length bound, and endpoint in `[k1-1,k2]`. This second assertion does not assume a threshold rule for `f` and does not separately assert final adjacency.

## SAP.P003a.T11

Let `q(x)=1` for real `x≤0` and zero otherwise. Then for every real `x`, `q(x)<1/2 iff x>0`; some real `x` rejects; and there is no real rejecting `x` that is no larger than every rejecting real `u`. Separately, for every real `x`, the design tail probability `P(x≤|estimate(O)-tau(v)|)` for `v=(0,0,0,2)` and `m=1` equals this function `q(x)`. This states one concrete law and one concrete level, not a general no-minimum theorem.

## SAP.P003a.T12

For every finite type `Omega`, real functions `w,D` on it, hypotheses `w(i)>0` for every `i` and `sum_i w(i)=1`, real `alpha` with `0<alpha<1`, define `Q(x)=sum_i 1_{x≤D(i)}w(i)`. Then either every attained value has `Q(D(i))≥alpha`, or there exists an index `i` with positive weight, `Q(D(i))<alpha`, such that, for every `j`, `Q(D(j))<alpha iff D(i)≤D(j)`, and the total weight of rejecting indices equals `Q(D(i))`. In either case the total rejecting weight is strictly less than `alpha`. Normalization excludes the empty finite type; deviations `D` are otherwise arbitrary real values, not required nonnegative or distinct.

## SAP.P003a.T13

For every positive natural `n` and every potential table `w` on `n` labeled units, its four cell counts sum to `n`, the sum of treatment potential outcomes equals its `(a+b)` cell count, the sum of control potential outcomes equals its `(a+c)` count, and `tableTau(w)=(b-c)/n=tau(tableCounts(w))`. In addition, `tauQ(10,0,0,10)=0` whereas `(10-0)/20=1/2`, and `tauQ(0,20,0,0)=1` whereas `(0-0)/20=0`. The latter equalities are numerical facts about the alternative numerator `a-c`.

## SAP.P003a.T14

Three assertions are conjoined. For every integer-indexed normalized summable nonnegative mass function `f`, `PrintedDecrease f` is false. Both the mass at zero and the fair mass on `{0,1}` satisfy `IsSD`; the mass at zero also explicitly fails `PrintedDecrease`. The fair law has first moment `1/2`. Finally, for every positive natural `k` and real mass function `g` satisfying **IsMass**, `sum_j g(j)=1` and `latticeMean(k,g)=(sum_j j g(j))/k`. For every integer `j` the mass defined by `if 2j=1/2 then 1 else 0` is zero; this last witness is included under the same quantifiers but is independent of `k,g`. There is no separate function of a rational coordinate denoting a mass on `k^{-1}Z` in this proposition: coordinates are represented by the index convention `j↦j/k` in the definitions.

## SAP.P003a.T9

The fair law on `{0,1}` is SD and has mean `1/2`; the half-at-zero, half-at-two law is an `IsMass` law with mean 1, mass zero at 1, mass `1/2` at 2, and fails `IsSD`. For every integer `i`, summing over the two Boolean values with mass `1/2` each gives the fair mass for `B` and gives `dependentSumMass(i)` for `B+B`. Thus the displayed laws are explicitly the marginal and sum laws of two identical fair Boolean random variables. No general dependent-sum theorem is asserted.

## SAP.P003a.T10

For every integer-indexed real `f`, `IsSD f` implies `IsSD((f(i)+f(i-1))/2)`. Separately, for every `f` and integer `c`, **only** `SDShape f c` is assumed to conclude `SDShape(smoothMass f)(c+1)`; this clause assumes neither nonnegativity nor summability nor normalization. Finally, for every `f` satisfying `IsSD` and integer `p` with `p=0 or p=1`, `paritySmooth f p` is SD and for every integer `k` its masses at both `p+2k` and `p+2k+1` equal `f(k)/2`. The convolutions encode independent fair Bernoulli smoothing by their formulas.

## SAP.P003a.T15

For every population count vector `v` and natural `m`, if `m>0`, `v.total=2m`, and `v.b+v.c≥1`, then `j↦P_v(m*estimate(O)=j)` for integers `j` satisfies `IsSD`. The equality inside this probability is rational equality; the resulting probabilities are real. Thus the random variable is the integer-scaled estimator in a balanced design, and the conclusion includes nonnegativity, normalized summability, an absolutely summable first moment, and symmetry/decrease about its half-integer mean.

## SAP.P003a.T16

For every natural `n`, potential table `w`, treated label subset `z`, and natural `m` with `m>0`, `n=2m`, and `|z|=m`,

`tableEstimator(w,z) = (sum_i [Y_i(1) if i in z, else -Y_i(0)])/m`.

In addition, define the integer contribution of an oriented pair `(w1,w2)` as `Y_1(1)-Y_2(0)` for Boolean orientation true and `Y_2(1)-Y_1(0)` for orientation false. Its ordered outcomes (true,false) are, respectively: `(0,1)` for pair `(10,11)`; `(1,1)` for `(10,10)`; `(0,0)` for `(10,01)`; `(1,0)` for `(10,00)`; `(0,0)` for `(11,11)`; and `(1,-1)` for `(11,00)`. These are deterministic outcome identities; no sampling construction or independence of a remaining assignment is asserted.

## SAP.P003a.T17

Define `V(o)=o.a*o.b/(o.a+o.b)^3+o.c*o.d/(o.c+o.d)^3` in the reals, `SE(o)=sqrt(V(o))`, and for a fixed real `C` define `R_C(o,v)=C` if `SE(o)=0`, otherwise `(estimate(o)-tau(v))/SE(o)`.

For every real `C` and count vectors `o,v`, if both arms of `o` are positive and `v.total=o.total`, then `V(o)≥0`, `SE(o)=0 iff o.a*o.b=0 and o.c*o.d=0`, the statistic equals `C` when `SE=0`, and it equals the quotient when `SE>0`. For every `C`, `o=(0,2,0,3)` has `V=SE=0`, its estimate minus `tau(0,0,1,4)` is `1/5`, and its extended statistic equals `C`. Under population `(0,0,1,4)` and treated size 2, the two-sided exact tail at this observed statistic is 1 for `C=0`, and `2/5` for `C=10^6`.

Finally, for every `v`, naturals `m,K`, reals `alpha,C` with `0<m<v.total`, `K>0`, `0≤alpha≤1`, draw the observed assignment and `K` Monte Carlo assignments independently and uniformly from `Assignment v.total m` (the uniform law on their finite product). Represent `v` by a canonical labeled table consisting of consecutive blocks of the four types. Form the observed counts from the first assignment and treated type-count states from the other `K`. Define

`rank=(1+sum_{i<K} 1_{|R_C(O_i,v)|≥|R_C(O_0,v)|})/(K+1)`.

Then the probability that `rank≤alpha` is at most `alpha`. The real extension `C` is fixed before all these draws, and ties are counted inclusively.

## SAP.P003a.T21

At rational level `17/18` with observed counts `(1,6,0,2)`, the accepted integer effect-numerator set is exactly `{0,1}` and the rational interval is `[0,1/9]`. The observed estimator is `1/7`, which does not lie in this interval. The p-value for population `(1,0,1,7)` is `29/36<17/18`. This proposition does not separately assert that this latter population is possible.

## SAP.P003a.T22

For every observed count vector `o` and possible population vector `u`, the effect numerator of `u` is in `candidateNumerators o`, and `u.a+u.b≤o.total`. There exists a count vector `v` such that `firstOnLine o u.effect (u.a+u.b)=some v`, and then there exists a natural `k≤o.total` with `k≤v.a`, `k≤v.d`, and `u=reuseVector v k`. The order is `forall o,u`, possible-table hypothesis, membership/bound, `exists v`, first-on-line equality, `exists k`, the bounds and representation.

Additionally, for `o=(0,1,0,1)` the distinct possible vectors are exactly `(0,0,0,2),(0,0,1,1),(0,1,0,1),(0,1,1,0)`. For numerator 0 and treatment-success total 0 the first table is `(0,0,0,2)`; for numerator 0 and treatment-success total 1 it is `(0,1,1,0)`. There is no positive-arm assumption here; the combinatorial assertion also covers zero arms and empty populations.

## SAP.P003a.T23

For every integers `k1,k2,u` and function `f:Z→Bool`, if `k1≤k2`, run the corrected sentinel search with fuel `k2-k1+2`, initial bracket `(k1-1,k2+1)`, obtaining endpoint `e` and ordered trace `L`. Every queried integer `c` with `f(c)=true` satisfies `e<c`. If `u≤e`, then every queried `c≤u` has `f(c)=false`. For every natural trace positions `i<j<length(L)`, if `f(L[i])=true`, then `L[j]<L[i]`. Lean uses defaulted list indexing in the last clause, but the explicit index bounds make both accesses in range. No monotonicity, probability model, stochastic error guarantee, or unqueried-index assertion is assumed or concluded.
