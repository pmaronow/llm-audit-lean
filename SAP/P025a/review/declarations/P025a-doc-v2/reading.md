# Blind source and closure reading

This file was saved before opening `claims.json`, `record.json`, or `binding.json`.
The review covers the eleven declarations in `closure.json`, not an omission task.
All 43 entries of `INPUT-INVENTORY.json` matched SHA-256 before any review output
was written. Hashing those files did not display or interpret claim, record, or
binding contents. The inventory's own SHA-256 is
`7cc7a4b2b71254f15a367eb1b18402d779b011add4cdb8ee7267a0de357c6f2e`.

I read both Challenge files, the Defs import file, and all nine Defs component
files in full, including every named source definition in the eleven closures.
Line-zero closure entries are generated proofs at the array-index, finite-index,
and other proof-valued source expressions, not additional adjustable premises.
Their enclosing source expressions were read. I have not printed their compiled
proof terms or rechecked the supplied proof certificate. No prior review,
handoff, integration narrative, run log, or other campaign material was read.

## Notation, fully expanded to finite sums, sets, and Mathlib notions

This dictionary applies to every section below; a symbol here always means the
displayed expression, not an additional assumption. All outcomes, masses,
probability bounds, and weights are real numbers. Indices `Fin n` are the
integers `0,...,n-1`; cuts count the entries strictly before them.

* `M(y) = (sum_i y_i)/n` is the population/sample arithmetic mean on `Fin n`.
* `R(y,a,w) = (sum_i a_i w_i y_i)/(sum_i a_i w_i)` on a finite type.
* `B(α,β) = {w : for every i, 1/β ≤ w_i ≤ 1/α}`.
  `Bγ = {w : for every i, 1 ≤ w_i ≤ γ}`.
* `Lγ(k)_i = γ` for `i<k`, and `1` otherwise;
  `Hγ(k)_i = 1` for `i<k`, and `γ` otherwise.
  `l(k)=R(y,a,Lγ(k))`, `h(k)=R(y,a,Hγ(k))`.
  Original-scale lower weights are `1/α` before the cut and `1/β` after it;
  original-scale upper weights reverse those two values. They equal
  `(1/β)Lγ(k)` and `(1/β)Hγ(k)` when `γ=β/α` and the bounds are positive.
* `A(y,a,α,β) = {v : there exists a function w in B(α,β) with R(y,a,w)=v}`;
  its normalized counterpart uses `Bγ`. Endpoints are `sInf A` and `sSup A`.
  `IsLeast A v` means `v∈A` and `v≤x` for every `x∈A`;
  `IsGreatest` has the reversed inequality. No uniqueness of weights follows
  merely from uniqueness of an extreme real value.
* The corrected lower cut is the least `k∈Fin n` such that `l(k)≤y_k`.
  The upper cut is the least `k∈Fin n` such that `h(k)≤y_k`.
  The printed lower cut instead uses `y_k≤l(k)`. Leastness includes membership
  and comparison with every other qualifying finite index.
* `N_L(k)=γ sum_{i<k} a_i y_i + sum_{k≤i} a_i y_i` and
  `D_L(k)=γ sum_{i<k} a_i + sum_{k≤i} a_i`.
  `N_H(k)=sum_{i<k} a_i y_i + γ sum_{k≤i} a_i y_i` and
  `D_H(k)=sum_{i<k} a_i + γ sum_{k≤i} a_i`.
* The printed lower expression is `none` unless `2≤k≤n`. Otherwise it is
  `some ((γ sum_{i<k} a_i y_i + sum_{k-2≤i} a_i y_i) /
  (γ sum_{i<k} a_i + sum_{k-2≤i} a_i))`.
  Thus the two positions `k-2,k-1` occur both in the prefix and in the tail.
* For a finite sampling law with mass `p_ω` and sample `S_ω`, actual unit
  inclusion is `π_i=sum_ω p_ω 1{i∈S_ω}`. Class mass for a map `c` is
  `a_j=sum_{i:c(i)=j} π_i`; class size is the cardinality of that fiber.
* `bL(p,γ)=p/(γ(1-p)+p)`, `bH(p,γ)=γp/(1-p+γp)`, and
  `I(p,γ)=[bL(p,γ),bH(p,γ)]`, a real closed interval.
  `Q(p,π1,π0)=(p/π1)/(p/π1+(1-p)/π0)`.
  `O(pG,pE)=pG(1-pE)/((1-pG)pE)`.
* A quota family is the set of all subsets of `Fin N` with cardinality `s`.
  Its uniform mass is the reciprocal of its cardinality. Its marginal for a
  labeled unit is the number of members containing that unit divided by the
  family cardinality. A joint product mass is the product of coordinate masses.
  Event probability is the finite sum of mass times the event indicator.
  Coordinate independence here asserts factorization for every rectangular
  event, with an arbitrary event in every coordinate.
* An affine segment of weights is `w(t)=(1-t)wL+t wH`. `ContinuousOn` below is
  ordinary real continuity on the closed interval `[0,1]`.
* The two-coordinate objective is
  `F(x,z)=(c1+xp u+zq v)/(c2+xp+zq)`.

### Shared totalization audit

Lean real division is total and `x/0=0`; none of the positive finite boxes used
in these statements has zero objective denominator. For `n>0`, positive masses,
and `0<α≤β≤1`, every admissible weight is positive, the attainable set is
nonempty (constant `1/β` works), and every ratio lies between the smallest and
largest outcome. Consequently real `sInf` and `sSup` do not use empty-set or
unbounded-set fallback values here. The same holds with normalized bounds
`γ≥1`. The definitions alone do not protect arbitrary out-of-domain arguments;
the theorem hypotheses or concrete data do.

Natural subtraction is truncated. It is used in `n-1` only under `n>0`, in
`n-k` only under `k≤n`, and in `k-2,k-1` in the printed-expression identities
only under `k≥2`. At printed cuts zero and one the expression returns `none`
before its invalid class indices could be used. This `Option` is an explicit
undefined-index convention, not a real value produced by division by zero.
Finite cardinalities are cast exactly to reals; no integer division occurs in
the real-valued fractions. Empty sums are zero and empty products one. Empty
prefixes and tails occur legitimately, while nonempty data keep their combined
denominators positive. There is no `Real.log`, real power, limsup, liminf,
conditional expectation, default partial-function value, or `ENNReal.toReal`
in the mathematical objectives.

## SAP.P025a.T1 — P025-T1

The theorem is the conjunction `T1WholeStatement`, not just a formula for a
generic estimator (`Challenge/Part1.lean:8`; `Defs/WholeW1.lean:103`). Its fixed
data are `y=(0,1)`, sample masses `(1,1)`, `α=1/2`, `β=1`, `γ=2`.

It asserts `0<1/2≤1`, sorted outcomes, printed lower cut zero,
`l(0)=1/2`, `l(1)=1/3`, upper cut one, `h(1)=2/3`, and
`1/2-1/3=1/6`. For every real `u,v`, in order assuming `1≤u≤2` and
`1≤v≤2`, it bounds `v/(u+v)` between `1/3` and `2/3`. It asserts the entire
attainable set is `[1/3,2/3]`, and that `1/3` is absent from `[1/2,2/3]`.
The feasible vectors `(2,1)` and `(1,2)` explicitly attain the two endpoints.

The actual two-unit finite design has two equiprobable outcomes: `{1}` and
`{0,1}`. The mass is nonnegative and sums to one; its inclusions are `(1/2,1)`;
the full sample has probability `1/2`. For every pair of Boolean values the
joint distribution of the two inclusion indicators factors into its marginal
distributions, including the zero events. Unit one's indicator is constant,
so this is genuine, though degenerate, independence.

For every `u,v` in the same box it additionally asserts positive denominator,

`v/(u+v)-1/3=((2-u)+2(v-1))/(3(u+v)) ≥ 0`,

`2/3-v/(u+v)=(2(u-1)+(2-v))/(3(u+v)) ≥ 0`.

The general clauses quantify first over `n>0`, then a nondecreasing function
`y:Fin n→R`, then `γ≥1`. They assert printed cut zero, `l(0)=M(y)`, and,
if `γ>1` and some `y_i>y_0`, `l(1)<l(0)` and `l(0)` is not the least
normalized attainable value. They also assert

`M(y)-y_0=sum_i(y_i-y_0)/n ≥ 0`,

`l(1)-M(y)=(γ-1)(y_0-M(y))/(n+γ-1)`.

A separate universally quantified clause uses the same sorted nonempty sample
and then `0<α≤β≤1`. With `γ=β/α`, the original-scale zero-cut vector is
constant `1/β`, feasible, and has ratio `M(y)≥y_0`; its printed cut is zero.
Under strict ratio and varying outcomes, changing only its first coordinate to
`1/α` is feasible and strictly lowers the ratio, so `M(y)` is not the minimum
over the original box. The exact change is the preceding displayed fraction.

The docstring describes a refutation of the printed lower rule plus a general
zero-cut diagnosis. All denominators are positive (`n+γ-1≥n>0`). Concrete
sampling realizability is supplied, rather than treating arbitrary class
masses as probabilities. No junk value supports the counterexample.

## SAP.P025a.T10 — P025-T10

This conjunction uses class outcomes `(0,1,2,3)`, masses `(1,1,1,1)`, and
`α=1/2,β=1,γ=2` (`Defs/Part2.lean:46`, `Defs/WholeW1.lean:192`). Outcomes
are strictly increasing. The corrected lower cut is two and `l(2)=7/6`.
At that cut the printed expression is `some 1`, with `1≠7/6`. The printed
stopping rule chooses zero, where the expression is `none`. Also
`l(0)=3/2`, `l(1)=6/5`.

For every `w:Fin 4→R` in `[1,2]^4`, the theorem bounds `R≥7/6`, asserts
`sum w_i>0`, and gives

`R-7/6 = [7(2-w0)+(2-w1)+5(w2-1)+11(w3-1)]/(6 sum w_i) ≥ 0`.

Equality is equivalent to `w=(2,2,1,1)`. Thus uniqueness is explicitly in the
normalized box, not uniqueness after arbitrary rescaling. It supplies this
feasible vector, an attained minimum `7/6` over the original box, and the
`sInf` equality.

The underlying six-unit outcomes are `(0,0,1,1,2,3)`, with the same vector as
the map to the four class labels. A draw chooses independently a label from
each of `{0,1}` and `{2,3}`, and includes both units `4,5`; its four outcomes
have mass `1/4`. The assertions give normalization, inclusions
`(1/2,1/2,1/2,1/2,1,1)`, bounds `[1/2,1]` on every inclusion, class totals
all one, class sizes `(2,2,1,1)`, compatibility of unit and class outcomes,
and population mean `7/6`. Every class-size/class-mass ratio equals its
corresponding coordinate of `L2(2)`.

The only undefined object is the explicitly `Option`-valued literal lower
display at cut zero. The optimizer failure and residual certificate have
strictly positive real denominators and do not depend on that convention.

## SAP.P025a.T11 — P025-T11

This is a conjunction of `T11Statement`, a sample proof-repair statement, a
finite-population equal-bound statement, and positivity of every two-coordinate
denominator (`Defs/Part7.lean:10`, `Defs/WholeW1.lean:285`).

First, for each `n>0`, sorted real sample `y`, and `γ≥1`, for every finite
index `k` it gives

`h(k+1)-h(k)=(1-γ)(y_k-h(k))/sum_i Hγ(k+1)_i`.

If `γ=1`, all natural cuts have `h(k)=l(k)=M(y)`, and membership in the
normalized box is equivalent to being the constant-one function. If `γ>1`,
the set of finite indices satisfying `h(k)≥h(k+1)` is exactly the set
satisfying `h(k)≤y_k`; equivalently the increment is nonpositive exactly
when that outcome test holds. For all `γ≥1`, the outcome test implies
`h(k+1)≤y_k`.

Next, quantify over arbitrary real `c1,c2,p,q,u,v,a,b`, in that order, with
`c2≥0,p>0,q>0,a>0,a≤b,u<v`. Define
`A=c2*u-c1+a*q*(u-v)` and `B=c1-c2*v+b*p*(u-v)`.
The statement gives the exact cleared-denominator identities

`(c2+ap+aq)(c2+bp+aq)(F(a,a)-F(b,a))=(a-b)p A`,

`(c2+bp+bq)(c2+bp+aq)(F(b,b)-F(b,a))=(a-b)q B`,

and `A+B=(c2+bp+aq)(u-v)<0`. A further universal clause with the same
hypotheses says, when `a<b`, the two strict improvements are equivalent to
`A<0` and `B<0`, respectively, and at least one holds. When `a=b`, both
alternative objectives equal `F(b,a)`. Finally, for all `c2,p,q,a,b` with
the preceding positivity/order hypotheses, then every `x∈[a,b]` and
`z∈[a,b]`, `c2+xp+zq>0`; no condition on `c1,u,v` is needed for this fact.

The original-scale sample clause quantifies over `n>0`, sorted `y`, and then
`0<α≤β≤1`, setting `γ=β/α`. For every natural `k≤n`, the original upper
threshold vector is feasible and has value `h(k)`, its normalized denominator
is `k+γ(n-k)>0`, and its numerator is
`sum_{i<k}y_i+γ sum_{k≤i}y_i`. Each increment has the preceding numerator
and the explicit new denominator `k+1+γ(n-k-1)`.

If `γ=1`, then `α=β`, the original box contains only constant `1/α`, all
upper threshold vectors are that function, and both endpoints and all upper
values equal `M(y)`. The mean is at most the last outcome. There is a least
finite index with `M(y)≤y_k`, which is an upper cut with value `M(y)`;
the first stationary/nonincreasing-increment index is zero. If `γ>1`, an
upper cut exists which is also the first stationary index, dominates every
threshold value with natural cut `j≤n`, and is the greatest value in that
finite image. The outcome test implies `h(k+1)≤y_k` and, whenever the next
index exists, `y_k≤y_{k+1}`.

The population clause quantifies over `N,J>0`, real unit outcomes `z`,
strictly increasing class outcomes `y`, and a surjective map
`cls:Fin N→Fin J`, with `z_i=y_cls(i)`. It then quantifies over `0<c≤1`
and unit inclusions with `c≤π_i≤c`. Every `π_i=c`; class sizes `m_j` are
positive, class masses equal `c m_j>0`, and `m_j/a_j=1/c`. Class sizes sum
to `N`; their outcome-weighted mean and `R(y,a,m/a)` equal `M(z)`. The
class box is exactly constant `1/c`; its attainable set is `{M(z)}`, both
attained extrema equal `M(z)`, and both endpoints equal `M(z)`.

The docstring carefully separates equal-bound stationary indices from the
outcome-test cut, and restricts strict improvement to strict bounds. Positive
box denominators, guarded natural subtraction, surjective nonempty classes,
and `N>0` eliminate junk values, including in the population mean.

## SAP.P025a.T2 — P025-T2

The fixed data are class outcomes `(0,1)` and class masses `(1/2,1)`
(`Defs/Part2.lean:34`, `Defs/WholeW1.lean:138`). Every mass is within
`[1/2,1]`; outcomes are strictly increasing and the unit population mean is
`1/2`. The printed cut is zero, `l(0)=2/3`, `l(1)=1/2`, `h(1)=4/5`,
and the upper first cut is one. For every class index neither its lower nor
its upper threshold value equals its outcome (the `separation` predicate).
Also `1/2<2/3`. Every `1≤u,v≤2` has
`1/2≤v/(u/2+v)≤4/5`; the two endpoints are asserted to be the attained
extrema over the original box.

The residual statements for every such `u,v` are positivity of `u/2+v` and

`v/(u/2+v)-1/2=((2-u)+2(v-1))/(2(u+2v)) ≥ 0`,

`4/5-v/(u/2+v)=(4(u-1)+2(2-v))/(5(u+2v)) ≥ 0`.

The same two-unit sampling law as T1 is used. Its two outcome classes are
singletons; class totals are the actual inclusions `(1/2,1)`, and actual
class-size/mass weights are `(2,1)`, which recover the population mean.
A PMF assigns each draw `ENNReal.ofReal(1/2)`. The measure on all infinite
sequences of draws is Mathlib's independent countable product of that law.
It is asserted to be a probability measure, every coordinate has the PMF
law, all coordinate draws and all coordinate sample sets are mutually
independent. The first `h` copies form tagged population `Fin h × Fin 2`;
its size is `2h`, pooled membership agrees with membership in its own copy's
sample, and for `h>0` its mean is `1/2` and every pooled sample is nonempty.
Thus these are independent replicates, not repeated use of one random draw.

The general clause quantifies over `J>0`, strictly increasing `y`, positive
class masses, and `0<α≤β≤1`. It asserts the original-scale zero-cut
diagnosis: the printed lower cut is zero, its vector is constant `1/β` and
feasible, its value is the mass-weighted mean at least `y_0`. If `γ>1` and
some outcome exceeds `y_0`, changing its first coordinate to `1/α` strictly
improves it. In particular `γ>1` and `J≥2` imply that the printed value is
not the least attainable value.

All real residual and class denominators are positive. `ENNReal.ofReal`
truncation is irrelevant for the positive PMF masses. The empty tagged
population at `h=0` is permitted only in cardinality and membership facts;
the mean and nonempty-sample claims have the explicit guard `h>0`.
No integrals, expectations, or asymptotic ratios of pooled samples are
asserted in this theorem.

## SAP.P025a.T3 — P025-T3

For every `n>0`, nondecreasing real sample `y`, and then real bounds
`0<α≤β≤1`, set `γ=β/α` (`Defs/Part3.lean:27`,
`Defs/WholeW1.lean:167`). Both `h(n-1)` and `l(n-1)` are at most the
last outcome. There exist, in order, finite cuts `kL,kH` which are the
corrected first lower and upper cuts. Their scaled threshold vectors
`(1/β)Lγ(kL)` and `(1/β)Hγ(kH)` belong to the original box and have
values `l(kL),h(kH)`. Those values are attained global extrema, equal
the endpoints defined by `sInf` and `sSup`, and the entire attainable set
is exactly `[l(kL),h(kH)]`.

For every real `z` in that interval there exists `t∈[0,1]` such that
`(1/β)((1-t)Lγ(kL)+t Hγ(kH))` is feasible and has value `z`.
For every `k∈Fin n` both exact increments are asserted:

`l(k+1)-l(k)=(γ-1)(y_k-l(k))/sum_i Lγ(k+1)_i`,

`h(k+1)-h(k)=(1-γ)(y_k-h(k))/sum_i Hγ(k+1)_i`.

Writing `m=l(kL)`, outcomes before `kL` are strictly below `m`, and all
outcomes at or after it are at least `m`. For every normalized feasible
`u`, the residual is

`R(y,1,u)-m=sum_i[(u_i-Lγ(kL)_i)(y_i-m)]/sum_i u_i`;

every summand and the residual are nonnegative.

The additional whole-statement clause quantifies over the same data and then
over any cuts satisfying all the preceding `correctedSampleBounds` properties.
Along their original-scale affine segment every weight is feasible, the sum
of weights is positive, and the ratio is continuous on `[0,1]`. For each
original-box `w`, normalization `u_i=β w_i` belongs to the normalized box
and gives the same exact termwise nonnegative residual. This conditional
clause is paired with unconditional existence of such cuts; it is not the
sole assertion of existence or optimality.

There is no distinct-outcomes, strict-bounds, or separation premise. Ties,
singletons, equal bounds, and constant outcomes are included. All denominators
are positive, endpoints refer to nonempty bounded sets, and `n-1` and
`k+1≤n` are protected by finite indices.

## SAP.P025a.T4 — P025-T4

The theorem quantifies over `J>0`, functions `y,a:Fin J→R`, strictly
increasing `y`, all masses `a_j>0`, and then `0<α≤β≤1`
(`Defs/WholeW2.lean:32`). Set `γ=β/α`. For every natural cut `k≤J`,
`l(k)=N_L(k)/D_L(k)` and `h(k)=N_H(k)/D_H(k)`, with both denominators
positive. At cut `J-1`, both values are at most the last outcome.

For every `k∈Fin J`, the exact weighted increments are

`l(k+1)-l(k)=(γ-1)a_k(y_k-l(k))/D_L(k+1)`,

`h(k+1)-h(k)=(1-γ)a_k(y_k-h(k))/D_H(k+1)`.

There then exist corrected first cuts `kL,kH`. Their original-scale lower
and upper vectors are feasible, have values `l(kL),h(kH)`, and bound the
ratio for every original-box weight vector. They are attained least and
greatest values, and both endpoint definitions equal the displayed disjoint
prefix/tail fractions at those cuts. Only extreme values are asserted;
no uniqueness of optimizing vectors is asserted.

The masses are arbitrary positive reals; the theorem does not demand that
they arise from a particular sampling design, or impose a separation
condition. Equal bounds and a single class are included. The hypotheses
ensure every denominator is positive and both endpoint sets are nonempty
and bounded. Empty prefixes or tails are legitimate; `J-1` and finite
increment indices introduce no underflow.

## SAP.P025a.T5 — P025-T5

This is a fixed-data conjunction (`Defs/Part4.lean:10`,
`Defs/WholeW2.lean:184`), with no assumptions supplied by the caller.
The gallery infected/uninfected sample quotas are `(44,4)`, and the
exchange quotas `(291,288)`, so the two raw fractions are `44/48` and
`291/579`. The first population pair has stratum sizes
`(48,16,864,288)`, equal population prevalence `3/4`, gallery
inclusions `(11/12,1/4)` and exchange inclusions `(97/288,1)`.
The second pair has sizes `(48,12,1156,289)`, equal prevalence `4/5`,
gallery inclusions `(11/12,1/3)` and exchange inclusions
`(291/1156,288/289)`. All inclusions lie in `[1/4,1]`.

For each pair, substituting each raw fraction and its two inclusions into
`Q` gives that pair's common population prevalence. Actual directional
ratios are respectively
`(11/3,288/97)` and `(11/4,384/97)`; the exchange ratio in the first
pair and gallery ratio in the second are below three, and each other
ratio is above three. Both products equal `1056/97`. Both `3/4` and
`4/5` belong to both intervals at `γ=4`. In particular the gallery
lower endpoint is `11/15`, the exchange upper endpoint is
`388/484=97/121`, and `11/15≤3/4<4/5≤97/121`.

There are also two exact rounded-input variants. At common prevalence
`3/4`, inclusions `(1,249/917)` and `(503/1491,1)` produce sampled
fractions `917/1000` and `503/1000`, with `1491/503<3`. At common
prevalence `4/5`, inclusions `(1,332/917)` and `(503/1988,1)` do so,
with `917/332<3`. Each inclusion used is in `[1/4,1]`, and the theorem
includes `1/(503/1491)=1491/503` and `1/(332/917)=917/332`.
These variants are algebraic selection-probability identities, not a
separate finite sampling certificate with rounded integer counts.

For each of the seven quota families `(48,44),(16,4),(864,291),
(288,288),(12,4),(1156,291),(289,288)`, nonemptiness is asserted, every
member has the required cardinality, and the sum of uniform masses is
one. For every labeled unit the quota marginal is the corresponding
ratio `s/N` listed above. The exact count fractions satisfy the
rounding half-open intervals `91.7-0.05≤100(44/48)<91.7+0.05` and
`50.3-0.05≤100(291/579)<50.3+0.05`.

For each full pair the sample space is the product of its four labeled
quota families. A binary population is the disjoint union of its infected
units (outcome one) and uninfected units (outcome zero). Samples are the
tagged disjoint unions of the two selected subsets for each venue. The
theorem asserts that the joint sample space is nonempty, its product
mass is nonnegative and normalized, and every rectangular event factors
across the four coordinates. Every unit marginal under this joint law is
`s/N`; in particular the venue inclusions are the displayed constant-on-
stratum values in `[1/4,1]`. Both full binary population means equal the
pair's `q` (`3/4` or `4/5`). On every possible joint draw, each venue
has the stated infected and uninfected counts and total count, its raw
fraction is the count ratio, its inverse-inclusion denominator is
positive, and its Hajek estimator
`(sum_{i∈sample} y_i/π_i)/(sum_{i∈sample}1/π_i)` equals `q`.
Every draw also satisfies the displayed rounding inequalities.

The docstring explicitly describes a counterexample to the reading that
equality requires both actual directional ratios to exceed three. All
quota sizes fit their positive population sizes. All samples and quota
families used are nonempty; neither uniform mass nor Hajek ratios rely
on totalized division. `quotaMarginal` by itself would return zero for
an empty family, but that case does not occur. Product independence is
between stratum draws; units within a quota stratum need not be independent.

## SAP.P025a.T6 — P025-T6

The first universal clause quantifies over real `pG,pE,γ`, with hypotheses
in order `0<pE<pG<1` and `1≤γ` (`Defs/Part5.lean:10`). It gives three
equivalences: interval overlap is equivalent to `bL(pG,γ)≤bH(pE,γ)`;
that inequality is equivalent to `O(pG,pE)≤γ^2`; and overlap is equivalent
to `sqrt(O(pG,pE))≤γ`.

The fixed rounded data have odds ratio `455749/41749`, strictly between
`3.30^2` and `3.31^2`; the exact-count data have ratio `1056/97`, strictly
between `3.29^2` and `3.30^2`. Both ratios are strictly between `9` and
`16`. The two selection-ratio product identities from T5, including one
factor below three in each, are asserted. For every `γ≥1`, each of the
two numerical overlap assertions is equivalent to its precise square-root
threshold. Neither pair overlaps at `γ=3`; both overlap at `γ=4`.

For all `0<p<1` and `π1,π0>0`, with `q=Q(p,π1,π0)`, it asserts
`q=pπ0/(pπ0+(1-p)π1)` and
`q/(1-q)=(p/(1-p))(π0/π1)`.
For every `0<pE<pG<1` and four positive selection parameters
`g1,g0,e1,e0`, equality of the two `Q` values is equivalent to
`(g1/g0)(e0/e1)=O(pG,pE)`. A further universally quantified common-cap
clause adds equality and `g1/g0≤γ,e0/e1≤γ`, and concludes `O≤γ^2`;
there is no independently assumed `γ≥1` in that clause (positive ratios
and the caps already force `γ>0`).

Finally it bounds the square roots strictly by
`3.30399<sqrt(455749/41749)<3.30400` and
`3.29948<sqrt(1056/97)<3.29949`.

`Real.sqrt` is total with a special value on negative arguments, but
every argument here is positive. All binary and odds denominators are
positive under the stated strict prevalence/selection hypotheses or
the concrete positive inputs. No endpoint-prevalence cases are claimed.

## SAP.P025a.T7 — P025-T7

This theorem conjoins the negation of a universal printed sample claim
with a universal upper-half theorem (`Defs/Part6.lean:10,47`). The
negated proposition quantifies over `n>0`, sorted `y`, then
`0<α≤β≤1`, and demands existence of printed lower and upper first cuts
whose threshold values are attained extrema and whose interval is the
whole attainable set. Its lower test is specifically `y_k≤l(k)`.

The positive clause quantifies over those same data and hypotheses,
then supplies an upper first cut attaining the greatest ratio over the
whole original box. The negative clause does not spell out its witness
inside this particular statement. A concrete mathematical witness is
`n=2,y=(0,1),α=1/2,β=1`: the printed cut is zero and its value `1/2`
exceeds the feasible value `1/3` at weights `(2,1)`.

The docstring calls the printed sample lower optimizer/range assertion
false and preserves the upper formula. Every required witness condition
is finite and well-defined: nonempty sorted sample, positive ordered
probability bounds, and positive weight denominator. Real infima are
over nonempty bounded sets. No nonmeasurability or undefined integral
is involved. Whether the universal proposition matches the canonical
printed reading will be checked only in the claim stage.

## SAP.P025a.T8 — P025-T8

This conjoins a negated universal class formula, an explicit realizable
counterexample, the undefined-index fact at cut zero, and a universal
upper theorem (`Defs/Part6.lean:20,33,54`). The negated proposition
quantifies over `J>0`, strictly increasing real `y`, positive real class
masses, and `0<α≤β≤1`. It demands printed lower and upper cuts,
attained extrema at their threshold values, correctness of any real
value returned by the printed lower expression, and equality of the
upper endpoint with its threshold value. The lower display condition
is an implication from `some x`, so is vacuous if the display is `none`;
the optimizer demand itself is unconditional.

The explicit witness has `γ=2>1`, outcomes `(0,1,2,3)`, class masses
one, printed cut zero, value `3/2`, and attained least value `7/6`
over `[1,2]^4`. The zero-cut value is explicitly not the least value.
The underlying six-unit law, outcomes, and class map are exactly those
expanded in T10: normalized four-outcome law, every unit inclusion in
`[1/2,1]`, compatible outcome labels, actual class totals all one.
The printed lower expression at cut zero is `none`.

The final clause quantifies over the general positive class data and
positive ordered bounds and supplies an upper first cut attaining the
greatest value and the `sSup` endpoint. The docstring's refutation rests
on lower optimizer failure, independently of undefined display indices.
Positive masses, positive box weights, and nonempty classes eliminate
all denominator/infimum junk. Compatibility with any further conditions
carried by the canonical claim is reserved for the claim stage.

## SAP.P025a.T9 — P025-T9

For every `J>0`, strictly increasing real class outcomes `y`, positive
class masses, and then `0<α≤β≤1`, set `γ=β/α`
(`Defs/Part6.lean:65`). For each natural `k≤J`, the ratio at weights
`1/α` before the cut and `1/β` after it equals `N_L(k)/D_L(k)`.
For each finite corrected lower first cut, the lower endpoint equals
that same disjoint prefix/tail fraction.

For every natural `k` with `2≤k≤J`, let `u=k-2`, `v=k-1`,
`N=N_L(k)`, and `D=D_L(k)`. The printed expression is exactly
`some ((N+a_u y_u+a_v y_v)/(D+a_u+a_v))`, and the difference
between that fraction and `N/D` equals
`[a_u(y_u-N/D)+a_v(y_v-N/D)]/(D+a_u+a_v)`.
At both cuts zero and one the printed expression is `none`.

Thus the theorem identifies two duplicated class entries and gives
their exact algebraic error, without claiming that the error must
always be nonzero. It does not use the printed lower stopping rule to
choose the corrected endpoint. Underflow is explicitly guarded in
the finite indices `u,v`; the Option cases represent invalid class
indices. All real denominators are strictly positive, including the
one with the two extra positive masses. The endpoint set is nonempty
and bounded. The docstring claims a corrected display and an error
identity, not uniqueness of optimizers.

## Verification limits at the end of the blind stage

Only source/closure inspection, input hashing, and elementary mathematical
analysis have been completed. The local Lean executable exists, but the
packet's `.lake` contains only its build directory and no bundled Mathlib
dependency tree. No local scratch Lean has been run. An authorized SSH
preflight was attempted without any credential changes or alternate route;
the runtime rejected the connection with `Operation not permitted`.
The exact scoped preflight command was:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 dbl-ws 'cd /home/ubuntu/sap/assure/independent-fw-20261105/P025a-doc-v2 && pwd && df -BG . && cat /home/ubuntu/sap/tools/sap-lean && cat /home/ubuntu/sap/tools/lean_path.txt'
```

Consequently no remote helper, dependency path, memory availability, scratch
Lean, or remote input hashes have been inspected or certified. Nonvacuity and
counterexample checks will be justified mathematically where compilation is
not feasible, as the brief permits. The supplied certificate is treated only
as evidence of proof checking, not as evidence of semantic fidelity.
