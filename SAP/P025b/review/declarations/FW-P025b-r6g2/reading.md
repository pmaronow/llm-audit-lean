# Blind reading

This file was written before opening `claims.json` or `record.json`. I read the
five Challenge declarations and every named dependency in `closure.json`.
`scratch/ClosurePrint.lean` also prints all 51 line-zero auxiliary declarations;
its complete output is in `scratch/closure-print.txt`. These are numeral
instances, a proof that `2 ≤ n` implies `0 < n`, the outer-measure instance,
and the proof that the finite probability masses sum to one. They add no
mathematical assumptions. Definitions imported but absent from the statement
closures do not become hypotheses merely by being imported.

## SAP.P025b.T17

The Challenge docstring describes an exact audit of inferred counts, 42 corrected
Table 1 cells, the printed cells computed from rounded inputs, and all stated
gallery/exchange comparisons. The theorem has no parameters or hypotheses. It
asserts the conjunction below.

Write

* `L(p,g) = p / (g(1-p)+p)` and `U(p,g) = gp / (1-p+gp)` in the real field.
* `P(p,g,h) = 100 U(p,g)` if the Boolean `h` is true, and `100 L(p,g)` otherwise.
* `R(x,t)` for natural `t` means `t/10 - 1/20 ≤ x < t/10 + 1/20` (casts are
  into the reals).

For every integer `k`, separately for `(n,t,k0) = (48,917,44),
(160,675,108), (579,503,291)`,

`|100k/n - t/10| ≤ 1/20` if and only if `k = k0`.

The next conjunct consists of six real equalities:

`100 L(44/48,2)=1100/13`, `100 L(44/48,4)=220/3`,
`100 U(291/579,5/4)=48500/869`, `100 L(291/579,3/2)=9700/241`,
`100 U(291/579,3/2)=9700/161`, and
`100 U(291/579,5/2)=48500/677`.

A `TableCell` is the product `ℝ × ℝ × ℝ × Bool × ℕ × ℕ`, interpreted here as
`(p,q,g,h,tPrinted,tExact)`. The fixed list contains one lower (`h=false`) and
one upper (`h=true`) cell for each row in the following table. Entries for the
last two columns are `(tPrinted,tExact)`:

| p | q | g | lower pair | upper pair |
|---|---|---|---|---|
|44/48|917/1000|1|(917,917)|(917,917)|
|44/48|917/1000|5/4|(898,898)|(932,932)|
|44/48|917/1000|3/2|(880,880)|(943,943)|
|44/48|917/1000|2|(847,846)|(957,957)|
|44/48|917/1000|5/2|(815,815)|(965,965)|
|44/48|917/1000|3|(786,786)|(971,971)|
|44/48|917/1000|4|(734,733)|(978,978)|
|108/160|675/1000|1|(675,675)|(675,675)|
|108/160|675/1000|5/4|(624,624)|(722,722)|
|108/160|675/1000|3/2|(581,581)|(757,757)|
|108/160|675/1000|2|(509,509)|(806,806)|
|108/160|675/1000|5/2|(454,454)|(839,839)|
|108/160|675/1000|3|(409,409)|(862,862)|
|108/160|675/1000|4|(342,342)|(893,893)|
|291/579|503/1000|1|(503,503)|(503,503)|
|291/579|503/1000|5/4|(447,447)|(559,558)|
|291/579|503/1000|3/2|(403,402)|(603,602)|
|291/579|503/1000|2|(336,336)|(669,669)|
|291/579|503/1000|5/2|(288,288)|(717,716)|
|291/579|503/1000|3|(252,252)|(752,752)|
|291/579|503/1000|4|(202,202)|(802,802)|

For every cell, `R(P(p,g,h),tExact)` and `R(P(q,g,h),tPrinted)` hold. The list
has length 42, exactly six cells have different displayed integers, and in
each cell `tPrinted=tExact` or `tPrinted=tExact+1`.

The remaining conjuncts are:

* `L(44/48,3)=11/14`, `U(291/579,3)=291/387`, and the first is greater.
* `L(44/48,4)=11/15`, `U(291/579,4)=97/121`, and the first is smaller.
* For every real `g` in the finite set `{1,5/4,3/2,2,5/2,3}`,
  `U(291/579,g)<L(44/48,g)` and
  `U(503/1000,g)<L(917/1000,g)`.
* `4/5` is in the intersection of the two closed intervals with endpoints
  `L(p,4),U(p,4)` for `p=44/48,291/579`; it is also in the corresponding
  intersection for `p=917/1000,503/1000`.

Junk-value audit: division is real division, with `x/0=0` in general, but every
literal denominator is positive. Every `p` used in `L,U` is strictly between
zero and one, and every `g≥1`, so their denominators are positive too. The
integer quantifiers and natural display integers are cast without truncation.
The half-open rounding convention differs from the closed error condition used
to infer counts, but none of the fixed computed values lies on a boundary.
The list and finite comparison set are explicitly nonempty. There are no
integrals, partial operations, logarithms, roots, real powers, extended-real
conversions, infima, suprema, or limits here. The list records input/output
data; the asserted arithmetic checks that data rather than defining rounding
to be the desired conclusion.

## SAP.P025b.T18

The docstring says that the attainable set and its extrema depend only on the
ratio of the probability bounds and reduce to the sample mean at ratio one.

Quantifier order: for every natural `n>0`, every vector `y : Fin n → ℝ`, and
all real `α,β,α',β'` satisfying

`0<α≤β≤1`, `0<α'≤β'≤1`, and `β/α=β'/α'`,

all the following statements hold. For a finite index type, define the real
weighted mean

`F(y,a,w) = (Σ_i a_i w_i y_i)/(Σ_i a_i w_i)`.

The physical weight box is `∀i, 1/β≤w_i≤1/α`; its attainable set is
`S(y,a;α,β)={v∈ℝ | ∃w, (∀i,1/β≤w_i≤1/α) ∧ F(y,a,w)=v}`.
The normalized box is `∀i,1≤w_i≤g`, with analogous set
`S_norm(y,a;g)`. `lowerEndpoint` is the real `sInf S`, and `upperEndpoint`
is the real `sSup S`. Here every `a_i=1`.

The conclusions are

* `S(y,1;α,β)=S(y,1;α',β')`;
* `S(y,1;α,β)=S_norm(y,1;β/α)`;
* the corresponding two lower endpoints are equal, as are the upper endpoints;
* if `β/α=1`, then every vector `w` belongs to the physical box if and only if
  `w_i=1/α` for all `i`, and both endpoints equal `(Σ_i y_i)/n`.

All SAP definitions in this closure are unfolded in the preceding formulas.
Junk-value audit: `n>0` excludes an empty observation type and a zero sample
mean denominator. `α,β,α',β'` are positive. Every allowed weight is positive,
so each objective denominator is positive. These boxes are nonempty compact
finite products and the objective is continuous there; thus the image is
nonempty and bounded, and the real conditional infimum/supremum have their
ordinary meaning. Off this domain real division and real `sInf/sSup` are total
(empty or appropriately unbounded real sets have default extrema), but that
behavior is not used. No natural subtraction, extended-real operation,
integral, logarithm, root, real power, partial function, or sequence limsup/
liminf occurs. The cast of positive `n` into `ℝ` remains positive.

## SAP.P025b.T19

The docstring describes unique least cuts, feasible optimal physical weights,
equality of the weights of tied observations, the relation between adjacent
weight equality and the cut, positive finite denominators, constant/nonconstant
upper-cut behavior, and the strict-failure recurrences at ties. This is the
`T19WholeStatement` in `Defs/WholeW2.lean`, not the smaller `T19Statement`
in Part7 (the latter is absent from this statement closure).

Quantifier order: for every natural `n` with `2≤n`, every vector
`y : Fin n → ℝ` that is monotone in the usual order on `Fin n`, and all real
`α,β` with `0<α≤β≤1`, let `g=β/α`. For any natural prefix length `k`, put

`P_k=Σ_{i<n, i<k} y_i`, `T_k=Σ_{i<n, k≤i} y_i`,
`D_H(k)=k+g(n-k)`, `D_L(k)=gk+(n-k)`.

Both subtractions in these denominators take place in the reals, after casting
the natural numbers. Put `u_i(k)=1` for `i<k` and `g` otherwise, and
`l_i(k)=g` for `i<k` and `1` otherwise. Define

`H_k=(Σ_i u_i(k)y_i)/(Σ_i u_i(k))`,
`L_k=(Σ_i l_i(k)y_i)/(Σ_i l_i(k))`.

The first conclusion is universal over natural `k≤n`:
`D_H(k)>0`, `D_L(k)>0`,
`H_k=(P_k+gT_k)/D_H(k)`, `L_k=(gP_k+T_k)/D_L(k)`.

There then exist `kL,kH : Fin n`, simultaneously, such that the conjunction
below holds. Write their natural values as `k_L,k_H` and set
`wL_i=l_i(k_L)/β`, `wH_i=u_i(k_H)/β`.

1. `kL` is the least element of `{j : Fin n | L_j≤y_j}`, and `kH` is the
   least element of `{j : Fin n | H_j≤y_j}`. Explicitly, each satisfies its
   test and is at most every index satisfying that test. For every `jL,jH`,
   if both are such least cuts then `jL=kL` and `jH=kH`.
2. For every `i`, `wL_i=1/α` before `k_L` and `1/β` after it, while
   `wH_i=1/β` before `k_H` and `1/α` after it. Both vectors satisfy
   `1/β≤w_i≤1/α`.
3. With `S={v | ∃w, (∀i,1/β≤w_i≤1/α) ∧
   (Σ_i w_i y_i)/(Σ_i w_i)=v}`, the objective at `wL` is an element of `S`
   and is at most every element of `S`; the objective at `wH` is an element
   of `S` and is at least every element of `S`.
4. For every pair `i,j : Fin n`, `y_i=y_j` implies `wL_i=wL_j` and
   `wH_i=wH_j`.
5. If `1<g`, then for every adjacent pair (`j.val=i.val+1`),
   `wL_i=wL_j ↔ k_L≠j.val` and `wH_i=wH_j ↔ k_H≠j.val`.
   If that pair is tied, neither cut equals `j.val`.
6. For every real `c`, if all `y_i=c`, then `k_H=0` and all `wH_i=1/α`.
   If not every `y_i` equals `y_0`, then `H_0=(Σ_i y_i)/n`,
   `y_0<H_0`, and `0<k_H`.
7. For all adjacent `i,j` such that `j.val≤k_H` and `y_i=y_j`, write
   `r=i.val`, `s=j.val`. Then `y_i<H_r`,
   `H_s=((1-g)y_i+P_r+gT_r)/D_H(s)`,
   `((1-g)y_i+D_H(r)y_i)/D_H(s)=y_i`, that same expression is `<H_s`,
   `H_s-y_i=(D_H(r)/D_H(s))(H_r-y_i)>0`, `y_j<H_s`, and `s+1≤k_H`.
8. For all adjacent `i,j` such that `j.val≤k_L` and `y_i=y_j`,
   `y_i<L_r`, `L_s-y_i=D_L(r)(L_r-y_i)/D_L(s)>0`,
   `y_j<L_s`, and `s+1≤k_L`.

These unfold `lowerCut/upperCut` as Mathlib `IsLeast`, and the extrema in
item 3 as Mathlib `IsLeast/IsGreatest`. The first index is explicitly the
element of `Fin n` with value zero. `populationMean` is the real sum divided
by the cast of `n`. No SAP notion remains in these descriptions.

Junk-value audit: `n≥2`, positive `α,β`, and `g≥1` make all objective
denominators strictly positive. The formula denominators are used only at
`k≤n`, including the legitimate empty prefix `k=0` and empty tail `k=n`;
each denominator is positive there. Finite empty sums are zero, as intended.
No truncated natural subtraction is used. Cuts are `Fin n`, so the tested
observation always exists, and the two quantified adjacent indices are valid.
Existence of cuts is asserted, not assumed. No sInf/sSup default, integrals,
extended-real operations, logarithms, roots, real powers, partial functions,
or sequence extrema occur.

## SAP.P025b.T20

The docstring describes the complete binary attainable interval, its extrema,
the boundary cases, class counts, normalized class weight sums, and monotonicity
of their ratio. The theorem is a conjunction of two independently universally
quantified propositions (`T20Statement` and `BinaryDerivation`). Both quantify
in the following order: natural `n>0`; `y : Fin n → ℝ` with every `y_i=0`
or `y_i=1`; and real `α,β` with `0<α≤β≤1`. Put
`p=(Σ_i y_i)/n`, `g=β/α`.

For `F(w)=(Σ_i w_i y_i)/(Σ_i w_i)` and
`S={v | ∃w, (∀i,1/β≤w_i≤1/α) ∧ F(w)=v}`, put
`L=p/(g(1-p)+p)`, `U=gp/(1-p+gp)`.

The first proposition says `S=[L,U]` (the closed real order interval),
`sInf S=L`, and `sSup S=U`. If `p=0`, then both displayed formulas are
zero; if `p=1`, both are one; if `g=1`, both equal `p`.

The second proposition says that the number of `1` observations, cast to the
reals, is `np`, and the number of `0` observations is `n(1-p)`.
For every physical feasible vector `w`, let

`A=Σ_{i:y_i=1} βw_i`, `C=Σ_{i:y_i=0} βw_i`.

Then `1≤βw_i≤g` for every `i`, `F(w)=A/(A+C)`,
`np≤A≤gnp`, `n(1-p)≤C≤gn(1-p)`, and `n≤A+C` and `0<A+C`.
For every pair of reals `a∈[np,gnp]`, `c∈[n(1-p),gn(1-p)]`, one has
`0<a+c`. For every `a,a',c` in the corresponding intervals, `a≤a'`
implies `a/(a+c)≤a'/(a'+c)`. For every `a,c,c'` in the corresponding
intervals, `c≤c'` implies `a/(a+c')≤a/(a+c)`.

This unfolds all dependencies: `binaryClassSum` is the filtered sum defining
`A,C`; `normBox` is the pointwise inequality just given; `weightBox`,
`attainable`, `ratio`, `populationMean`, both endpoints, and the two binary
formulas have their formulas above.

Junk-value audit: `n>0` and the binary premise imply `0≤p≤1`; `g≥1` makes
both displayed formula denominators at least one. Allowed weights and their
sum are positive. Even when one binary class is empty, its class sum and count
are correctly zero and the other class makes `A+C>0`. Every abstract `a+c`
used in monotonicity is positive by the interval bounds. The feasible box is
nonempty compact and the image bounded, so the real conditional extrema are
ordinary extrema. There is no use of defaults for empty observation types,
unbounded extrema, integrals, partial functions, extended reals, logarithms,
roots, real powers, or limsup/liminf. Finite cardinality and `n` casts are
exact; there is no truncated subtraction.

## SAP.P025b.T21

The docstring says that, under Assumptions 1 and 2 on the valid finite cut
range, both actual pooled endpoints converge almost surely to limiting class
extrema.

Quantifier order: natural `N,J` with `N>0,J>0`; any finite type `κ` with a
measurable space and measurable singletons; a finite design `d` on population
`Fin N` and outcomes `κ`; a surjection `cls : Fin N → Fin J`; a strictly
increasing vector `y : Fin J → ℝ`; and real `α,β` with `0<α≤β≤1`.

Unfold a finite design as functions `S : κ → Finset (Fin N)` and
`q : κ → ℝ`, with `q_ω≥0` for every `ω` and `Σ_ω q_ω=1`. For any real
function `X` on `κ`, design expectation is the finite sum `Σ_ω q_ω X_ω`.
For each unit `i`, its inclusion probability is
`π_i=Σ_ω q_ω 1_{i∈S(ω)}`. Define the class total
`a_j=Σ_{i:cls(i)=j} π_i`. The hypotheses further require
`α≤π_i≤β` for every population unit.

For `g=β/α`, real class weights `w_j`, and class observations `y_j`, define
`F(w)=(Σ_j a_j w_j y_j)/(Σ_j a_j w_j)`. For any valid prefix `k : Fin J`,
let `u_j(k)=1` when `j.val<k.val`, `g` otherwise; let `l_j(k)=g` before
that prefix and `1` otherwise. Separation is exactly the extra hypothesis

`∀k : Fin J, y_k ≠ F(u(k)) ∧ y_k ≠ F(l(k))`.

The PMF has mass `ENNReal.ofReal(q_ω)`. Its `toMeasure` is a probability
measure on `κ`, and `jointLaw` is Mathlib's `Measure.infinitePi` of this
same probability measure at every natural coordinate. Thus draws are iid,
not repeated copies of one draw. Since `κ` is finite with measurable
singletons, all its sets are measurable. Its cylinder probability is the
product of the corresponding finite design probabilities.

For a path `ω : ℕ → κ` and a natural number of replicates `h`, use the
finite index type `Fin h × Fin N`. Its indicator is
`I_{r,i}=1` if `i∈S(ω(r.val))`, zero otherwise; its observation is
`Y_{r,i}=y_{cls(i)}`. Define the actual pooled attainable set

`S_h(ω)={v | ∃w, (∀r,i,1/β≤w_{r,i}≤1/α) ∧
  (Σ_{r,i} I_{r,i} w_{r,i}Y_{r,i})/(Σ_{r,i} I_{r,i} w_{r,i})=v}`.

Pooled lower/upper endpoints are the real `sInf/sSup` of this set. The
limiting set is

`S_∞={v | ∃W, (∀j,1/β≤W_j≤1/α) ∧
  (Σ_j a_j W_j y_j)/(Σ_j a_j W_j)=v}`,

with limiting extrema its real `sInf/sSup`. The conclusion is that for
almost every path under the product measure, all three clauses hold together:

* Eventually in the natural at-top filter, there exists `r : Fin h` such
  that the finite sample `S(ω(r.val))` is nonempty.
* The real sequence `h ↦ sInf S_h(ω)` tends at infinity to `sInf S_∞`
  in the ordinary real neighborhood filter.
* The sequence `h ↦ sSup S_h(ω)` tends to `sSup S_∞` in the same sense.

This is one full-measure event with all three properties. It imposes no
assertion on exceptional paths. These formulas unfold every SAP dependency,
including `pooledNonempty`, `pooledIndicator`, `PooledConvergence`, both
endpoint definitions, and the finite expectation and sampling-law machinery.

Junk-value audit: `κ` cannot be empty because its nonnegative probabilities
sum to one. `Fin N,Fin J` are nonempty; surjectivity gives every class a
unit. Positive inclusion bounds therefore give `a_j>0`. The limiting box is
nonempty compact, every limiting objective denominator is positive, and the
attainable set is bounded. The `ENNReal.ofReal` conversion would truncate
negative reals to zero, but all design probabilities are nonnegative and
their sum is exactly one, so it changes none of the finite probability data.
`Measure.infinitePi` has a default zero-measure branch for nonprobability
factors; the PMF factors are probability measures, so that branch cannot be
used. At `h=0`, or on any initially empty pooled sample, every ratio is
`0/0=0` and the attainable set is `{0}`; thus the actual totalized pooled
endpoints are both zero. The theorem explicitly asserts eventual nonemptiness
almost surely, after which every pooled denominator is positive. A finite
initial sequence of those totalized values cannot change either limit. Empty
classes, zero class totals, and vacuity from a zero joint measure are excluded
by the hypotheses. Real infima/suprema are never used on an empty or unbounded
image. A one-class design cannot satisfy separation, but the hypotheses allow
multiple classes and need not be inconsistent. There is no natural truncated
subtraction, `toReal` of infinity, integral of a nonintegrable function,
logarithm, root, real power, default partial function, or limsup/liminf.

Post-blind clarification of an unused Mathlib convention, checked during step 2:
the default real `sInf ∅` and `sSup ∅` are both exactly zero (compiled at the
end of `scratch/AuditChecks.lean`). The corresponding unbounded-side values
also reduce to the empty-set defaults. This makes the generic defaults mentioned
above explicit; none of these defaults is reached by the feasible attainable
sets, and no mathematical reading or comparison was changed.
