# Blind reading

Written before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. All five Challenge statements/docstrings and all entries
of their elaborated closures have been read. The 85 distinct generated closure
proof declarations were also printed in `scratch/closure-proofs.log`: they are
numeral/finite-index instances, the explicit rational positivity/normalization
proofs for the two four-phase designs, and standard measure/scalar instances.
They add no statistical hypotheses or alternative definitions.

## Notation unfolded for all sections

All finite sums below are Mathlib `Finset.univ` sums. `Fin n` is the set of
natural numbers strictly below `n`, numbered from zero. A `Design U Ω` is simply
a pair of functions `w : Ω → ℝ` and `s : Ω → U → Bool`; its constructor and field
projections have no implicit validity constraints. Where `U, Ω` are finite:

* Validity means every `w(ω) ≥ 0` and `Σω w(ω)=1`. Positivity means every
  `p(k)>0`, with `Iωk = 1` when `s(ω,k)=true` and zero otherwise,
  `E_D f = Σω w(ω)f(ω)`, `p(k)=E_D Iωk`, and
  `p(k,l)=E_D(Iωk Iωl)`.
* `C(k,l)=p(k,l)-p(k)p(l)` and
  `Var_D f = E_D[(f-E_D f)²]`.
* The estimated total is `t_D(y,ω)=Σk Iωk y(k)/p(k)`. The estimated mean is
  `t_D(y,ω)/|U|`.
* The uncorrected variance estimate `h_D(y,ω)` is the ordered double sum over
  `k,l` with `p(k,l)>0` of
  `Iωk Iωl [C(k,l)/p(k,l)] [y(k)/p(k)] [y(l)/p(l)]`, with zero summands when
  `p(k,l)≤0`.
* Let `Z={(k,l):k≠l and p(k,l)=0}`, an ordered set of pairs. Then
  `A_D(y)=Σ_Z y(k)y(l)`,
  `A*_D(y)=Σ_Z (y(k)²+y(l)²)/2`, and the realized quadratic correction is
  `c_D(y,ω)=Σ_Z [Iωk y(k)²/(2p(k))+Iωl y(l)²/(2p(l))]`.
  The corrected estimate is `h2_D=h_D+c_D`.
* An outcome expectation is the real Bochner integral `∫ f dμ`.
  `NoiseMoments μ ε σ²` says each real error is integrable with mean zero,
  every product `εk εl` is integrable, and its expectation is `σ²` for equal
  indices and zero for unequal indices. `UncorrelatedNoise` has the same
  integrability and mean conditions, but only imposes the zero off-diagonal
  product expectations; diagonal variances can differ.
* Raw outcomes are `βx(k)+εk(ξ)`; centered outcomes subtract their finite
  arithmetic population mean.
* For an ordered positive size vector `x : Fin N → ℝ`, write
  `X_left(k)=Σ_{a<k}x(a)`. The systematic predicate is
  `∃j∈Fin m, X_left(k)≤u+j(Σa x(a)/m)<X_left(k)+x(k)`.
  No hypotheses are part of this predicate itself. The printed proposed
  inclusion probability is `m x(k)/(Σa x(a))`.
* The one-coordinate negative-binomial mass used below is, for `j∈ℕ`,
  `b(j)=[Π_{i=0}^{j-1}(18/5+i)]/j! · (3/8)^(18/5) · (5/8)^j`.
  The finite-vector measure `μ_N` is the countable sum over all
  `v : Fin N → ℕ` of `ENNReal.ofReal(Πk b(v(k))) · δ_v`.
  `nbProductLaw` is `μ_8`; `nbProductLawN N` is `μ_N`.

These expansions also fix the meaning of every occurrence of the corresponding
SAP definition in each section below.

## SAP.P027a.T6

The theorem has no external parameters: it asserts a conjunction of universal
finite-phase formulas, universal outcome-model formulas, and fixed arithmetic.

For every natural `r>0` and every natural `m` (including zero in the first
conjunct), put `G=Fin r × Fin 2` and `K=Σg:G, Fin m`. A group `g=(i,b)` has
probability `p_g=1/(6r)` if `b=0`, and `5/(6r)` otherwise. The grouped design
has atom set `G`, weight `p_g`, and selects exactly group `g`. Its original-unit
lift has the same atoms and weights and selects all `(g,j)` in the chosen
group. The theorem says this lift is valid and positive, every marginal of a
unit in group `g` is `p_g`, joints are `p_g` for units in the same group and
zero otherwise, and two unit-selection functions agree for every atom exactly
when their group labels agree. There is no continuous start-law assertion in
this conjunct.

Next, for every `r,m>0`, followed by every `z:K→ℝ` with `Σk z(k)=0`, set
`Y_g=Σj z(g,j)`, `Q_g=Σj z(g,j)²`, `S=Σg Y_g²`, `Q=Σg Q_g`,
`q=2r`, `N=mq`, `D` the original design and `Dc` the grouped design. Set
`V=Var_D t_D(z)`, `H=E_D h_D(z)`, `Uc=E_D h2_D(z)`, and
`Gc=E_Dc h2_Dc(Y)`. The conclusions are all of the following:

* `Σg Y_g=0`, `A_D(z)=-S`, `S≥0`, and `S=0 ↔ ∀g,Y_g=0`;
  `E_D t_D(z)=0` and `V=Σg Y_g²/p_g`.
* `H=V-S`, `Uc=V-S+(N-m)Q`, `Gc=V+(q-2)S`.
* For every atom `g`, `t_D(z,g)=Y_g/p_g`,
  `h_D(z,g)=(1-p_g)Y_g²/p_g²`,
  `c_D(z,g)=(N-m)Q_g/p_g`, and `c_Dc(Y,g)=(q-1)Y_g²/p_g`.
* On that atom, `h2_D(z,g)-h2_Dc(Y,g)` equals both
  `(q-1)(mQ_g-Y_g²)/p_g` and
  `m(q-1)/p_g · Σj(z(g,j)-Y_g/m)²`, and is nonnegative.
* `Uc-Gc=(q-1)(mQ-S)`, `V≤Gc≤Uc`, and `(3q/5)S≤V≤3qS`.
* If `V>0`, then `-5/(3q)≤A_D(z)/V≤-1/(3q)` and
  `(q-2)/(3q)≤(Gc-V)/V≤5(q-2)/(3q)`.

The outcome-model conjunct quantifies, in order, over any measurable space
`Ξ`, any probability measure `μ` on it, `r,m>0`, real `β,σ²` with `σ²≥0`,
and errors `ε:K→Ξ→ℝ` satisfying the common second-moment condition above.
The size of a unit is 2 in a `b=0` group and 10 otherwise. The outcomes are
`zξ(k)=βx(k)+εk(ξ)-[Σl(βx(l)+εl(ξ))]/|K|` and their group totals are `Yξg`.
Let `L=16m²β²+mσ²(1-1/q)`,
`Vξ=Var_D t_D(zξ)`, and `Gcξ=E_Dc h2_Dc(Yξ)`.
There is an additional antecedent: `Vξ`, `Gcξ`, and every `Yξg²` are
integrable with respect to `μ`. Under it, every `Eμ Y_g²=L`,
`Eμ V=(9/5)q²L`, and `Eμ Gc=Eμ V+(q-2)qL`.
If `L>0`, `(Eμ Gc-Eμ V)/Eμ V=(5/9)(1-2/q)`.
This is a ratio of expectations, not an expectation of ratios.

Finally, on `Fin 4`, take weights `(1/12,5/12,1/12,5/12)` and a design that
selects exactly its atom index. For totals `(1,0,-1,0)`, the theorem asserts
`Σg Yg²=2`, total variance 24, expected corrected estimate 28, and
`(28-24)/24=1/6`. It does not describe an eight-unit outcome vector for this
last example.

Junk/domain audit: real division is total with `a/0=0`, but `r,m>0` imply
`q≥2,N>0,p_g>0` in all formulas using these denominators. Here `N-m` and
`q-2` are real subtractions, not truncated natural subtractions. In the first
conjunct `m=0` gives an empty unit type, but the sample-atom type is nonempty;
its unit statements are then appropriately universal over the empty set.
All correction branches at zero joint probabilities deliberately omit
unobservable cross terms, rather than divide by zero. The `V` and outcome
ratio denominators have positive guards; `L>0` implies positive expected
variance by the displayed formula. Finite sums are genuine expectations under
the asserted valid designs. The only Bochner integrals are under probability
measures with explicitly imposed integrability or error-moment conditions.
No log, sqrt, real powers, `toReal`, infimum/supremum, limsup/liminf, or partial
choice default is used. Modulo is by fixed positive 2 or 4. The docstring
expressly describes finite-phase scope and omissions, and calls the derived
integrability assumptions added conditions.

## SAP.P027a.T10

This is an unconditional conjunction about fixed data and one universally
quantified perturbation box. The units are `Fin 8`, atoms `Fin 4`, and atom
`g` selects precisely units `k` with `k mod 4=g`. Atom probabilities are
`(1/8,3/8,1/8,3/8)`. Sizes alternate `(1,3,1,3,1,3,1,3)` and outcomes
alternate `(1,-1,1,-1,1,-1,1,-1)`. The assertions are:

* The design is valid and positive, sizes are at least 1, their sum is 16,
  marginals are `xk/8` and equal the printed `m=2` PPS formula, and
  joints are the first marginal when the two unit indices agree modulo 4,
  zero otherwise. There are 48 ordered unequal zero-joint pairs.
* `A(y)=-16`, `A*(y)=48`, `E_D t(y)=0`,
  `Var_D t(y)=256/3`, `E_D h(y)=208/3`, `E_D h2(y)=352/3`,
  and `Var_D t(y)≤E_D h2(y)`.
* For every atom `g`, total estimate is 16 for even `g` and `-16/3`
  otherwise; uncorrected variance estimate is 224 for even `g` and
  `160/9` otherwise. Mean variance is `4/3`, expected mean-scale
  uncorrected estimate is `13/12`, their difference is `-1/4`, and
  the expected estimate is strictly below variance.
* Left cumulative sizes are `(0,1,4,5,8,9,12,13)`. Each size is at most
  3, the size at index 1 is 3, and `2·3≤16`.
  For every real `β` and unit `k`,
  `yk=βxk+(yk-βxk)`. This is an algebraic residual representation,
  with no distribution asserted for those particular residuals.
* For every atom `g` and real `u` in the corresponding cell
  `[0,1),[1,4),[4,5),[5,8)`, the size-based systematic predicate
  with `m=2` agrees with the atom's selected units.
* Let `ν=(ENNReal.ofReal 8)⁻¹ · Lebesgue|[0,8)` and let `s(u)` be
  the Boolean vector obtained from the systematic predicate. Its start
  interval has positive length, `ν` is a probability measure, each start
  belongs to exactly one of the four cells, the cells have masses equal
  to the four atom weights, and the selected vector agrees with that
  atom throughout its cell. For every real function `F` on Boolean
  sample vectors, `F(s(u))` is integrable and its integral equals
  `Σg w(g)F(selected(g))`.
* For every `y':Fin 8→ℝ`, if every `|y'k-yk|<1/8`, then
  `A(y')≤-13/4`; also `-13/4<0`.
* The vector of natural counts alternating 0 and 2 yields the stated
  sizes after adding 1. `μ_8` is a probability measure and its singleton
  mass for that vector is `b(0)^4 b(2)^4>0`.

Junk/domain audit: the fixed marginals, population size 8, sample size 2,
interval length 8, and numerical denominators are positive. All zero-joint
terms are intentionally dropped. The arbitrary `F` has a finite domain, and
the integral statement includes integrability explicitly. Real-power use in
`b(j)` has the positive base `3/8`; factorials never vanish, and the empty
product at `j=0` is 1. `ENNReal.ofReal` clips negatives, but these masses are
positive; `toReal` maps infinity to zero in general, but the measure here is
asserted to be a probability. There are no truncated subtractions, empty
index types, extrema, or partial defaults. The normalized start-law definition
would be degenerate at nonpositive lengths, but is used here only at 8.
The docstring explicitly says this witness challenges an inference about the
noisy additive model and does not refute the literal proportional-outcome
assertion. The mathematical theorem itself contains no probabilistic Gaussian
residual witness or positive-probability outcome event.

## SAP.P027a.T11

The first conjunct quantifies, in order, over finite types `U,Ω`, a measurable
type `Ξ`, a probability measure `μ` on it, and a design `D`; then assumes
validity, positive marginals and `|U|>0`; then quantifies over a real size
function `x` satisfying `xk≥1`, a real `β`, and real errors `εk(ξ)` satisfying
the uncorrelated finite-second-moment condition above. For
`yk(ξ)=βxk+εk(ξ)`, it concludes:

* For every `k`, `Eμ yk=βxk`; for every distinct `k,l`,
  `Eμ(yk yl)=β²xk xl`.
* `A_D(yξ)` and `B_D(yξ)` are integrable, where
  `B_D(y)=E_D[h_D(y)/|U|²]-Var_D[t_D(y)/|U|]`.
* `Eμ A_D(yξ)=β² A_D(x)≥0` and
  `Eμ B_D(yξ)=β² A_D(x)/|U|²≥0`.

This is an outcome expectation of conditional design quantities, with the
size function and design held fixed. Neither independence of the errors nor
identical variances are hypothesized. No extra integrability of `A` or `B`
is assumed: it is concluded.

The second conjunct independently quantifies over finite `U,Ω` and a valid,
positive design with `|U|>0`, and every real `y:U→ℝ`. It says
`B_D(y)=A_D(y)/|U|²`, `B_D(y)≥0 ↔ A_D(y)≥0`, and
`B_D(y)≥0` when all outcomes are nonnegative or all are nonpositive.

The last conjunct returns to the fixed eight-unit design, sizes and outcomes
in T10. It asserts validity, positivity, sizes at least 1,
`A_D(x)=176`, `(3/2)² A_D(x)=396`,
`A_D(y)=-16`, and `B_D(y)=-1/4`. For every measurable probability
space and every `Fin 8` family of uncorrelated mean-zero finite-second-moment
errors, it further concludes, for every real `β`,
`Eμ A_D(βx+ε)=176β²` and `Eμ B_D(βx+ε)=176β²/64`,
and explicitly `Eμ A_D((3/2)x+ε)=396`.

Junk/domain audit: `|U|>0` is explicit in both general conjuncts, so the
population mean and bias division cannot be zero-denominator conventions.
Validity precludes an empty atom type. `U` is nonempty; the fixed example
has eight units. Marginal denominators are positive; the joint-denominator
branch matches observed pairs as above. Probability and second-moment
hypotheses ensure the product and quadratic integrals exist, and relevant
integrability is an explicit conclusion. No hidden common-variance,
independence, sign-of-β, or sampling-rate condition occurs. There are no real
powers, logs, roots, extended-real conversions, extrema or partial defaults.
The docstring says usual measure-theoretic conditions and nonempty population
are presupposed and distinguishes outcome-average from populationwise
conservativity.

## SAP.P027a.T12

This theorem unconditionally asserts five propositions. For `x=(30,1,1,1,1,1,1,1)`
and `m=2`, its printed probabilities are `60/37` at index 0 and `2/37`
elsewhere. Sizes sum to 37, printed probabilities sum to 2, and the first
exceeds 1 by `23/37`. For every finite atom type and every valid design on
these eight units, it is impossible that all actual marginals equal this
printed vector. Separately, for every such valid design every marginal is
at most 1.

The natural count vector `v=(29,0,0,0,0,0,0,0)` yields these sizes after
adding 1. `μ_8` is asserted to be a probability measure with all coordinate
masses `μ_8{v:vk=j}.toReal=b(j)`. Each coordinate has expectation 6 and
centered second moment 16, and both the coordinate and its squared deviation
from 6 are integrable. Its specified singleton has real mass
`b(29)b(0)^7>0`.

Finally, for every `row∈Fin 6`, take respectively

| row | N | m | L | first printed probability |
| --- | ---: | ---: | ---: | ---: |
| 0 | 8 | 2 | 8 | 16/15 |
| 1 | 40 | 2 | 40 | 80/79 |
| 2 | 120 | 30 | 5 | 150/124 |
| 3 | 600 | 30 | 21 | 630/620 |
| 4 | 240 | 60 | 5 | 300/244 |
| 5 | 1200 | 60 | 21 | 1260/1220 |

Define a natural vector with first entry `L-1` and other entries zero, and
real sizes `xk=1+vk`. The theorem concludes `N≥2`, `0<m<N`,
`L=(N-1)/(m-1)+1` **with natural-number division**, `Σx=L+N-1`,
and sizes `(L,1,...,1)`. There exists an index of value zero whose printed
probability equals the last column and exceeds 1. The vector measure `μ_N`
is a probability, the specified singleton has positive real mass, and for
every finite valid design not all its marginals equal this printed vector.

Junk/domain audit: the `N-1`, `m-1`, and `L-1` expressions in the row
construction are natural truncated subtraction. The six fixed rows all have
`N≥2,m≥2,L≥5`, so no truncation or division by zero occurs. Natural division
is floor division, so the formula for `L` really is the first strictly
infeasible integer size (not a real-valued fraction). The sums of positive
sizes are nonzero. All real rational denominators are positive. The masses
use a positive real-power base and nonzero factorial as in T10. Countable
nonnegative sums of Dirac measures define the vector measures, and probability
assertions rule out infinity in every `toReal`. The separate finite-moment
assertion prevents undefined Bochner moments from being passed off as actual
moments. The universal impossibility assertion allows an empty atom type,
but then validity is impossible; the actual vector witnesses are nonempty
and explicit. There are no partial choices, infima/suprema, or limits.
The docstring describes witnesses of a printed probability above one; it
does not claim impossibility for every random size vector.

## SAP.P027a.T13

There are six conjuncts, with independent universal quantifiers unless stated
otherwise. In all constructions below indices have their `Fin N` order.

First, for every natural `N≥2`, then natural `m` with `0<m<N`, then every
real vector `x:Fin N→ℝ` with all entries strictly positive:

* Any finite valid design whose marginals equal `m xk/Σx` must satisfy
  `m xk≤Σx` for every unit.
* There exists a real `c>0` with `Σk min(1,c xk)=m`.
* If every `m xk≤Σx`, then `c=m/Σx` gives sum `m`, and each capped
  probability equals the printed one.

Second, for every natural `N` (even zero) and positive-entry real vector,
the real function `c↦Σk min(1,c xk)` is continuous, nondecreasing, equals
zero at zero, and equals `N` for every `c≥Σk 1/xk`.

Third, for every `N≥2,0<m<N` and real vector `π` satisfying
`0<πk≤1` and `Σπ=m`, let `ν=Lebesgue|[0,1)` and use the systematic
predicate in the common notation with sizes `π` and sample size `m`.
The theorem says `ν` is a probability, every `u∈[0,1)` selects exactly
`m` distinct indices (cardinality of a finite set), every unit's selection
event is measurable, its indicator is integrable with integral `πk`, and
for every pair `k,l` the product of their indicators is integrable and its
integral equals the real measure of the intersection of their selection
events. The systematic spacing in the definition is `(Σπ)/m`, equal to
1 under the hypotheses. This gives actual joint probabilities of this
ordered design, rather than specifying independent inclusion.

Fourth, for every positive size vector with `N≥2,0<m<N`, feasibility
implies `m/Σx>0` and the entire preceding systematic law for the printed
vector. For every such size vector, feasible or otherwise, there is a
`c>0` with cap sum `m` for which the same entire law holds for
`πk=min(1,c xk)`.

Fifth, the explicit `Fin 8` vector `(30,1,...,1)` gives capped probabilities
`π=(1,1/7,...,1/7)` using `c=1/7`. A finite design on atoms `Fin 7`, each
of weight `1/7`, selects unit 0 together with unit `g+1`. This design is
valid and positive, has the stated marginals, and its pair probabilities
are the marginal on the diagonal, `1/7` on off-diagonal pairs involving
unit 0, and zero otherwise. The capped probabilities sum to 2, whereas
naively capping the printed ones sums to `51/37≠2`. For each atom `g`, on
the half-open cell `[g/7,(g+1)/7)` the continuous systematic sample Boolean
vector equals that atom's sample, and the cell has `ν`-mass `1/7`. For
every real statistic `F` on Boolean sample vectors, its composition with
the systematic sample is integrable and its integral equals the finite
design expectation.

Sixth, for every `N≥2,0<m<N`, define the measurable-size-vector event
`F={v:Fin N→ℕ | ∀k, m(1+vk)≤Σa(1+va)}`. The accepted vector measure is
Mathlib's conditional measure `cond μ_N F`. On sequences of full vectors
`w:ℕ→(Fin N→ℕ)`, use the infinite product measure with every coordinate
law `μ_N`. The output is `w(n)` at the **least** natural `n` with `w(n)∈F`
if there is one, and the all-zero natural vector if no such index exists.
The theorem concludes:

* `μ_N` is a probability and `μ_N(F)>0`; the conditional measure is a
  probability, with real values `cond μ_N F(B)=μ_N(B∩F)/μ_N(F)` for
  every measurable vector set `B`.
* The sequence law is a probability; almost every sequence contains an
  accepted vector; output is measurable; and pushing the sequence law
  forward through output equals that conditional law.

Junk/domain audit: size positivity and `N≥2` give `Σx>0`; `m>0` makes the
systematic spacing division legitimate. Positive capped probabilities follow
from positive `c,x`, while the cap permits equality to 1, hence certainty
units. `Σ1/x` uses strictly positive denominators; when `N=0` the empty
sum and conclusion `N=0` of regularity are correct empty finite-sum identities.
No natural subtraction occurs in these statements. All `toReal` occurrences
are of subevents of asserted probability measures, so infinity is excluded.
Conditioning could be a zero/default normalization at zero mass in general,
but acceptance is explicitly positive and finite here. `Nat.find` is used
only inside its existence branch; the all-zero no-acceptance default is
explicitly confined to a null set by the almost-sure termination conclusion.
Infinite product measures encode independent repetitions of full vectors;
they do not repeat a single draw. Every displayed integral is accompanied
by integrability. The one real power in the NB mass has positive base.
There are no logs, roots, infima/suprema or limsup/liminf. The docstring
claims existence of two valid repairs, including the conditioning of the
size law in the formula-preserving repair, and makes no claim about the
unavailable simulation implementation.

Post-blind implementation addendum: after saving the blind text, inspection of
Mathlib `Probability/ProductMeasure.lean:355` confirmed that `Measure.infinitePi`
is defined to be the zero measure if any component is not a probability.
`WholeRedrawRecipe` asserts `IsProbabilityMeasure (nbProductLawN N)` before
its sequence-law conclusions, so that fallback is excluded for every use in
T13. Mathlib `Probability/ConditionalProbability.lean:76` defines `cond μ F`
as `(μ F)⁻¹ • μ.restrict F`, exactly the normalization described above.
