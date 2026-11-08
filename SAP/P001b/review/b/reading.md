# Blind reading of the Challenge statements

This file was written and saved after reading only the SAP Defs and Challenge
sources and the relevant Mathlib definitions, before opening `claims.json` or
`record.json`. Challenge docstrings are not used to supply missing hypotheses or
conclusions. All theorem names below are in the namespace `SAP.P001b`.

## Conventions followed down to Mathlib

* A measure takes values in the extended nonnegative reals. A probability measure
  means exactly that its measure of the whole space is one. On such a measure,
  `probability μ A = (μ A).toReal` is the ordinary real probability: every set has
  finite outer measure. In general `ENNReal.toReal ∞ = 0`; this convention must
  not be mistaken for a probability. All uses here have probability measures.
* Real and planar `volume` are Lebesgue measure, with planar volume the product
  of the two real volume measures. Measurability of a real-valued function means
  measurability into the Borel sigma algebra. `AEMeasurable f μ` means that there
  exists a measurable function equal to `f` outside a μ-null set.
* `Density ν f` means: `f : R -> R` is almost everywhere measurable for Lebesgue
  measure, nonnegative at every point, Lebesgue integrable, and ν is the measure
  whose value on a measurable A is the nonnegative Lebesgue integral of `f` over
  A. `JointDensity` makes exactly the same assertions on R squared. Neither
  predicate alone says that ν has total mass one; the theorem hypotheses add
  that separately. `ENNReal.ofReal r` clips a negative r to zero, but the
  everywhere nonnegativity in these predicates prevents such clipping.
* Real `∫` is Mathlib's Bochner integral, using volume if no measure is printed.
  Set integrals restrict the measure to the indicated set. This integral is
  defined as zero for a nonintegrable function. `Integrable` requires almost
  everywhere strong measurability and finite integral of the absolute value.
  `∫⁻` is the extended nonnegative integral and can equal infinity. These two
  integrals must not be confused.
* A sum `∑ i : Fin n` is the finite sum over indices 0 through n-1. `∑'` is the
  unconditional infinite sum (limit over finite subsets); in R it is zero if
  the family is not summable. `Summable` asserts existence of that limit.
* For finite weights w, write `P_w(A) = sum_{i in A} w_i` and
  `E_w(Y) = sum_i w_i Y_i`. The finite conditional mean used here is
  `E_w(Y | X=x) = sum_{i:X_i=x} w_i Y_i / P_w(X=x)`.
  Finite conditional independence of Y and Z given X means, for every x,y,z
  in that order, if `P_w(X=x)>0`, then
  `P_w(X=x,Y=y,Z=z) P_w(X=x) = P_w(X=x,Y=y) P_w(X=x,Z=z)`.
  These definitions do not independently impose normalization or positivity of
  w; those facts must come from the particular theorem.
* Real division is total, with `a/0=0`. Real square root is the nonnegative
  square root on nonnegative inputs and zero on nonpositive inputs. Subtractions
  between real quantities are ordinary signed subtraction.
* `μ.map X` is the pushforward for an almost everywhere measurable X; all
  random-variable maps here are explicitly measurable or are continuous
  coordinate maps. `μ.comap j`, for an injective map carrying measurable sets to
  null-measurable sets, measures a set by the measure of its image. Outside its
  defining conditions `comap` is zero. The subtype inclusions below satisfy the
  conditions once their sets are measurable. A subtype has its induced sigma
  algebra. `ν₁.prod ν₂` is the product measure.
* A set's `range` is its literal pointwise image, not essential range or
  topological support. A countable set means its subtype is countable; finite
  and empty sets are included. `Pairwise` means for all distinct indices.
  Disjoint sets have empty intersection. Closed intervals include both ends.
* `HasDerivAt F a x` says that the ordinary two-sided derivative at x exists and
  equals a. `DifferentiableAt` asserts existence of the derivative. `deriv`
  returns that derivative when it exists and zero otherwise. `ContinuousAt`
  has its usual neighborhood-limit meaning. In this installed Mathlib,
  `ContDiff R ⊤` has order `ω` in `WithTop (WithTop N)` and asserts real
  analyticity, in particular smoothness; it is stronger than just C-infinity.

Source checkpoints: Mathlib `Measure/Typeclasses/Probability.lean:64`,
`Measure/MeasureSpaceDef.lean:410`, `Function/L1Space/Integrable.lean:59`,
`Integral/Bochner/Basic.lean:158`, `Measure/WithDensity.lean:40`,
`Measure/Map.lean:104`, `Measure/Comap.lean:64`, `Measure/Prod.lean:175`,
`Topology/Algebra/InfiniteSum/Defs.lean:106-148` (additive declarations generated
from `HasProd`, `Multipliable`, `tprod`), `Basic/ENNReal/Basic.lean:228-231,284`,
`Analysis/Calculus/Deriv/Basic.lean:130,153`, and
`Analysis/Calculus/ContDiff/Defs.lean:1068`. Paths in this paragraph are relative
to `/home/ubuntu/sal/deps/mathlib/Mathlib/`, with `Measure`, `Integral`, and
`Function` paths under `MeasureTheory`.

## T20

This is a conjunction of two universally quantified assertions.

First, for every type E and every pair of real functions t,c on E, assuming in
order that t is everywhere nonnegative and c is everywhere nonnegative:

1. `{x:t(x)>0}={x:c(x)>0}` if and only if, for every x with t(x)+c(x)>0,
   `0 < t(x)/(t(x)+c(x)) < 1`.
2. If there exists a real epsilon>0 such that for every x with t(x)+c(x)>0,
   `epsilon < t(x)/(t(x)+c(x)) < 1-epsilon`, then those two positive sets agree.

Second, independently quantify E,t,c again and assume, in order, nonnegativity
of t, nonnegativity of c, finiteness of `{x:t(x)+c(x)>0}`, and equality of their
positive sets. Then there exists epsilon>0, chosen after t and c and before x,
giving the same uniform strict inequalities at every positive-total-mass x.
There is no assumption that these functions are normalized, summable, or have
positive total mass, and E is not required to be nonempty or countable.

## T21

This is a closed assertion about a particular four-point model, with no external
hypotheses. The indices i=0,1,2,3 have respective weights 3/8,1/8,1/8,3/8;
latent types U=(0,0,1,1); and displayed binary genders D=(0,1,0,1).
For every real d, `Y_i(d)=20+40 U_i+5d`; the observed outcome is `Y_i(D_i)`.
For a Boolean d the displayed leaflet is precisely `(0,d,false)`.
Voters are k=0,...,99, and k votes no exactly when
`k+1 <= 20+40 U_i+5 (if d then 1 else 0)`. The counted share is the number of
such voters, as a real number (with 100 voters this also is the percentage).

The statement conjoins all of the following:

* All four weights are nonnegative and their sum is one.
* For every Boolean d the leaflet's three coordinates equal 0,d,false.
* For every i and Boolean d, counted share equals `Y_i(if d then 1 else 0)`.
* For every i, the observed outcome equals `Y_i(1)D_i+Y_i(0)(1-D_i)`;
  both potential outcomes at 0 and 1 and the observed outcome are in [0,100];
  and `Y_i(1)-Y_i(0)=5`.
* `P(D=1)=P(D=0)=1/2` and `E(D | the constant-zero variable = 0)=1/2`.
* `P((Y(0),Y(1))=(60,65),D=1)=3/8`,
  `P((Y(0),Y(1))=(60,65))=1/2`, and the product of this latter probability
  with `P(D=1)` equals 1/4.
* The pair `(Y(0),Y(1))` and D fail the finite conditional independence
  definition above when conditioning on the constant-zero real variable.
* `E(Y_observed | D=1)=55`, `E(Y_observed | D=0)=30`, their difference is 25,
  the weighted mean of `Y(1)-Y(0)` is 5, and the real numbers 25 and 5 differ.

The conditional means displayed here have denominators 1,1/2,1/2 respectively.
There is no general implication about arbitrary leaflet descriptions asserted.

## T22

`T22Statement` is definitionally `T21Statement`. Thus T22 states every assertion
in the preceding T21 reading, about exactly the same fixed objects and with no
external hypotheses. It has no additional universal ignorability or
identification assertion.

## T23

For every type Omega with a sigma algebra, every probability measure μ, and
every pair of sets A,B, assume in order that A and B are measurable. Then:

* `A subset B` is equivalent to `for every omega, omega in A implies omega in B`.
* If A is a subset of B, `P(A)<=P(B)` and `P(B\A)=P(B)-P(A)`.
* `P(empty)=0` and `0<=P(A)<=1`.
* `P(A-complement)=1-P(A)`.
* `P(A union B)=P(A)+P(B)-P(A intersection B)`.
* If A is a subset of B and A differs from B, it is false that every member
  of B belongs to A.

The subset and inequality hypotheses in the last item are local implications,
not assumptions restricting the other items.

## T24

There are three independent conjuncts.

First, for every measurable space Omega, probability measure μ, countable
index type I, and family A indexed by I, assume in order: each A_i is
measurable, each A_i is nonempty, the family is pairwise disjoint, and its union
is Omega. Then for every measurable set B:

* `P(B)=sum_i P(B intersection A_i)`.
* If every `P(A_i)>0`, also
  `P(B)=sum_i [P(B intersection A_i)/P(A_i)] P(A_i)`.
* For every measurable C, its probability is nonnegative;
  `(C nonempty and C-complement nonempty)` is equivalent to
  `(C differs from empty and C differs from Omega)`; and
  `P(B)=P(B intersection C)+P(B intersection C-complement)`.
* `P(empty)>=0` and `P(empty)` is not strictly positive.

Second, independently, for every type Omega and set A (no measure or nonempty
type hypothesis), let F consist of the nonempty members of `{A,A-complement}`.
Every member of F is nonempty, any two distinct members are disjoint, and the
union of F is Omega. For empty Omega this family itself is empty.

Third, the real arithmetic identity `1/8+1/12=5/24` holds. The ratios occur only
inside the implication requiring strictly positive cell probabilities.

## T25

On a one-element space, give the sole point weight one and let its integer
value be zero. This closed statement says `P(0<4)=1`,
`sum_{k=1,2,3} P(0=k)=0`, and these two quantities differ. There are no
external hypotheses.

## T26

For every real function q on the integers, assume in order q(k)>=0 for every k,
unconditional summability of q, and `sum_k q(k)=1`. Define
`F(x)=sum_{k integer, k<=x} q(k)` for real x. Then:

* `sum_{k integer, k<4} q(k)=F(3)`.
* `F(3)-(q(1)+q(2)+q(3))=F(0)`.
* `F(3)=q(1)+q(2)+q(3)` if and only if `F(0)=0`.

All cutoffs in these sums use the real coercion of the integer index.

## T27

Indices are pairs `(m,k)` with m a nonnegative integer and 0<=k<2^m.
Define locations `a_(m,k)=(2k+1)/2^(m+1)`, weights
`w_(m,k)=(1/2)^(2m+1)`, and `F(x)=sum_{a_i<=x} w_i`.
This closed conjunction asserts: w is summable; its sum is one; every weight
is strictly positive; the set of locations is countable; for every pair of real
numbers a,b, assumptions `0<a`, `a<b`, `b<1` imply `F(a)<F(b)`; F is continuous
at 1/3; and there is no epsilon>0 such that every real x with
`abs(x-1/3)<epsilon` satisfies `F(x)=F(1/3)`.
No separate probability measure, atomlessness-at-1/3 assertion, or exact
description of the set of locations occurs in the proposition.

## T28

This is the conjunction of four parts.

1. For every measurable space Omega, probability measure μ, and measurable
   real X, then for every countability structure on its literal range and
   every real x,
   `P(X<=x)=sum_{t in range X, t<=x} P(X=t)`.
2. For every natural m and weights w on the m+1 indices 0,...,m, assume
   nonnegative weights and sum one. For every strictly increasing real X on
   these indices, and then every real x: if x<X_0, `P_w(X<=x)=0`;
   for each l=0,...,m-1, if `X_l<=x<X_(l+1)`, that probability is
   `sum_{i<=l} w_i`; and if `X_m<=x`, it is one.
3. For every natural n and weights w on 0,...,n-1, assume nonnegativity and sum
   one. For every real X on those indices and real a,b, assume a<=b and, for
   every index i, not `a<X_i<=b`. Then `P_w(X<=a)=P_w(X<=b)`.
4. For the six indices with weights 1/6 and values i+1, the CDF at
   -1,1,3/2,2,6,7 is respectively 0,1/6,1/6,1/3,1,1.

The third part has an impossible normalization if n=0, but it also has ordinary
nonempty instances. No entire theorem is restricted to an empty index type.

## T29

Define `U(x)=max(0,min(1,x))`; let f be the indicator of [0,1], g the indicator
of (0,1), and h equal f except h(1/3)=3/2. With no external hypotheses:

* For every real x, f(x),g(x),h(x) are nonnegative.
* For every real x, each of their integrals over (-infinity,x] equals U(x).
* f,g,h are pairwise different as pointwise functions.
* U is not differentiable at 0 and is not differentiable at 1.
* For every real r, if 0<r<=1, the four difference quotients
  `(U(-r)-U(0))/(-r)`, `(U(r)-U(0))/r`,
  `(U(1-r)-U(1))/(-r)`, `(U(1+r)-U(1))/r`
  equal respectively 0,1,1,0.
* f(0)=f(1)=1.

The statement does not explicitly contain `Density` or an integrability
conjunct, but these particular functions are bounded, supported in [0,1],
measurable, and genuinely integrable.

## T30

This is a conjunction of six independent parts, using U from T29.

1. For every probability measure ν on R and real functions f,g, assume
   `Density ν f` and then `Density ν g`. Then f=g Lebesgue almost everywhere;
   for almost every x, the CDF `F(t)=ν((-infinity,t])` has derivative f(x) at x;
   for every x at which F is differentiable, its derivative is nonnegative;
   and the integral of f over R is one.
2. For every probability measure ν and real f,h, assume in order
   `Density ν f`, everywhere nonnegative h, and h=f almost everywhere. Then
   `Density ν h`, and for every real x, `F(x)=integral_{(-infinity,x]} h`.
3. For every planar probability ν and planar f,g, if f and then g satisfy
   `JointDensity ν`, they agree planar Lebesgue almost everywhere.
4. For every real y in (0,1), the function
   `u -> derivative_at_v=y [U(u) U(v)]` is not differentiable at u=0.
   The inner derivative exists for all u at each such interior y; thus its
   value is U(u) and no undefined-derivative default is needed here.
5. For every real x,y in [0,1], `U(x)U(y)=xy`.
6. For every planar probability ν, joint f, and real fx,fy, assume in order
   `JointDensity ν f`, `Density (first marginal of ν) fx`, and
   `Density (second marginal of ν) fy`. Then ν equals the product of its
   marginals if and only if `f(x,y)=fx(x)fy(y)` planar almost everywhere.

## T31

Start with interval I_empty=[0,1]. For a Boolean list `b::w`, take the interval
associated to w, cut out its centered open gap of length `(1/4)^(length(w)+1)`,
and choose its right closed remainder if b=true and its left closed remainder
if b=false. Let C_n be the union of all intervals from lists of length n and
`C=intersection_{n>=0} C_n`. Define `f=2 indicator_C`, and on the subtype C
define `μ=2 times (Lebesgue measure pulled back by the inclusion j:C->R)`.

Without external hypotheses the statement asserts: C is closed; its Lebesgue
measure is 1/2; μ is a probability measure; j is measurable; f is a density of
the pushforward of μ by j; the literal range of j equals C; `{x:f(x)>0}=C`;
and, for every real a,b with a<b, [a,b] is not a subset of C.
This asserts absence of every nondegenerate interval, not absence of singleton
intervals. It asserts no stage-length formula.

## T32

First, for every measurable space Omega, probability μ, and real X, assume X
is measurable; then for every real f assume f is a density of the law of X.
It follows that for every real t the μ-measure of `{omega:X(omega)=t}` is zero,
the literal range of X is uncountable, and Omega itself is uncountable.

Second, independently, fix `C=[0,1/2] \ Q`, where Q is the set of real images of
rational numbers. There exists a measure ν on the subtype C such that all of
the following hold: C is measurable; its Lebesgue measure is 1/2; ν is a
probability measure; the inclusion j:C->R is measurable with literal range C;
the pushforward of ν has density `2 indicator_C`; C is uncountable both as a
set and as a type; and for every real a,b with a<b, [a,b] is not a subset of
the literal range of j. ν is existentially quantified before these conclusions.

## T33

For every type Omega, every real-valued X on Omega, and then every pair of real
functions g,h, `g composed X = h composed X` as pointwise functions if and only
if for every real x in the literal range of X, g(x)=h(x). No measurable space,
probability, measurability, surjectivity, or almost-everywhere interpretation
is assumed. Empty Omega is allowed but is not required.

## T34

Let f(x,y)=1 if 0<x<1 and -1<y<0, and zero otherwise. Without external
hypotheses: f is everywhere nonnegative and planar integrable; its planar
integral is one; its integral over `{(x,y):0<=x<=1 and y<=x}` is one; its
iterated integral `integral_{x in [0,1]} integral_{y in [0,x]} f(x,y)` is zero;
and those latter two quantities differ. These are integrals of the specified
function, rather than probabilities named through a separately constructed law.

## T35

For every planar probability ν and real planar f, assume `JointDensity ν f`.
Set `I=integral_{x in [0,1]} integral_{y in [0,x]} f(x,y)`.
Then `P(0<=x<=1 and 0<=y<=x)=I`;
`P(0<=x<=1 and y<=x)=I+P(0<=x<=1 and y<0)`;
and `P(0<=x<=1 and y<=x)=I` if and only if the latter negative-y probability
is zero. No global restriction that y be nonnegative is assumed. Global
integrability comes from `JointDensity`; the iterated integral is justified
by Fubini, with exceptional nonintegrable sections irrelevant to the outer
integral.

## T36

Define on all of R squared

`f(x,y) = [exp(x)/(1+exp(x))]^2 / [pi (1+y^2 exp(2x))]`.

This closed conjunction asserts that f is real analytic (hence smooth),
strictly positive everywhere, planar integrable, and has planar integral one;
the extended nonnegative integral `integral_x f(x,0)` is infinity; and for
every real y different from zero, `x -> f(x,y)` is integrable on R.
The infinite slice uses `∫⁻`, so does not assert that a real Bochner integral
equals infinity. Both denominators in the defining function are positive.

## T37

First, for every planar probability ν and real planar f, assume
`JointDensity ν f`. Then for almost every real y,
`M(y)=nonnegative integral_x f(x,y)` is finite. Also, for every real-valued g,
assume in order g is nonnegative everywhere and its extended nonnegative
embedding equals M(y) for almost every y. Then g is a density of the second
marginal of ν, and for every real y that marginal CDF equals
`integral_{(-infinity,y]} g`. No separate measurability assumption on g occurs.

Second, independently, for every planar real f assume global Borel
measurability and everywhere nonnegativity. Then for every real x, assume the
section `y -> f(x,y)` is integrable and its real integral c is strictly
positive. The section divided by c is integrable, nonnegative everywhere, and
has integral one. This second part does not require f itself to be a joint
density or globally integrable, and asserts no conditional-probability kernel
identity. The slice hypotheses ensure a finite strictly positive denominator.

## T38

Mathlib `gaussianReal m v` takes a nonnegative real variance v, not a standard
deviation; at variance zero it is the Dirac measure at m. Let W be the law of
the constant-zero function under `gaussianReal 0 1`. This closed assertion says:

* W is Dirac at zero, W({0})=1, no real f satisfies `Density W f`, and for every
  real m and every nonnegative real variance s with s>0,
  `W != gaussianReal m s`.
* For every real x, 0*x=0.
* Both 1 and -1 lie in [-1,1]; `1-rho^2=0` at both values; and
  `2(1-rho^2)=0` at both values.
* `2 pi sqrt(1-rho^2)=0` at both values.
* For every real pair (x,y), both values at rho=1 and rho=-1 of the function
  below with mx=my=0 and sx=sy=1 equal zero; each resulting planar real
  integral is zero; and 0 differs from 1.

The function in the last item is exactly

`exp(-[((x-mx)/sx)^2+((y-my)/sy)^2
       -2 rho (x-mx)(y-my)/(sx sy)]/[2(1-rho^2)])
 / [2 pi sx sy sqrt(1-rho^2)]`.

It is expressly a totalized real expression. Its zero values at the endpoints
come from Lean's division-by-zero convention, not an ordinary mathematical
definition of a Gaussian density at singular correlation. The separate
zero-denominator assertions have their usual mathematical meanings.
