# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or
`architect-report.md`. Sources: the four Challenge declarations and every
declaration listed in their `closure.json` closures. Generated closure declarations
were also inspected with `scratch/Inspect.lean` and `sap-lean`.

Throughout, λ is Lebesgue measure on the real line and λ² = λ ⊗ λ is planar
Lebesgue measure. All set integrals mean integration against the restriction of
these measures to the indicated set, not oriented interval integration.
`IsProbabilityMeasure ν` means ν(universe) = 1. `AEMeasurable h λ` means h agrees
λ-almost everywhere with a measurable function. For a real function,
`Integrable h λ` means almost-everywhere strong measurability and finite integral
of |h|. Here this is the usual Lebesgue integrability condition, allowing null-set
changes. `ν = λ.withDensity (ofReal ∘ h)` means
ν(A) = ∫⁻_A max(h,0) dλ for measurable A, with extended nonnegative values.

## SAP.P001b.T35

Locations: `SAP/P001b/Challenge/Part2.lean:48–51`,
`SAP/P001b/Defs/Part4.lean:68–77`,
`SAP/P001b/Defs/Part1.lean:12–24`.

**Unfolded statement and quantifiers.** For every measure ν on ℝ², every proof
that ν(ℝ²) = 1, and every real-valued function f on ℝ², suppose that f is
λ²-almost-everywhere measurable, f(z) ≥ 0 at every z, ∫|f| dλ² is finite, and
ν = λ².withDensity (z ↦ max(f(z),0)). There are no other hypotheses.
Define the following notation solely to describe the unfolded formula:

- A = {(x,y) : 0 ≤ x ≤ 1 and 0 ≤ y ≤ x};
- B = {(x,y) : 0 ≤ x ≤ 1 and y ≤ x};
- C = {(x,y) : 0 ≤ x ≤ 1 and y < 0};
- I = ∫_[0,1] (∫_[0,x] f(x,y) dλ(y)) dλ(x).

The conclusion is the conjunction ν(A) = I, ν(B) = I + ν(C), and
(ν(B) = I if and only if ν(C) = 0). Each displayed probability is formally
`(ν event).toReal`, so the equalities are in ℝ. The docstring describes the
nonnegative-Y triangular event and the exact zero-missing-mass criterion.
`JointDensity` has been fully expanded in the hypothesis above; `probability`
is precisely extended measure followed by `toReal`.

**Junk and totalization audit.** `ENNReal.toReal ∞ = 0`, but ν is a probability
measure, so this convention cannot affect any of these probabilities. `ofReal`
discards negative values; pointwise f ≥ 0 prevents that from changing the
integrand. The real Bochner integral is defined as zero for a non-integrable
function. Global integrability of f guarantees integrability on every measurable
planar subset. Individual vertical sections may fail integrability on exceptional
x, and the inner real integral then takes its default zero. Fubini gives
integrable sections almost everywhere; such exceptional x do not affect the outer
integral. For x < 0 the set [0,x] is empty, but the outer integral only uses
0 ≤ x ≤ 1. These are genuine set integrals with the boundary convention immaterial
for an absolutely continuous law. There is no division, logarithm, square root,
real power, discrete subtraction, infimum, sequence limit, partial function, or
empty index type in the statement or its SAP dependency closure.

## SAP.P001b.T36

Locations: `SAP/P001b/Challenge/Part2.lean:53–61`,
`SAP/P001b/Defs/Part4.lean:79–83`,
`SAP/P001b/Defs/Part2.lean:29–31` and generated
`SAP.P001b.dyadicLocation._proof_1`.

**Unfolded statement and quantifiers.** This is a conjunction of unconditional
facts about the particular real function

f(x,y) = (eˣ/(1+eˣ))² / [π(1+y²e²ˣ)]

on ℝ². It asserts:

1. f is real analytic everywhere;
2. for every z ∈ ℝ², f(z) > 0;
3. f is λ²-integrable;
4. ∫ f dλ² = 1;
5. ∫⁻_ℝ max(f(x,0),0) dλ(x) = ∞;
6. for every y ∈ ℝ, if y ≠ 0, x ↦ f(x,y) is λ-integrable.

There are no quantified input data or premises to make these facts conditional.
The first predicate is `ContDiff ℝ ⊤ f`. **In this version of Mathlib its order
type is `WithTop ENat`: the outer top is analytic order ω; the embedded ENat top
is the smaller smooth order ∞.** Consequently the first clause does assert
analyticity, not merely smoothness. This follows from
`Mathlib/Analysis/Calculus/ContDiff/Defs.lean:91–92,1060–1068,1196–1198`.

The Challenge docstring calls this a restriction to density and extended-integral
facts, retaining analyticity, positivity, normalization, the infinite zero slice,
and integrability off zero. It expressly omits boundedness, the logistic slice
formula and normalization, joint-CDF mixed derivatives, the limit of f(x,0),
positivity of nonzero slice integrals, and the marginal-CDF derivative assertion.
It expressly disclaims a refutation on the domain where real slice integrals
exist finitely.

**Generated closure dependency.** `dyadicLocation._proof_1` is just a proof that
the natural numeral 1+1 is at least two, reused in elaboration of real numeral 2.
No dyadic distribution or dyadic-location function enters this assertion.

**Junk and totalization audit.** All exponents here are natural powers or `exp`;
there is no `rpow`. Real division is total with a/0 = 0, but 1+eˣ > 0 and
π(1+y²e²ˣ) > 0 everywhere, so no division default is reached. `ofReal` does not
truncate f because f > 0. The extended slice integral uses a genuine ∞ in
`ℝ≥0∞` and never converts it to a real number. It is not the zero-valued
non-integrable Bochner integral. The planar real integral and every asserted
nonzero-slice integral have explicit integrability, so their defaults are
excluded. The lower Lebesgue integral is a supremum over dominated nonnegative
simple functions (a nonempty family containing zero); ∞ is a genuine unbounded
integral, not a supremum junk value. There is no log, sqrt, truncated subtraction,
empty index type, sequence limsup/liminf, or partial function.

## SAP.P001b.T37

Locations: `SAP/P001b/Challenge/Part2.lean:63–73`,
`SAP/P001b/Defs/WholeW1.lean:274–294`,
`SAP/P001b/Defs/Part1.lean:12–24`, and generated
`SAP.P001b.T37WholeStatement._proof_1`.

The theorem uses `T37WholeStatement`, not the older `T37Statement` in Part4.
It is the conjunction of two independently quantified universal assertions.

**First assertion.** For every probability measure ν on ℝ² and every function
f : ℝ² → ℝ, assume f is λ²-almost-everywhere measurable, everywhere nonnegative,
λ²-integrable, and ν = λ².withDensity (ofReal ∘ f). Define
L(y) = ∫⁻_ℝ max(f(x,y),0) dλ(x) ∈ [0,∞]. Then:

- L(y) < ∞ for λ-almost every y;
- for every g : ℝ → ℝ, if g(y) ≥ 0 for all y and
  max(g(y),0) = L(y) for λ-almost every y, g is a density of the second
  marginal and gives its CDF at every threshold.

Fully expanding that last conclusion: g is λ-almost-everywhere measurable,
everywhere nonnegative and λ-integrable; the pushforward ν ∘ snd⁻¹ equals
λ.withDensity (ofReal ∘ g); and, for every t ∈ ℝ,
((ν ∘ snd⁻¹)((−∞,t])).toReal = ∫_(−∞,t] g(v) dλ(v).
There is no separate measurability premise on g; almost-everywhere agreement
is sufficient. The order is ν, probability instance, f, joint-density premise,
then the almost-everywhere finiteness conjunction with the universal assertion
over g and its two premises.

**Second assertion.** For every f : ℝ² → ℝ, suppose f(x,y) ≥ 0 at every point.
For every x ∈ ℝ, suppose y ↦ f(x,y) is λ-integrable and
c = ∫ f(x,t) dλ(t) > 0. Then q(y) = f(x,y)/c is λ-integrable,
q(y) ≥ 0 for every y, and ∫ q dλ = 1. This assertion needs no joint probability
measure, total planar normalization, or global joint measurability premise.
It normalizes each selected positive integrable slice. It does not explicitly
assert a conditional-kernel or conditional-distribution identity.

The Challenge docstring and definition docstring both describe the almost-everywhere
marginal version result and normalization at each selected positive integrable
slice, and state that the usual measure-theoretic conditions are assumed.

**Generated closure dependency.** `T37WholeStatement._proof_1` is the ordinary
`OuterMeasureClass` instance for real measures, used by almost-everywhere
notation. It adds no hypothesis or specialized interpretation of null sets.

**Junk and totalization audit.** `ofReal` truncation is neutralized by f,g ≥ 0.
The extended marginal L may be infinite or behave exceptionally at null values;
agreement with real g and finiteness are only asserted almost everywhere. A
nonnegative finite measurable version can therefore replace those values. The
lower-integral definition remains meaningful on exceptional nonmeasurable
sections; Fubini supplies the usual section integrals almost everywhere.
`toReal ∞ = 0` cannot affect probabilities because the projection of ν is a
probability measure. Mathlib's measure-map fallback on a non-a.e.-measurable
map is irrelevant: snd is continuous and measurable. All concluded real
integrals have integrability, either as a hypothesis or as a simultaneous
conclusion. The conditional denominator is finite by integrability and strictly
positive by an explicit hypothesis; neither division by zero nor the Bochner
non-integrability default is used there. The version g can differ on a null set,
including by changes that destroy literal Borel measurability; `Density` uses
a.e. measurability and so handles such versions correctly. There is no log,
sqrt, rpow, truncated subtraction, empty index type, sequence limit, or
partial function.

## SAP.P001b.T38

Locations: `SAP/P001b/Challenge/Part2.lean:75–81`,
`SAP/P001b/Defs/Part4.lean:98–112`,
`SAP/P001b/Defs/Part1.lean:16–19`,
`SAP/P001b/Defs/Part2.lean:49–53`, and generated
`SAP.P001b.T31Statement._proof_1`, `SAP.P001b.dyadicLocation._proof_1`.

**Unfolded statement and quantifiers.** This is an unconditional conjunction.
Let γ = N(0,1) be Mathlib's `gaussianReal 0 1`, and let W be its pushforward
by the constant zero map ℝ → ℝ. Then W = δ₀, W({0}) = 1, there is no
f : ℝ → ℝ that is a.e. measurable, everywhere nonnegative and λ-integrable
with W = λ.withDensity (ofReal ∘ f), and, for every m ∈ ℝ and s ∈ ℝ≥0
with s > 0, W ≠ N(m,s). The parameter s in `gaussianReal m s` is variance.
For s > 0 this law has the density
exp(−(t−m)²/(2s))/sqrt(2πs). (Mathlib also defines N(m,0) = δ_m,
but the quantified comparison excludes variance zero.)

The remaining conjunction states:

1. for every real x, 0*x = 0;
2. 1 and −1 each belong to [−1,1];
3. 1−1² = 0 and 1−(−1)² = 0;
4. 2(1−1²) = 0 and 2(1−(−1)²) = 0;
5. 2π sqrt(1−1²) = 0 and 2π sqrt(1−(−1)²) = 0;
6. at every xy ∈ ℝ², B(0,0,1,1,1;xy) = 0 and B(0,0,1,1,−1;xy) = 0;
7. each of these two functions has planar real integral zero, and 0 ≠ 1.

Here the SAP definition has been fully unfolded as

B(mx,my,sx,sy,ρ;(x,y)) =
 exp(−[((x−mx)/sx)² + ((y−my)/sy)²
       − 2ρ(x−mx)(y−my)/(sx*sy)] / [2(1−ρ²)])
 / [2π*sx*sy*sqrt(1−ρ²)],

using total real operations. Its general parameters are arbitrary reals, with
no domain guards in the definition. The theorem uses only mx=my=0, sx=sy=1,
ρ=±1. There are no additional hypotheses about joint normal variables or
independence; no such variables are quantified. The docstring describes the
zero normal combination and the unusable printed correlation endpoints.

**Generated closure dependencies.** Both `_proof_1` declarations named after
`T31Statement` and `dyadicLocation` prove that the natural numeral 1+1 is at
least two, for elaboration of numeral 2. The fat-Cantor and dyadic constructions
themselves do not enter T38.

**Junk and totalization audit.** The constant pushforward map is measurable,
so the measure-map nonmeasurability fallback is unused. In `Density`, `ofReal`
is exact on a nonnegative candidate and integrability is explicit. No
`toReal` of a measure occurs here. In the general B formula, sx=0 or sy=0
would cause totalized divisions, and |ρ| > 1 would invoke `Real.sqrt` on a
negative argument (returning zero). Those parameter choices are not used.
At the tested endpoints |ρ|=1, both 2(1−ρ²) and sqrt(1−ρ²) really are zero.
Lean then makes the exponent's quotient zero, exp(0)=1, and the final quotient
1/0=0. Thus the statements that B vanishes and integrates to zero expressly
describe a totalized formula. They must not be interpreted as evaluation of an
ordinary defined real quotient, or as the density of a degenerate Gaussian
law. The zero function is integrable, so the two zero integrals are not
Bochner non-integrability defaults. `sqrt(0)=0` is a valid boundary value;
the actual out-of-domain operation is division by zero. The SAP definition's
own docstring explicitly acknowledges total real division at endpoints. There
is no log, rpow, truncated subtraction, empty index type, sequence limit,
infimum, or other partial-function default.
