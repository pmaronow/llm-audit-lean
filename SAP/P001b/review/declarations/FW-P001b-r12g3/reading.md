# Blind reading

This file was saved before opening `claims.json` or `record.json`. All source declarations named by `closure.json`, including the generated declarations, have been read. Generated declarations were inspected by compiling `scratch/Blind.lean` with `sap-lean`. Throughout, λ denotes real Lebesgue measure, λ² denotes the product/planar Lebesgue measure, and “a.e.” is with respect to the displayed Lebesgue measure. A set integral is an integral with respect to the restriction of that measure to the set. Probability laws here are Mathlib measures with `IsProbabilityMeasure`, i.e. total mass one. Their event probabilities are the real numbers obtained by applying `ENNReal.toReal` to their measures.

## SAP.P001b.T30

Source: `SAP/P001b/Challenge/Part2.lean:10–24`; full statement: `SAP/P001b/Defs/WholeW2.lean:52–92`.

Unfolded definitions:

- `probability ν A` means `(ν A).toReal` (`Defs/Part1.lean:13–14`).
- `CDFDensity ν f`, for a real measure ν and real function f, means f is a.e. measurable for λ, f(x) ≥ 0 at **every** real x, and, for **every** real threshold x, the extended nonnegative integral of `ENNReal.ofReal (f(t))` over t ≤ x equals ν((−∞,x]). This is not defined by assuming integrability or equality of weighted measures (`Defs/WholeW2.lean:18–20`).
- `JointCDFDensity ν f`, for a measure on ℝ² and real function f on ℝ², means f is a.e. measurable for λ², f(z) ≥ 0 at every z, and, for every real x and y, the extended integral over u ≤ x of the extended integral over v ≤ y of `ENNReal.ofReal (f(u,v))` equals ν((−∞,x] × (−∞,y]) (`Defs/WholeW2.lean:26–30`).
- `unitUniformLaw` is λ restricted to the closed interval [0,1]. `uniformDistributionFunction(t)` is max(0,min(1,t)). `jointDistributionFunction ν x y` is `(ν ((−∞,x] × (−∞,y]))).toReal` (`Defs/WholeW2.lean:33–37`; `Defs/Part2.lean:20`).
- A measure pushforward is Mathlib `Measure.map`; product measures are Mathlib `Measure.prod`. `IndepFun` means the two inverse-image σ-algebras are independent: measurable events determined by the two functions have intersection probability equal to the product of their probabilities. `f =ᵐ[λ] g` means λ-a.e. pointwise equality. `HasDerivAt F d x` is ordinary two-sided real differentiability with derivative d, and `DifferentiableAt ℝ F x` asserts existence of such a derivative.

The theorem is a conjunction of the following six independently universally quantified assertions; quantifier order is as written below.

1. For every probability measure ν on ℝ, then every f,g : ℝ → ℝ, if f and g both satisfy the above lower-tail definition for ν, then f = g λ-a.e.; the real CDF F(t) = `(ν ((−∞,t])).toReal` has derivative f(x) at λ-a.e. x; for every x, if F is differentiable at x then its derivative is nonnegative; f is Bochner integrable over λ; its integral is one; and, for every threshold x, F(x) equals the real integral of f over (−∞,x]. The two-density premise does not limit the one-density conclusions, since g can be chosen to equal f.
2. For every real probability measure ν, then every f,h : ℝ → ℝ, if f satisfies the lower-tail definition, h is nonnegative at every point, and h=f λ-a.e., then h satisfies that same lower-tail definition, h is integrable, and, at every x, F(x) is the integral of h on (−∞,x]. No separate measurability of h is assumed; a.e. measurability follows from the equality.
3. For every planar probability measure ν, then every f,g : ℝ² → ℝ, if both satisfy the iterated lower-rectangle definition, then f=g λ²-a.e.
4. Put U=λ restricted to [0,1] and ν=U×U. U and ν are probability measures; the coordinate projections are independent under ν; for every t the CDF of U is max(0,min(1,t)); for every x,y the joint CDF of ν is the product of these clamped values; for every x,y in [0,1] it is xy. Finally, for every y with 0<y<1, at **every** real u the function v ↦ F(u,v) has derivative max(0,min(1,u)) at y, but u ↦ `deriv (v ↦ F(u,v)) y` is not differentiable at u=0. Thus the failed outer derivative is taken only after an inner derivative whose existence at all relevant u is explicitly asserted.
5. For every planar probability measure ν, then every f : ℝ² → ℝ and fx,fy : ℝ → ℝ, if f is an iterated lower-rectangle density of ν and fx,fy are lower-tail densities of its first and second marginal pushforwards, then (a) ν equals the product of those marginals iff f(u,v)=fx(u)fy(v) λ²-a.e., and (b) that a.e. factorization holds iff the pointwise product function itself is an iterated lower-rectangle density of ν. Equality to the product law expresses independence of the coordinate variables.
6. For every type Ω (any universe), then every measurable-space structure on Ω, probability measure μ on Ω, and X,Y : Ω → ℝ, if X and Y are measurable and each actual range is countable, then X and Y are independent iff, for every real x,y, `(μ {ω | X(ω)=x and Y(ω)=y}).toReal` equals `(μ {ω | X(ω)=x}).toReal * (μ {ω | Y(ω)=y}).toReal`. The factorization is pointwise at all real pairs, including values outside the ranges.

Junk-value audit:

- `ENNReal.toReal ∞ = 0`, but every use of `probability` here is on an event of a probability measure, hence finite. The marginal pushforwards are along measurable coordinate projections. No infinite mass is converted to zero.
- `ENNReal.ofReal r = 0` for r≤0, but every density supplied to it is required to be nonnegative everywhere. The defining lower-tail integrals use extended nonnegative reals directly, without converting potentially infinite integrals to real zero.
- A lower integral exists as an extended value even for a nonmeasurable integrand. Global a.e. measurability is required, and Tonelli controls the iterated expression up to exceptional sections. Finite lower-rectangle values and the probability normalization give integrability globally; arbitrary exceptional slices need not be integrable individually. This is a substantive a.e. integral notion, not reliance on a default finite value.
- Bochner integrals default to zero for nonintegrable functions. Integrability of f and h is explicitly concluded from their density premises, and hence also holds on the lower half-lines. These equalities do not use the default.
- `deriv` is zero when a derivative fails to exist. The nonnegative-derivative claim assumes differentiability. In the uniform example the inner derivative is explicitly shown to exist for every u; the outer failure is an actual failure of differentiability, not the numeric value of a default derivative.
- `Measure.map` for a non-a.e.-measurable map can return a default Dirac measure for a nonzero source measure. All maps here are measurable projections or explicitly assumed measurable functions, so this convention does not apply.
- No variable division, truncated subtraction, logarithm, square root, real power, infimum/supremum, limsup/liminf, or partial inverse appears. The countable-range assertion can include an empty range syntactically, but a probability measure cannot be carried by an empty Ω, so it does not make the probability assertion vacuous.

Closure auxiliaries: `T30WholeStatement._proof_1` and `._proof_3` are the standard outer-measure-class instances on real and planar measures. `._proof_2` is the standard continuous scalar multiplication instance on ℝ. They add no mathematical assumptions or definitions.

## SAP.P001b.T31

Source: `SAP/P001b/Challenge/Part2.lean:26–30`; statement: `SAP/P001b/Defs/Part4.lean:35–42`.

The objects are entirely fixed; the theorem has no external hypotheses. For a finite Boolean list w, define a closed interval I(w) recursively (`Defs/Part2.lean:34–40`). I([])=[0,1]. If I(w)=[L,R] and the length of w is k, let m=(L+R)/2 and h=4^(−(k+1))/2. Then I(false::w)=[L,m−h] and I(true::w)=[m+h,R]. Thus each step deletes the central open interval of length 4^(−(k+1)). Define K_n as the union of I(w) over every Boolean list of length n (`cantorStage`, lines 42–43). Define C as the intersection of K_n over all natural n including 0 (`fatCantorSet`, line 44). Define f(x)=2 for x∈C and f(x)=0 otherwise (`cantorDensity`, line 45). On the subtype C={x:ℝ // x∈C}, with its inherited measurable space, define ν as twice the pullback of λ along subtype inclusion i(x)=x.val (`cantorProbability`, lines 46–47). For measurable subsets B of this subtype the intended pullback is λ(i(B)).

The conclusion is that C is closed; its extended Lebesgue measure is 1/2; ν is a probability measure; i:C→ℝ is measurable; the pushforward i_*ν has density f; the **literal range** of i is C; the set {x | f(x)>0} is C; and, for every real a and then b, if a<b, the closed interval [a,b] is not a subset of C.

Here `Density (i_*ν) f` unfolds (`Defs/Part1.lean:17–19`) into: f is a.e. measurable for λ; f(x)≥0 for every x; f is Bochner integrable for λ; and `i_*ν = λ.withDensity (x ↦ ENNReal.ofReal(f(x)))`. On measurable A the latter weighted measure is the extended integral of `ENNReal.ofReal(f)` over A. This states an actual absolutely continuous probability law. The support assertion in the theorem is precisely the positive-density set, not a separate definition of topological support.

The docstring describes this as refuting a printed assertion and discloses omission of a geometric-series calculation and quantitative stage-component bounds. The assertion supposedly refuted cannot be identified from this theorem alone.

Junk-value audit:

- Only divisions by fixed, nonzero real numerals 2 and 4 occur in the construction. Exponent `w.length+1` is a natural number and is always positive. There is no natural subtraction or lossy cast.
- In `volume C = 1/2`, the numeral division is in the extended nonnegative reals with nonzero finite denominator 2; it denotes the ordinary finite half.
- `Measure.comap` would default to the zero measure if the function were not injective or did not send measurable sets to null-measurable sets. Subtype inclusion is injective; C is closed, hence Borel, so its measurable subsets have Borel images in ℝ. Thus this pullback is the genuine restricted Lebesgue law, and the asserted probability normalization also rules out a zero default.
- The pushforward map is measurable, so its possible default Dirac law is not used. The integrability included in `Density` prevents the Bochner zero default; f has values only 0 and 2 so `ofReal` does not discard negative values. There is no `toReal` here.
- The subtype is not empty: the asserted positive volume and probability law force nonemptiness. The recursion has a specified base case and total list pattern matching, with no missing branch or arbitrary value. There are no other potentially partial operations from the requested list.

Closure auxiliaries: `cantorInterval._f` is the displayed structural recursion using the already-computed suffix interval, and `cantorInterval.match_1` is ordinary list case analysis. `cantorProbability._proof_1` is the standard scalar-tower instance for extended nonnegative reals. `T31Statement._proof_1` and the shared `dyadicLocation._proof_1` are both the standard proof that natural numeral 2 is at least two; neither imports any dyadic example or further condition.

## SAP.P001b.T32

Source: `SAP/P001b/Challenge/Part2.lean:32–35`; statement: `SAP/P001b/Defs/Part4.lean:44–54`.

This is a conjunction of a universal assertion and an existential fixed-set example.

First, for every type Ω, measurable-space structure on Ω, probability measure μ, and function X:Ω→ℝ, assume X is measurable; then for every real function f, assume `Density (μ.map X) f`. Expanded, f is λ-a.e. measurable, nonnegative at every real number, Bochner integrable, and the pushforward law of X is the weighted Lebesgue measure with weight `ENNReal.ofReal ∘ f`. The conclusion is: for every real t the event {ω | X(ω)=t} has extended μ-measure zero; the actual set range(X) is not countable; and the type Ω is not countable. These are literal range and sample-space cardinality conclusions, not just claims about essential ranges.

Second, fix C=[0,1/2] minus the set of real casts of rational numbers. There exists a measure ν on the subtype C such that all the following hold simultaneously: C is Borel measurable; λ(C)=1/2; ν is a probability law; subtype inclusion i is measurable; its literal range is C; its pushforward has density f_C(x)=2 on C and 0 elsewhere (with the full `Density` expansion above); C as a real set is not countable; the subtype C is not a countable type; and for every real a,b with a<b, [a,b] is not contained in range(i). The measure ν is quantified after C is fixed, and there are no further external hypotheses.

Junk-value audit:

- `Measure.map` has genuine pushforward semantics because X and the subtype inclusion are explicitly measurable. No default measure can furnish the conclusion.
- `Density` includes integrability, so no nonintegrable Bochner integral is interpreted as zero. Nonnegativity prevents `ofReal` from hiding negative values.
- The halves in the real interval and extended measure are divisions by fixed nonzero 2. The rational-to-real map is the injective standard field embedding and contains no truncation. The set difference is ordinary set difference, not numeric subtraction.
- The probability hypothesis rules out an empty Ω, and the example's positive volume/probability rules out empty C. No derivative, `toReal`, log/sqrt/rpow, infimum/supremum, limit operation, or unspecified partial value occurs.

The only additional closure item is `T31Statement._proof_1`, the numeral-2 instance described above; the fat-Cantor construction is not a dependency of this declaration.

## SAP.P001b.T33

Source: `SAP/P001b/Challenge/Part2.lean:37–40`; statement: `SAP/P001b/Defs/Part4.lean:56–58`.

For every type Ω, then every X:Ω→ℝ, then every g,h:ℝ→ℝ, the composite functions g∘X and h∘X are equal as functions Ω→ℝ if and only if, for every real x belonging to the actual image {X(ω) | ω∈Ω}, g(x)=h(x). Composition means (g∘X)(ω)=g(X(ω)); function equality is pointwise equality by extensionality. There is no probability measure, σ-algebra, measurability, continuity, or a.e. qualifier. This is a pointwise statement for arbitrary functions. No SAP definitions other than `T33Statement` are in its closure.

Junk-value audit: no arithmetic or partial operation occurs. Empty Ω is permitted and yields an empty image; both sides then hold, as appropriate for the same equivalence. This does not make the universally quantified assertion vacuous on nonempty types.

## SAP.P001b.T34

Source: `SAP/P001b/Challenge/Part2.lean:42–46`; statement: `SAP/P001b/Defs/Part4.lean:60–66`.

Define f:ℝ²→ℝ by f(x,y)=1 when 0<x<1 and −1<y<0, and f(x,y)=0 otherwise (`negativeRectangleDensity`, `Defs/Part2.lean:26–27`). This is the indicator of the open unit-area negative rectangle R=(0,1)×(−1,0). Let E={(x,y) | 0≤x and x≤1 and y≤x}. All data are fixed and there are no hypotheses or existential quantifiers. The conclusion is the conjunction: f is pointwise nonnegative; f is Bochner integrable over λ²; its total integral is one; its integral over E is one; the iterated real integral over x∈[0,1] and then y∈[0,x] of f(x,y) is zero; and those last two displayed integrals are unequal. A probability measure is not named in the statement, but the nonnegative normalized density defines the law λ².withDensity(ofReal∘f), so the integral on E is its event probability.

The docstring calls this a refutation of a printed formula and says it retains only this rectangle example, omitting a second uniform-square example. The actual formula being refuted is not supplied as an explicit universal assertion inside this theorem.

Junk-value audit: the only integrals are Bochner integrals. Global integrability is explicitly concluded; restriction to E preserves it. Every inner section on [0,x] for x∈[0,1] is identically zero because y cannot be negative there, so its zero integral is genuine, and the outer integrand is integrable. There is no nonintegrable default involved. The density's normalization is nonzero, no empty probability space is used, and there is no division, cast, `toReal`, logarithm/square root/power, extremum, limit, or partial inverse.
