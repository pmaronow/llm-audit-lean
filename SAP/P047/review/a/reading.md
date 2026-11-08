# Blind reading of the Lean statements

This file was written after reading all supplied Defs and Challenge files and the relevant Mathlib definitions, and **before opening `claims.json` or `record.json`**. Challenge docstrings are not treated as theorem hypotheses. There are three theorem stubs, each asserting a proposition defined in Defs; none has an additional argument or hypothesis outside that proposition.

## Shared objects and conventions

`UnitData = ℝ × Bool × (ℝ × ℝ)` has the usual product Borel measurable structure. Write a unit as `u = (W,A,(Y₀,Y₁))`, identifying `false` with arm 0 and `true` with arm 1. The functions `covariate`, `arm a`, and `potential a` are respectively `W`, `1{A=a}`, and `Yₐ`. `observed = A Y₁ + (1-A)Y₀` expresses consistency by definition. The conditioning sigma algebra `covariateSigma` is the pullback of the Borel sigma algebra along W, hence precisely sigma(W), and is a sub-sigma algebra of the ambient measurable space.

A `CausalLaw L` consists of a probability measure P on this space and a Borel measurable function e:ℝ→ℝ, with the following assumption (`Ignorable`): for each a∈{0,1}, and then for every Borel measurable f:ℝ→ℝ such that f(Yₐ) is P-integrable,

`E_P[1{A=a} f(Yₐ) | W] = pₐ(W) E_P[f(Yₐ) | W]` P-almost surely,

where p₁=e and p₀=1-e. The exceptional null set can depend on a and f. This is a scalar-potential conditional factorization, not an explicitly assumed joint factorization for (Y₀,Y₁). Taking f=1 calibrates e(W) as the conditional treatment probability, and in particular implies 0≤e(W)≤1 almost surely. The structure does not otherwise impose outcome moment, covariate distribution, or overlap conditions.

`BoundedOverlap L B ε` means, jointly: B>0, ε>0, ε≤1/2; for each a, |Yₐ|≤B P-almost surely; and ε≤e(W)≤1-ε P-almost surely. Bounds are almost sure, not pointwise on all possible units.

Write

* `Z = score L = A Y/e(W) - (1-A)Y/(1-e(W))`, with Y the observed outcome;
* `θ = ate L = ∫(Y₁-Y₀)dP`;
* `Z₁ = treatedScore L = A Y/e(W)` and `μ₁ = treatedMean L = ∫Y₁dP`.

`sampleLaw P` is the countable product P^ℕ. The coordinates of s:ℕ→UnitData are independent with the same law P; the n-observation estimator uses coordinates 0 through n-1. Define `θ̂ₙ(s) = (1/n)∑_{i<n} Z(sᵢ)` and `μ̂₁ₙ(s) = (1/n)∑_{i<n} Z₁(sᵢ)`. All divisions in these definitions are real division, including casts of natural sample sizes to ℝ. At n=0 Lean defines these estimators as zero; finite-sample assertions explicitly require n≥1. For n≥1 and α∈(0,1), let

`hₙ = (B/ε) sqrt(2 log(2/α)/n)`, `Cₙ(s) = [θ̂ₙ(s)-hₙ, θ̂ₙ(s)+hₙ]`,

and `h₁ₙ = (1/ε) sqrt(log(2/α)/(2n))`. `intervalWidth` is the real difference of the displayed endpoints, rather than a general set-diameter operation.

`TreatedMeanModel L ε` means ε>0, 0≤Y₁≤1 P-almost surely, and ε≤e(W) P-almost surely. It adds no bound on Y₀ and no explicit upper overlap bound away from 1. It still uses the entire `CausalLaw`, including both scalar factorization assumptions. Calibration implies e≤1 almost surely.

### Relevant Mathlib meanings

* `μ.real S = (μ S).toReal`. All measures used in probabilities here are probability measures, so these are finite ordinary event probabilities, in [0,1]. The measurable propensity and the measurable procedures below make the relevant events measurable.
* Conditional expectation is Mathlib's Bochner conditional expectation (`MeasureTheory/Function/ConditionalExpectation/Basic.lean`, definition `condExp`). It defaults to zero for a nonintegrable integrand, an invalid sub-sigma algebra, or a failure of sigma-finiteness after restriction. Here sigma(W) is a genuine sub-sigma algebra, restricted probability measures are finite, and the displayed boundedness assumptions give integrability whenever needed for a conclusion. Tests in the factorization assumptions explicitly require integrability, and their products with arm indicators are integrable.
* Bochner integrals default to zero if nonintegrable (`MeasureTheory/Integral/Bochner/Basic.lean`, `integral`). Under `BoundedOverlap` the potential outcomes, score, and sample estimators are integrable. Under `TreatedMeanModel`, the treated score is bounded almost surely even if Y₀ is nonintegrable: multiplication by the treatment indicator removes the control outcome pointwise.
* `variance Z P` is `(∫⁻ |Z-∫Z dP|² dP).toReal` (`Probability/Moments/Variance.lean`). It would default to zero for infinite variance; bounded score here ensures genuine finite variance. `v.toNNReal` clips a real v below at zero; variance here is already nonnegative.
* `gaussianReal 0 v` is the centered real Gaussian of variance v, and for v=0 is the Dirac probability measure at 0 (`Probability/Distributions/Gaussian/Real.lean`).
* `TendstoInDistribution` (`MeasureTheory/Function/ConvergenceInDistribution.lean`) asserts almost-everywhere measurability for every indexed random variable, measurability of the limiting variable, and weak convergence of their pushforward probability measures. Here the limiting variable is the identity on the specified Gaussian probability space.
* Real supremum/infimum and real filter limsup/liminf are conditionally complete operations. Every set being optimized below is nonempty because of an inserted 0 or 1 and is contained in [0,1]; all sequences of risks, coverage, and width probabilities are likewise bounded in [0,1]. Thus these are the ordinary finite extrema and limits superior/inferior, with no unbounded or empty-set convention determining an assertion. `atTop` on ℕ means n→∞ and on ℝ means K→+∞. Real `sqrt` is the nonnegative square root, with its extension to negative arguments unused in the substantive formulas. The logarithm arguments are positive in interval conclusions.

## Theorem `SAP.P047.T1`

This is the conjunction of the following two independently universally quantified assertions.

First: for every `CausalLaw L`, every real B, and every real ε, if `BoundedOverlap L B ε`, then all of the following hold:

1. `E_P[Z | W] = E_P[Y₁-Y₀ | W]` P-almost surely.
2. `∫Z dP = θ`.
3. `|Z|≤B/ε` P-almost surely.
4. For every natural n with n≥1, all of the following hold:
   * `∫θ̂ₙ dP^ℕ = θ`.
   * For every real t≥0, `P^ℕ(t≤|θ̂ₙ-θ|) ≤ 2 exp(-n t² ε²/(2B²))`. The event uses ≥, including t=0.
   * For every real α with 0<α<1, simultaneously:
     - `P^ℕ(θ∈Cₙ) ≥ 1-α`;
     - hₙ≥0;
     - for every sequence s (not merely almost every sequence), the endpoint width is both `2hₙ` and `(2B/ε) sqrt(2 log(2/α))/sqrt(n)`;
     - `sqrt(n) (2hₙ) = (2B/ε) sqrt(2 log(2/α))`.

Second: for every `CausalLaw L` and then every real ε, if `TreatedMeanModel L ε`, then:

1. `0≤Z₁≤1/ε` P-almost surely.
2. For every natural n≥1, simultaneously:
   * `∫μ̂₁ₙ dP^ℕ = μ₁`;
   * for every real t≥0, `P^ℕ(t≤|μ̂₁ₙ-μ₁|) ≤ 2 exp(-2n ε²t²)`;
   * for every real α∈(0,1), `P^ℕ(μ₁∈[μ̂₁ₙ-h₁ₙ,μ̂₁ₙ+h₁ₙ]) ≥ 1-α`.

The statement does not separately assert a conditional expectation identity for Z₁ or a sample mean of control outcomes under the weaker treated-only model.

## Theorem `SAP.P047.T2`

For every real B and then every real ε, assuming B>0, ε>0, and ε≤1/2, the following conjunction holds.

Define, for each real K,

`R_{B,ε}(K) = sup({0} ∪ { P_L^ℕ(K < sqrt(n)|θ̂ₙ-θ_L|) : L a CausalLaw, BoundedOverlap L B ε, n∈ℕ, n≥1 })`.

The same B and ε are used for every law and every sample size inside this supremum. Its event is a strict exceedance. Then `R_{B,ε}(K)→0` as the real K→+∞.

Additionally, for every `CausalLaw L` with `BoundedOverlap L B ε`, all of the following hold:

1. For every natural n≥1 and then every real K≥0,
   `P_L^ℕ(K ≤ sqrt(n)|θ̂ₙ-θ_L|) ≤ 2 exp(-K²ε²/(2B²))`.
   This event is non-strict.
2. `Var_{P_L}(Z)≤B²/ε²`.
3. Under the fixed sample law P_L^ℕ, `sqrt(n)(θ̂ₙ-θ_L)` converges in distribution, as natural n→∞, to `N(0,Var_{P_L}(Z))`. This includes the variance-zero point mass. The definition also asserts almost-everywhere measurability for all n, including n=0.

The normal convergence is for each fixed L, not a convergence uniformly over populations. The root-n tightness is uniform over both L and every positive n with the given common B and ε.

## Additional objects for `SAP.P047.T3`

`uniform01` is Lebesgue measure restricted to (0,1], of total mass 1. It is the ordinary uniform probability law on the unit interval; the endpoint convention changes no mass.

`JointIgnorable L` strengthens the scalar tests to the following: for each a∈{0,1}, then every Borel measurable f:ℝ²→ℝ with f(Y₀,Y₁) integrable,

`E_P[1{A=a} f(Y₀,Y₁) | W] = pₐ(W) E_P[f(Y₀,Y₁) | W]` P-almost surely.

`UnknownModel L` requires all of:

1. The distribution of W under P equals `uniform01`.
2. `JointIgnorable L`.
3. For each a, Yₐ equals 0 or 1 P-almost surely.
4. `1/4≤e(W)≤3/4` P-almost surely.

All `CausalLaw` assumptions remain in force. There is no smoothness or other complexity bound on the measurable propensity or on the potential-outcome regressions.

An observed unit is `(W,A,Y)∈ℝ×Bool×ℝ`. `observedSample n s` is the ordered n-tuple of these observations from indices i=0,…,n-1 (`Fin n`). No procedure below receives L, e, or the unobserved potential outcomes as an argument.

`fairBool` gives mass 1/2 to each Boolean. The fixed measure `baselineLaw`, denoted S here, is obtained by drawing W uniform, A fair Boolean, and V fair Boolean independently, and setting Y₀=0 and Y₁=1{V=true}. This is a fully specified measure on UnitData; it is not a quantifier over possible baselines.

For a measurable space R with a probability measure Q, every procedure has one independent seed r∼Q: the joint sample-and-seed measure is P_L^ℕ⊗Q. No atomlessness, standard Borel, or nonemptiness hypothesis is explicitly imposed on R; existence of a probability measure excludes an empty underlying type. A singleton seed includes deterministic procedures.

For a real-valued estimator family E, let

`risk_E(n,η) = sup({0} ∪ { (P_L^ℕ⊗Q)(η≤|Eₙ(observedSample(n,s),r)-θ_L|) : UnknownModel L })`,

and define `strictRisk_E(n,η)` with η<|error| instead. Supremum laws may vary with n and η.

For families of extended-real endpoints loₙ, hiₙ define

`coverage(n) = inf({1} ∪ { (P_L^ℕ⊗Q)(loₙ≤θ_L≤hiₙ) : UnknownModel L })`,

where the endpoints are evaluated on `(observedSample(n,s),r)` and θ_L is included into the extended reals. No assumption lo≤hi or finiteness of endpoints is imposed. Finally

`widthProb(n) = (S^ℕ⊗Q)(loₙ + 1/6 < hiₙ)`.

Addition of the finite real 1/6 is extended-real addition. For finite ordered endpoints this is exactly width>1/6. Unbounded intervals containing finite points satisfy this event; reversed endpoints and intervals with both endpoints equal to the same infinity do not. This definition avoids subtracting infinities. All interval probabilities use the same endpoint functions under each population, including S.

## Theorem `SAP.P047.T3`

The theorem is universe-polymorphic: for every type R in the fixed arbitrary universe, every measurable-space structure on R, every measure Q on R, and every proof that Q is a probability measure, the following two assertions hold as a conjunction.

1. For every family `E : (n:ℕ) → ((Fin n → ObservedUnit) × R) → ℝ`, if Eₙ is measurable for every n, then both:
   * for every natural n≥1, `risk_E(n,1/12)≥1/2`;
   * there exists a real η>0, chosen after Q and the whole estimator family E, such that `limsup_{n→∞} strictRisk_E(n,η)>0`.

2. For every pair of endpoint families `lo,hi : (n:ℕ) → ((Fin n → ObservedUnit) × R) → EReal`, if loₙ and hiₙ are each measurable for every n, then for every real α with 0<α<1/2, assuming

   `liminf_{n→∞} coverage(n) ≥ 1-α`,

   one has both

   `liminf_{n→∞} widthProb(n) ≥ 1-2α` and `0<1-2α`.

Thus honesty is uniform over `UnknownModel` before taking the asymptotic lower limit, while the width conclusion is under the one fixed baseline S. It uses strict width>1/6. The assertion does not explicitly state that S can be equipped with a propensity to be an `UnknownModel`, and does not separately quantify over larger model classes.
