# Blind reading of the Challenge statements

This file was written from `SAP/P001c/Defs*.lean`, `Defs/Part1`–`Part6`,
`Challenge.lean`, `Challenge/Part1`–`Part2`, and the Mathlib definitions they use,
before opening `claims.json` or `record.json`. The prose in the Challenge
docstrings is not an additional Lean hypothesis or conclusion.

## Conventions and expansion of definitions

Every theorem with an implicit `Ω` quantifies over every type and every
sigma-algebra on it. Inside its statement, each `μ` is universally quantified
and has total mass one. All random variables mentioned below are real-valued
unless another range is specified. `Fin n` has indices `0,...,n-1`;
`Finset.range n` has the same indices. All divisions, subtractions, and square
roots in the displayed statistical formulas take place in the real numbers.

* `probability μ A = (μ A).toReal`. On a probability space this is the real
  value of the measure of `A`, including its outer-measure evaluation when `A`
  is not measurable. `ENNReal.toReal` maps infinity to zero, but a probability
  measure never assigns infinity to a set.
* `expectation μ X` is the Mathlib Bochner integral `∫ X dμ`.
  `meanSquaredError μ X c = ∫(X-c)² dμ`. Mathlib sets a Bochner integral to
  zero outside its integrable domain. `MemLp X 2 μ` means almost everywhere
  strong measurability and finite second absolute moment; on these probability
  spaces it ensures the ordinary first and second moments exist.
* Mathlib `covariance X Y μ = ∫(X-E X)(Y-E Y) dμ`.
  `variance X μ` is the real conversion of the nonnegative extended integral
  `∫⁻ ‖X-E X‖ₑ² dμ`. Infinite extended variance would therefore become zero.
  The uses below either assume square integrability or specify laws giving it.
* `correlationCoefficient μ X Y = Cov(X,Y)/(sqrt(Var X)sqrt(Var Y))`.
  `affineRisk μ X Y a b = E[(Y-a-bX)²]`.
  Write `β = Cov(X,Y)/Var X` and `α = E Y-β E X` for
  `regressionSlope` and `regressionIntercept`.
* `isConditionalMean μ X Y m` means: `m` is measurable, `Y` and `m∘X`
  are integrable, and for every measurable subset `A` of the range of `X`,
  `∫_{X∈A}Y dμ = ∫_{X∈A}m(X) dμ`. Measurability of `X` is not included in
  this definition itself. The L² hypotheses in its uses give almost everywhere
  measurable versions, or measurability of `X` is separately assumed.
* `cdfAt μ X x = Pμ(X≤x)`. `convergesInProbability μ Z c` means
  `∀ ε>0, Pμ(dist(Z_n,c)≥ε)→0` as natural `n→∞`. On the reals the distance
  is `|Z_n-c|`. `convergesInDistribution μ Z ν` means: for every real `x`
  at which `t↦ν((−∞,t])` is continuous, `Pμ(Z_n≤x)→ν((−∞,x])`.
* `isIID μ X` says all `X_i` are measurable, the whole family is jointly
  independent, and every `X_i` is identically distributed with `X_0`.
  Mathlib `IdentDistrib` includes almost everywhere measurability and equality
  of pushforward laws. `iIndepFun` and `IndepFun` express independence of the
  sigma-algebras induced by the functions (finite joint independence for the
  indexed family). No pairwise-only convention is used.
* `sampleAverage X n = (Σ_{i<n}X_i)/n`, including its real-division value zero
  at `n=0`. `empiricalLaw X n ω = n⁻¹ Σ_{i<n}δ_{X_i(ω)}` with an extended
  nonnegative scalar; at `n=0` it is the zero measure. Positive sample size
  is imposed on assertions calling it a probability law.
  `pluginVariance X n = (Σ_{i<n}X_i²)/n-((Σ_{i<n}X_i)/n)²`.
* For a finite real weight vector `w`, `finiteMean w x = Σ_i w_i x_i`,
  `finiteProbability w A = Σ_i 1_{A(i)}w_i`,
  `finiteVariance w x = Σ_i w_i(x_i-Σ_j w_j x_j)²`, and finite covariance
  and correlation use the corresponding centered products and square-root
  normalization. The definition alone does not normalize the weights. All
  weights used below are explicitly normalized: `nullWeights=(1/2,1/2,0)`,
  `signWeights=(1/2,1/2)`, and `equalWeights N` assigns `1/N` to each index
  with `N>0` when used for the general population formulas.
* `fairCoinLoss(c)=((0-c)²+(1-c)²)/2`.
  `normalPDF(m,s,y)=exp(−(y-m)²/(2s²))/(s sqrt(2π))`.
  Mathlib `gaussianReal m v` has mean `m` and **variance** `v≥0`; for `v=0`
  it is `δ_m`.
* `bivariatePDF(mx,my,sx,sy,ρ)(x,y)` is
  `exp(−[((x-mx)/sx)²+((y-my)/sy)²−2ρ(x-mx)(y-my)/(sx sy)]/[2(1-ρ²)])`
  divided by `2π sx sy sqrt(1-ρ²)`.
  `isJointDensity ν f` requires almost everywhere measurability of `f` for
  two-dimensional Lebesgue measure, pointwise nonnegativity, integrability,
  and `ν=volume.withDensity(ofReal∘f)`. `withDensity` integrates its extended
  nonnegative argument over measurable sets. `intervalUniform a b` uses
  the Lebesgue density `1_[a,b]/(b-a)`; its only use here has `a=0,b=1`.
  `μ.map X` is the pushforward law when `X` is almost everywhere measurable.
  In this Mathlib version its fallback outside that domain can be an arbitrary
  Dirac mass; the law equalities below involve measurable functions.
* `covarianceEntries μ X j k = Cov(X_j,X_k)`.
  `affinePredictor b x = b_0+Σ_{k<K}b_{k+1}x_k`.
  `coordinatePartial f x k = deriv(t↦f(x with x_k replaced by x_k+t))(0)`.
  `HasDerivAt f d x` asserts actual differentiability with derivative `d`;
  `deriv f x` is the derivative value, set to zero if differentiability fails.
  `Matrix.IsSymm` means equality with the transpose.
* `powerTailMass(k)=7(1/8)^(k+1)` for `k∈ℕ`. A real infinite sum `Σ'`
  is totalized outside summability, but the finite real moment sums below
  have explicit summability premises as conclusions. The infinite fourth
  moment uses a nonnegative extended-real sum and asserts infinity.
* `varianceConsistent μ V v` is exactly `n V_n→v` in probability;
  `standardErrorConsistent μ V v` is exactly
  `sqrt(n)sqrt(V_n)→sqrt(v)` in probability.

## CDF and process definitions

`isCDF F` means `0≤F(x)≤1` for every real `x`, monotonicity, right
continuity at every `x` (the limit along `[x,∞)`), limit zero at minus
infinity, and limit one at plus infinity.

`CDFSpace = lp (fun _ : ℝ => ℝ) ∞` is the space of all bounded real
functions on the reals, with the supremum norm; it is not an almost everywhere
quotient and has no measurability restriction on its functions. Mathlib
`Memℓp f ∞` means the range of `|f|` is bounded above. `embedCDF f` is this
same function when bounded and is zero otherwise. `cdfSet` is the subset
whose underlying functions are CDFs. `empiricalCDF X n ω` embeds the CDF
of `empiricalLaw X n ω`; for `n=0` it is the zero function.

For a normed real space `E`, `hadamardDerivative D H T F L` says that,
for every `h∈H`, every sequence of positive real `t_n→0`, and every
sequence `h_n→h` in norm with `F+t_n h_n∈D` for every `n`,
`[T(F+t_n h_n)-T(F)]/t_n→L(h)`. `L` is a continuous real linear map.
There is no separate requirement `F∈D` in this definition.

`supNorm h = sup_x |h(x)|`, defined as a real conditional supremum.
`cdfHadamard T F` says there exists a real linear functional `L` on **all**
real functions on the reals such that (i) there is a real `C≥0` with
`|L(h)|≤C supNorm(h)` for every bounded `h`, and (ii) for every bounded
`h`, every positive `t_n→0`, and every sequence of bounded `h_n` with
`supNorm(h_n-h)→0` and all `F+t_n h_n` CDFs, the corresponding difference
quotients converge to `L(h)`. The additivity and real homogeneity of `L`
are required even on unbounded functions. Every supremum used in its limit
condition is of a bounded function.

`cdfTangent F` consists of bounded functions `h` satisfying both:
for each `ε>0` there is `δ>0` such that
`|F(x)-F(y)|<δ ⇒ |h(x)-h(y)|<ε` for all real `x,y`; and
`F(x)∈{0,1} ⇒ h(x)=0` for every real `x`.

For a probability law `νB` on the Borel sigma-algebra of `CDFSpace`,
`isCDFBridge F νB` requires `νB((cdfTangent F)ᶜ)=0` and, for every natural
`r` and every `x,a : Fin r→ℝ`, that
`v=Σ_jΣ_k a_j[min(F(x_j),F(x_k))-F(x_j)F(x_k)]a_k` is nonnegative and
the `νB` law of `Σ_j a_j h(x_j)` is `gaussianReal 0 (max(v,0))`.
There is no existence assertion in this predicate.

`upperExpectation μ Z` is the real infimum of `Eμ g` over all measurable,
integrable real functions `g` dominating `Z` at every point.
`outerWeakConvergence μ Z ν` means that for every bounded continuous real
function `f` on the target topological measurable space, both
`upperExpectation μ (f∘Z_n)` and
`−upperExpectation μ (−f∘Z_n)` converge to `Eν f`.
The CDF process itself need not be measurable. For the bounded tests used
on probability spaces the defining infima have constant majorants and real
lower bounds. Finally `quadraticFunctional(G)=(G(0)-1/2)²`.

## T39

For every measurable space `Ω`, the following two universally quantified
assertions hold together:

1. For every probability measure `μ` on `Ω`, every natural `n`, and
   every family `X_i`, if all `X_i` are measurable and jointly independent,
   then for every real vectors `m,a` and nonnegative real vector `v` on
   `Fin n`, if each `v_i>0`, each `X_i` has law `N(m_i,v_i)`, and some
   coefficient `a_i` is nonzero, then for every real `b` the law of
   `Σ_i a_i X_i+b` is `N(Σ_i a_i m_i+b, Σ_i a_i²v_i)` and the latter
   variance is strictly positive. The nonzero coefficient hypothesis
   excludes `n=0` in this part.
2. For every real `mx,my,sx,sy,ρ`, if `sx,sy>0` and `−1<ρ<1`, let
   `f` be the displayed bivariate density and `ν` its density measure.
   Then `ν` is a probability measure, `f` is its joint density in the
   sense above, its two coordinate functions are L², their means are
   `mx,my`, their standard deviations are `sx,sy`, and their correlation
   is `ρ`. If `ρ=0`, the coordinates are independent and, at every point,
   `f(x,y)=normalPDF(mx,sx,x)normalPDF(my,sy,y)`.

## T40

For every measurable `Ω`: for every probability `μ` and every L² `X`,
`∀c∈ℝ, E[(X-c)²]=Var X+(E X-c)²`; and, for every real `c`, the risk
at `E X` is at most the risk at `c`, with equality if and only if `c=E X`.
Independently of `Ω`, for every real `c`, `fairCoinLoss(c)=c²-c+1/2≥1/4`,
with equality exactly at `c=1/2`, and twice this loss is both
`(0-c)²+(1-c)²` and `2c²-2c+1`. Its values at `−2,2,1/2` are
`13/2,5/2,1/4`, respectively; twice those values are `13,5,1/2`.
Under the two equal weights the vector `(0,1)` has mean `1/2`, variance
`1/4`, and its squared-error mean at any `c` is `fairCoinLoss(c)`.

## T41

There are no hypotheses. On `Fin 3` put weights `(1/2,1/2,0)` and vectors
`X=(0,1,0)`, `Y+=(0,1,1)`, `Y−=(1,0,0)`. All three means are `1/2`,
all three variances are `1/4` and strictly positive,
`Cov(X,Y+)=1/4`, `Cov(X,Y−)=−1/4`, and the respective correlations are
`1,−1`. The weighted probabilities of `Y+=X` and `Y−=1-X` are one.
Nevertheless there exist no real `a,b` with `Y+_i=a+bX_i` for **every**
index `i`, and no real `a,b` with `Y−_i=a-bX_i` for every index.

## T42

For every measurable `Ω`, every probability `μ`, and every real `X,Y`,
if `X,Y∈L²(μ)` and both variances are positive, then their correlation
belongs to `[−1,1]`. It equals `1` if and only if there are real `a,b`
with `b>0` and `Y=a+bX` almost surely. It equals `−1` if and only if
there are real `a,b` with `b>0` and `Y=a-bX` almost surely.

## T43

For every measurable `Ω`, probability `μ`, and `X,Y∈L²(μ)` with
`Var X>0`, define `α,β` and risk `R(a,b)` as above. Then:

* For every real `a,b`, the function `t↦R(t,b)` has derivative
  `−2E[Y-a-bX]` at `a`, and `t↦R(a,t)` has derivative
  `−2E[(Y-a-bX)X]` at `b`.
* For every `a,b`, the two normal equations
  `E[Y-a-bX]=E[(Y-a-bX)X]=0` hold if and only if `a=α,b=β`.
* For every `a,b`, `R(α,β)≤R(a,b)` and equality holds exactly when
  `a=α,b=β`.
* For **every** measurable real function `m` satisfying the full
  `isConditionalMean μ X Y m` predicate and `m∘X∈L²(μ)`, the following
  further conjunction holds. For every `a,b`, the iterated `deriv` values
  `R_aa(a,b),R_bb(a,b),R_ab(a,b)` are, respectively,
  `2, 2E[X²], 2E[X]`. These are equalities of total derivative values,
  rather than separate second differentiability assertions.
  Their determinant expression is `4Var X>0`.
  For every `a,b`, `E[(m(X)-α-βX)²]≤E[(m(X)-a-bX)²]`.
  The residual `Y-(α+βX)` has mean zero, has zero expected product with
  `X`, and has covariance zero with `X`. Finally, for every real `a,b`,
  if `x↦a+bx` is also a conditional mean of `Y` given `X` in that
  predicate's sense, then `m(X)=α+βX` almost surely.

The supplied `m` is an antecedent only of the last bullet, not of the first
three bullets. Existence of a conditional mean version is not asserted.

## T44

There are no hypotheses. With two equal weights and `X=(−1,1)`, `A=X`,
`B=(0,2)`, `Var X=1`, `Cov(X,A)=Cov(X,B)=1`, the mean squared difference
between `X` and `B` is one, `B≠X` as functions, and the mean squared
difference between `X` and itself is zero.

## T45

For every measurable `Ω`, probability `μ`, and `X,Y∈L²(μ)` with
`Var X>0`, for every real `a,b`:
`Cov(X,a+bX)=Cov(X,Y)` if and only if `b=β`; the conjunction of that
covariance equality and `E[a+bX]=E Y` holds if and only if `b=β,a=α`.
Also, for every `a,b`, `R(α,β)≤R(a,b)` with equality exactly when
`a=α,b=β`.

## T46

For every measurable `Ω`, probability `μ`, and real functions `X,W`,
if both are measurable and they are independent, `X` has the density
`1_[0,1]` with respect to Lebesgue measure, and `W` has law `N(0,1)`,
put `Y=10X²+W`. Then `X,Y∈L²`; `x↦10x²` is a conditional mean of
`Y` given `X` in the event-integral sense above; `E X=1/2`,
`E X²=1/3`, `E X³=1/4`, `Var X=1/12`, `E Y=10/3`,
`Cov(X,Y)=5/6`, `β=10`, and `α=−5/3`.
For every real `a,b`, `R(−5/3,10)≤R(a,b)`, with equality if and only if
`a=−5/3,b=10`.

## T48

For every measurable `Ω`, probability `μ`, natural `K`, and
`X:Ω→(Fin K→ℝ)`, if each coordinate is L², then every entry of
`covarianceEntries μ X` is `Cov(X_j,X_k)`, the matrix is symmetric,
its `k,k` entry is `Var X_k` for each `k`, and
`Var(Σ_k X_k)=Σ_jΣ_k Cov(X_j,X_k)`. `K=0` is allowed, and gives the
zero-dimensional case in addition to all nonempty dimensions.

## T49

For every natural `K`, every real vector `b` on `Fin(K+1)`, and every
real vector `x` on `Fin K`, the affine function `A_b` has
`A_b(0)=b_0`. For every coordinate `k`, increasing `x_k` by one changes
`A_b` by `b_{k+1}`; `t↦A_b(x with x_k=t)` has derivative `b_{k+1}` at
`x_k`; and `coordinatePartial A_b x k=b_{k+1}`. The quantification over
coordinates is after the intercept conclusion, so the latter remains
asserted when `K=0`.

## T50

For every measurable `Ω`, the following conjunction holds:

* For every natural `N>0` and every `x:Fin N→ℝ`, for every real `t`
  the equal-weight probability of `x_i=t` is its multiplicity divided
  by `N`; the weighted mean is `Σ_i x_i/N`; and the weighted variance
  is `Σ_i(x_i-Σ_j x_j/N)²/N`.
* The range of `(3,4,3,10)` is exactly `{3,4,10}`; its equal-weight
  masses there are `1/2,1/4,1/4`, its mean is `5`, and its variance is
  `17/2`.
* For every probability `μ` on `Ω` and every L² `Z`,
  `Var Z=E[Z²]-(E Z)²` and
  `E[Z²]+(E Z)²-Var Z=2(E Z)²`.
* For every deterministic real sequence `x` and every natural `n>0`,
  the measure `ν=(1/n)Σ_{i<n}δ_{x_i}` is a probability measure,
  `Eν[id]=Σ_{i<n}x_i/n`, and
  `Varν[id]=Σ_{i<n}x_i²/n-(Σ_{i<n}x_i/n)²`.

## T51

For every measurable `Ω`, probability `μ`, real random sequence `Z`
with every `Z_n` measurable, and then every real constant `c`,
`Z_n→c` in probability if and only if: for every real `p` satisfying
`0≤p<1`, for every real `ε>0`, there exists a natural `N` such that
for every natural `n≥N`, `p≤Pμ(|Z_n-c|<ε)`.

## T52

For every measurable `Ω` and every probability `μ`, both assertions hold:
for every measurable real `X` and then every measurable real set `D`,
`Eμ[1_{X∈D}]=Pμ(X∈D)`; and, for every IID real sequence `X` and then
every fixed real `x`, the sample average of `1_{X_i≤x}` converges in
probability to `Pμ(X_0≤x)`. This is a separate assertion at each `x`,
not a simultaneous supremum assertion.

## T53

There are no hypotheses. For every natural `k`, `p_k=7(1/8)^(k+1)≥0`.
The series of `p_k` is summable and sums to one. The real series of
`2^k p_k` and `2^(2k)p_k` are both summable and have sums `7/6` and
`7/4`. The extended nonnegative sum `Σ_k ofReal(2^(4k)p_k)` is infinity.
Finally `7/4-(7/6)²=7/18>0`. No random variable, product probability
space, or sample sequence is quantified over in this statement.

## T54

For every measurable `Ω`, probability `μ`, and IID real sequence `X`,
if `X_0∈L²(μ)` and `Var X_0>0`, then for every natural `n>0`,
`Eμ[pluginVariance X n]=((n-1)/n)Var X_0`, and the sequence
`pluginVariance X n` converges in probability to `Var X_0`.
Here `n-1` is real subtraction after casting `n`, not natural truncated
subtraction. No fourth-moment assumption is imposed.

## T55

For every measurable `Ω`, probability `μ`, two real sequences of
statistics `θhat,Vhat`, and real `θ`, if each statistic is measurable
at each natural `n` and `Vhat_n(ω)≥0` for **all** `n,ω`, then for
every probability law `ν` on the reals with `id∈L²(ν)`, if
`sqrt(n)(θhat_n-θ)` converges in distribution to `ν`, the following
hold with `v=Varν[id]`:

* `n Vhat_n→v` in probability if and only if `n Vhat_n-v→0` in probability.
* `sqrt(n)sqrt(Vhat_n)→sqrt(v)` in probability if and only if the same
  quantity minus `sqrt(v)` tends to zero in probability.
* The two uncentered consistency properties in these bullets are equivalent.

The limiting law is not required to be Gaussian or to have positive variance.
The assumed convergence of `θhat` is not itself a conclusion.

## T56

For every measurable `Ω`, probability `μ`, and IID real sequence `X`,
if `X_0` has law `(δ_0+δ_1)/2`, let `F(x)=Pμ(X_0≤x)`. Then the following
conjunction holds:

* The constant functional `T≡7` on `CDFSpace` has
  `hadamardDerivative cdfSet univ T (embedCDF F) 0`.
* The constant functional `G↦7` on real functions has `cdfHadamard` at `F`.
* For every natural `n` and every `ω`, `sqrt(n)(7-7)=0`.
* For every nonnegative real `v>0`, the constant-zero sequence does **not**
  converge in distribution under `μ` to `N(0,v)`.
* The functional `Q(G)=(G(0)-1/2)²` has `cdfHadamard` at `F` and `Q(F)=0`.
* For every natural `n>0`, writing `F_{n,ω}` for the CDF of the empirical
  law, `Eμ[(sqrt(n)Q(F_n))²]=(3n-2)/(16n²)`.
* `sqrt(n)Q(F_n)` converges in probability to zero.

No particular derivative witnessing `cdfHadamard Q F` is identified, and
no IID realization is constructed by this assertion.

## T57

For every measurable `Ω`, and every measurable-space structure on
`CDFSpace` equal to its norm-topology Borel sigma-algebra, take successively:
every probability `μ`, every IID real sequence `X`, every functional
`T:CDFSpace→ℝ`, and every continuous real linear functional `L` on
`CDFSpace`. Put `F(x)=Pμ(X_0≤x)`. Assume the sequential Hadamard
derivative predicate for `T` at `embedCDF F`, on domain `cdfSet`,
tangentially to `cdfTangent F`, with derivative `L`.
Then for every Borel probability `νB` on `CDFSpace`, assume its tangent
support and all its finite-dimensional Gaussian laws as in `isCDFBridge F νB`.
Assume also that `ω↦T(empiricalCDF X n ω)` is measurable for every
natural `n`, and that `h↦L(h)` is L² under `νB`. For every supplied proof
that its variance `v` is strictly positive, the following two conclusions
hold together:

1. `sqrt(n)(empiricalCDF X n-embedCDF F)` converges in the two-sided
   bounded-continuous-test outer expectation sense to the **supplied** law `νB`.
2. `sqrt(n)(T(empiricalCDF X n)-T(embedCDF F))` converges in distribution
   to `N(0,v)`.

Neither existence of `νB` nor measurability of the full empirical CDF as a
`CDFSpace`-valued function is asserted or assumed. Positive derivative
variance, scalar plug-in measurability, L² derivative image, and the bridge
law conditions are antecedents of **both** conclusions.
