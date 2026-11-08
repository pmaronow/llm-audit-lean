# Blind reading

This file was written before opening `claims.json` or `record.json`.

## SAP.P017.T16 (P017-T16)

Source: `SAP/P017/Challenge/Part1.lean:137–140`; statement definition:
`SAP/P017/Defs/Part6.lean:127–137`. Fingerprint:
`afb06b9c0f6812e9e187a07eb135ccc766654208bb0fda4ba842576db845de0d`.

### Fully unfolded mathematical statement

The quantifiers, in order, are:

1. Arbitrary types Ω and Ξ (independent universes), each equipped with a measurable space.
2. A probability measure G on Ω and a function τ : Ω → ℝ.
3. Hypotheses that τ is measurable and Bochner integrable with respect to G.
4. A probability measure P on Ξ and a sequence of real functions
   h : ℕ → Ξ → ℝ.
5. The hypothesis that there is a finite nonnegative real variance v, strictly
   positive, such that the random variables √n(hₙ − μ) converge in distribution
   under P to the identity random variable under N(0,v), where μ = ∫ τ dG.
   Mathlib's convergence in distribution includes P-almost-everywhere
   measurability of √n(hₙ − μ) for every n and almost-everywhere measurability of
   the limiting identity. It asserts weak convergence of their probability laws,
   equivalently convergence of integrals of every bounded continuous real test
   function. There is no Gaussian decomposition or moment rate hypothesis.

Define S to be the closed topological support of the pushforward G.map τ:
x ∈ S means every neighborhood U of x in ℝ has (G.map τ)(U) > 0.
Thus for measurable B, (G.map τ)(B) = G(τ⁻¹(B)). Define extended real endpoints
a = inf { (x : EReal) : x ∈ S } and b = sup { (x : EReal) : x ∈ S }.
Set c = [min(b − μ, μ − a)]₊ in [0,∞], where conversion from EReal preserves
+∞ and finite nonnegative values and sends negative values, including −∞, to
zero. Under the hypotheses μ lies between the extended support endpoints, so
this conversion does not change the intended nonnegative radius.

For x ∈ ℝ define C(x) = x if c = +∞. Otherwise, with r the finite real value
of c, define C(x) = min(μ+r, max(μ−r,x)).

The conclusion is the conjunction of:

* For every ε > 0 there exists a real M > 0 such that, for all sufficiently
  large n ∈ ℕ,
  P({ω ∈ Ξ : |√n(C(hₙ(ω)) − μ)| > M}) < ε.
  Here real-valued probability is precisely `(P A).toReal`.
* For every n ∈ ℕ and every ω ∈ Ξ (pointwise, not just almost surely),
  |C(hₙ(ω)) − μ| ≤ |hₙ(ω) − μ|.

The witness v can depend on all the preceding data. The bound M can depend on
ε and those data; the eventual starting index can depend on M and ε. There is
no positive-radius hypothesis. There is no relation required between G and P,
nor an IID sampling or empirical-statistic requirement on h. Only the indicated
asymptotic distribution connects h to the population mean. The conclusion is
boundedness in probability, not asymptotic normality of the clipped target.

### Closure read

Every unit declaration listed in `closure.json` was read:

* `populationMean`, `effectSupport`, `supportInf`, `supportSup`, `effectRadius`,
  `clipReal`, `clipTarget`, `pr`, `sqrtN`, `BoundedInProbability`, and
  `RootNNormal`, in `SAP/P017/Defs/Part1.lean` at lines 17, 20, 23, 25, 27,
  31, 33, 53, 55, 61, and 70 respectively.
* `T16Statement`, in `SAP/P017/Defs/Part6.lean:128`.
* `RootNNormal._proof_1` and `RootNNormal._proof_2`, inspected with `#print`.
  The first supplies the Borel opens-measurability instance for ℝ. The second
  supplies that `gaussianReal 0 v` is a probability measure for every v. They
  add no mathematical assumption or different definition.

Mathlib's definitions of measure support, real-valued measure, extended-real
conversion, Gaussian law, and convergence in distribution were also inspected.
For v > 0, `gaussianReal 0 v` is Lebesgue measure with the usual Gaussian
density (mean zero, variance v); the zero-variance Dirac branch is excluded by
the strict positivity hypothesis on v.

### Totalization and edge cases

* The Bochner integral defining μ is a total function and would return zero
  for a nonintegrable integrand. `Integrable τ G` expressly excludes that case.
  No expectation or variance of h is taken, so no missing estimator moment
  assumption is being bypassed by an integral convention.
* A pushforward of a non-AE-measurable function can be the zero measure in
  Mathlib. The measurable τ hypothesis prevents this. S is a nonempty closed
  support of a probability law on ℝ and carries that law almost surely.
* The infimum and supremum are taken in EReal, a complete lattice. Thus
  inf ∅ = +∞ and sup ∅ = −∞, while genuinely unbounded supports have the
  appropriate infinite endpoints. The empty case cannot occur here. No
  conditional-completeness default for infima or suprema in ℝ is used.
* Extended-real subtraction has totalized infinity cases. Every subtraction
  here has the finite μ as one operand, so neither +∞−+∞ nor −∞−−∞ occurs.
  An upper endpoint +∞ contributes +∞ to b−μ; a lower endpoint −∞ contributes
  +∞ to μ−a. The integral mean lies between the endpoints. The EReal-to-ENNReal
  conversion discards negative values in general; that truncation has no effect
  for these data.
* ENNReal.toReal sends +∞ to zero. `clipTarget` tests c = +∞ first and returns
  x in that case, so it does not accidentally turn an infinite interval into
  the point μ. For finite c it is the genuine nonnegative radius. If c=0,
  C(x)=μ; the scaled clipped error and pointwise left side are zero.
* `clipReal` is total even for a negative real radius (its interval endpoints
  would be reversed). Only a nonnegative real radius from ENNReal is supplied
  here, so that behavior is irrelevant.
* Real-valued probability sends an infinite measure value to zero via toReal.
  P is a probability measure, so every set has finite measure and this never
  changes its value. Measures are total on all sets. The distribution hypothesis
  supplies AE measurability of the scaled estimator; at n>0 it consequently
  supplies AE measurability of hₙ and of the relevant clipped-error events. At
  n=0 the scaled error is identically zero even if h₀ itself is not measurable.
* The cast ℕ → ℝ is exact and nonnegative. `Real.sqrt` returns zero on negative
  reals, but its argument here is always nonnegative. √0=0 is harmless, and
  √n>0 when n≥1. The pointwise inequality includes n=0; the probability bound
  is eventual as n tends to infinity.
* Both base spaces must be nonempty because each carries a probability
  measure. The index ℕ is nonempty and atTop is a proper filter. There is no
  empty-index or degenerate-filter escape.
* No division by zero, logarithm, real power, truncated natural subtraction,
  limsup/liminf, chosen partial inverse, or conditional-law default occurs in
  the unit definitions used here. The Gaussian density's division and square
  root have positive variance. All measures here are finite, hence σ-finite;
  no conditional distributions require an additional standard Borel assumption.

### Initial assessment, without the canonical claim

The definitions express ordinary clipping to the largest symmetric closed
interval about the integrable population mean lying within the support bounds,
with an identity map for infinite radius. The two conclusions are compatible:
clipping cannot increase absolute error about its center, and a contraction
of a sequence bounded in probability is bounded in probability. Nothing in
the hypotheses visibly assumes either conclusion. The docstring describes
the displayed conclusion and expressly includes the zero and infinite cases.
Comparison with the intended claim remains for the next stage.
