import Mathlib
import SAP.P011b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-- The two covariates in the four-vertex regression examples (zero-based positions). -/
def w1StarX (upper : Bool) : Fin 4 → ℝ :=
  if upper then ![0, 1, -1, 0] else ![3, -1, -1, -1]

/-- The correctly specified intercept and slope in the two examples. -/
def w1StarB (upper : Bool) : Fin 2 → ℝ :=
  if upper then ![1/2, 1/4] else ![3/8, 1/8]

/-- The repeated intercept/covariate design. Only positive block counts are used. -/
def w1StarD (upper : Bool) (K : ℕ) : Matrix (Fin (4*K)) (Fin 2) ℝ :=
  fun i j => if j = 0 then 1 else w1StarX upper (localIndex (by decide) i)

/-- The block mean vectors, in centre/leaf order. -/
def w1StarMu (upper : Bool) : Fin 4 → ℝ :=
  if upper then ![1/2, 3/4, 1/4, 1/2] else ![3/4, 1/4, 1/4, 1/4]

/-- The mean offsets from the target intercept. -/
def w1StarOffset (upper : Bool) : Fin 4 → ℝ :=
  if upper then ![0, 1/4, -1/4, 0] else ![3/8, -1/8, -1/8, -1/8]

/-- Explicit full-rank Gram matrices and intercept weights for both star designs. -/
def W1StarDesignFacts : Prop :=
  ∀ (upper : Bool) (K : ℕ), 0 < K →
    (∑ i : Fin (4*K), w1StarX upper (localIndex (by decide) i)) = 0 ∧
    (w1StarD upper K)ᵀ * w1StarD upper K =
      Matrix.diagonal (![4*(K : ℝ), if upper then 2*(K : ℝ) else 12*(K : ℝ)]) ∧
    ((w1StarD upper K)ᵀ * w1StarD upper K).det ≠ 0 ∧
    (∀ i, olsTheta (w1StarD upper K) 0 i = (starModel upper K).theta i) ∧
    (∀ y, betaHat (starModel upper K) y = ols (w1StarD upper K) y 0)

/-- The index of position r of block b; the block type itself excludes K=0 here. -/
def w1StarAt (K : ℕ) (b : Fin K) (r : Fin 4) : Fin (4*K) :=
  ⟨4*b.val + r.val, by omega⟩

/-- The observed four-vector in one block. -/
def w1StarExtract (K : ℕ) (b : Fin K) (y : Fin (4*K) → ℝ) : Fin 4 → ℝ :=
  fun r => y (w1StarAt K b r)

/-- A leaf pattern is specified by its actual binary values, not its latent draws. -/
def w1LeafEvent (s : Fin 3 → Bool) : Set (Fin 4 → ℝ) :=
  {y | ∀ j, y j.succ = if s j then 1 else 0}

/-- The conditional probability of the centre, as a function of the three leaves. -/
def w1CenterProb (upper : Bool) (l : Fin 3 → ℝ) : ℝ :=
  (if upper then 1/2 else 3/4) +
    (∑ j, (l j - (if upper then (![3/4, 1/4, 1/2] : Fin 3 → ℝ) j else 1/4)))/12

/-- Actual one-block leaf independence, marginal probabilities, and conditional
Bernoulli centre probabilities, with a positive conditioning-event denominator. -/
def W1StarBlockLaw : Prop :=
  ∀ upper : Bool,
    iIndepFun (fun j : Fin 3 => fun y : Fin 4 → ℝ => y j.succ)
      (starModel upper 1).law ∧
    (∀ j : Fin 3, probability (starModel upper 1) {y | y j.succ = 1} =
      if upper then (![3/4, 1/4, 1/2] : Fin 3 → ℝ) j else 1/4) ∧
    (∀ s : Fin 3 → Bool,
      0 < probability (starModel upper 1) (w1LeafEvent s) ∧
      probability (starModel upper 1) ({y | y 0 = 1} ∩ w1LeafEvent s) /
        probability (starModel upper 1) (w1LeafEvent s) =
          w1CenterProb upper (fun j => if s j then 1 else 0) ∧
      (if upper then (3/8 : ℝ) else 11/16) ≤
        w1CenterProb upper (fun j => if s j then 1 else 0) ∧
      w1CenterProb upper (fun j => if s j then 1 else 0) ≤
        (if upper then (5/8 : ℝ) else 15/16))

/-- Blocks are independent and each has exactly the displayed one-block law. -/
def W1StarIID : Prop :=
  ∀ (upper : Bool) (K : ℕ), 0 < K →
    iIndepFun (fun b : Fin K => w1StarExtract K b) (starModel upper K).law ∧
    ∀ b : Fin K, (starModel upper K).law.map (w1StarExtract K b) =
      (starModel upper 1).law

/-- Coverage restricted to the domain where the printed real interval exists. -/
def w1DomainCoverage {n : ℕ} (m : Model n) (V : (Fin n → ℝ) → ℝ) (α : ℝ) : ℝ :=
  probability m {y | 0 ≤ V y ∧
    |betaHat m y - beta m| ≤ normalQuantile α * Real.sqrt (V y)}

/-- The negative-estimate event vanishes, and the printed-domain coverage has
exactly the same limit as coverage with the standing clipped-square-root convention. -/
def W1StarCoverageDomain : Prop :=
  Tendsto (fun k => probability ((starFamily false).model k)
    {y | V1 ((starFamily false).model k).G (weighted ((starFamily false).model k) y) < 0})
    atTop (𝓝 0) ∧
  ∀ α : ℝ, 0 < α → α < 1 →
    Tendsto (fun k => w1DomainCoverage ((starFamily false).model k)
      (fun y => V1 ((starFamily false).model k).G
        (weighted ((starFamily false).model k) y)) α)
      atTop (𝓝 (2*Phi (normalQuantile α * Real.sqrt (8/9)) - 1))

/-- Saturation identifies every selected maximum with the oracle, at every sample;
the two maximal estimators therefore have the two asserted probability limits. -/
def W1StarMaximumLimits : Prop :=
  ∀ (upper : Bool)
    (A : ∀ k, (Fin ((starFamily upper).size k) → ℝ) → Graph ((starFamily upper).size k)),
    (∀ k y, Maximizes ((starFamily upper).model k).R ((starFamily upper).model k).d
      (fun B => V1 B (weighted ((starFamily upper).model k) y)) (A k y)) →
    (∀ k y, A k y = ((starFamily upper).model k).G) ∧
    InProbability (starFamily upper)
      (fun k y => ((starFamily upper).size k : ℝ)*
        V1 (A k y) (weighted ((starFamily upper).model k) y))
      (fun _ => if upper then 53/192 else 3/16)

/-- P011-T15; package README line 3 and vignette lines 100–105; Section 2,
pp. 2240–2241; Corollary 1, p. 2245.
The two correctly specified binary star regressions satisfy the standing assumptions,
full-rank design identities, independent Bernoulli leaf and conditional centre laws,
and saturated binary and fractional constraints. Their raw maximal variance estimates
converge below and above the true variance, respectively. The first has ratio 8/9,
underestimation probability tending to one, and the stated strict undercoverage for
both the clipped and printed-domain intervals; negative estimates vanish in probability.
The explicit mean offsets have the stated negative and positive quadratics, while
true-error products converge to the true variance in both models. -/
def T15WholeStatement : Prop :=
  T15Statement ∧ W1StarDesignFacts ∧ W1StarBlockLaw ∧ W1StarIID ∧
  (∀ (upper : Bool) (K : ℕ), 0 < K →
    (∀ i, expectation (starModel upper K) (fun y => y i) =
      w1StarMu upper (localIndex (by decide) i)) ∧
    (∀ i, delta (starModel upper K) i = w1StarOffset upper (localIndex (by decide) i))) ∧
  W1StarCoverageDomain ∧ W1StarMaximumLimits

/-- The lower star model with no recruitment edges forced. Its law, true graph,
weights and degree caps are unchanged. -/
def w1UnforcedModel (K : ℕ) : Model (4*K) :=
  { starModel false K with R := emptyGraph (4*K) }

/-- Positive sizes n=4(k+1), with nested true graphs and empty recruitment graphs. -/
def w1UnforcedFamily : Family where
  size := fun k => 4*(k+1)
  positive := by intro k; omega
  grows := (starFamily false).grows
  model := fun k => w1UnforcedModel (k+1)

/-- The necessity assertion about a raw compatible maximum in T16(i).
Correctly specified, full-rank two-column OLS models already suffice to test it. -/
def W1RawMaximumNecessity : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 → Valid F →
    ∀ (D : ∀ k, Matrix (Fin (F.size k)) (Fin 2) ℝ) (b : Fin 2 → ℝ),
      (∀ k, ((D k)ᵀ * D k).det ≠ 0) →
      (∀ k, MeanModel (F.model k) (D k) b) →
      (∀ k i, (F.model k).theta i = olsTheta (D k) 0 i) →
      (∀ A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k),
        (∀ k y, Maximizes (F.model k).R (F.model k).d
          (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
        Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y))) →
      0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop

/-- P011-T16; Section 2, pp. 2240–2241; (3.1), p. 2242; package vignette
lines 100–105.
The printed claim is false: conservativeness of a raw compatible maximum does not
require nonnegative limiting oracle mean bias. In the lower binary star regression,
leave recruitment empty and retain the true stars and degree caps. The full-rank,
correctly specified intercept model satisfies Assumption 2 with (1,3,27/128,2).
Its oracle mean bias is constantly -3/128, but the feasible empty graph has scaled
estimate equal to the sample variance, converging to 15/64 > 27/128. Maximizers exist
and every maximizing selection is conservative. Thus the claimed necessity fails. -/
def T16WholeStatement : Prop :=
  Scaling w1UnforcedFamily 1 3 (27/128) 2 ∧ Valid w1UnforcedFamily ∧
  (∀ k,
    MeanModel (w1UnforcedFamily.model k) (w1StarD false (k+1)) (w1StarB false) ∧
    ((w1StarD false (k+1))ᵀ * w1StarD false (k+1)).det ≠ 0 ∧
    (∀ i, (w1UnforcedFamily.model k).theta i = olsTheta (w1StarD false (k+1)) 0 i) ∧
    (∀ y, betaHat (w1UnforcedFamily.model k) y = ols (w1StarD false (k+1)) y 0) ∧
    beta (w1UnforcedFamily.model k) = 3/8 ∧
    scaledTrue w1UnforcedFamily k = 27/128 ∧
    meanBias (w1UnforcedFamily.model k) = -3/128 ∧
    meanVariance (w1UnforcedFamily.model k) = 3/16 ∧
    meanSpread (w1UnforcedFamily.model k) = 3/64 ∧
    Compatible (w1UnforcedFamily.model k).R (w1UnforcedFamily.model k).d
      (emptyGraph (w1UnforcedFamily.size k)) ∧
    (∀ y, (w1UnforcedFamily.size k : ℝ) *
      V1 (emptyGraph (w1UnforcedFamily.size k)) (weighted (w1UnforcedFamily.model k) y) =
        sampleVariance (weighted (w1UnforcedFamily.model k) y))) ∧
  InProbability w1UnforcedFamily
    (fun k y => sampleVariance (weighted (w1UnforcedFamily.model k) y)) (fun _ => 15/64) ∧
  (∃ A : ∀ k, (Fin (w1UnforcedFamily.size k) → ℝ) → Graph (w1UnforcedFamily.size k),
    ∀ k y, Maximizes (w1UnforcedFamily.model k).R (w1UnforcedFamily.model k).d
      (fun B => V1 B (weighted (w1UnforcedFamily.model k) y)) (A k y)) ∧
  (∀ A : ∀ k, (Fin (w1UnforcedFamily.size k) → ℝ) → Graph (w1UnforcedFamily.size k),
    (∀ k y, Maximizes (w1UnforcedFamily.model k).R (w1UnforcedFamily.model k).d
      (fun B => V1 B (weighted (w1UnforcedFamily.model k) y)) (A k y)) →
    Conservative w1UnforcedFamily
      (fun k y => V1 (A k y) (weighted (w1UnforcedFamily.model k) y))) ∧
  Filter.liminf (fun k => meanBias (w1UnforcedFamily.model k)) atTop = -3/128 ∧
  ¬ W1RawMaximumNecessity

/-- The correlation factor in the auxiliary homoskedastic estimator. -/
def w1CorrelationFactor {n : ℕ} (m : Model n) : ℝ :=
  1 + (∑ i, ∑ j, adjacency m.G i j * rho m i j)/(n : ℝ)

/-- Explicit independent-sign family used to show that a sign correction alone
cannot remove the between-unit mean spread. The ceil denominator is only used at n>0. -/
def w1AlternatingWeight (n : ℕ) : ℝ :=
  (n : ℝ) / (2 * (((n+1)/2 : ℕ) : ℝ))

def w1AlternatingModel (n : ℕ) : Model n where
  law := uniformLaw (fun u : Fin n → Bool => fun i =>
    (if i.val % 2 = 0 then 2 else 0) + sign (u i))
  probability := by dsimp [uniformLaw]; infer_instance
  theta := fun _ => w1AlternatingWeight n
  G := emptyGraph n
  R := emptyGraph n
  d := fun _ => 0

def w1AlternatingFamily : Family where
  size := fun k => k+1
  positive := by intro k; omega
  grows := signFamily.grows
  model := fun k => w1AlternatingModel (k+1)

/-- P011-T19; proof of Proposition 2, p. 2246.
For positive common variance under Assumptions 2 and 3, the auxiliary error is
k times the sample-variance error, where k is the true scaled variance divided by
the common variance and lies between zero and 1+c2. The sample-variance remainder
after subtracting between-unit mean spread converges to zero in probability.
Vanishing mean spread, in particular equal weighted unit means, suffices for auxiliary
consistency. The explicit alternating-mean independent-sign family satisfies all these
standing assumptions with positive common variance, yet its mean spread tends to one
and its auxiliary error exceeds 1/2 with probability tending to one. -/
def T19WholeStatement : Prop :=
  (∀ (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
      (hs : ∀ k, Homoskedastic (F.model k)) (hpos : ∀ k, 0 < meanVariance (F.model k)),
    T19Statement F c1 c2 c3 c4 h hs hpos ∧
    (∀ k, w1CorrelationFactor (F.model k) = scaledTrue F k / meanVariance (F.model k) ∧
      0 ≤ w1CorrelationFactor (F.model k) ∧ w1CorrelationFactor (F.model k) ≤ 1+c2) ∧
    ((∀ k i, expectation (F.model k) (fun y => weighted (F.model k) y i) =
        beta (F.model k)) →
      InProbability F (fun k y => (F.size k : ℝ)*V2star (F.model k) y) (scaledTrue F))) ∧
  Scaling w1AlternatingFamily 2 1 1 2 ∧ Valid w1AlternatingFamily ∧
  (∀ k, Homoskedastic (w1AlternatingFamily.model k) ∧
    0 < meanVariance (w1AlternatingFamily.model k) ∧
    meanVariance (w1AlternatingFamily.model k) = w1AlternatingWeight (k+1)^2 ∧
    beta (w1AlternatingFamily.model k) = 1) ∧
  Tendsto (fun k => meanSpread (w1AlternatingFamily.model k)) atTop (𝓝 1) ∧
  Tendsto (fun k => probability (w1AlternatingFamily.model k)
    {y | |(w1AlternatingFamily.size k : ℝ)*V2star (w1AlternatingFamily.model k) y -
      scaledTrue w1AlternatingFamily k| > 1/2}) atTop (𝓝 1)

end
end SAP.P011b
