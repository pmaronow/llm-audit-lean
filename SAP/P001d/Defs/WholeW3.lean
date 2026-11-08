import Mathlib
import SAP.P001d.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
namespace SAP.P001d

/-- Correlation in Definition 2.2.5. Its use below is guarded by positive
standard deviations for each distinct pair to which the definition is applied. -/
def wholeCorrelation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U V : Ω → ℝ) : ℝ :=
  covariance U V μ / (Real.sqrt (variance U μ) * Real.sqrt (variance V μ))

/-- The conditional law of the l independently and uniformly drawn block labels. -/
def wholeBlockLaw (l : ℕ) [NeZero l] : Measure (Fin l → Fin l) :=
  Measure.pi (fun _ : Fin l => (PMF.uniformOfFintype (Fin l)).toMeasure)

/-- Repeat the block resampling experiment independently B times. -/
def wholeBlockReplicateLaw (l B : ℕ) [NeZero l] : Measure (Fin B → Fin l → Fin l) :=
  Measure.pi (fun _ : Fin B => wholeBlockLaw l)

/-- Apply the estimator to all lm observations in the resampled intact blocks. -/
def wholeBlockEstimate {l m : ℕ} (T : (Fin l → Fin m → ℝ) → ℝ)
    (x : Fin l → Fin m → ℝ) (a : Fin l → Fin l) : ℝ :=
  T (blockResample x a)

/-- The block bootstrap standard error is the standard deviation under the
finite conditional resampling law, with the observed array held fixed. -/
def wholeBlockSE {l m : ℕ} [NeZero l] (T : (Fin l → Fin m → ℝ) → ℝ)
    (x : Fin l → Fin m → ℝ) : ℝ :=
  Real.sqrt (variance (wholeBlockEstimate T x) (wholeBlockLaw l))

/-- P001-T64; Example 3.5.8: pp. 140–141 (PDF pp. 158–159). Block bootstrap
steps: p. 141 (PDF p. 159). Theorem 3.5.5: p. 137 (PDF p. 155).
IID clusters with common finite variances and common correlations between
distinct units have the stated diagonal and off-diagonal covariances, their
explicit count expansion, the design-effect variance, and both endpoint formulas.
Correlation requires positive standard deviations only for distinct pairs;
singleton clusters may have zero variance. The corrected block bootstrap draws
l intact clusters independently and uniformly, retains lm observation slots,
applies the estimator to each resample, permits any finite number of independent
repetitions, and uses the estimator's conditional standard deviation. -/
def T64WholeStatement : Prop :=
  (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {m : ℕ}, 0 < m → ∀ X : ℕ → Ω → Fin m → ℝ,
      IID μ X → (∀ i j, MemLp (fun ω => X i ω j) 2 μ) →
      ∀ l : ℕ, 0 < l → ∀ s ρ : ℝ, ρ ∈ Set.Icc 0 1 →
      (∀ i j, variance (fun ω => X i ω j) μ = s) →
      (∀ i j k, j ≠ k →
        0 < Real.sqrt (variance (fun ω => X i ω j) μ) ∧
        0 < Real.sqrt (variance (fun ω => X i ω k) μ)) →
      (∀ i j k, j ≠ k →
        wholeCorrelation μ (fun ω => X i ω j) (fun ω => X i ω k) = ρ) →
      0 ≤ s ∧
      (∀ i j, covariance (fun ω => X i ω j) (fun ω => X i ω j) μ = s) ∧
      (∀ i j k, j ≠ k →
        covariance (fun ω => X i ω j) (fun ω => X i ω k) μ =
          wholeCorrelation μ (fun ω => X i ω j) (fun ω => X i ω k) *
            Real.sqrt (variance (fun ω => X i ω j) μ) *
            Real.sqrt (variance (fun ω => X i ω k) μ) ∧
        covariance (fun ω => X i ω j) (fun ω => X i ω k) μ = ρ * s) ∧
      (∀ i, (∑ j, ∑ k, covariance (fun ω => X i ω j) (fun ω => X i ω k) μ) =
        (m : ℝ) * s + (m : ℝ) * ((m : ℝ) - 1) * ρ * s) ∧
      (∀ i, variance (clusterMean X l) μ =
        (∑ j, ∑ k, covariance (fun ω => X i ω j) (fun ω => X i ω k) μ) /
          ((l : ℝ) * (m : ℝ)^2)) ∧
      variance (clusterMean X l) μ =
        ((m : ℝ) * s + (m : ℝ) * ((m : ℝ) - 1) * ρ * s) /
          ((l : ℝ) * (m : ℝ)^2) ∧
      variance (clusterMean X l) μ = s / ((l : ℝ) * m) * (1 + ρ * ((m : ℝ) - 1)) ∧
      (ρ = 0 → variance (clusterMean X l) μ = s / ((l : ℝ) * m) ∧
        variance (clusterMean X l) μ = s / ((l * m : ℕ) : ℝ)) ∧
      (ρ = 1 → variance (clusterMean X l) μ = s / (l : ℝ))) ∧
  (∀ {l m : ℕ} (hl : 0 < l), 0 < m → ∀ x : Fin l → Fin m → ℝ,
    letI : NeZero l := ⟨Nat.ne_of_gt hl⟩
    let ν := wholeBlockLaw l
    IsProbabilityMeasure ν ∧
    iIndepFun (fun i (a : Fin l → Fin l) => a i) ν ∧
    (∀ i j, prob ν {a | a i = j} = 1 / (l : ℝ)) ∧
    (∀ a : Fin l → Fin l, prob ν {b | b = a} = (1 / (l : ℝ))^l) ∧
    Fintype.card (Fin l × Fin m) = l * m ∧
    (∀ a i j, blockResample x a i j = x (a i) j) ∧
    (∀ (T : (Fin l → Fin m → ℝ) → ℝ) a,
      wholeBlockEstimate T x a = T (fun i j => x (a i) j)) ∧
    (∀ B : ℕ,
      IsProbabilityMeasure (wholeBlockReplicateLaw l B) ∧
      iIndepFun (fun r (a : Fin B → Fin l → Fin l) => a r)
        (wholeBlockReplicateLaw l B) ∧
      ∀ T : (Fin l → Fin m → ℝ) → ℝ,
        iIndepFun (fun r (a : Fin B → Fin l → Fin l) => wholeBlockEstimate T x (a r))
          (wholeBlockReplicateLaw l B)) ∧
    (∀ T : (Fin l → Fin m → ℝ) → ℝ,
      MemLp (wholeBlockEstimate T x) 2 ν ∧
      wholeBlockSE T x = Real.sqrt (variance (wholeBlockEstimate T x) ν)))

/-- P001-T65; Theorem 4.1.4 and the stacked system: p. 148 (PDF p. 166);
rest of the proof and Theorem 4.1.5: p. 149 (PDF p. 167); proof of 4.1.5:
p. 150 (PDF p. 168). Definitions 4.1.2–4.1.3: pp. 146–148.
For every nonempty intercept design the correctly indexed scalar residuals stack
as Y-Xb, and the squared criterion is their dot product. Normalizing by n leaves
its minimizers unchanged, and a minimizer exists. An invertible Gram matrix gives
the unique inverse-formula minimizer. Every minimizer, including those of singular
designs, satisfies the normal equations and has zero residual mean, zero empirical
residual-regressor cross moments, and zero empirical residual-regressor covariances.
These identities hold for every realized sample, hence for IID samples. -/
def T65WholeStatement : Prop :=
  ∀ {n K : ℕ}, 0 < n → ∀ (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ),
    (∀ i, X i 0 = 1) →
    (∀ (b : Fin (K+1) → ℝ) i,
      (Y - X.mulVec b) i = Y i - (b 0 + ∑ k : Fin K, b k.succ * X i k.succ)) ∧
    (∀ b, olsRSS X Y b = dotProduct (Y - X.mulVec b) (Y - X.mulVec b)) ∧
    (∀ b, (∀ c, olsRSS X Y b / (n : ℝ) ≤ olsRSS X Y c / (n : ℝ)) ↔
      (∀ c, olsRSS X Y b ≤ olsRSS X Y c)) ∧
    (∃ b, ∀ c, olsRSS X Y b ≤ olsRSS X Y c) ∧
    (IsUnit (X.transpose * X).det →
      (∀ b, olsRSS X Y (olsCoef X Y) ≤ olsRSS X Y b ∧
        (olsRSS X Y b = olsRSS X Y (olsCoef X Y) ↔ b = olsCoef X Y)) ∧
      (X.transpose * X).mulVec (olsCoef X Y) = X.transpose.mulVec Y) ∧
    (∀ b, (∀ c, olsRSS X Y b ≤ olsRSS X Y c) →
      let e := Y - X.mulVec b
      X.transpose.mulVec e = 0 ∧
      (X.transpose * X).mulVec b = X.transpose.mulVec Y ∧
      (∑ i, e i) / (n : ℝ) = 0 ∧
      (∀ k, (∑ i, e i * X i k) / (n : ℝ) = 0) ∧
      (∀ k, (∑ i, e i * X i k) / (n : ℝ) -
        ((∑ i, e i) / (n : ℝ)) * ((∑ i, X i k) / (n : ℝ)) = 0))

end SAP.P001d
