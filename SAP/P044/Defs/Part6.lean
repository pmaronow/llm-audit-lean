import SAP.P044.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P044

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

noncomputable section

def T5Statement : Prop :=
  ((∀ i : Fin 3, degree (fun i j => decide (i ≠ j)) i = 2 ∧
      twoWalkDegree (fun i j => decide (i ≠ j)) i = 2 ∧
      degreeScale (fun i j => decide (i ≠ j)) i = 8) ∧
    (∀ i : Fin 3, baseline 8 (![1/64,1,-1/2] i) (![-3/4,1,5/4] i) = ![-5/8,9,21/4] i) ∧
    baseline 8 (1/64) (-3/4) < 0) ∧
  (∀ i j : Fin 3, (∑ k : Fin 3,
      (if i ≠ k then (1 : ℕ) else 0) * (if k ≠ j then 1 else 0)) =
        if i = j then 2 else 1) ∧
  ((∀ i j : Fin 3, (∑ k : Fin 3, if (i ≠ k ∧ k ≠ j) then (1 : ℕ) else 0) =
      if i = j then 2 else 1) ∧
    (let B : Fin 3 → ℝ := ![-5/8,9,21/4]
     (∀ i, dilatedOutcomes B i .d11 = ![-5/4,18,21/2] i) ∧
     (∀ i, dilatedOutcomes B i .d10 = ![-15/16,27/2,63/8] i) ∧
     (∀ i, dilatedOutcomes B i .d01 = ![-25/32,45/4,105/16] i) ∧
     (∀ i, dilatedOutcomes B i .d00 = ![-5/8,9,21/4] i))) ∧
  (∀ (a : ℝ) (ha : 0 ≤ a),
    0 < normalPair {x : ℝ × ℝ | |x.1| < 1 / (4 * (a + 1)) ∧ -1 < x.2 ∧ x.2 < -1/2} ∧
    (∀ x : ℝ × ℝ, |x.1| < 1 / (4 * (a + 1)) ∧ -1 < x.2 ∧ x.2 < -1/2 →
      baseline a x.1 x.2 < -1/4)) ∧
  (∀ (a : ℝ) (ha : 0 ≤ a),
    0 < baselineLaw a (Set.Iio 0) ∧ halfNormalLaw (Set.Iio 0) = 0 ∧
      baselineLaw a ≠ halfNormalLaw) ∧
  (normalPair.real (Set.Ioo (-1/32 : ℝ) (1/32) ×ˢ Set.Ioo (-1 : ℝ) (-1/2)) =
      (standardNormalCDF (1/32) - standardNormalCDF (-1/32)) *
        (standardNormalCDF (-6) - standardNormalCDF (-8)) ∧
    0 < (standardNormalCDF (1/32) - standardNormalCDF (-1/32)) *
        (standardNormalCDF (-6) - standardNormalCDF (-8))) ∧
  (∀ (g e : ℝ)
    (hg : g ∈ Set.Ioo (-1/32 : ℝ) (1/32))
    (he : e ∈ Set.Ioo (-1 : ℝ) (-1/2)),
    baseline 8 g e < -1/4) ∧
  ((∫ g : ℝ, |g| ∂gaussianReal 0 1) = Real.sqrt (2 / Real.pi)) ∧
  (ProbabilityTheory.variance (fun g : ℝ => |g|) (gaussianReal 0 1) = 1 - 2 / Real.pi) ∧
  ((∫ g : ℝ, |g| ^ 2 ∂gaussianReal 0 1) = 1) ∧
  (∀ (a : ℝ) (ha : 0 ≤ a),
    (∫ x, baseline a x.1 x.2 ∂normalPair) = a * Real.sqrt (2 / Real.pi) + 1 ∧
    ProbabilityTheory.variance (fun x : ℝ × ℝ => baseline a x.1 x.2) normalPair =
      a ^ 2 * (1 - 2 / Real.pi) + 1/16) ∧
  ((∫ x, baseline 8 x.1 x.2 ∂normalPair) = 8 * Real.sqrt (2 / Real.pi) + 1 ∧
    variance (fun x : ℝ × ℝ => baseline 8 x.1 x.2) normalPair = 64 * (1 - 2 / Real.pi) + 1/16 ∧
    (∫ x, baseline 8 x.1 x.2 ∂normalPair) - (∫ g : ℝ, |g| ∂gaussianReal 0 1) =
      7 * Real.sqrt (2 / Real.pi) + 1 ∧
    variance (fun x : ℝ × ℝ => baseline 8 x.1 x.2) normalPair -
      variance (fun g : ℝ => |g|) (gaussianReal 0 1) = 63 * (1 - 2 / Real.pi) + 1/16 ∧
    0 < 7 * Real.sqrt (2 / Real.pi) + 1 ∧ 0 < 63 * (1 - 2 / Real.pi) + 1/16) ∧
  (∀ {N : ℕ} (A : Adjacency N)
    (hiso : ∀ i, 1 ≤ degree A i) (i : Fin N),
    1 ≤ (∫ x, baseline (degreeScale A i) x.1 x.2 ∂normalPair) -
      (∫ g : ℝ, |g| ∂gaussianReal 0 1)) ∧
  (∀ a : ℝ, MemLp (fun x : ℝ × ℝ => baseline a x.1 x.2) 2 normalPair) ∧
  (MemLp (fun g : ℝ => |g|) 2 (gaussianReal 0 1)) ∧
  (∀ (a : ℝ) (_ha : 1 ≤ a),
    (∫ x, baseline a x.1 x.2 ∂normalPair) - (∫ g : ℝ, |g| ∂gaussianReal 0 1) =
      (a - 1) * Real.sqrt (2 / Real.pi) + 1)

def T6Statement : Prop :=
  (∀ {N : ℕ} (B : Fin N → ℝ) (i : Fin N),
    dilatedOutcomes B i .d00 = B i ∧ dilatedOutcomes B i .d11 = 2 * B i ∧
    dilatedOutcomes B i .d10 = (3/2) * B i ∧ dilatedOutcomes B i .d01 = (5/4) * B i) ∧
  (∀ (a : ℝ) (ha : 0 ≤ a),
    (∫ x, baseline a x.1 x.2 ∂normalPair) = a * Real.sqrt (2 / Real.pi) + 1 ∧
    ProbabilityTheory.variance (fun x : ℝ × ℝ => baseline a x.1 x.2) normalPair =
      a ^ 2 * (1 - 2 / Real.pi) + 1/16) ∧
  ((∫ g : ℝ, |g| ∂gaussianReal 0 1) = Real.sqrt (2 / Real.pi)) ∧
  ((∫ g : ℝ, |g| ^ 2 ∂gaussianReal 0 1) = 1) ∧
  (∀ (a : ℝ),
    MemLp (fun x : ℝ × ℝ => baseline a x.1 x.2) 2 normalPair) ∧
  (∀ {N : ℕ} (_hN : 0 < N) (B : Fin N → ℝ),
    tau (dilatedOutcomes B) .d11 .d00 = (∑ i, B i) / N ∧
    tau (dilatedOutcomes B) .d10 .d00 = (1/2 : ℝ) * ((∑ i, B i) / N) ∧
    tau (dilatedOutcomes B) .d01 .d00 = (1/4 : ℝ) * ((∑ i, B i) / N)) ∧
  (let B : Fin 3 → ℝ := ![-5/8,9,21/4];
    tau (dilatedOutcomes B) .d11 .d00 = 109/24 ∧
    tau (dilatedOutcomes B) .d10 .d00 = 109/48 ∧
    tau (dilatedOutcomes B) .d01 .d00 = 109/96) ∧
  ((∑ i : Fin 3, (![-5/8,9,21/4] : Fin 3 → ℝ) i) / 3 = 109/24) ∧
  (∀ {N : ℕ} (hN : 0 < N) (A : Adjacency N)
    (hdiag : ∀ i, A i i = false),
    (∫ x, tau (dilatedOutcomes (generatedBaselines A x)) .d11 .d00 ∂normalPopulation N) =
      1 + Real.sqrt (2 / Real.pi) * ((∑ i, (degreeScale A i : ℝ)) / N)) ∧
  (∀ {N : ℕ} (hN : 0 < N) (A : Adjacency N)
    (hdiag : ∀ i, A i i = false) (hiso : ∀ i, 1 ≤ degree A i),
    (∫ x, tau (dilatedOutcomes (generatedBaselines A x)) .d11 .d00 ∂normalPopulation N) =
      1 + Real.sqrt (2 / Real.pi) * ((∑ i, (degreeScale A i : ℝ)) / N) ∧
    1 + Real.sqrt (2 / Real.pi) ≤
      (∫ x, tau (dilatedOutcomes (generatedBaselines A x)) .d11 .d00 ∂normalPopulation N) ∧
    Real.sqrt (2 / Real.pi) < 1) ∧
  (∀ {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Fin N → ℝ) (hLaw : ∀ i, HasLaw (fun ω => B ω i) halfNormalLaw P),
    (∫ ω, tau (dilatedOutcomes (B ω)) .d11 .d00 ∂P) = Real.sqrt (2 / Real.pi) ∧
    Real.sqrt (2 / Real.pi) < 1) ∧
  (∀ {N : ℕ} (_hN : 0 < N) (A : Adjacency N),
    Integrable (fun x => tau (dilatedOutcomes (generatedBaselines A x)) .d11 .d00)
      (normalPopulation N)) ∧
  (∀ {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (_hN : 0 < N)
      (P : Measure Ω) [IsProbabilityMeasure P] (B : Ω → Fin N → ℝ)
      (_hLaw : ∀ i, HasLaw (fun ω => B ω i) halfNormalLaw P),
    Integrable (fun ω => tau (dilatedOutcomes (B ω)) .d11 .d00) P)

end
end SAP.P044
