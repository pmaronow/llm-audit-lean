import SAP.P044.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P044

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

noncomputable section

def bankWeight (R c : ℕ) : ℝ := ((c : ℝ) + 1) / ((R : ℝ) + 1)

def T7Statement : Prop :=
  (let f := fun r => exposure cycle8Adj (cycle8Assignments r)
    let p := marginal (fun _ : Fin 8 => (1/8 : ℚ)) f
    let q := fun i a => (smoothedWeight f i a : ℚ)
    (∀ i, ∃ j, cycle8Adj i j = true) ∧
    Function.Injective cycle8Assignments ∧
    (∀ i a, exposureCount f i a = match a with | .d11 => 2 | .d10 => 1 | .d01 => 3 | .d00 => 2) ∧
    (∀ i a, p i a = match a with | .d11 => 1/4 | .d10 => 1/8 | .d01 => 3/8 | .d00 => 1/4) ∧
    (∀ i a, q i a = match a with | .d11 => 1/3 | .d10 => 2/9 | .d01 => 4/9 | .d00 => 1/3) ∧
    (∀ i, ∑ a, q i a = 4/3) ∧
    (∀ r a, htMean f cycle8Y q a r =
      match a with | .d11 => 3/2 | .d10 => 27/32 | .d01 => 135/128 | .d00 => 3/4) ∧
    (∀ r a, htMean f cycle8Y p a r = cycle8Y 0 a) ∧
    (∑ b, (smoothedJoint f (0 : Fin 8) (1 : Fin 8) .d11 b : ℚ)) = 17/72 ∧
    q 0 .d11 = 1/3 ∧ (17/72 : ℚ) ≠ 1/3 ∧
    expect (fun _ : Fin 8 => (1/8 : ℚ)) (htContrast f cycle8Y q .d11 .d00) = 3/4 ∧
    tau cycle8Y .d11 .d00 = 1) ∧
  ((∀ r, (Finset.univ.filter (fun i => cycle8Assignments r i)).card = 3) ∧
    (∀ r a, (Finset.univ.filter (fun i => exposure cycle8Adj (cycle8Assignments r) i = a)).card =
      match a with | .d11 => 2 | .d10 => 1 | .d01 => 3 | .d00 => 2)) ∧
  (let f := fun r => exposure cycle8Adj (cycle8Assignments r)
    let q := fun i a => (smoothedWeight f i a : ℚ)
    (∀ r a, (Finset.univ.filter (fun i => f r i = a)).card =
      match a with | .d11 => 2 | .d10 => 1 | .d01 => 3 | .d00 => 2) ∧
    (∀ r, htContrast f cycle8Y q .d11 .d00 r = 3/4 ∧
      htContrast f cycle8Y q .d10 .d00 r = 3/32 ∧
      htContrast f cycle8Y q .d01 .d00 r = 39/128 ∧
      htContrast f cycle8Y q .d11 .d00 r - tau cycle8Y .d11 .d00 = -1/4 ∧
      htContrast f cycle8Y q .d10 .d00 r - tau cycle8Y .d10 .d00 = -13/32 ∧
      htContrast f cycle8Y q .d01 .d00 r - tau cycle8Y .d01 .d00 = 7/128)) ∧
  (tau cycle8Y .d10 .d00 = 1/2 ∧ tau cycle8Y .d01 .d00 = 1/4) ∧
  (let f := fun r => exposure cycle8Adj (cycle8Assignments r)
  let p := marginal (fun _ : Fin 8 => (1/8 : ℚ)) f
  (∀ r, htContrast f cycle8Y p .d11 .d00 r = 1 ∧
    htContrast f cycle8Y p .d10 .d00 r = 1/2 ∧
    htContrast f cycle8Y p .d01 .d00 r = 1/4) ∧
  (∀ i a, 0 < p i a))

def T8Statement : Prop :=
  (∀ {R N : ℕ} {D : Type*} [Fintype D] [DecidableEq D]
      (hR : 0 < R) (_hN : 0 < N) (f : Fin R → Fin N → D)
      (y w : Fin N → D → ℝ) (a : D) (_hw : ∀ i, 0 < w i a),
    (∀ i j b, marginal (fun _ : Fin R => (1/R : ℝ)) f i a = exposureCount f i a / (R : ℝ) ∧
      joint (fun _ : Fin R => (1/R : ℝ)) f i j a b = jointCount f i j a b / (R : ℝ)) ∧
    expect (fun _ : Fin R => (1/R : ℝ)) (htMean f y w a) =
      (∑ i, y i a * marginal (fun _ : Fin R => (1/R : ℝ)) f i a / w i a) / N ∧
    ((∀ i, 0 < marginal (fun _ : Fin R => (1/R : ℝ)) f i a) →
      expect (fun _ : Fin R => (1/R : ℝ))
        (htMean f y (marginal (fun _ : Fin R => (1/R : ℝ)) f) a) = (∑ i, y i a) / N) ∧
    (expect (fun _ : Fin R => (1/R : ℝ)) (htMean f y (smoothedWeight f) a) -
      (∑ i, y i a) / N =
      (∑ i, y i a * (((exposureCount f i a : ℝ) - R) /
        ((R : ℝ) * ((exposureCount f i a : ℝ) + 1)))) / N) ∧
    (∀ i, ((exposureCount f i a : ℝ) / R) / (smoothedWeight f i a : ℝ) - 1 =
      ((exposureCount f i a : ℝ) - R) / ((R : ℝ) * ((exposureCount f i a : ℝ) + 1)) ∧
      (exposureCount f i a < R →
        ((exposureCount f i a : ℝ) - R) / ((R : ℝ) * ((exposureCount f i a : ℝ) + 1)) < 0)) ∧
    (2 ≤ Fintype.card D → ∀ i,
      (∑ b, (smoothedWeight f i b : ℝ)) = ((R : ℝ) + Fintype.card D) / ((R : ℝ) + 1) ∧
      1 < ∑ b, (smoothedWeight f i b : ℝ))) ∧
  (∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : ℕ) (p : unitInterval)
    (D : Ω → Bool) (C : Ω → ℕ)
    (hD : HasLaw D (bernoulliMeasure true false p) μ)
    (hC : HasLaw C (binomial R p) μ) (hDC : IndepFun D C μ)
    (_hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1),
    Integrable (fun ω => (if D ω then (1 : ℝ) else 0) /
      bankWeight R (C ω)) μ ∧
    (∫ ω, (if D ω then (1 : ℝ) else 0) / bankWeight R (C ω) ∂μ) =
      1 - (1 - (p : ℝ)) ^ (R + 1) ∧
    1 - (1 - (p : ℝ)) ^ (R + 1) < 1)

end
end SAP.P044
