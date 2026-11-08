import SAP.P017.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u1 u2 u3 u4 u5

namespace SAP.P017

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/-- Mathematical statement for P017-T8.
The usual measure-theoretic conditions are assumed. -/
def T8Statement : Prop :=
    (∀ {Ξ : Type u1} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ)
    (μ c : ℝ) (v : ℝ≥0) (hc : 0 < c) (hv : 0 < v)
    (hhm : ∀ n, Measurable (hat n)) (hr : NormalRemainder P hat Z ε μ v)
    (n : ℕ) (hn : 1 ≤ n),
    let tilde := fun ω => μ + Z n ω / sqrtN n
    (∀ x y, |clipReal μ c x - clipReal μ c y| ≤ |x - y| ∧
      |residual μ c x - residual μ c y| ≤ |x - y|) ∧
    (∀ᵐ ω ∂P, |residual μ c (hat n ω)| ≤ |residual μ c (tilde ω)| + |ε n ω| / sqrtN n) ∧
    ((∫ ω, residual μ c (hat n ω) ^ 2 ∂P) ≤
      2 * (∫ ω, residual μ c (tilde ω) ^ 2 ∂P) + 2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) ∧
    (∀ x, residual μ c x ^ 2 = max (|x - μ| - c) 0 ^ 2 ∧
      residual μ c x ^ 2 ≤ (if |x - μ| > c then (x - μ) ^ 2 else 0) ∧
      (if |x - μ| > c then (x - μ) ^ 2 else 0) ≤ (x - μ) ^ 4 / c ^ 2) ∧
    ((∫ ω, (tilde ω - μ) ^ 4 ∂P) = 3 * (v : ℝ) ^ 2 / (n : ℝ) ^ 2) ∧
    ((∫ ω, residual μ c (hat n ω) ^ 2 ∂P) ≤
      6 * (v : ℝ) ^ 2 / (c ^ 2 * (n : ℝ) ^ 2) + 2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) ∧
    (∀ᵐ ω ∂P, |tilde ω - clipReal μ c (hat n ω)| ≤
      |residual μ c (tilde ω)| + |ε n ω| / sqrtN n) ∧
    ((∫ ω, (tilde ω - clipReal μ c (hat n ω)) ^ 2 ∂P) ≤
      6 * (v : ℝ) ^ 2 / (c ^ 2 * (n : ℝ) ^ 2) + 2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) ∧
    ((∫ ω, residual μ c (tilde ω) ^ 2 ∂P) ≤
      (∫ ω, if |tilde ω - μ| > c then (tilde ω - μ) ^ 2 else 0 ∂P)) ∧
    ((∫ ω, if |tilde ω - μ| > c then (tilde ω - μ) ^ 2 else 0 ∂P) = normalTail n c (Real.sqrt v))) ∧
    (∀ {Ξ : Type u2} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ)
    (μ c : ℝ) (v : ℝ≥0) (hc : 0 < c) (hv : 0 < v)
    (hhm : ∀ n, Measurable (hat n)) (hr : NormalRemainder P hat Z ε μ v)
    (he : SmallRemainderMS P ε),
    SmallMSE P (fun n ω => residual μ c (hat n ω)) ∧
    SmallMSE P (fun n ω => μ + Z n ω / sqrtN n - clipReal μ c (hat n ω))) ∧
    (∀ μ c x y : ℝ,
      |x - clipReal μ c y| ≤ |residual μ c x| + |clipReal μ c x - clipReal μ c y|) ∧
    (∀ {Ξ : Type u3} [MeasurableSpace Ξ]
    (P : Measure Ξ) (hat : ℕ → Ξ → ℝ) (μ : ℝ),
    (∀ x y : ℝ, x - clipTarget μ ⊤ x = 0 ∧ y - clipTarget μ ⊤ x = y - x) ∧
    SmallMSE P (fun n ω => hat n ω - clipTarget μ ⊤ (hat n ω)))

/-- Mathematical statement for P017-T9. -/
def T9Statement : Prop :=
    ¬ (∀ {Ω D Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (_hτm : Measurable τ) (_hτi : Integrable τ G)
    (_hc : 0 < effectRadius G τ) (O : Ω → D) (_hOm : Measurable O)
    (P : Measure Ξ) [IsProbabilityMeasure P]
    (data : Ξ → ℕ → Ω) (_hdata : Measurable data)
    (hat : ℕ → Ξ → ℝ) (H : ℕ → Measure D → ℝ)
    (_hfactor : ∀ n : ℕ, 1 ≤ n → ∀ s : Ξ,
      hat n s = H n (empiricalObserved O n (data s)))
    (_hh : RootNNormal P hat (populationMean G τ)),
    ∀ n : ℕ, 1 ≤ n → ∀ s : Ξ,
      Representable G τ
        (clipTarget (populationMean G τ) (effectRadius G τ) (hat n s)))

/-- Mathematical statement for P017-T10.
The usual measure-theoretic conditions are assumed. -/
def T10Statement : Prop :=
    (∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : Ξ → ℝ) (hhm : Measurable hat)
    (hcond : max (supportSup (effectSupport P hat) - (populationMean G τ : EReal))
      ((populationMean G τ : EReal) - supportInf (effectSupport P hat)) ≤ (effectRadius G τ : EReal)),
    (effectSupport P hat ⊆ {x | inside (populationMean G τ) (effectRadius G τ) x}) ∧
    pr P {ω | inside (populationMean G τ) (effectRadius G τ) (hat ω)} = 1 ∧
    {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} =
      {ω | inside (populationMean G τ) (effectRadius G τ) (hat ω)} ∧
    pr P {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} = 1 ∧
    (pr P {ω | inside (populationMean G τ) (effectRadius G τ) (hat ω)} = 0 →
      pr P {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} = 0)) ∧
    (∀ {Ω : Type u3} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hS : effectSupport G τ = univ),
    effectRadius G τ = ⊤ ∧ ∀ x, clipTarget (populationMean G τ) (effectRadius G τ) x = x) ∧
    (∀ {Ω : Type u4} {Ξ : Type u5}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hS : effectSupport G τ = Ici 0)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : Ξ → ℝ) (hhm : Measurable hat)
    (hneg : 0 < pr P {ω | hat ω < 0}),
    effectRadius G τ = ENNReal.ofReal (populationMean G τ) ∧
    ¬ (max (supportSup (effectSupport P hat) - (populationMean G τ : EReal))
      ((populationMean G τ : EReal) - supportInf (effectSupport P hat)) ≤ (effectRadius G τ : EReal)) ∧
    pr P {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} ≤
      1 - pr P {ω | hat ω < 0} ∧
    pr P {ω | hat ω = clipTarget (populationMean G τ) (effectRadius G τ) (hat ω)} < 1)

/-- Mathematical statement for P017-T11. -/
def T11Statement : Prop :=
    (∀ (n : ℕ) (hn : 1 ≤ n) (c σ : ℝ)
    (hc : 0 < c) (hσ : 0 < σ),
    normalTail n c σ =
      c * σ * Real.sqrt (2 / Real.pi) * Real.exp (-(c ^ 2 * (n : ℝ)) / (2 * σ ^ 2)) / sqrtN n +
      2 * σ ^ 2 * normalCDF (-c * sqrtN n / σ) / (n : ℝ)) ∧
    (∀ (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ),
    Tendsto (fun n : ℕ => (n : ℝ) * normalTail n c σ) atTop (𝓝 0) ∧
    ∀ k : ℝ, 0 < k → Tendsto (fun n : ℕ => (n : ℝ) ^ k * normalTail n c σ) atTop (𝓝 0))

/-- The printed claim is false: P017-T9; Proposition 1 and its all-realizations
gloss, PDF p. 2. Even with IID full-data draws from the population G and a
measurable estimator given by a measurable functional of their observed empirical distribution, the
Definition 2 target need not be an admissibly weighted population mean.
The IID experiment is a counterexample within the printed sampling setting.
The usual measure-theoretic conditions are assumed. -/
def T9SamplingStatement : Prop :=
  ¬ (∀ {Ω D Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (_hτm : Measurable τ) (_hτi : Integrable τ G)
    (_hc : 0 < effectRadius G τ) (O : Ω → D) (_hOm : Measurable O)
    (P : Measure Ξ) [IsProbabilityMeasure P]
    (data : Ξ → ℕ → Ω) (_hdata : Measurable data)
    (_hlaw : P.map data = iidSamples G)
    (hat : ℕ → Ξ → ℝ) (H : ℕ → Measure D → ℝ)
    (_hHm : ∀ n : ℕ, 1 ≤ n → Measurable (H n))
    (_hhm : ∀ n, Measurable (hat n))
    (_hfactor : ∀ n : ℕ, 1 ≤ n → ∀ s : Ξ,
      hat n s = H n (empiricalObserved O n (data s)))
    (_hh : RootNNormal P hat (populationMean G τ)),
    ∀ n : ℕ, 1 ≤ n → ∀ s : Ξ,
      Representable G τ
        (clipTarget (populationMean G τ) (effectRadius G τ) (hat n s)))

end
end SAP.P017
