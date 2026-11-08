import SAP.P017.Defs
import AronowAudit.P017.P017_Audit
import AronowAudit.P017.Wave1.Checks.FidP017Contracts
import AronowAudit.P017.Wave1.Gap.GLP017B1
import AronowAudit.P017.Wave1.Gap.GLP017B2
import AronowAudit.P017.Wave1.Gap.GLP017B4
import AronowAudit.P017.Wave1.Gap.GP017B1
import AronowAudit.P017.Wave1.Gap.GP017B1b
import AronowAudit.P017.Wave1.Gap.GP017B2
import AronowAudit.P017.Wave1.Gap.GP017B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u1 u2 u3 u4 u5

namespace SAP.P017.Bridge

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T8_correspondence : SAP.P017.T8Statement.{u1, u2, u3} ↔
    ((∀ {Ξ : Type u1} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ)
    (μ c : ℝ) (v : ℝ≥0) (hc : 0 < c) (hv : 0 < v)
    (hhm : ∀ n, Measurable (hat n)) (hr : AronowAudit.P017.NormalRemainder P hat Z ε μ v)
    (n : ℕ) (hn : 1 ≤ n),
    let tilde := fun ω => μ + Z n ω / AronowAudit.P017.sqrtN n
    (∀ x y, |AronowAudit.P017.clipReal μ c x - AronowAudit.P017.clipReal μ c y| ≤ |x - y| ∧
      |AronowAudit.P017.residual μ c x - AronowAudit.P017.residual μ c y| ≤ |x - y|) ∧
    (∀ᵐ ω ∂P, |AronowAudit.P017.residual μ c (hat n ω)| ≤ |AronowAudit.P017.residual μ c (tilde ω)| + |ε n ω| / AronowAudit.P017.sqrtN n) ∧
    ((∫ ω, AronowAudit.P017.residual μ c (hat n ω) ^ 2 ∂P) ≤
      2 * (∫ ω, AronowAudit.P017.residual μ c (tilde ω) ^ 2 ∂P) + 2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) ∧
    (∀ x, AronowAudit.P017.residual μ c x ^ 2 = max (|x - μ| - c) 0 ^ 2 ∧
      AronowAudit.P017.residual μ c x ^ 2 ≤ (if |x - μ| > c then (x - μ) ^ 2 else 0) ∧
      (if |x - μ| > c then (x - μ) ^ 2 else 0) ≤ (x - μ) ^ 4 / c ^ 2) ∧
    ((∫ ω, (tilde ω - μ) ^ 4 ∂P) = 3 * (v : ℝ) ^ 2 / (n : ℝ) ^ 2) ∧
    ((∫ ω, AronowAudit.P017.residual μ c (hat n ω) ^ 2 ∂P) ≤
      6 * (v : ℝ) ^ 2 / (c ^ 2 * (n : ℝ) ^ 2) + 2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) ∧
    (∀ᵐ ω ∂P, |tilde ω - AronowAudit.P017.clipReal μ c (hat n ω)| ≤
      |AronowAudit.P017.residual μ c (tilde ω)| + |ε n ω| / AronowAudit.P017.sqrtN n) ∧
    ((∫ ω, (tilde ω - AronowAudit.P017.clipReal μ c (hat n ω)) ^ 2 ∂P) ≤
      6 * (v : ℝ) ^ 2 / (c ^ 2 * (n : ℝ) ^ 2) + 2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) ∧
    ((∫ ω, AronowAudit.P017.residual μ c (tilde ω) ^ 2 ∂P) ≤
      (∫ ω, if |tilde ω - μ| > c then (tilde ω - μ) ^ 2 else 0 ∂P)) ∧
    ((∫ ω, if |tilde ω - μ| > c then (tilde ω - μ) ^ 2 else 0 ∂P) = AronowAudit.P017.normalTail n c (Real.sqrt v))) ∧
    (∀ {Ξ : Type u2} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ)
    (μ c : ℝ) (v : ℝ≥0) (hc : 0 < c) (hv : 0 < v)
    (hhm : ∀ n, Measurable (hat n)) (hr : AronowAudit.P017.NormalRemainder P hat Z ε μ v)
    (he : AronowAudit.P017.SmallRemainderMS P ε),
    AronowAudit.P017.SmallMSE P (fun n ω => AronowAudit.P017.residual μ c (hat n ω)) ∧
    AronowAudit.P017.SmallMSE P (fun n ω => μ + Z n ω / AronowAudit.P017.sqrtN n - AronowAudit.P017.clipReal μ c (hat n ω))) ∧
    (∀ μ c x y : ℝ,
      |x - AronowAudit.P017.clipReal μ c y| ≤ |AronowAudit.P017.residual μ c x| + |AronowAudit.P017.clipReal μ c x - AronowAudit.P017.clipReal μ c y|) ∧
    (∀ {Ξ : Type u3} [MeasurableSpace Ξ]
    (P : Measure Ξ) (hat : ℕ → Ξ → ℝ) (μ : ℝ),
    (∀ x y : ℝ, x - AronowAudit.P017.clipTarget μ ⊤ x = 0 ∧ y - AronowAudit.P017.clipTarget μ ⊤ x = y - x) ∧
    AronowAudit.P017.SmallMSE P (fun n ω => hat n ω - AronowAudit.P017.clipTarget μ ⊤ (hat n ω)))) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T9_correspondence : SAP.P017.T9Statement ↔
    (¬ (∀ {Ω D Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (_hτm : Measurable τ) (_hτi : Integrable τ G)
    (_hc : 0 < AronowAudit.P017.effectRadius G τ) (O : Ω → D) (_hOm : Measurable O)
    (P : Measure Ξ) [IsProbabilityMeasure P]
    (data : Ξ → ℕ → Ω) (_hdata : Measurable data)
    (hat : ℕ → Ξ → ℝ) (H : ℕ → Measure D → ℝ)
    (_hfactor : ∀ n : ℕ, 1 ≤ n → ∀ s : Ξ,
      hat n s = H n (AronowAudit.P017.empiricalObserved O n (data s)))
    (_hh : AronowAudit.P017.RootNNormal P hat (AronowAudit.P017.populationMean G τ)),
    ∀ n : ℕ, 1 ≤ n → ∀ s : Ξ,
      AronowAudit.P017.Representable G τ
        (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat n s)))) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T10_correspondence : SAP.P017.T10Statement.{u1, u2, u3, u4, u5} ↔
    ((∀ {Ω : Type u1} {Ξ : Type u2} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : Ξ → ℝ) (hhm : Measurable hat)
    (hcond : max (AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport P hat) - (AronowAudit.P017.populationMean G τ : EReal))
      ((AronowAudit.P017.populationMean G τ : EReal) - AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport P hat)) ≤ (AronowAudit.P017.effectRadius G τ : EReal)),
    (AronowAudit.P017.effectSupport P hat ⊆ {x | AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) x}) ∧
    AronowAudit.P017.pr P {ω | AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat ω)} = 1 ∧
    {ω | hat ω = AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat ω)} =
      {ω | AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat ω)} ∧
    AronowAudit.P017.pr P {ω | hat ω = AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat ω)} = 1 ∧
    (AronowAudit.P017.pr P {ω | AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat ω)} = 0 →
      AronowAudit.P017.pr P {ω | hat ω = AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat ω)} = 0)) ∧
    (∀ {Ω : Type u3} [MeasurableSpace Ω]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hS : AronowAudit.P017.effectSupport G τ = univ),
    AronowAudit.P017.effectRadius G τ = ⊤ ∧ ∀ x, AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) x = x) ∧
    (∀ {Ω : Type u4} {Ξ : Type u5}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (hτm : Measurable τ) (hτi : Integrable τ G) (hS : AronowAudit.P017.effectSupport G τ = Ici 0)
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat : Ξ → ℝ) (hhm : Measurable hat)
    (hneg : 0 < AronowAudit.P017.pr P {ω | hat ω < 0}),
    AronowAudit.P017.effectRadius G τ = ENNReal.ofReal (AronowAudit.P017.populationMean G τ) ∧
    ¬ (max (AronowAudit.P017.supportSup (AronowAudit.P017.effectSupport P hat) - (AronowAudit.P017.populationMean G τ : EReal))
      ((AronowAudit.P017.populationMean G τ : EReal) - AronowAudit.P017.supportInf (AronowAudit.P017.effectSupport P hat)) ≤ (AronowAudit.P017.effectRadius G τ : EReal)) ∧
    AronowAudit.P017.pr P {ω | hat ω = AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat ω)} ≤
      1 - AronowAudit.P017.pr P {ω | hat ω < 0} ∧
    AronowAudit.P017.pr P {ω | hat ω = AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ) (hat ω)} < 1)) := Iff.rfl

/-- The SAP statement differs only in names of definitionally equal notions. -/
theorem T11_correspondence : SAP.P017.T11Statement ↔
    ((∀ (n : ℕ) (hn : 1 ≤ n) (c σ : ℝ)
    (hc : 0 < c) (hσ : 0 < σ),
    AronowAudit.P017.normalTail n c σ =
      c * σ * Real.sqrt (2 / Real.pi) * Real.exp (-(c ^ 2 * (n : ℝ)) / (2 * σ ^ 2)) / AronowAudit.P017.sqrtN n +
      2 * σ ^ 2 * AronowAudit.P017.normalCDF (-c * AronowAudit.P017.sqrtN n / σ) / (n : ℝ)) ∧
    (∀ (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ),
    Tendsto (fun n : ℕ => (n : ℝ) * AronowAudit.P017.normalTail n c σ) atTop (𝓝 0) ∧
    ∀ k : ℝ, 0 < k → Tendsto (fun n : ℕ => (n : ℝ) ^ k * AronowAudit.P017.normalTail n c σ) atTop (𝓝 0))) := Iff.rfl

/-- The sampling law, estimator measurability, and population notions agree by definition. -/
theorem T9Sampling_correspondence : SAP.P017.T9SamplingStatement ↔
  (¬ (∀ {Ω D Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace Ξ]
    (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
    (_hτm : Measurable τ) (_hτi : Integrable τ G)
    (_hc : 0 < AronowAudit.P017.effectRadius G τ) (O : Ω → D) (_hOm : Measurable O)
    (P : Measure Ξ) [IsProbabilityMeasure P]
    (data : Ξ → ℕ → Ω) (_hdata : Measurable data)
    (_hlaw : P.map data = AronowAudit.P017.iidSamples G)
    (hat : ℕ → Ξ → ℝ) (H : ℕ → Measure D → ℝ)
    (_hHm : ∀ n : ℕ, 1 ≤ n → Measurable (H n))
    (_hhm : ∀ n, Measurable (hat n))
    (_hfactor : ∀ n : ℕ, 1 ≤ n → ∀ s : Ξ,
      hat n s = H n (AronowAudit.P017.empiricalObserved O n (data s)))
    (_hh : AronowAudit.P017.RootNNormal P hat (AronowAudit.P017.populationMean G τ)),
    ∀ n : ℕ, 1 ≤ n → ∀ s : Ξ,
      AronowAudit.P017.Representable G τ
        (AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ)
          (AronowAudit.P017.effectRadius G τ) (hat n s)))) := Iff.rfl

end
end SAP.P017.Bridge
