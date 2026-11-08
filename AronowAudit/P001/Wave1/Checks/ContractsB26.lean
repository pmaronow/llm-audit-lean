import AronowAudit.P001.Wave1.Gap.WLP001dB1
import AronowAudit.P001.Wave1.Gap.WLP001bB2

namespace AronowAudit.P001.Wave1.ContractsB26

open MeasureTheory ProbabilityTheory Filter AronowAudit.P001
open scoped BigOperators ENNReal NNReal Topology

universe u

noncomputable section
local instance instDecidableContractsB26P001 (p : Prop) : Decidable p := Classical.propDecidable p

-- The mapper writes `Type*`; `Type u` makes that universe explicit.
-- All remaining binders and conclusions below are copied verbatim from the maps.

/-- Approved statement: `~/lean-work/runs/map-P001d/map.json`, record 7 (P001-T8).
Both `ref1-P001d` and `ref2-P001d` accept this record with no fixes. -/
def approvedContract_P001_T8 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {K τ : ℕ}
  (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX]
  (κ : Measure ℝ) [SFinite κ] (f : ℝ → (Fin K → ℝ) → ℝ)
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (t : Fin τ → ℝ)
  (hf : Measurable (fun xy : (Fin K → ℝ) × ℝ => f xy.2 xy.1))
  (hg : Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hfn : ∀ y x, 0 ≤ f y x) (hgn : ∀ y x, 0 ≤ g y x t)
  (hfnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (f y x) ∂κ)=1)
  (hgnorm : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ)=1)
  (htrue : μ.map (fun ω => (X ω,Y ω)) =
    (νX.prod κ).withDensity (fun xy => ENNReal.ofReal (f xy.2 xy.1)))
  (hdom : ∀ᵐ xy ∂(νX.prod κ), 0 < f xy.2 xy.1 → 0 < g xy.2 xy.1 t)
  (hent : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
    f xy.2 xy.1*Real.log (f xy.2 xy.1)) (νX.prod κ))
  (hcross : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
    f xy.2 xy.1*Real.log (g xy.2 xy.1 t)) (νX.prod κ)),
  averageKLExt νX κ f g t ≠ ∞ ∧
  (averageKLExt νX κ f g t).toReal =
    (∫ x, ∫ y, f y x*Real.log (f y x) ∂κ ∂νX) - expectedLogLikelihood μ X Y g t ∧
  averageKL νX κ f g t = (averageKLExt νX κ f g t).toReal

example : approvedContract_P001_T8 := @AronowAudit.P001.Wave1.normalized_averaged_kl_entropy_identity

/-- Approved statement: `~/lean-work/runs/map-P001d/map.json`, record 0 (P001-T6).
Both `ref1-P001d` and `ref2-P001d` accept this record with no fixes. -/
def approvedContract_P001_T6 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {n K : ℕ} (hn : 0 < n)
  (P : Ω → Matrix (Fin n) (Fin K) ℝ) (hP : Measurable P)
  (u : Ω → Fin n → ℝ) (hu2 : ∀ i, MemLp (fun ω => u ω i) 2 μ)
  (hu0 : ∀ i, IsCEF μ P (fun ω => u ω i) (fun _ => 0))
  (huncorr : ∀ i j, i ≠ j → IsCEF μ P (fun ω => u ω i * u ω j) (fun _ => 0))
  (v : Matrix (Fin n) (Fin K) ℝ → Fin n → ℝ)
  (hv : ∀ i, IsCEF μ P (fun ω => (u ω i)^2) (fun p => v p i))
  (V c : ℝ) (hV : 0 ≤ V) (hc : 0 < c)
  (hvar : ∀ᵐ ω ∂μ, ∀ i, v (P ω) i ≤ V),
  let good := fun p : Matrix (Fin n) (Fin K) ℝ =>
    ∀ b : Fin K → ℝ, c * (∑ k, (b k)^2) ≤ (∑ i, (p.mulVec b i)^2) / (n : ℝ)
  let A := fun p : Matrix (Fin n) (Fin K) ℝ => (p.transpose * p)⁻¹ * p.transpose
  let q := fun p : Matrix (Fin n) (Fin K) ℝ =>
    if good p then ∑ k, ∑ i, (A p k i)^2 * v p i else 0
  let Z := fun ω => if good (P ω) then ∑ k, (olsCoef (P ω) (u ω) k)^2 else 0
  IsCEF μ P Z q ∧
  (∀ᵐ ω ∂μ, good (P ω) →
    q (P ω) ≤ V * (∑ k, (fixedDesignGram (P ω))⁻¹ k k) / (n : ℝ) ∧
    V * (∑ k, (fixedDesignGram (P ω))⁻¹ k k) / (n : ℝ) ≤
      V * (K : ℝ) / (c * (n : ℝ))) ∧
  mean μ Z ≤ V * (K : ℝ) / (c * (n : ℝ))

example : approvedContract_P001_T6 := @AronowAudit.P001.Wave1.random_design_noise_conditional_trace

/-- Approved statement: `~/lean-work/runs/map-P001b/map.json`, record 15 (P001-T17).
Both `ref1-P001b` and `ref2-P001b` accept this record with no fixes. -/
def approvedContract_P001_T17 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
  (hiid : IID μ Z) (hlaw : μ.map (Z 0)=finiteLawMeasure placeboLaw),
  FCondIndep placeboLaw placeboW placeboD placeboX ∧
  FCondIndep placeboLaw (fun i => (2+placeboZ i,3+placeboZ i)) placeboD placeboX ∧
  placeboMoment.det=17/54 ∧
  (∀ a b c : ℝ, placeboRisk (29/68) 0 (4/17) ≤ placeboRisk a b c ∧
    (placeboRisk a b c=placeboRisk (29/68) 0 (4/17) ↔ a=29/68 ∧ b=0 ∧ c=4/17)) ∧
  (∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleF Z n ω/(n : ℝ)) atTop (nhds (64/531))) ∧
  (∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleWald Z n ω/(n : ℝ)) atTop (nhds (18496/135315))) ∧
  (∀ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 → ∀ critical : ℕ → ℝ,
    (∀ n : ℕ, 3 < n → prob (fReference 1 (n-3)) (Set.Iic (critical n))=1-α) →
    Tendsto (fun n => prob μ {ω | critical n < placeboSampleF Z n ω}) atTop (nhds 1)) ∧
  (∀ c : ℝ, Tendsto (fun n => prob μ {ω | c < placeboSampleWald Z n ω}) atTop (nhds 1)) ∧
  240*placeboRisk (7/12) 0 0=175/3 ∧
  240*placeboRisk (29/68) 0 (4/17)=885/17 ∧
  ((240*placeboRisk (7/12) 0 0-240*placeboRisk (29/68) 0 (4/17))/
    (240*placeboRisk (29/68) 0 (4/17)/(240-3))=5056/177)

example : approvedContract_P001_T17 := @AronowAudit.P001.Wave1.placebo_iid_f_wald_failure

end
end AronowAudit.P001.Wave1.ContractsB26
