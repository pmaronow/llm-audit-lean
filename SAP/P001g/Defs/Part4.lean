import SAP.P001g.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P001g

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w z u1 v1

def T115Statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
   (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ) (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (hp : 0 < prob μ {ω | D ω=1} ∧ 0 < prob μ {ω | D ω=0}),
  let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
   let arm := fun Z d => (∫ ω in {ω | D ω=d},Z ω ∂μ)/prob μ {ω | D ω=d}
   (IndepFun (fun ω => (Y0 ω,Y1 ω)) D μ → mean μ (fun ω => Y1 ω-Y0 ω)=arm Y 1-arm Y 0) ∧
   arm Y 1-arm Y 0=arm (fun ω => Y1 ω-Y0 ω) 1+arm Y0 1-arm Y0 0

def DiscreteATEStatement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
   (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ) (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (p : E → ℝ) (hp : IsCEF μ X D p) (ε : ℝ) (hε : 0 < ε)
   (hpos : ∀ ω,ε < p (X ω) ∧ p (X ω) < 1-ε)
   (hCI : CI μ X hX (fun ω => (Y0 ω,Y1 ω)) D)
   (m0 m1 : E → ℝ)
   (hm0 : IsCEF (μ.restrict {ω | D ω=0}) X (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m0)
   (hm1 : IsCEF (μ.restrict {ω | D ω=1}) X (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m1)
   (hmi0 : Integrable (m0 ∘ X) μ) (hmi1 : Integrable (m1 ∘ X) μ),
  mean μ (fun ω => Y1 ω-Y0 ω)=
   (∑' x : E,m1 x*prob μ {ω | X ω=x})-(∑' x : E,m0 x*prob μ {ω | X ω=x})

def GeneralIgnorabilityStatement : Prop :=
  (∀ {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1)
    (hD : Measurable D) (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ)
    (hbinary : ∀ ω, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsCEF μ X D p) (ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ ω, ε < p (X ω) ∧ p (X ω) < 1 - ε)
    (hCI : CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D)
    (m0 m1 : E → ℝ)
    (hm0 : IsCEF (μ.restrict {ω | D ω = 0}) X
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m0)
    (hm1 : IsCEF (μ.restrict {ω | D ω = 1}) X
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m1)
    (hmi0 : Integrable (m0 ∘ X) μ) (hmi1 : Integrable (m1 ∘ X) μ),
    IsCEF μ X (fun ω => Y1 ω - Y0 ω) (fun x => m1 x - m0 x) ∧
    mean μ (fun ω => Y1 ω - Y0 ω) =
      mean μ (fun ω => m1 (X ω) - m0 (X ω))) ∧
    (∀ {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1)
    (hD : Measurable D) (hbinary : ∀ ω, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsCEF μ X D p) (ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ ω, ε < p (X ω) ∧ p (X ω) < 1 - ε)
    (hCI : CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D),
    CI μ (p ∘ X) (hp.1.comp hX) D X ∧
    CI μ (p ∘ X) (hp.1.comp hX) (fun ω => (Y0 ω, Y1 ω)) D ∧
    IsCEF μ (p ∘ X) D id ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ ω ∂μ, δ < (p ∘ X) ω ∧ (p ∘ X) ω < 1 - δ))

def T116Statement : Prop :=
  DiscreteATEStatement.{u, v} ∧ GeneralIgnorabilityStatement.{w, z, u1, v1}

def T117Statement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y0 Y1 D : Ω → ℝ),
    Measurable Y0 → Measurable Y1 → Measurable D → Integrable Y0 μ → Integrable Y1 μ →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    0 < prob μ {ω | D ω = 0} → 0 < prob μ {ω | D ω = 1} →
    ∀ (p : (Fin K → ℝ) → ℝ), IsCEF μ X D p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) ∧ p (X ω) < 1 - ε) →
    CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D →
    let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
    mean μ (fun ω => Y1 ω - Y0 ω) =
      mean μ (fun ω => Y ω * D ω / p (X ω) - Y ω * (1 - D ω) / (1 - p (X ω))) ∧
    (∀ m0 m1 q : (Fin K → ℝ) → ℝ,
      Measurable m0 → Measurable m1 → Measurable q →
      Integrable (m0 ∘ X) μ → Integrable (m1 ∘ X) μ →
      ((IsCEF (μ.restrict {ω | D ω = 0}) X Y m0 ∧
        IsCEF (μ.restrict {ω | D ω = 1}) X Y m1 ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < q (X ω) ∧ q (X ω) < 1 - η) ∨
        q ∘ X =ᵐ[μ] p ∘ X) →
      mean μ (fun ω => Y1 ω - Y0 ω) =
        mean μ (fun ω => m1 (X ω) + D ω * (Y ω - m1 (X ω)) / q (X ω) -
          m0 (X ω) - (1 - D ω) * (Y ω - m0 (X ω)) / (1 - q (X ω))))

end

end SAP.P001g
