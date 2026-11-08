import SAP.P043.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P043

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
universe u v

/-! General probability-law mediation quantities; assignment and consistency are built into the product law and observed response. -/

def randomizedLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) : Measure (Ω × Bool) :=
  μ.prod (bernoulliMeasure true false p)

def lawArmMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (t : Bool)
    (f : Bool → Ω → ℝ) : ℝ :=
  (∫ z in {z : Ω × Bool | z.2 = t}, f z.2 z.1 ∂(randomizedLaw μ p)) /
    ((randomizedLaw μ p) {z : Ω × Bool | z.2 = t}).toReal

def lawContrast {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (f : Bool → Ω → ℝ) : ℝ :=
  lawArmMean μ p true f - lawArmMean μ p false f

def lawReducedForm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (m : MediationModel Ω) : ℝ :=
  lawContrast μ p (observedSupport m)

def lawMediated {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : MediationModel Ω) : ℝ :=
  ∫ i, m.support false (m.knowledge true i) i -
    m.support false (m.knowledge false i) i ∂μ

def lawDirect {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : MediationModel Ω) : ℝ :=
  ∫ i, m.support true (m.knowledge true i) i -
    m.support false (m.knowledge true i) i ∂μ

def IntegrableMediationPotentials {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : MediationModel Ω) : Prop :=
  Integrable (m.knowledge false) μ ∧
  Integrable (m.knowledge true) μ ∧
  Integrable (fun i => m.support false (m.knowledge false i) i) μ ∧
  Integrable (fun i => m.support false (m.knowledge true i) i) μ ∧
  Integrable (fun i => m.support true (m.knowledge true i) i) μ

def MediationLawClaims {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (m : MediationModel Ω) : Prop :=
  lawReducedForm μ p m =
    (∫ i, m.support true (m.knowledge true i) i ∂μ) -
      (∫ i, m.support false (m.knowledge false i) i ∂μ) ∧
  lawReducedForm μ p m = lawMediated μ m + lawDirect μ m ∧
  (lawReducedForm μ p m ≥ lawMediated μ m ↔ lawDirect μ m ≥ 0) ∧
  (lawReducedForm μ p m > lawMediated μ m ↔ lawDirect μ m > 0) ∧
  (lawDirect μ m ≥ 0 → lawReducedForm μ p m ≥ lawMediated μ m) ∧
  (lawDirect μ m ≥ 0 → lawReducedForm μ p m ≤ 0 → lawMediated μ m ≤ 0) ∧
  (lawDirect μ m ≥ 0 → lawReducedForm μ p m = 0 → lawMediated μ m ≤ 0)

def LinearMediationLawClaims {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (α a σ b c : ℝ)
    (u₁ u₂ : Ω → ℝ) : Prop :=
  lawContrast μ p (linearModel α a σ b c u₁ u₂).knowledge = a ∧
  lawMediated μ (linearModel α a σ b c u₁ u₂) = a * b ∧
  lawDirect μ (linearModel α a σ b c u₁ u₂) = c ∧
  lawReducedForm μ p (linearModel α a σ b c u₁ u₂) = a * b + c ∧
  (lawReducedForm μ p (linearModel α a σ b c u₁ u₂) ≥
    lawMediated μ (linearModel α a σ b c u₁ u₂) ↔ c ≥ 0) ∧
  (∀ (n : ℕ) (d : Fin n → ℝ), c = ∑ j, d j →
    (lawReducedForm μ p (linearModel α a σ b c u₁ u₂) ≥
      lawMediated μ (linearModel α a σ b c u₁ u₂) ↔ 0 ≤ ∑ j, d j))

/-- Population mediation comparison, its linear specialization and the net-channel condition. -/
def MediationRepairConclusions {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (m : MediationModel Ω) : Prop :=
  MediationLawClaims μ p m ∧
  (∀ i, m.support true (m.knowledge true i) i -
    m.support false (m.knowledge false i) i =
      (m.support true (m.knowledge true i) i -
        m.support false (m.knowledge true i) i) +
      (m.support false (m.knowledge true i) i -
        m.support false (m.knowledge false i) i)) ∧
  (∀ (α a σ b c : ℝ) (u₁ u₂ : Ω → ℝ),
    Integrable u₁ μ → Integrable u₂ μ →
    LinearMediationLawClaims μ p α a σ b c u₁ u₂ ∧
    (0 < a →
      lawReducedForm μ p (linearModel α a σ b c u₁ u₂) / a = b + c / a ∧
      (lawReducedForm μ p (linearModel α a σ b c u₁ u₂) / a ≥ b ↔ c ≥ 0))) ∧
  (∀ (n : ℕ) (d : Fin n → ℝ), (∀ j, 0 ≤ d j) → 0 ≤ ∑ j, d j) ∧
  (∃ d : Fin 2 → ℝ, 0 ≤ ∑ j, d j ∧ ¬ (∀ j, 0 ≤ d j))

/-- Independent nondegenerate Bernoulli assignment; exactly the five finite expectations
of the canonical claim. The fixed witness records failure of the null inference
when the net-channel sign premise is removed. -/
def T2Statement : Prop :=
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : unitInterval), 0 < (p : ℝ) ∧ (p : ℝ) < 1 →
    ∀ (m : MediationModel Ω), IntegrableMediationPotentials μ m →
      MediationRepairConclusions μ p m) ∧
  (reducedForm linearPopulation (1/2) linearWitness = 0 ∧
    mediated linearPopulation linearWitness = 3/50 ∧
    direct linearPopulation linearWitness = -3/50 ∧
    0 < mediated linearPopulation linearWitness)

end
end SAP.P043
