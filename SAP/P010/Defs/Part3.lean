import SAP.P010.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P010

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology BigOperators

/-- A population state stores potential responses, binary checks, an arm,
and a finite real covariate vector. Arm labels start at zero. -/
abbrev Population (K d : ℕ) :=
  (Fin K → ℝ) × (Fin K → Bool) × Fin K × (Fin d → ℝ)

def potentialOutcome {K d : ℕ} (a : Fin K) (ω : Population K d) : ℝ := ω.1 a
def potentialCheck {K d : ℕ} (a : Fin K) (ω : Population K d) : Bool := ω.2.1 a
def arm {K d : ℕ} (ω : Population K d) : Fin K := ω.2.2.1
def features {K d : ℕ} (ω : Population K d) : Fin d → ℝ := ω.2.2.2
def response {K d : ℕ} (ω : Population K d) : ℝ := ω.1 (arm ω)
def check {K d : ℕ} (ω : Population K d) : Bool := ω.2.1 (arm ω)
def allPass {K d : ℕ} : Set (Population K d) := {ω | ∀ a, ω.2.1 a = true}
def sameCheck {K d : ℕ} : Set (Population K d) := {ω | ∀ a b, ω.2.1 a = ω.2.1 b}
def assigned {K d : ℕ} (a : Fin K) : Set (Population K d) := {ω | arm ω = a}
def passed {K d : ℕ} : Set (Population K d) := {ω | check ω = true}
def wouldPass {K d : ℕ} (a : Fin K) : Set (Population K d) := {ω | ω.2.1 a = true}

/-- Restricted Bochner integral divided by event mass. Ordinary conditional
means require a positive event mass and an integrable restricted integrand;
T21 and T23 explicitly certify both conditions for their witnesses. -/
noncomputable def meanOn {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (E : Set Ω) : ℝ :=
  (∫ ω in E, f ω ∂μ) / (μ E).toReal

noncomputable def passRate {K d : ℕ} (μ : Measure (Population K d)) (a : Fin K) : ℝ :=
  (μ (passed ∩ assigned a)).toReal / (μ (assigned a)).toReal

def randomAssignment {K d : ℕ} (μ : Measure (Population K d)) : Prop :=
  (∀ a, IndepFun (fun ω => (potentialOutcome a ω, potentialCheck a ω)) arm μ) ∧
  (∀ a, 0 < μ (assigned a))

def positivePassRates {K d : ℕ} (μ : Measure (Population K d)) : Prop :=
  ∀ a, 0 < passRate μ a

def populationAssumptions {K d : ℕ} (μ : Measure (Population K d)) : Prop :=
  IsProbabilityMeasure μ ∧ randomAssignment μ ∧ positivePassRates μ

def covariateRandomAssignment {K d : ℕ} (μ : Measure (Population K d)) : Prop :=
  (∀ a, IndepFun (fun ω => (potentialOutcome a ω, potentialCheck a ω, features ω)) arm μ) ∧
  (∀ a, 0 < μ (assigned a))

def covariateBalance {K d : ℕ} (μ : Measure (Population K d)) : Prop :=
  ∀ b : Bool, 0 < μ {ω | check ω = b} →
    IndepFun features arm ((μ {ω | check ω = b})⁻¹ • μ.restrict {ω | check ω = b})

end SAP.P010
