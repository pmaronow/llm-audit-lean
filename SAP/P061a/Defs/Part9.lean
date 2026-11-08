import SAP.P061a.Defs.Part8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

/-- Positivity-only ordinary-mean contract; targeted moments express existence, not totalized values. -/
def positivityWellDefined : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g : Exposures Ω N) (y : Responses Ω N)
    (d d' : ℝ), 0 < N → positiveExposure D g d → positiveExposure D g d' →
    targetMoment D g y d ∧ targetMoment D g y d' ∧
    (∀ i, exposureMean D g y i d = conditionalExposureMean D g y i d ∧
      exposureMean D g y i d' = conditionalExposureMean D g y i d') ∧
    populationContrast D g y d d' = (N : ℝ)⁻¹ * ∑ i, unitContrast D g y i d d'

/-- Equations (4)–(8) on finite positive-probability support, retaining arbitrary feasible assignments. -/
def T11Statement : Prop :=
  ∀ {Ω : Type} {N : ℕ} (D : AtomicDesign Ω) (g : Exposures Ω N) (y : Responses Ω N)
    (d d' : ℝ), 0 < N → positiveExposure D g d → positiveExposure D g d' →
    {z : Ω | supported D z}.Finite →
    targetMoment D g y d ∧ targetMoment D g y d' ∧
    (∀ i e, e=d ∨ e=d' → exposureProbability D g i e =
      ∑' z, if supported D z ∧ g i z=e then D.mass z else 0) ∧
    (∀ i, exposureMean D g y i d = conditionalExposureMean D g y i d ∧
      exposureMean D g y i d' = conditionalExposureMean D g y i d') ∧
    (∀ e, e=d ∨ e=d' → populationExposureMean D g y e =
      (N : ℝ)⁻¹ * ∑ i, conditionalExposureMean D g y i e) ∧
    (∀ i, unitContrast D g y i d d' =
      conditionalExposureMean D g y i d - conditionalExposureMean D g y i d') ∧
    populationContrast D g y d d' = populationExposureMean D g y d - populationExposureMean D g y d' ∧
    populationContrast D g y d d' = (N : ℝ)⁻¹ * ∑ i, unitContrast D g y i d d'



end SAP.P061a
