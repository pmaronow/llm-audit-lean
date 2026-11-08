import SAP.P061a.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

def T6Statement : Prop :=
  (∀ (Ω : Type) [Fintype Ω] (N : ℕ) (D : AtomicDesign Ω)
      (g : Exposures Ω N) (y : Responses Ω N) (d d' : ℝ), 0 < N →
    (∀ i, 0 < exposureProbability D g i d) → (∀ i, 0 < exposureProbability D g i d') →
    ((∀ i, exposureMean D g y i d = conditionalExposureMean D g y i d ∧
      exposureMean D g y i d' = conditionalExposureMean D g y i d') ∧
    populationContrast D g y d d' = (N : ℝ)⁻¹ * ∑ i,
      (conditionalExposureMean D g y i d-conditionalExposureMean D g y i d')) ∧
    populationContrast D g y d d' = populationExposureMean D g y d - populationExposureMean D g y d' ∧
    populationContrast D g y d d' = (N : ℝ)⁻¹ * ∑ i, unitContrast D g y i d d') ∧
  (∀ (N : ℕ) (D : AtomicDesign (Fin N → Fin 2)) (y : Responses (Fin N → Fin 2) N),
    0 < N → (∀ i, 0 < exposureProbability D (fun i z => (z i).val) i 1) →
    (∀ i, 0 < exposureProbability D (fun i z => (z i).val) i 0) →
    populationContrast D (fun i z => (z i).val) y 1 0 = (N : ℝ)⁻¹ * ∑ i,
      (conditionalExposureMean D (fun i z => (z i).val) y i 1 -
       conditionalExposureMean D (fun i z => (z i).val) y i 0))


end SAP.P061a
