import SAP.P061a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

def T3Statement : Prop :=
  (∀ (N : ℕ) (S : Set (Fin N → ℝ)) (D : AtomicDesign S) (y : Responses S N)
      (d d' : ℝ), 0 < N →
    (∀ i, 0 < exposureProbability D (coordinateExposure S) i d ∧
      0 < exposureProbability D (coordinateExposure S) i d') →
    targetMoment D (coordinateExposure S) y d → targetMoment D (coordinateExposure S) y d' →
    (∀ i, independent D (fun z => z.val i) (fun z => otherCoordinates z.val i)) →
    (∀ i e, e = d ∨ e = d' → ∀ w,
      0 < eventProbability D (fun z => otherCoordinates z.val i = w) →
      ∃ z : S, supported D z ∧ z.val = insertCoordinate i e w) ∧
    (∀ i e, e = d ∨ e = d' → HasMean D (hybridResponse S y i e) ∧
      exposureMean D (coordinateExposure S) y i e = mean D (hybridResponse S y i e)) ∧
    populationContrast D (coordinateExposure S) y d d' = averageDirectContrast S D y d d') ∧
  (∀ (Ω : Type) (N : ℕ) (D : AtomicDesign Ω) (g : Exposures Ω N) (y : Responses Ω N)
      (H : Fin N → (Fin N → ℝ) → ℝ) (d d' : ℝ), 0 < N →
    (∀ i, 0 < exposureProbability D g i d ∧ 0 < exposureProbability D g i d') →
    targetMoment D g y d → targetMoment D g y d' →
    (∀ i, independent D (g i) (fun z => otherCoordinates (fun j => g j z) i)) →
    (∀ i z, supported D z → g i z = d ∨ g i z = d' → y i z = H i (fun j => g j z)) →
    (∀ i e, e = d ∨ e = d' →
      HasMean D (fun z => H i (insertCoordinate i e (otherCoordinates (fun j => g j z) i))) ∧
      exposureMean D g y i e =
        mean D (fun z => H i (insertCoordinate i e (otherCoordinates (fun j => g j z) i)))) ∧
    populationContrast D g y d d' = (N : ℝ)⁻¹ * ∑ i,
      mean D (fun z => H i (insertCoordinate i d (otherCoordinates (fun j => g j z) i)) -
        H i (insertCoordinate i d' (otherCoordinates (fun j => g j z) i))))


end SAP.P061a
