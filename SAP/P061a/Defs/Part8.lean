import SAP.P061a.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

/-- All corrected first-moment conclusions for one target, with a second-target implication. -/
def FirstMomentFacts {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) (d : ℝ) : Prop :=
    ((∀ i, Summable (fun z => D.mass z * (if g i z = d then y i z else 0)) ∧
      exposureMean D g y i d = conditionalExposureMean D g y i d ∧
      HasMean D (fun z => (if g i z = d then y i z else 0) / exposureProbability D g i d) ∧
      mean D (fun z => |(if g i z = d then y i z else 0) / exposureProbability D g i d|) =
        mean D (fun z => |if g i z = d then y i z else 0|) / exposureProbability D g i d ∧
      mean D (fun z => (if g i z = d then y i z else 0) / exposureProbability D g i d) =
        exposureMean D g y i d) ∧
    HasMean D (estimateExposureMean D g y d) ∧ mean D (estimateExposureMean D g y d) = populationExposureMean D g y d ∧
    (∀ d' : ℝ, (∀ i, 0 < exposureProbability D g i d') → targetMoment D g y d' →
      HasMean D (estimateContrast D g y d d') ∧
      mean D (estimateContrast D g y d d') = populationContrast D g y d d' ∧
      populationContrast D g y d d' = (N : ℝ)⁻¹ * ∑ i, unitContrast D g y i d d')) ∧
    (∀ i, conditionalExposureMean D g (fun j z => |y j z|) i d =
      mean D (fun z => |if g i z=d then y i z else 0|) / exposureProbability D g i d) ∧
    populationExposureMean D g y d = (N : ℝ)⁻¹ * ∑ i, conditionalExposureMean D g y i d


def T8Statement : Prop :=
  (∀ (Ω : Type) (N : ℕ) (D : AtomicDesign Ω) (g : Exposures Ω N) (y : Responses Ω N) (d : ℝ),
    0 < N → (∀ i, 0 < exposureProbability D g i d) → targetMoment D g y d →
    FirstMomentFacts D g y d) ∧
  (∀ (Ω : Type) (N : ℕ) (D : AtomicDesign Ω) (g : Exposures Ω N) (y : Responses Ω N) (d : ℝ),
    0 < N → (∀ i, 0 < exposureProbability D g i d) →
    ({z : Ω | supported D z}.Finite → targetMoment D g y d) ∧
    ((∀ i z z', supported D z → supported D z' → g i z=d → g i z'=d → y i z=y i z') →
      targetMoment D g y d ∧ ∀ i, ∃ a : ℝ,
        (∀ z, supported D z → g i z=d → y i z=a) ∧
        mean D (fun z => |if g i z=d then y i z else 0|)=|a| *exposureProbability D g i d))


end SAP.P061a
