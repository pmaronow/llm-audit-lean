import AronowAudit.P004.Wave1.FiniteConditioningBlueprint
import AronowAudit.P004.Wave1.FiniteConditioning.FC2
import AronowAudit.P004.Wave1.FiniteConditioning.FC7

namespace AronowAudit.P004.Wave1.FiniteConditioning

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Pull the own-coin coefficient through conditioning, then use absolute domination. -/
theorem fc8_proof : FC8 := by
  classical
  intro N p hp J i hi U α β A hα
  have hA : 0 ≤ A := (abs_nonneg (α false)).trans (hα false)
  have hαdep : ∀ z z' : Assignment N, (∀ j ∈ J, z j = z' j) →
      α (z i) = α (z' i) := by
    intro z z' hzz'
    exact congrArg α (hzz' i hi)
  have hβdep : ∀ z z' : Assignment N, (∀ j ∈ J, z j = z' j) →
      β (z i) = β (z' i) := by
    intro z z' hzz'
    exact congrArg β (hzz' i hi)
  have hβ : ∀ z : Assignment N, conditionOn p J (fun z => β (z i)) z = β (z i) := by
    intro z
    have h := (fc2_proof p hp J).2.2.2 (fun z => β (z i)) (fun _ => 1) hβdep z
    rw [(fc2_proof p hp J).1 1 z] at h
    simpa only [mul_one] using h
  have hcond : ∀ z : Assignment N,
      conditionOn p J (fun z => α (z i) * U z + β (z i)) z =
        α (z i) * conditionOn p J U z + β (z i) := by
    intro z
    rw [(fc2_proof p hp J).2.1 (fun z => α (z i) * U z) (fun z => β (z i)) z,
      (fc2_proof p hp J).2.2.2 (fun z => α (z i)) U hαdep z, hβ z]
  have he : (fun z => α (z i) * U z + β (z i) -
      conditionOn p J (fun z => α (z i) * U z + β (z i)) z) =
      (fun z => α (z i) * (U z - conditionOn p J U z)) := by
    funext z
    rw [hcond z]
    ring
  have hmono : ∀ X Y : Assignment N → ℝ,
      (∀ z, |X z| ≤ |Y z|) → l2Norm p X ≤ l2Norm p Y :=
    (fc7_proof p hp).2.2.2.2.2.2.1
  have hscale : ∀ (c : ℝ) (X : Assignment N → ℝ),
      l2Norm p (fun z => c * X z) = |c| * l2Norm p X :=
    (fc7_proof p hp).2.2.2.2.1
  rw [he]
  calc
    _ ≤ l2Norm p (fun z => A * (U z - conditionOn p J U z)) := by
      apply hmono
      intro z
      rw [abs_mul, abs_mul, abs_of_nonneg hA]
      exact mul_le_mul_of_nonneg_right (hα (z i)) (abs_nonneg _)
    _ = A * l2Norm p (fun z => U z - conditionOn p J U z) := by
      rw [hscale A (fun z => U z - conditionOn p J U z), abs_of_nonneg hA]

end
end AronowAudit.P004.Wave1.FiniteConditioning
