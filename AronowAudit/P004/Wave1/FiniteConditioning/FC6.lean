import AronowAudit.P004.Wave1.FiniteConditioningBlueprint
import AronowAudit.P004.Wave1.FiniteConditioning.FC2
import AronowAudit.P004.Wave1.FiniteConditioning.FC3
import AronowAudit.P004.Wave1.FiniteConditioning.FC4

namespace AronowAudit.P004.Wave1.FiniteConditioning

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Orthogonality gives contraction and monotonicity of the projection error. -/
theorem fc6_proof : FC6 := by
  classical
  intro N p hp J U
  have hsecond : ∀ X : Assignment N → ℝ, 0 ≤ expect p (fun z => (X z)^2) := by
    intro X
    have h := expect_mono p hp (fun _ => 0) (fun z => (X z)^2)
      (fun z => sq_nonneg (X z))
    simpa only [expect_const] using h
  -- This is the defining cylinder invariance.
  have hdepends : ∀ (K : Finset (Fin N)) (X : Assignment N → ℝ)
      (z z' : Assignment N), (∀ k ∈ K, z k = z' k) →
      conditionOn p K X z = conditionOn p K X z' := by
    intro K X z z' hzz'
    have hden : (∏ k ∈ K, coin (p k) (z k)) =
        ∏ k ∈ K, coin (p k) (z' k) := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [hzz' k hk]
    have hnum : (fun y : Assignment N =>
        if ∀ k ∈ K, y k = z k then X y else 0) =
        (fun y : Assignment N => if ∀ k ∈ K, y k = z' k then X y else 0) := by
      funext y
      have he : (∀ k ∈ K, y k = z k) ↔ (∀ k ∈ K, y k = z' k) := by
        constructor
        · intro hy k hk
          exact (hy k hk).trans (hzz' k hk)
        · intro hy k hk
          exact (hy k hk).trans (hzz' k hk).symm
      exact if_congr he rfl rfl
    unfold conditionOn
    rw [hnum, hden]
  have horth : ∀ (K : Finset (Fin N)) (X F : Assignment N → ℝ),
      (∀ z z', (∀ k ∈ K, z k = z' k) → F z = F z') →
      expect p (fun z => (X z - conditionOn p K X z) * F z) = 0 := by
    intro K X F hF
    have hidem : conditionOn p K (conditionOn p K X) = conditionOn p K X :=
      (fc4_proof p hp K K (fun _ hk => hk) X).1
    have hcond : conditionOn p K
        (fun z => F z * (X z - conditionOn p K X z)) = (fun _ => 0) := by
      funext z
      rw [(fc2_proof p hp K).2.2.2 F
        (fun z => X z - conditionOn p K X z) hF z]
      rw [(fc2_proof p hp K).2.2.1 X (conditionOn p K X) z]
      rw [hidem]
      ring
    calc
      _ = expect p (fun z => F z * (X z - conditionOn p K X z)) := by
        apply congrArg (expect p)
        funext z
        ring
      _ = expect p (conditionOn p K
          (fun z => F z * (X z - conditionOn p K X z))) :=
        (fc3_proof p hp K _).symm
      _ = 0 := by rw [hcond, expect_const]
  constructor
  · have ho := horth J U (conditionOn p J U) (hdepends J U)
    have he : (fun z => (U z)^2) =
        (fun z => (U z - conditionOn p J U z)^2 +
          2 * ((U z - conditionOn p J U z) * conditionOn p J U z) +
          (conditionOn p J U z)^2) := by
      funext z
      ring
    have hpyth := congrArg (expect p) he
    simp only [expect_add, expect_mul, ho, mul_zero, add_zero] at hpyth
    apply Real.sqrt_le_sqrt
    have hn := hsecond (fun z => U z - conditionOn p J U z)
    linarith
  · intro I hIJ
    have hF : ∀ z z', (∀ k ∈ J, z k = z' k) →
        conditionOn p J U z - conditionOn p I U z =
          conditionOn p J U z' - conditionOn p I U z' := by
      intro z z' hzz'
      rw [hdepends J U z z' hzz',
        hdepends I U z z' (fun k hk => hzz' k (hIJ hk))]
    have ho := horth J U
      (fun z => conditionOn p J U z - conditionOn p I U z) hF
    have he : (fun z => (U z - conditionOn p I U z)^2) =
        (fun z => (U z - conditionOn p J U z)^2 +
          2 * ((U z - conditionOn p J U z) *
            (conditionOn p J U z - conditionOn p I U z)) +
          (conditionOn p J U z - conditionOn p I U z)^2) := by
      funext z
      ring
    have hpyth := congrArg (expect p) he
    simp only [expect_add, expect_mul, ho, mul_zero, add_zero] at hpyth
    apply Real.sqrt_le_sqrt
    have hn := hsecond (fun z => conditionOn p J U z - conditionOn p I U z)
    linarith

end
end AronowAudit.P004.Wave1.FiniteConditioning
