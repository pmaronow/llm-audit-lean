import AronowAudit.P004.Wave1.FiniteConditioningBlueprint

namespace AronowAudit.P004.Wave1.FiniteConditioning

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Disjoint coordinate sources give independence of the entire two finite families. -/
theorem fc9_proof : FC9 := by
  classical
  intro N p _hp V S B hself hsymm hV hdisjoint
  refine ⟨hself, hsymm, ?_⟩
  intro I J hsep A C
  let T : Set (Fin N) := {k | ∃ i ∈ I, k ∈ S i}
  let W : Set (Fin N) := {k | ∃ j ∈ J, k ∈ S j}
  have hd : Disjoint T W := by
    rw [Set.disjoint_left]
    intro k hkT hkW
    obtain ⟨i, hi, hki⟩ := hkT
    obtain ⟨j, hj, hkj⟩ := hkW
    exact Set.disjoint_left.mp (hdisjoint i j (hsep i hi j hj)) hki hkj
  have hI : DependsOn (fun z (i : I) => V i z) T := by
    intro x y hxy
    funext i
    exact hV i (fun k hk => hxy k ⟨i, i.property, hk⟩)
  have hJ : DependsOn (fun z (j : J) => V j z) W := by
    intro x y hxy
    funext j
    exact hV j (fun k hk => hxy k ⟨j, j.property, hk⟩)
  have hF : DependsOn
      (fun z => if A (fun i => V i z) then (1 : ℝ) else 0) T := by
    intro x y hxy
    exact congrArg (fun v : I → ℝ => if A v then (1 : ℝ) else 0) (hI hxy)
  have hG : DependsOn
      (fun z => if C (fun j => V j z) then (1 : ℝ) else 0) Tᶜ := by
    intro x y hxy
    have he : (fun j : J => V j x) = (fun j : J => V j y) := by
      apply hJ
      intro k hk
      exact hxy k (Set.disjoint_right.mp hd hk)
    exact congrArg (fun v : J → ℝ => if C v then (1 : ℝ) else 0) he
  dsimp only [prob]
  calc
    _ = expect p (fun z =>
        (if A (fun i => V i z) then (1 : ℝ) else 0) *
        (if C (fun j => V j z) then (1 : ℝ) else 0)) := by
      apply congrArg (expect p)
      funext z
      split_ifs <;> simp_all
    _ = _ := GraphCompletion.expect_mul_of_disjoint_depends p T _ _ hF hG

end
end AronowAudit.P004.Wave1.FiniteConditioning
