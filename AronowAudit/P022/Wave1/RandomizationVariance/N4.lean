import AronowAudit.P022.Wave1.RandomizationVarianceBlueprint

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.RandomizationVariance
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators
noncomputable section

theorem sum_positions {N a k : ℕ} (h : a + k ≤ N) (f : Fin N → ℝ) :
    (∑ s : Fin N, if a ≤ s.val ∧ s.val < a + k then f s else 0) =
      ∑ i : Fin k, f ⟨a + i.val, by omega⟩ := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun i _ => (⟨a + i.val, by omega⟩ : Fin N)) ?_ ?_ ?_ ?_
  · intro i _
    simp only [mem_filter, mem_univ, true_and]
    have := i.isLt
    omega
  · intro i _ j _ hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp at this
    omega
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    refine ⟨⟨s.val - a, by omega⟩, mem_univ _, ?_⟩
    apply Fin.ext
    dsimp
    omega
  · intro i _
    rfl

theorem sum_treat_mul (d : Design) (f : Fin d.N → ℝ) :
    (∑ s, treatCoef d s * f s) =
      (∑ i : Fin d.m, f ⟨i.val, by have := d.sample_le; omega⟩) / (d.m : ℝ) := by
  have h : 0 + d.m ≤ d.N := by have := d.sample_le; omega
  simp only [treatCoef, ite_mul, zero_mul]
  have heq : (fun s : Fin d.N => if s.val < d.m then (1 / (d.m : ℝ)) * f s else 0) =
      (fun s => if 0 ≤ s.val ∧ s.val < 0 + d.m then (1 / (d.m : ℝ)) * f s else 0) := by
    funext s
    simp
  rw [heq, sum_positions h]
  simp only [zero_add]
  rw [← Finset.mul_sum]
  ring

theorem sum_ctrl_mul (d : Design) (f : Fin d.N → ℝ) :
    (∑ s, ctrlCoef d s * f s) =
      -(∑ i : Fin d.k, f ⟨d.m + i.val, by have := d.sample_le; omega⟩) / (d.k : ℝ) := by
  simp only [ctrlCoef, ite_mul, zero_mul]
  rw [sum_positions d.sample_le, ← Finset.mul_sum]
  ring

theorem n4_proof : N4 := by
  intro d
  have hm : (d.m : ℝ) ≠ 0 := by exact_mod_cast (show d.m ≠ 0 by have := d.treatment_min; omega)
  have hk : (d.k : ℝ) ≠ 0 := by exact_mod_cast (show d.k ≠ 0 by have := d.control_min; omega)
  have ht : ∑ s, treatCoef d s = 1 := by
    simpa [hm] using sum_treat_mul d (fun _ => 1)
  have hc : ∑ s, ctrlCoef d s = -1 := by
    simpa [hk] using sum_ctrl_mul d (fun _ => 1)
  refine ⟨ht, ?_, hc, ?_, ?_⟩
  · calc
      (∑ s, treatCoef d s ^ 2) = ∑ s, treatCoef d s * (1 / (d.m : ℝ)) := by
        apply sum_congr rfl
        intro s _
        unfold treatCoef
        split_ifs <;> ring
      _ = 1 / (d.m : ℝ) := by rw [← Finset.sum_mul, ht, one_mul]
  · calc
      (∑ s, ctrlCoef d s ^ 2) = ∑ s, ctrlCoef d s * (-(1 / (d.k : ℝ))) := by
        apply sum_congr rfl
        intro s _
        unfold ctrlCoef
        split_ifs <;> ring
      _ = 1 / (d.k : ℝ) := by rw [← Finset.sum_mul, hc]; ring
  · apply sum_eq_zero
    intro s _
    unfold treatCoef ctrlCoef
    split_ifs <;> first | omega | ring

end
end AronowAudit.P022.Wave1.RandomizationVariance
