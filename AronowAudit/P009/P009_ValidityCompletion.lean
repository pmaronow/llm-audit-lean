import AronowAudit.P009.P009_Audit
import AronowAudit.P004.P004_FiniteGraphCompletion

namespace AronowAudit.P009.ValidityCompletion
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

 theorem outcome_depends {n : ℕ} (E : Experiment n) (j : Fin n) :
    DependsOn (E.outcome j) {i | Interferes E i j} := by
  classical
  apply AronowAudit.P004.GraphCompletion.depends_of_update
  intro z i hi b
  by_contra he
  apply hi
  exact Or.inr ⟨Function.update z i b,z,
    fun ℓ hℓ => Function.update_of_ne hℓ _ _,he⟩

theorem effect_depends {n : ℕ} (E : Experiment n) (j : Fin n) :
    DependsOn (effect E j) {i | Interferes E i j} := by
  classical
  intro z z' hz
  have hout := outcome_depends E j
  have hp (b : Bool) : potential E j b z=potential E j b z' := by
    apply hout
    intro i hi
    by_cases hij : i=j
    · subst i; simp
    · simp only [Function.update_of_ne hij]
      exact hz i hi
  exact congrArg₂ (fun a b : ℝ => a-b) (hp true) (hp false)

theorem indicator_nonneg {n : ℕ} (E : Experiment n) (i j : Fin n) : 0≤I E i j := by
  classical
  unfold I
  split_ifs <;> norm_num

theorem outgoing_nonneg {n : ℕ} (E : Experiment n) (i : Fin n) : 0≤outgoing E i :=
  Finset.sum_nonneg (fun j _ => indicator_nonneg E i j)

theorem unit_hamming {n : ℕ} (E : Experiment n) (K : ℝ) (hK : BoundedEffects E K)
    (z z' : Assignment n) (j : Fin n) :
    |effect E j z-effect E j z'| ≤ 2*K*(∑ i, |bit (z i)-bit (z' i)| *I E i j) := by
  classical
  have hk : 0≤K := (abs_nonneg _).trans (hK j z)
  have hnn (i : Fin n) : 0≤|bit (z i)-bit (z' i)| *I E i j :=
    mul_nonneg (abs_nonneg _) (indicator_nonneg E i j)
  by_cases he : effect E j z=effect E j z'
  · rw [he,sub_self,abs_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hnn i))
  · have hex : ∃ i,Interferes E i j ∧ z i≠z' i := by
      by_contra hno
      push_neg at hno
      exact he ((effect_depends E j) (fun i hi => hno i hi))
    obtain ⟨i,hi,hd⟩ := hex
    have hbit : |bit (z i)-bit (z' i)|=1 := by
      cases hz : z i <;> cases hz' : z' i <;> simp_all [bit]
    have hs := Finset.single_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin n))) => hnn i)
      (Finset.mem_univ i)
    rw [hbit,show I E i j=1 from if_pos hi,one_mul] at hs
    calc
      _ ≤ |effect E j z|+|effect E j z'| := abs_sub _ _
      _ ≤ K+K := add_le_add (hK j z) (hK j z')
      _ = 2*K := by ring
      _ ≤ 2*K*(∑ i,|bit (z i)-bit (z' i)| *I E i j) :=
        le_mul_of_one_le_right (by positivity) hs

theorem assignment_ATE_hamming_completed {n : ℕ} (hn : 0<n) (E : Experiment n)
    (K : ℝ) (hK : BoundedEffects E K) (z z' : Assignment n) :
    |ateAt E z-ateAt E z'| ≤ 2*K/(n:ℝ)*
      (∑ i, |bit (z i)-bit (z' i)| *outgoing E i) := by
  classical
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hs : (∑ j,2*K*(∑ i,|bit (z i)-bit (z' i)| *I E i j)) =
      2*K*(∑ i,|bit (z i)-bit (z' i)| *outgoing E i) := by
    rw [←Finset.mul_sum,Finset.sum_comm]
    simp only [←Finset.mul_sum,outgoing]
  calc
    _ = |∑ j,(effect E j z-effect E j z')|/(n:ℝ) := by
      rw [ateAt,ateAt,←sub_div,←Finset.sum_sub_distrib,abs_div,abs_of_pos hnR]
    _ ≤ (∑ j,|effect E j z-effect E j z'|)/(n:ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hnR.le
    _ ≤ (∑ j,2*K*(∑ i,|bit (z i)-bit (z' i)| *I E i j))/(n:ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _ => unit_hamming E K hK z z' j)) hnR.le
    _ = _ := by rw [hs]; ring

end
end AronowAudit.P009.ValidityCompletion

namespace AronowAudit.P009
/-- T38 finite step before Hölder (Supplement A p. 40): toggling coordinates
gives the weighted Hamming bound with the actual outgoing interference counts. -/
theorem assignment_ATE_hamming {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (K : ℝ) (hK : BoundedEffects E K) (z z' : Assignment n) :
    |ateAt E z-ateAt E z'| ≤ 2*K/(n:ℝ)*
      (∑ i, |bit (z i)-bit (z' i)| *outgoing E i) := by
  exact ValidityCompletion.assignment_ATE_hamming_completed hn E K hK z z'
end AronowAudit.P009

