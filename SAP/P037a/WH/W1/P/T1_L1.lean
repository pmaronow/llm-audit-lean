import SAP.P037a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W1.P.T1_L1

open SAP.P037a
open scoped BigOperators Classical

private theorem stratum_one_zero (j : Fin 4) (hj : 2 ≤ j.val) :
    AronowAudit.P037.stratumCountMass 1 j = 0 := by
  fin_cases j
  · norm_num at hj
  · norm_num at hj
  · norm_num [AronowAudit.P037.stratumCountMass, Nat.choose]
  · norm_num [AronowAudit.P037.stratumCountMass, Nat.choose]

private theorem stratum_three_pos (j : Fin 4) :
    0 < AronowAudit.P037.stratumCountMass 3 j := by
  fin_cases j <;> norm_num [AronowAudit.P037.stratumCountMass,
    Nat.choose]

private theorem school_count_one_zero (k : Fin 13) (hk : 4 < k.val) :
    AronowAudit.P037.schoolCountMass 1 k = 0 := by
  classical
  unfold AronowAudit.P037.schoolCountMass
  apply Finset.sum_eq_zero
  intro c hc
  by_cases hsum : (∑ s : Fin 4, (c s).val) = k.val
  · rw [if_pos hsum]
    obtain ⟨s, hs⟩ : ∃ s : Fin 4, 2 ≤ (c s).val := by
      by_contra hn
      push_neg at hn
      have hle : ∀ s : Fin 4, (c s).val ≤ 1 := by
        intro s
        have hs' := hn s
        omega
      have htotal' : (∑ s : Fin 4, (c s).val) ≤ 4 := by
        calc
          (∑ s : Fin 4, (c s).val) ≤ ∑ _s : Fin 4, (1:ℕ) :=
            Finset.sum_le_sum (fun s hs => hle s)
          _ = 4 := by norm_num [Fin.sum_univ_four]
      omega
    have hz := stratum_one_zero (c s) hs
    exact Finset.prod_eq_zero (Finset.mem_univ s) hz
  · simp [hsum]

private theorem school_count_three_pos (k : Fin 13) :
    0 < AronowAudit.P037.schoolCountMass 3 k := by
  classical
  let c : Fin 4 → Fin 4 := fun s => ⟨min 3 (k.val - 3*s.val), by omega⟩
  have hcount : (∑ s : Fin 4, (c s).val) = k.val := by
    fin_cases k <;> norm_num [c, Fin.sum_univ_four]
  have hprod : 0 < ∏ s : Fin 4, AronowAudit.P037.stratumCountMass 3 (c s) := by
    apply Finset.prod_pos
    intro s hs
    exact stratum_three_pos (c s)
  have hle : (∏ s : Fin 4, AronowAudit.P037.stratumCountMass 3 (c s)) ≤
      AronowAudit.P037.schoolCountMass 3 k := by
    unfold AronowAudit.P037.schoolCountMass
    have hh := Finset.single_le_sum
      (f := fun v : Fin 4 → Fin 4 =>
        if (∑ s : Fin 4, (v s).val) = k.val then
          ∏ s : Fin 4, AronowAudit.P037.stratumCountMass 3 (v s) else 0)
      (s := Finset.univ) (a := c) (fun v _ => by
        split_ifs
        · exact Finset.prod_nonneg (fun s _ => AronowAudit.P037.stratum_count_nonneg 3 (v s))
        · exact le_rfl) (Finset.mem_univ c)
    simpa only [hcount, ite_true] using hh
  exact lt_of_lt_of_le hprod hle

private theorem countMass_one_support (k : Fin 13) :
    0 < countMass 1 k ↔ k.val ≤ 4 := by
  constructor
  · intro hp
    by_contra hk
    have hz : countMass 1 k = 0 := by
      rw [SAP.P037a.Bridge.countMass_eq]
      exact school_count_one_zero k (by omega)
    rw [hz] at hp
    norm_num at hp
  · intro hk
    rw [SAP.P037a.Bridge.countMass_eq]
    exact AronowAudit.P037.school_count_common_support 1 (Or.inl rfl) k hk

private theorem countMass_three_support (k : Fin 13) : 0 < countMass 3 k := by
  rw [SAP.P037a.Bridge.countMass_eq]
  exact school_count_three_pos k

private theorem countMass_nonneg_referents (i : Fin 4) (k : Fin 13) :
    0 ≤ countMass (stratumReferents i) k := by
  rw [SAP.P037a.Bridge.countMass_eq]
  exact AronowAudit.P037.school_count_nonneg _ _

private theorem countMass_referents_pos (i : Fin 4) (k : Fin 13) :
    0 < countMass (stratumReferents i) k ↔ i.val ≥ 2 ∨ k.val ≤ 4 := by
  fin_cases i <;> simp [stratumReferents, countMass_one_support, countMass_three_support]

private theorem assignmentMass_pos_iff (w : CompositionAssignment) :
    0 < assignmentMass w ↔
      ((treatmentPair w.1).1.val ≥ 2 ∨ w.2.1.val ≤ 4) ∧
      ((treatmentPair w.1).2.val ≥ 2 ∨ w.2.2.val ≤ 4) := by
  unfold assignmentMass
  let a := countMass (stratumReferents (treatmentPair w.1).1) w.2.1
  let b := countMass (stratumReferents (treatmentPair w.1).2) w.2.2
  have ha : 0 ≤ a := countMass_nonneg_referents _ _
  have hb : 0 ≤ b := countMass_nonneg_referents _ _
  change 0 < (1/6:ℝ) * a * b ↔ _
  constructor
  · intro hp
    have hapos : 0 < a := by
      by_contra hn
      have ha0 : a = 0 := le_antisymm (le_of_not_gt hn) ha
      rw [ha0] at hp
      norm_num at hp
    have hbpos : 0 < b := by
      by_contra hn
      have hb0 : b = 0 := le_antisymm (le_of_not_gt hn) hb
      rw [hb0] at hp
      norm_num at hp
    exact ⟨(countMass_referents_pos _ _).mp hapos,
      (countMass_referents_pos _ _).mp hbpos⟩
  · rintro ⟨ha', hb'⟩
    exact mul_pos (mul_pos (by norm_num) ((countMass_referents_pos _ _).mpr ha'))
      ((countMass_referents_pos _ _).mpr hb')

end SAP.P037a.WH.W1.P.T1_L1

theorem SAP.P037a.WH.W1.T1_L1_proof : SAP.P037a.WH.W1.T1_L1 := by
  unfold SAP.P037a.WH.W1.T1_L1 SAP.P037a.compositionFullSupport
  refine ⟨?_, ?_, ?_⟩
  · exact SAP.P037a.WH.W1.P.T1_L1.countMass_one_support
  · exact SAP.P037a.WH.W1.P.T1_L1.countMass_three_support
  · simp_rw [SAP.P037a.WH.W1.P.T1_L1.assignmentMass_pos_iff]
    simp only [Finset.card_filter, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    norm_num [treatmentPair]

