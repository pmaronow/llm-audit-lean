import SAP.P020.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020.WH.W1.P.T17_L1

open scoped BigOperators
open SAP.P020

noncomputable section

theorem copied_arm_sum (P : ClusterPopulation) (h : ℕ)
    (s : CopyAssignments P h) (a : Bool) (v : Fin P.M → ℝ) :
    (∑ c ∈ W1CopiedArm P h a s, v c.2) =
      ∑ r, armSum P a v (s r).val := by
  classical
  simp only [W1CopiedArm, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [armSum, W1ArmSet, ← Finset.sum_filter]

theorem copied_arm_card (P : ClusterPopulation) (h : ℕ)
    (s : CopyAssignments P h) (a : Bool) :
    (W1CopiedArm P h a s).card =
      ∑ r, (W1ArmSet a (s r).val).card := by
  classical
  simp only [W1CopiedArm, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [W1ArmSet, ← Finset.card_eq_sum_ones, ← Finset.sum_filter]

theorem copied_population_size (P : ClusterPopulation) (h : ℕ) :
    W1CopiedN P h = h * populationSize P := by
  classical
  simp only [W1CopiedN, populationSize]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Finset.sum_const, nsmul_eq_mul]

theorem copied_total_sum (P : ClusterPopulation) (h : ℕ)
    (v : Fin P.M → ℝ) :
    (∑ c : Fin h × Fin P.M, v c.2) = (h : ℝ) * ∑ j, v j := by
  classical
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Finset.sum_const, nsmul_eq_mul]

end

end SAP.P020.WH.W1.P.T17_L1

theorem SAP.P020.WH.W1.T17_L1_proof : SAP.P020.WH.W1.T17_L1 := by
  intro P h hh s
  classical
  have hcardT : (W1CopiedArm P h true s).card = h * P.mt := by
    rw [SAP.P020.WH.W1.P.T17_L1.copied_arm_card]
    calc
      (∑ r, (W1ArmSet true (s r).val).card) = ∑ _r : Fin h, P.mt := by
        apply Finset.sum_congr rfl
        intro r hr
        have hvalid : (s r).val ∈ AronowAudit.P020.assignments (Bridge.toPopulation P) := by
          change (s r).val ∈ SAP.P020.assignments P
          exact (s r).property
        have hc := AronowAudit.P020.assignment_arm_counts
          (Bridge.toPopulation P) (s r).val hvalid
        simpa [Bridge.toPopulation, W1ArmSet] using hc.1
      _ = h * P.mt := by simp
  have hcardC : (W1CopiedArm P h false s).card = h * controlCount P := by
    rw [SAP.P020.WH.W1.P.T17_L1.copied_arm_card]
    calc
      (∑ r, (W1ArmSet false (s r).val).card) = ∑ _r : Fin h, controlCount P := by
        apply Finset.sum_congr rfl
        intro r hr
        have hvalid : (s r).val ∈ AronowAudit.P020.assignments (Bridge.toPopulation P) := by
          change (s r).val ∈ SAP.P020.assignments P
          exact (s r).property
        have hc := AronowAudit.P020.assignment_arm_counts
          (Bridge.toPopulation P) (s r).val hvalid
        change (Finset.univ \ (s r).val).card = P.M - P.mt
        exact hc.2
      _ = h * controlCount P := by simp
  have hN := SAP.P020.WH.W1.P.T17_L1.copied_population_size P h
  have htotal1 := SAP.P020.WH.W1.P.T17_L1.copied_total_sum P h P.y1
  have htotal0 := SAP.P020.WH.W1.P.T17_L1.copied_total_sum P h P.y0
  have hATE : W1CopiedATE P h = averageTreatmentEffect P := by
    unfold W1CopiedATE averageTreatmentEffect
    rw [hN, htotal1, htotal0]
    rw [Nat.cast_mul]
    have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
    have hpop : (populationSize P : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt
        (AronowAudit.P020.populationSize_pos (Bridge.toPopulation P)))
    field_simp
    <;> ring
  have hsize : ∀ a : Bool,
      (∑ c ∈ W1CopiedArm P h a s, (P.n c.2 : ℝ)) =
          ∑ r, armSize P a (s r).val ∧
        0 < ∑ r, armSize P a (s r).val := by
    have hposArm (r : Fin h) (a : Bool) : 0 < armSize P a (s r).val := by
      have hvalid : (s r).val ∈ AronowAudit.P020.assignments (Bridge.toPopulation P) := by
        change (s r).val ∈ SAP.P020.assignments P
        exact (s r).property
      have hc := AronowAudit.P020.assignment_arm_counts
        (Bridge.toPopulation P) (s r).val hvalid
      have hct : ((s r).val).card = P.mt := by
        simpa [Bridge.toPopulation] using hc.1
      have hcc : (controls (s r).val).card = controlCount P := by
        change (Finset.univ \ (s r).val).card = P.M - P.mt
        exact hc.2
      unfold armSize armSum
      cases a
      · have hne : (controls (s r).val).Nonempty :=
          Finset.card_pos.mp (by rw [hcc]; exact Nat.sub_pos_of_lt P.mt_lt)
        simp only [Bool.false_eq_true, ↓reduceIte]
        change 0 < ∑ j ∈ controls (s r).val, (P.n j : ℝ)
        exact Finset.sum_pos (fun j _ => by exact_mod_cast P.n_pos j) hne
      · have hne : ((s r).val).Nonempty :=
          Finset.card_pos.mp (by rw [hct]; exact P.mt_pos)
        simp only [↓reduceIte]
        change 0 < ∑ j ∈ (s r).val, (P.n j : ℝ)
        exact Finset.sum_pos (fun j _ => by exact_mod_cast P.n_pos j) hne
    intro a
    constructor
    · simpa [armSize] using
        SAP.P020.WH.W1.P.T17_L1.copied_arm_sum P h s a (fun j => (P.n j : ℝ))
    · have hne : (Finset.univ : Finset (Fin h)).Nonempty :=
        ⟨⟨0, hh⟩, Finset.mem_univ _⟩
      exact Finset.sum_pos (fun r _ => hposArm r a) hne
  have hest : W1CopiedEstimator P h s = copiedDifferenceInMeans P h s := by
    unfold W1CopiedEstimator copiedDifferenceInMeans
    rw [SAP.P020.WH.W1.P.T17_L1.copied_arm_sum P h s true P.y1,
      SAP.P020.WH.W1.P.T17_L1.copied_arm_sum P h s true (fun j => (P.n j : ℝ)),
      SAP.P020.WH.W1.P.T17_L1.copied_arm_sum P h s false P.y0,
      SAP.P020.WH.W1.P.T17_L1.copied_arm_sum P h s false (fun j => (P.n j : ℝ))]
    simp [armSize]
  exact ⟨by simp, hcardT, hcardC, hN, hATE, hsize, hest⟩
