import SAP.P037b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037b.WH.W2.P.T22_L1

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def blockLaw : AronowAudit.P037.FiniteDesign CutoffBlockW2 where
  weight := fun _ => (1 : ℝ) / 924
  nonneg := by intro b; norm_num
  total := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cutoffBlockCardW2]
    norm_num

noncomputable def blocksLaw : AronowAudit.P037.FiniteDesign (Fin 4 → CutoffBlockW2) :=
  AronowAudit.P037.productDesign (fun _ : Fin 4 => blockLaw)

lemma localLabel_ne_zero (self peers refs s : Finset (Fin 12)) :
    localTreatedLabel self peers refs s ≠ 0 := by
  simp only [localTreatedLabel]
  split_ifs <;> norm_num

lemma blockLabelMean (self peers refs : Finset (Fin 12)) (k : Fin 5) :
    AronowAudit.P037.designMean blockLaw
      (fun b => if localTreatedLabel self peers refs b.val = k then (1 : ℝ) else 0) =
      (((seedSubsets 12 6).filter
        (fun s => localTreatedLabel self peers refs s = k)).card : ℝ) / 924 := by
  classical
  let e : CutoffBlockW2 ≃ {s : Finset (Fin 12) // s ∈ seedSubsets 12 6} := {
    toFun := fun b => ⟨b.val, by
      change b.val ∈ Finset.univ.powersetCard 6
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, b.property⟩⟩
    invFun := fun s => ⟨s.val, by
      have hs : s.val ∈ Finset.univ.powersetCard 6 := by
        simpa [seedSubsets] using s.property
      exact (Finset.mem_powersetCard.mp hs).2⟩
    left_inv := by intro b; cases b; rfl
    right_inv := by intro s; cases s; rfl }
  unfold AronowAudit.P037.designMean blockLaw
  change (∑ b : CutoffBlockW2, (1 / 924 : ℝ) *
    (if localTreatedLabel self peers refs b.val = k then 1 else 0)) = _
  let f : CutoffBlockW2 → ℝ := fun b =>
    (1 / 924 : ℝ) * (if localTreatedLabel self peers refs b.val = k then 1 else 0)
  let g : {s : Finset (Fin 12) // s ∈ seedSubsets 12 6} → ℝ := fun s =>
    (1 / 924 : ℝ) * (if localTreatedLabel self peers refs s.val = k then 1 else 0)
  have heq : (∑ b : CutoffBlockW2, f b) = ∑ s, g s := by
    apply Fintype.sum_equiv e f g
    intro b
    rfl
  rw [heq]
  have hsub : (∑ s : {s : Finset (Fin 12) // s ∈ seedSubsets 12 6}, g s) =
      ∑ s ∈ seedSubsets 12 6,
        (1 / 924 : ℝ) * (if localTreatedLabel self peers refs s = k then 1 else 0) := by
    symm
    exact Finset.sum_subtype (seedSubsets 12 6) (fun _ => Iff.rfl)
      (fun s => (1 / 924 : ℝ) * (if localTreatedLabel self peers refs s = k then 1 else 0))
  rw [hsub]
  rw [← Finset.mul_sum]
  have hcount : (((seedSubsets 12 6).filter
      (fun s => localTreatedLabel self peers refs s = k)).card : ℝ) =
      ∑ s ∈ seedSubsets 12 6,
        (if localTreatedLabel self peers refs s = k then (1 : ℝ) else 0) := by
    exact_mod_cast (Finset.card_filter
      (fun s => localTreatedLabel self peers refs s = k) (seedSubsets 12 6))
  rw [← hcount]
  ring

lemma labelProb (self peers refs : Finset (Fin 12)) (k : Fin 5) :
    eventProbability cutoffDesignW2 (fun z => cutoffExposureW2 self peers refs z = k) =
      localExposureProbability5 12 6 self peers refs k := by
  classical
  have hmass (z : CutoffAssignmentsW2) : cutoffDesignW2.mass z =
      (1 / 2 : ℝ) * ∏ j : Fin 4, blockLaw.weight (z.2 j) := by
    simp [cutoffDesignW2, blockLaw, Finset.prod_const, Fintype.card_fin]
    norm_num
  have hfalse (k : Fin 5) : AronowAudit.P037.designMean blocksLaw
      (fun _ : Fin 4 → CutoffBlockW2 => if (0 : Fin 5) = k then (1 : ℝ) else 0) =
      if (0 : Fin 5) = k then (1 : ℝ) else 0 := by
    exact AronowAudit.P037.designMean_const blocksLaw _
  have htrue : AronowAudit.P037.designMean blocksLaw
      (fun w => if localTreatedLabel self peers refs (w 0).val = k then (1 : ℝ) else 0) =
      AronowAudit.P037.designMean blockLaw
        (fun b => if localTreatedLabel self peers refs b.val = k then (1 : ℝ) else 0) := by
    simpa [blocksLaw] using
      (AronowAudit.P037.product_design_coordinate_mean
        (fun _ : Fin 4 => blockLaw) 0
        (fun b => if localTreatedLabel self peers refs b.val = k then (1 : ℝ) else 0))
  have hcalc : eventProbability cutoffDesignW2
      (fun z => cutoffExposureW2 self peers refs z = k) =
      (1 / 2 : ℝ) * ((if (0 : Fin 5) = k then (1 : ℝ) else 0) +
        AronowAudit.P037.designMean blockLaw
          (fun b => if localTreatedLabel self peers refs b.val = k then (1 : ℝ) else 0)) := by
    unfold eventProbability
    simp_rw [hmass]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [cutoffExposureW2, Bool.false_eq_true, if_true, if_false]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    change (1 / 2 : ℝ) *
        AronowAudit.P037.designMean blocksLaw
          (fun w => if localTreatedLabel self peers refs (w 0).val = k then 1 else 0) +
      (1 / 2 : ℝ) * AronowAudit.P037.designMean blocksLaw
          (fun _ : Fin 4 → CutoffBlockW2 => if (0 : Fin 5) = k then 1 else 0) = _
    rw [htrue, hfalse k]
    ring
  by_cases hk : k = 0
  · subst k
    rw [hcalc]
    simp only [eq_self_iff_true, if_true]
    have hz : AronowAudit.P037.designMean blockLaw
        (fun b => if localTreatedLabel self peers refs b.val = 0 then (1 : ℝ) else 0) = 0 := by
      unfold AronowAudit.P037.designMean blockLaw
      apply Finset.sum_eq_zero
      intro b hb
      simp [localLabel_ne_zero]
    rw [hz]
    simp [localExposureProbability5]
  · rw [hcalc]
    have hzero : (0 : Fin 5) ≠ k := Ne.symm hk
    simp only [hzero, if_false, zero_add]
    rw [blockLabelMean]
    simp [localExposureProbability5, hk, Nat.choose]
    field_simp <;> ring

end SAP.P037b.WH.W2.P.T22_L1

theorem SAP.P037b.WH.W2.T22_L1_proof : SAP.P037b.WH.W2.T22_L1 := by
  intro self peers refs k
  exact SAP.P037b.WH.W2.P.T22_L1.labelProb self peers refs k
