import SAP.P045a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

open scoped BigOperators Classical
open Finset

namespace SAP.P045a.WH.W1.P.T3_L1

open SAP.P045a.WH.W1

private theorem firstStage_card : (firstStageSets 6 3).card = 20 := by
  rw [firstStageSets, Finset.card_powersetCard]
  norm_num [Nat.choose]

private theorem local_card (k : ℕ) (hk : k = 1 ∨ k = 2) :
    (AronowAudit.P045.fixedAssignments 3 k).card = 3 := by
  rcases hk with rfl | rfl
  · rw [AronowAudit.P045.fixed_three_supports.1]
    decide
  · rw [AronowAudit.P045.fixed_three_supports.2]
    decide

private abbrev ToyLocalSupport (H : Finset (Fin 6)) :=
  {u : Fin 6 → AronowAudit.P045.Assignment 3 //
    ∀ g, u g ∈ AronowAudit.P045.fixedAssignments 3 (if g ∈ H then 2 else 1)}

private abbrev ToyFirstStage := {H : Finset (Fin 6) // H ∈ firstStageSets 6 3}

private def toySupportEquiv :
    {w : W1ToyOutcome // w ∈ w1ToySupport} ≃ Σ H : ToyFirstStage, ToyLocalSupport H.val where
  toFun w :=
    ⟨⟨w.val.1, (Finset.mem_filter.mp w.property).2.1⟩,
      ⟨w.val.2, (Finset.mem_filter.mp w.property).2.2⟩⟩
  invFun x :=
    ⟨(x.1.val, x.2.val), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨x.1.property, x.2.property⟩⟩⟩
  left_inv := by
    intro w
    cases w
    rfl
  right_inv := by
    intro x
    cases x
    rfl

private theorem toy_support_card : w1ToySupport.card = 14580 := by
  classical
  calc
    w1ToySupport.card = Fintype.card {w : W1ToyOutcome // w ∈ w1ToySupport} := by simp
    _ = Fintype.card (Σ H : ToyFirstStage, ToyLocalSupport H.val) :=
      Fintype.card_congr toySupportEquiv
    _ = ∑ H : ToyFirstStage, Fintype.card (ToyLocalSupport H.val) := by simp
    _ = ∑ H : ToyFirstStage, 729 := by
      apply Finset.sum_congr rfl
      intro H hH
      let S : Fin 6 → Finset (AronowAudit.P045.Assignment 3) :=
        fun g => AronowAudit.P045.fixedAssignments 3 (if g ∈ H.val then 2 else 1)
      have he : ToyLocalSupport H.val ≃ {u : Fin 6 → AronowAudit.P045.Assignment 3 // u ∈ Fintype.piFinset S} := by
        refine Equiv.subtypeEquiv (Equiv.refl _) ?_
        intro u
        simp [S]
      rw [Fintype.card_congr he]
      rw [Fintype.card_coe, Fintype.card_piFinset]
      have hc (g : Fin 6) : (S g).card = 3 := by
        apply local_card
        by_cases hg : g ∈ H.val <;> simp [hg]
      simp_rw [hc]
      norm_num [Finset.card_univ]
    _ = 14580 := by
      change (Fintype.card ToyFirstStage : ℕ) * 729 = 14580
      norm_num [ToyFirstStage, firstStageSets, Finset.card_powersetCard, Nat.choose]

private theorem local_cr_mass (k : ℕ) (hk : k = 1 ∨ k = 2) (z : Assignment 3) :
    crMass 3 k z = if z ∈ fixedAssignments 3 k then 1/3 else 0 := by
  unfold crMass
  have hcard : (fixedAssignments 3 k).card = 3 := local_card k hk
  rw [hcard]
  norm_num

private theorem toy_support_iff (w : W1ToyOutcome) :
    w ∈ w1ToySupport ↔ w.1 ∈ firstStageSets 6 3 ∧
      ∀ g, w.2 g ∈ fixedAssignments 3 (if g ∈ w.1 then 2 else 1) := by
  simp [w1ToySupport]

private theorem toy_mass_support_formula (w : W1ToyOutcome) :
    w1ToyMass w = if w ∈ w1ToySupport then (1:ℝ)/14580 else 0 := by
  classical
  by_cases hH : w.1 ∈ firstStageSets 6 3
  · by_cases hLoc : ∀ g, w.2 g ∈ fixedAssignments 3 (if g ∈ w.1 then 2 else 1)
    · have hs : w ∈ w1ToySupport := (toy_support_iff w).2 ⟨hH, hLoc⟩
      have hp : (∏ g, crMass 3 (if g ∈ w.1 then 2 else 1) (w.2 g)) = (1/3:ℝ)^6 := by
        simp_rw [fun g => local_cr_mass (if g ∈ w.1 then 2 else 1) (by
          by_cases hg : g ∈ w.1 <;> simp [hg]) (w.2 g)]
        simp [hLoc]
      simp [w1ToyMass, hH, hs]
      rw [firstStage_card, hp]
      norm_num
    · have hs : w ∉ w1ToySupport := by
        intro hw
        exact hLoc ((toy_support_iff w).1 hw).2
      obtain ⟨g, hg⟩ := not_forall.mp hLoc
      have hz : crMass 3 (if g ∈ w.1 then 2 else 1) (w.2 g) = 0 := by
        rw [local_cr_mass (if g ∈ w.1 then 2 else 1) (by
          by_cases hmem : g ∈ w.1 <;> simp [hmem])]
        simp [hg]
      have hp : (∏ j, crMass 3 (if j ∈ w.1 then 2 else 1) (w.2 j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ g) hz
      simp [w1ToyMass, hH, hs, hp]
  · have hs : w ∉ w1ToySupport := by
      intro hw
      exact hH ((toy_support_iff w).1 hw).1
    simp [w1ToyMass, hH, hs]

end SAP.P045a.WH.W1.P.T3_L1

open SAP.P045a.WH.W1.P.T3_L1

theorem SAP.P045a.WH.W1.T3_L1_proof : SAP.P045a.WH.W1.T3_L1 := by
  refine ⟨toy_support_card, ?_, ?_, ?_⟩
  · intro w
    rw [toy_mass_support_formula]
    split_ifs <;> norm_num
  · calc
      (∑ w : W1ToyOutcome, w1ToyMass w) =
          ∑ w : W1ToyOutcome, if w ∈ w1ToySupport then (1:ℝ)/14580 else 0 := by
        apply Finset.sum_congr rfl
        intro w hw
        exact toy_mass_support_formula w
      _ = ∑ w ∈ w1ToySupport, (1:ℝ)/14580 := by
        rw [Finset.sum_ite]
        simp only [Finset.sum_const_zero, add_zero, Finset.filter_univ_mem]
      _ = 1 := by rw [Finset.sum_const, nsmul_eq_mul, toy_support_card]; norm_num
  · exact toy_mass_support_formula

