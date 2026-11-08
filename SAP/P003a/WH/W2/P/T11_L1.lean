import SAP.P003a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W2.P.T11_L1

open scoped BigOperators

lemma finiteTail_antitone {Ω : Type*} [Fintype Ω] (w D : Ω → ℝ)
    (hw : ∀ i, 0 ≤ w i) {x y : ℝ} (hxy : x ≤ y) :
    SAP.P003a.finiteTail w D y ≤ SAP.P003a.finiteTail w D x := by
  unfold SAP.P003a.finiteTail
  apply Finset.sum_le_sum
  intro i hi
  by_cases hy : y ≤ D i
  · have hx : x ≤ D i := le_trans hxy hy
    simp [hy, hx]
  · simp only [if_neg hy]
    by_cases hx : x ≤ D i
    · simp [hx, hw i]
    · simp [hx]

end SAP.P003a.WH.W2.P.T11_L1

theorem SAP.P003a.WH.W2.T11_L1_proof : SAP.P003a.WH.W2.T11_L1 := by
  classical
  intro Ω inst w D hw hn α hα hα1
  have huni : (Finset.univ : Finset Ω).Nonempty := by
    by_contra h
    have hempty : (Finset.univ : Finset Ω) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    rw [hempty, Finset.sum_empty] at hn
    norm_num at hn
  letI : Nonempty Ω := ⟨Classical.choose huni⟩
  obtain ⟨m, hm, hmin⟩ := Finset.univ.exists_min_image D Finset.univ_nonempty
  have hmle : ∀ j, D m ≤ D j := by
    intro j
    exact hmin j (Finset.mem_univ j)
  have htail_min : SAP.P003a.finiteTail w D (D m) = 1 := by
    unfold SAP.P003a.finiteTail
    simp_rw [if_pos (hmle _)]
    exact hn
  let S := Finset.univ.filter (fun i => α ≤ SAP.P003a.finiteTail w D (D i))
  have hS : S.Nonempty := by
    refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [htail_min]
    exact le_of_lt hα1
  obtain ⟨d, hdS, hmax⟩ := S.exists_max_image (fun i => D i) hS
  have hdα : α ≤ SAP.P003a.finiteTail w D (D d) :=
    (Finset.mem_filter.mp hdS).2
  have hdom : ∀ j, α ≤ SAP.P003a.finiteTail w D (D j) → D j ≤ D d := by
    intro j hj
    exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  refine ⟨d, hdα, hdom, ?_⟩
  intro x
  constructor
  · intro hx
    by_contra hnot
    have hxd : x ≤ D d := le_of_not_gt hnot
    have hmono := SAP.P003a.WH.W2.P.T11_L1.finiteTail_antitone w D (fun i => (hw i).le) hxd
    unfold SAP.P003a.finiteTail at *
    linarith
  · intro hdx
    by_cases hE : (Finset.univ.filter (fun i => x ≤ D i) : Finset Ω).Nonempty
    · let E := Finset.univ.filter (fun i => x ≤ D i)
      obtain ⟨e, heE, hemin⟩ := E.exists_min_image D hE
      have hxe : x ≤ D e := (Finset.mem_filter.mp heE).2
      have htail_eq : SAP.P003a.finiteTail w D x =
          SAP.P003a.finiteTail w D (D e) := by
        unfold SAP.P003a.finiteTail
        apply Finset.sum_congr rfl
        intro j hj
        have hcond : (x ≤ D j) ↔ (D e ≤ D j) := by
          constructor
          · intro hjx
            exact hemin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjx⟩)
          · intro hej
            exact le_trans hxe hej
        simp only [hcond]
      by_contra hnot
      have hαx : α ≤ SAP.P003a.finiteTail w D x := le_of_not_gt hnot
      have hαe : α ≤ SAP.P003a.finiteTail w D (D e) := by
        rw [← htail_eq]
        exact hαx
      have hed := hdom e hαe
      have hde : D d < D e := lt_of_lt_of_le hdx hxe
      exact (not_lt_of_ge hed) hde
    · have hnone : ∀ i, ¬ x ≤ D i := by
        intro i hxi
        exact hE ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩⟩
      have hzero : SAP.P003a.finiteTail w D x = 0 := by
        unfold SAP.P003a.finiteTail
        simp [hnone]
      rw [hzero]
      exact hα

