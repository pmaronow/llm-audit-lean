import SAP.P008a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a.WH.W1.P.T7_L4

open scoped BigOperators Classical

lemma radius_pos (j : Fin 4) : 0 < wholeRiskRadius j := by
  fin_cases j <;> norm_num [wholeRiskRadius]

lemma radius_le (j : Fin 4) : wholeRiskRadius j ≤ 5 / 2 := by
  fin_cases j <;> norm_num [wholeRiskRadius]

lemma radius_injective : Function.Injective wholeRiskRadius := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    first | rfl | norm_num [wholeRiskRadius] at hab

end SAP.P008a.WH.W1.P.T7_L4

theorem SAP.P008a.WH.W1.T7_L4_proof : SAP.P008a.WH.W1.T7_L4 := by
  intro hinj hdist
  have hfieldcard : wholeRiskField.card = 640004 := by
    change (Finset.univ.image wholeRiskEmbedding).card = 640004
    rw [Finset.card_image_of_injective Finset.univ hinj]
    simp [WholeRiskLabel, WholeRiskTriple, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin]
  refine ⟨hfieldcard, ?_⟩
  intro i j
  have hpointinj : Function.Injective (wholeRiskPoint i j) := by
    intro k₁ k₂ heq
    have he : wholeRiskEmbedding (Sum.inr (i, j, k₁)) =
        wholeRiskEmbedding (Sum.inr (i, j, k₂)) := by
      simpa [wholeRiskEmbedding] using heq
    have hlabels := hinj he
    have htriple : (i, j, k₁) = (i, j, k₂) := Sum.inr.inj hlabels
    exact congrArg (fun t : WholeRiskTriple => t.2.2) htriple
  have hset : wholeRiskCircle i j = Finset.univ.image (wholeRiskPoint i j) := by
    ext x
    constructor
    · intro hx
      simp only [wholeRiskCircle, Finset.mem_filter] at hx
      rcases hx with ⟨hxfield, hdistx⟩
      change x ∈ Finset.univ.image wholeRiskEmbedding at hxfield
      rcases Finset.mem_image.mp hxfield with ⟨l, -, hl⟩
      subst x
      cases l with
      | inl c =>
          by_cases hc : c = i
          · subst c
            simp [wholeRiskEmbedding] at hdistx
            linarith [SAP.P008a.WH.W1.P.T7_L4.radius_pos j]
          · have hsep := hdist.2.1 i c (Ne.symm hc)
            have hjle := SAP.P008a.WH.W1.P.T7_L4.radius_le j
            simp [wholeRiskEmbedding] at hdistx
            linarith
      | inr t =>
          rcases t with ⟨c, r, k⟩
          have hdistx : dist (wholeRiskCentre i) (wholeRiskPoint c r k) =
              wholeRiskRadius j := by
            simpa [wholeRiskEmbedding] using hdistx
          by_cases hc : c = i
          · subst c
            have hr : wholeRiskRadius r = wholeRiskRadius j := by
              calc
                wholeRiskRadius r = dist (wholeRiskCentre i) (wholeRiskPoint i r k) :=
                  (hdist.1 i r k).symm
                _ = wholeRiskRadius j := hdistx
            have hrj : r = j := SAP.P008a.WH.W1.P.T7_L4.radius_injective hr
            subst r
            exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
          · have hclose : dist (wholeRiskCentre c) (wholeRiskPoint c r k) ≤ 5 / 2 := by
              rw [hdist.1 c r k]
              exact SAP.P008a.WH.W1.P.T7_L4.radius_le r
            have hfar := hdist.2.2 c i hc (wholeRiskPoint c r k) hclose
            linarith [hdistx, SAP.P008a.WH.W1.P.T7_L4.radius_le j]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨k, -, hkx⟩
      subst x
      simp only [wholeRiskCircle, Finset.mem_filter]
      constructor
      · change wholeRiskPoint i j k ∈ Finset.univ.image wholeRiskEmbedding
        exact Finset.mem_image.mpr
          ⟨Sum.inr (i, j, k), Finset.mem_univ _, by simp [wholeRiskEmbedding]⟩
      · exact hdist.1 i j k
  refine ⟨hset, ?_⟩
  rw [hset]
  rw [Finset.card_image_of_injective Finset.univ hpointinj]
  simp
