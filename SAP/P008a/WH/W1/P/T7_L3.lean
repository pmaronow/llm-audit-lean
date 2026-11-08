import SAP.P008a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a.WH.W1.P.T7_L3

open SAP.P008a.WH.W1

lemma radius_pos (j : Fin 4) : 0 < wholeRiskRadius j := by
  fin_cases j <;> norm_num [wholeRiskRadius]

lemma radius_le (j : Fin 4) : wholeRiskRadius j ≤ (5 / 2 : ℝ) := by
  fin_cases j <;> norm_num [wholeRiskRadius]

lemma radius_injective : Function.Injective wholeRiskRadius := by
  intro j m h
  fin_cases j <;> fin_cases m <;> first | rfl | norm_num [wholeRiskRadius] at h

end SAP.P008a.WH.W1.P.T7_L3

open SAP.P008a.WH.W1
open SAP.P008a.WH.W1.P.T7_L3

theorem SAP.P008a.WH.W1.T7_L3_proof : SAP.P008a.WH.W1.T7_L3 := by
  intro hAlg hDist x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl l =>
          simp only [wholeRiskEmbedding] at hxy
          by_cases hil : i = l
          · subst l
            rfl
          · have hzero : dist (wholeRiskCentre i) (wholeRiskCentre l) = 0 := by
              rw [hxy]
              exact dist_self _
            have hsep := hDist.2.1 i l hil
            rw [hzero] at hsep
            norm_num at hsep
      | inr t =>
          simp only [wholeRiskEmbedding] at hxy
          by_cases hit : i = t.1
          · subst i
            have hzero : dist (wholeRiskCentre t.1) (wholeRiskPoint t.1 t.2.1 t.2.2) = 0 := by
              rw [hxy]
              exact dist_self _
            rw [hDist.1 t.1 t.2.1 t.2.2] at hzero
            linarith [radius_pos t.2.1]
          · have hfar := hDist.2.2 t.1 i (Ne.symm hit)
              (wholeRiskPoint t.1 t.2.1 t.2.2)
              (by rw [hDist.1 t.1 t.2.1 t.2.2]; exact radius_le t.2.1)
            rw [← hxy] at hfar
            norm_num at hfar
  | inr t =>
      cases y with
      | inl i =>
          simp only [wholeRiskEmbedding] at hxy
          by_cases hit : i = t.1
          · subst i
            have hzero : dist (wholeRiskCentre t.1) (wholeRiskPoint t.1 t.2.1 t.2.2) = 0 := by
              rw [← hxy]
              exact dist_self _
            rw [hDist.1 t.1 t.2.1 t.2.2] at hzero
            linarith [radius_pos t.2.1]
          · have hfar := hDist.2.2 t.1 i (Ne.symm hit)
              (wholeRiskPoint t.1 t.2.1 t.2.2)
              (by rw [hDist.1 t.1 t.2.1 t.2.2]; exact radius_le t.2.1)
            rw [hxy] at hfar
            norm_num at hfar
      | inr s =>
          simp only [wholeRiskEmbedding] at hxy
          rcases t with ⟨i, j, k⟩
          rcases s with ⟨l, m, n⟩
          by_cases hclusters : i = l
          · subst l
            have hradius : wholeRiskRadius j = wholeRiskRadius m := by
              calc
                wholeRiskRadius j = dist (wholeRiskCentre i) (wholeRiskPoint i j k) :=
                  (hDist.1 i j k).symm
                _ = dist (wholeRiskCentre i) (wholeRiskPoint i m n) :=
                  congrArg (dist (wholeRiskCentre i)) hxy
                _ = wholeRiskRadius m := hDist.1 i m n
            have hj : j = m := radius_injective hradius
            subst m
            have hsmul : wholeRiskRadius j • wholeRiskDirection k =
                wholeRiskRadius j • wholeRiskDirection n := by
              apply add_left_cancel
              exact hxy
            have hdir : wholeRiskDirection k = wholeRiskDirection n :=
              smul_right_injective Plane (ne_of_gt (radius_pos j)) hsmul
            have hk : k = n := hAlg.2.2 hdir
            subst n
            rfl
          · have hfar := hDist.2.2 i l hclusters
              (wholeRiskPoint i j k)
              (by rw [hDist.1 i j k]; exact radius_le j)
            rw [hxy, hDist.1 l m n] at hfar
            linarith [radius_le m]
