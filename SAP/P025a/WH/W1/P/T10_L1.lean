import SAP.P025a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a.WH.W1.P.T10_L1

open scoped BigOperators

lemma sum_lower_bound (w : Fin 4 → ℝ) (hw : SAP.P025a.normBox 2 w) :
    4 ≤ ∑ i : Fin 4, w i := by
  norm_num [Fin.sum_univ_succ]
  have h0 : (1 : ℝ) ≤ w 0 := (hw 0).1
  have h1 : (1 : ℝ) ≤ w 1 := (hw 1).1
  have h2 : (1 : ℝ) ≤ w 2 := (hw 2).1
  have h3 : (1 : ℝ) ≤ w 3 := (hw 3).1
  linarith

lemma tail_slack_nonnegative (w : Fin 4 → ℝ) (hw : SAP.P025a.normBox 2 w) :
    0 ≤ SAP.P025a.wholeTailSlack w := by
  unfold SAP.P025a.wholeTailSlack
  apply add_nonneg
  · apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (by norm_num) (sub_nonneg.mpr (by linarith [(hw 0).2]))
      · exact sub_nonneg.mpr (by linarith [(hw 1).2])
    · exact mul_nonneg (by norm_num) (sub_nonneg.mpr (hw 2).1)
  · exact mul_nonneg (by norm_num) (sub_nonneg.mpr (hw 3).1)

end SAP.P025a.WH.W1.P.T10_L1

theorem SAP.P025a.WH.W1.T10_L1_proof : SAP.P025a.WH.W1.T10_L1 := by
  intro w hw
  have hsum : 4 ≤ ∑ i : Fin 4, w i :=
    SAP.P025a.WH.W1.P.T10_L1.sum_lower_bound w hw
  have hS : 0 < ∑ i : Fin 4, w i := by linarith
  have hid :
      SAP.P025a.ratio SAP.P025a.fourOutcomes (fun _ => 1) w - 7/6 =
        SAP.P025a.wholeTailSlack w / (6 * ∑ i : Fin 4, w i) := by
    unfold SAP.P025a.ratio SAP.P025a.fourOutcomes SAP.P025a.wholeTailSlack
    field_simp [ne_of_gt hS]
    norm_num [Fin.sum_univ_succ]
    ring
  have hslack := SAP.P025a.WH.W1.P.T10_L1.tail_slack_nonnegative w hw
  have hden : 0 < 6 * ∑ i : Fin 4, w i := by positivity
  exact ⟨hS, hid, div_nonneg hslack hden.le⟩
