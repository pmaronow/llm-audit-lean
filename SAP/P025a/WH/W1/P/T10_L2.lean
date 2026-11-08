import SAP.P025a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a.WH.W1.P.T10_L2

open scoped BigOperators

private theorem sum_four (f : Fin 4 → ℝ) :
    (∑ i : Fin 4, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp [Fin.sum_univ_succ]
  ring

end SAP.P025a.WH.W1.P.T10_L2

theorem SAP.P025a.WH.W1.T10_L2_proof : SAP.P025a.WH.W1.T10_L2 := by
  intro w hbox
  have hden : (∑ i : Fin 4, w i) = w 0 + w 1 + w 2 + w 3 := by
    exact SAP.P025a.WH.W1.P.T10_L2.sum_four w
  have hdenratio :
      (∑ i : Fin 4, (1 : ℝ) * w i) = w 0 + w 1 + w 2 + w 3 := by
    simp [SAP.P025a.WH.W1.P.T10_L2.sum_four]
  have hnum :
      (∑ i : Fin 4, (fun _ : Fin 4 => (1 : ℝ)) i * w i *
        SAP.P025a.fourOutcomes i) = w 1 + 2 * w 2 + 3 * w 3 := by
    simp [SAP.P025a.fourOutcomes, SAP.P025a.WH.W1.P.T10_L2.sum_four]
    ring
  have hdenpos : 0 < w 0 + w 1 + w 2 + w 3 := by
    have h0 := (hbox 0).1
    have h1 := (hbox 1).1
    have h2 := (hbox 2).1
    have h3 := (hbox 3).1
    linarith
  have hratio :
      AronowAudit.P025.ratio SAP.P025a.fourOutcomes (fun _ => 1) w =
        (w 1 + 2 * w 2 + 3 * w 3) / (w 0 + w 1 + w 2 + w 3) := by
    simp only [AronowAudit.P025.ratio, hnum, hdenratio]
  have hrel :
      6 * (w 1 + 2 * w 2 + 3 * w 3) -
        7 * (w 0 + w 1 + w 2 + w 3) = SAP.P025a.wholeTailSlack w := by
    simp [SAP.P025a.wholeTailSlack]
    ring
  have hratio_slack :
      (AronowAudit.P025.ratio SAP.P025a.fourOutcomes (fun _ => 1) w = 7 / 6) ↔
        SAP.P025a.wholeTailSlack w = 0 := by
    rw [hratio, div_eq_div_iff (ne_of_gt hdenpos) (by norm_num : (6 : ℝ) ≠ 0)]
    constructor
    · intro h
      linarith [hrel]
    · intro h
      linarith [hrel]
  constructor
  · intro heq
    have hslack : SAP.P025a.wholeTailSlack w = 0 := hratio_slack.mp heq
    have h0 : 0 ≤ 2 - w 0 := sub_nonneg.mpr (hbox 0).2
    have h1 : 0 ≤ 2 - w 1 := sub_nonneg.mpr (hbox 1).2
    have h2 : 0 ≤ w 2 - 1 := sub_nonneg.mpr (hbox 2).1
    have h3 : 0 ≤ w 3 - 1 := sub_nonneg.mpr (hbox 3).1
    have ht0 : 0 ≤ 7 * (2 - w 0) := mul_nonneg (by norm_num) h0
    have ht1 : 0 ≤ 2 - w 1 := h1
    have ht2 : 0 ≤ 5 * (w 2 - 1) := mul_nonneg (by norm_num) h2
    have ht3 : 0 ≤ 11 * (w 3 - 1) := mul_nonneg (by norm_num) h3
    have hsum :
        7 * (2 - w 0) + (2 - w 1) + 5 * (w 2 - 1) + 11 * (w 3 - 1) = 0 := by
      simpa [SAP.P025a.wholeTailSlack] using hslack
    have hw0 : w 0 = 2 := by linarith
    have hw1 : w 1 = 2 := by linarith
    have hw2 : w 2 = 1 := by linarith
    have hw3 : w 3 = 1 := by linarith
    have hv : w = ![2, 2, 1, 1] := by
      funext i
      fin_cases i <;> simp [hw0, hw1, hw2, hw3]
    exact hv
  · intro hv
    subst w
    norm_num [SAP.P025a.ratio, SAP.P025a.fourOutcomes, Fin.sum_univ_succ]
