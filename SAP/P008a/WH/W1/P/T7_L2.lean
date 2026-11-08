import SAP.P008a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a.WH.W1.P.T7_L2

open scoped BigOperators

lemma riskCentre_dist_sq (i l : Fin 4) :
    dist (wholeRiskCentre i) (wholeRiskCentre l) ^ 2 =
      ∑ a : Fin 2, dist (wholeRiskCentre i a) (wholeRiskCentre l a) ^ 2 := by
  exact EuclideanSpace.dist_sq_eq _ _

lemma riskCentre_separated (i l : Fin 4) (hil : i ≠ l) :
    (20 : ℝ) ≤ dist (wholeRiskCentre i) (wholeRiskCentre l) := by
  have hs : (20 : ℝ) ^ 2 ≤ dist (wholeRiskCentre i) (wholeRiskCentre l) ^ 2 := by
    rw [riskCentre_dist_sq]
    fin_cases i <;> fin_cases l <;>
      norm_num [wholeRiskCentre, Fin.sum_univ_succ, dist_eq_norm] at *
  have hn : 0 ≤ dist (wholeRiskCentre i) (wholeRiskCentre l) := dist_nonneg
  nlinarith

lemma riskPoint_own_dist (i j : Fin 4) (k : RiskCell)
    (hk : ‖wholeRiskDirection k‖ = 1) :
    dist (wholeRiskCentre i) (wholeRiskPoint i j k) = wholeRiskRadius j := by
  have he : dist (wholeRiskCentre i) (wholeRiskPoint i j k) =
      ‖wholeRiskRadius j • wholeRiskDirection k‖ := by
    simp [wholeRiskPoint, dist_eq_norm']
  rw [he, norm_smul, hk]
  fin_cases j <;> norm_num [wholeRiskRadius]

end SAP.P008a.WH.W1.P.T7_L2

theorem SAP.P008a.WH.W1.T7_L2_proof : SAP.P008a.WH.W1.T7_L2 := by
  intro hunit
  refine ⟨?_, ?_, ?_⟩
  · intro i j k
    exact SAP.P008a.WH.W1.P.T7_L2.riskPoint_own_dist i j k (hunit k)
  · intro i l hil
    exact SAP.P008a.WH.W1.P.T7_L2.riskCentre_separated i l hil
  · intro i l hil x hix
    have hcentres := SAP.P008a.WH.W1.P.T7_L2.riskCentre_separated l i (Ne.symm hil)
    have htri := dist_triangle (wholeRiskCentre l) x (wholeRiskCentre i)
    have hsym : dist x (wholeRiskCentre i) = dist (wholeRiskCentre i) x := dist_comm _ _
    rw [hsym] at htri
    nlinarith
