import SAP.P026a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.WH.W1.P.T6_L2

open Finset
open scoped BigOperators

lemma predict_expansion (w : Fin 6 × Fin 15) (β : Fin 4 → ℝ) (i : Fin 16) :
    w1Predict (w1FeDesign w) β i =
      β 0 + ((armIndicator paperTableUnitDesign true w i : ℚ) : ℝ) * β 1 +
        (if i.val < 6 then 0 else 1) * β 2 + (paperTableX i : ℝ) * β 3 := by
  simp [w1Predict, w1FeDesign, Fin.sum_univ_succ]
  ring

lemma same_treatment_first_pair (w : Fin 6 × Fin 15) :
    armIndicator paperTableUnitDesign true w 0 =
      armIndicator paperTableUnitDesign true w 1 := by
  simp [armIndicator, paperTableUnitDesign, paperTableDesign, paperTableCluster]

end SAP.P026a.WH.W1.P.T6_L2

theorem SAP.P026a.WH.W1.T6_L2_proof : SAP.P026a.WH.W1.T6_L2 := by
  intro w β hzero
  have hform (i : Fin 16) := SAP.P026a.WH.W1.P.T6_L2.predict_expansion w β i
  have h0 := hzero 0
  have h1 := hzero 1
  rw [hform] at h0 h1
  rw [← SAP.P026a.WH.W1.P.T6_L2.same_treatment_first_pair] at h1
  norm_num [paperTableX] at h0 h1
  have hx : β 3 = 0 := by linarith
  have hr0 := hzero 0
  have hr2 := hzero 2
  have hr4 := hzero 4
  have hr5 := hzero 5
  rw [hform 0] at hr0
  rw [hform 2] at hr2
  rw [hform 4] at hr4
  rw [hform 5] at hr5
  have hfirst : β 0 = 0 ∧ β 1 = 0 := by
    rcases w with ⟨a, b⟩
    fin_cases a
    all_goals
      simp [armIndicator, paperTableUnitDesign, paperTableDesign,
        paperTableCluster, SAP.P026a.twoOfFourLaw, paperTableX, hx] at hr0 hr2 hr4 hr5
      constructor <;> linarith
  have h6 := hzero 6
  rw [hform 6] at h6
  have hblock : β 2 = 0 := by
    rw [hfirst.1, hfirst.2, hx] at h6
    norm_num at h6
    exact h6
  funext j
  fin_cases j <;> simp [hfirst.1, hfirst.2, hx, hblock]

