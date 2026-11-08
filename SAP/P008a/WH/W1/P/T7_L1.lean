import SAP.P008a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a.WH.W1.P.T7_L1

open scoped BigOperators

lemma riskDenominator_pos (k : RiskCell) : 0 < wholeRiskDenominator k := by
  unfold wholeRiskDenominator
  nlinarith [sq_nonneg (wholeRiskEll k)]

lemma riskOnePlus (k : RiskCell) :
    1 + wholeRiskU k = 2 * (40000 : ℝ)^2 / wholeRiskDenominator k := by
  have hden : (40000 : ℝ)^2 + wholeRiskEll k ^ 2 ≠ 0 := by
    have hp := riskDenominator_pos k
    simpa only [wholeRiskDenominator] using ne_of_gt hp
  simp only [wholeRiskU, wholeRiskDenominator]
  field_simp [hden]
  ring

lemma riskUnitCoordinates (k : RiskCell) :
    wholeRiskU k ^ 2 + wholeRiskV k ^ 2 = 1 := by
  have hden : (40000 : ℝ)^2 + wholeRiskEll k ^ 2 ≠ 0 := by
    have hp := riskDenominator_pos k
    simpa only [wholeRiskDenominator] using ne_of_gt hp
  simp only [wholeRiskU, wholeRiskV, wholeRiskDenominator]
  field_simp [hden]
  ring

lemma riskOnePlus_ne (k : RiskCell) : 1 + wholeRiskU k ≠ 0 := by
  rw [riskOnePlus]
  exact div_ne_zero (by norm_num) (ne_of_gt (riskDenominator_pos k))

lemma riskRatio (k : RiskCell) :
    wholeRiskV k / (1 + wholeRiskU k) = wholeRiskEll k / 40000 := by
  rw [riskOnePlus]
  have hden : (40000 : ℝ)^2 + wholeRiskEll k ^ 2 ≠ 0 := by
    have hp := riskDenominator_pos k
    simpa only [wholeRiskDenominator] using ne_of_gt hp
  simp only [wholeRiskV, wholeRiskDenominator]
  field_simp [hden, (by norm_num : (40000 : ℝ) ≠ 0)]

lemma riskRatio_strictMono :
    StrictMono (fun k : RiskCell => wholeRiskV k / (1 + wholeRiskU k)) := by
  intro k l hkl
  change wholeRiskV k / (1 + wholeRiskU k) <
    wholeRiskV l / (1 + wholeRiskU l)
  rw [riskRatio, riskRatio]
  have hval : (k.val : ℝ) < (l.val : ℝ) := by
    exact_mod_cast hkl
  dsimp [wholeRiskEll]
  nlinarith

lemma riskDirection_norm (k : RiskCell) : ‖wholeRiskDirection k‖ = 1 := by
  have hsq : ‖wholeRiskDirection k‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [wholeRiskDirection, Fin.sum_univ_succ] using riskUnitCoordinates k
  have hn := norm_nonneg (wholeRiskDirection k)
  nlinarith

lemma riskDirection_injective : Function.Injective wholeRiskDirection := by
  intro k l hkl
  have hu : wholeRiskU k = wholeRiskU l := by
    have h := congrArg (fun x : Plane => x 0) hkl
    simpa [wholeRiskDirection] using h
  have hv : wholeRiskV k = wholeRiskV l := by
    have h := congrArg (fun x : Plane => x 1) hkl
    simpa [wholeRiskDirection] using h
  have hr : wholeRiskV k / (1 + wholeRiskU k) =
      wholeRiskV l / (1 + wholeRiskU l) := by
    rw [hu, hv]
  exact riskRatio_strictMono.injective hr

end SAP.P008a.WH.W1.P.T7_L1

theorem SAP.P008a.WH.W1.T7_L1_proof : SAP.P008a.WH.W1.T7_L1 := by
  unfold SAP.P008a.WH.W1.T7_L1 SAP.P008a.WholeRiskAlgebra
  refine ⟨?_, SAP.P008a.WH.W1.P.T7_L1.riskRatio_strictMono,
    SAP.P008a.WH.W1.P.T7_L1.riskDirection_injective⟩
  intro k
  refine ⟨SAP.P008a.WH.W1.P.T7_L1.riskDenominator_pos k,
    SAP.P008a.WH.W1.P.T7_L1.riskOnePlus_ne k,
    SAP.P008a.WH.W1.P.T7_L1.riskUnitCoordinates k,
    SAP.P008a.WH.W1.P.T7_L1.riskRatio k,
    SAP.P008a.WH.W1.P.T7_L1.riskDirection_norm k⟩
