import SAP.P005a.Defs.WholeW3
import SAP.P005a.Bridge
import AronowAudit.P005.Wave1.Gap.GP005B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W3

noncomputable section
open SAP.P005a Finset
open scoped BigOperators Matrix

set_option maxHeartbeats 800000

/-- All missing T12 clauses are finite arithmetic or definition bridges around
existing proved results. There are no new mathematical leaves. -/
theorem T12_assembly : T12WholeStatement := by
  classical
  have hbase : T12Statement :=
    SAP.P005a.Bridge.T12_correspondence.mp
      AronowAudit.P005.interacted_inverse_counterexample
  rcases hbase with
    ⟨hx0, hx2, hpositive, hy2, hlo, hhi, hactual, hprinted, hcorrected, _⟩
  have hs : weightScale ^ 2 = (3 / 20 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : weightScale ≠ 0 := by
    intro hz
    rw [hz] at hs
    norm_num at hs
  have ha0 : popMean weightA = 0 := by
    norm_num [popMean, mean, weightA, AronowAudit.P005.univ_six]
  have ha2 : popMean (fun i => weightA i ^ 2) = (40 / 6 : ℝ) := by
    norm_num [popMean, mean, weightA, AronowAudit.P005.univ_six]
  have hstd : standardized T12Population :=
    AronowAudit.P005.standardized_scalar weightA (fun _ => 0) weightY weightScale
      ha0 (by
        change weightScale ^ 2 * popMean (fun i => weightA i ^ 2) = 1
        rw [hs, ha2]
        norm_num)
  have hL (A : Finset (Fin 6)) : armL T12Population A 0 0 =
      (3 / 20 : ℝ) * sampleCov A weightA weightA := by
    have h : sampleCov A weightX weightX =
        weightScale ^ 2 * sampleCov A weightA weightA :=
      AronowAudit.P005.sampleCov_scale_both A weightA weightScale
    change sampleCov A weightX weightX = _
    simpa only [hs] using h
  have hLX (A : Finset (Fin 6)) :
      armL T12Population A 0 0 = sampleCov A weightX weightX := rfl
  have hdet (A : Finset (Fin 6)) :
      (armL T12Population A).det = sampleCov A weightX weightX := by
    rw [Matrix.det_fin_one, hLX]
  have hreg : interactedRegular T12Population 2 := by
    intro S hS
    rw [hdet, hdet]
    exact ⟨ne_of_gt (hpositive S hS).1, ne_of_gt (hpositive S hS).2⟩
  have hcards (S : Finset (Fin 6)) (hS : S ∈ design 6 2) :
      S.card = 2 ∧ (control S).card = 4 := by
    have ht : S.card = 2 := (Finset.mem_powersetCard.mp hS).2
    refine ⟨ht, ?_⟩
    rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [ht]
  have hlev : leverage T12Population = fun i => (3 / 20 : ℝ) * weightA i ^ 2 := by
    have h : leverage T12Population = fun i => weightScale ^ 2 * weightA i ^ 2 :=
      AronowAudit.P005.scalar_leverage weightA (fun _ => 0) weightY weightScale
    simpa only [hs] using h
  have hlevx : leverage T12Population = fun i => weightX i ^ 2 := by
    funext i
    rw [hlev]
    dsimp only [weightX]
    rw [mul_pow, hs]
  have hinj : Function.Injective weightX := by
    intro i j hij
    change weightScale * weightA i = weightScale * weightA j at hij
    have ha := mul_left_cancel₀ hs0 hij
    fin_cases i <;> fin_cases j <;> norm_num [weightA] at ha
    all_goals rfl

  -- Reducing 1-by-1 matrices identifies the paper's objects with scalar OLS.
  have hN (A : Finset (Fin 6)) : armN T12Population A T12Population.yC 0 =
      sampleCov A weightX weightY := by
    change mean A (fun i => weightY i * weightX i) -
      mean A weightY * mean A weightX = _
    simp only [sampleCov, mul_comm]
  have hInv (H : Finset (Fin 6)) : ((armL T12Population H)⁻¹) 0 0 =
      (sampleCov H weightX weightX)⁻¹ := by
    rw [Matrix.inv_subsingleton]
    simp [Ring.inverse_eq_inv, hLX]
  have hmatrix (A H : Finset (Fin 6)) :
      dot (xMean T12Population A)
        ((armL T12Population H)⁻¹ *ᵥ armN T12Population A T12Population.yC) =
      mean A weightX * (sampleCov H weightX weightX)⁻¹ * sampleCov A weightX weightY := by
    simp only [dot, Matrix.mulVec, dotProduct, Fin.sum_univ_one, hInv, hN]
    change mean A weightX * ((sampleCov H weightX weightX)⁻¹ *
      sampleCov A weightX weightY) = _
    ring
  have hsub (A H : Finset (Fin 6)) :
      dot (xMean T12Population A)
        (((armL T12Population H)⁻¹ - 1) *ᵥ armN T12Population A T12Population.yC) =
      mean A weightX * ((sampleCov H weightX weightX)⁻¹ - 1) *
        sampleCov A weightX weightY := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [dot, Pi.sub_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_one, hInv, hN]
    change mean A weightX * ((sampleCov H weightX weightX)⁻¹ *
      sampleCov A weightX weightY - sampleCov A weightX weightY) = _
    ring
  have hbeta (A : Finset (Fin 6)) :
      dot (xMean T12Population A) (armBetaHat T12Population A T12Population.yC) =
        mean A weightX * scalarSlope A weightX weightY := by
    unfold armBetaHat
    rw [hmatrix]
    unfold scalarSlope
    ring
  have hprintedScalar : T12PrintedEstimator = fun S =>
      (1 / 8 : ℝ) * sampleCov (control S) (fun i => weightX i ^ 2) weightY +
        mean (control S) weightX * ((sampleCov S weightX weightX)⁻¹ - 1) *
          sampleCov (control S) weightX weightY := by
    funext S
    unfold T12PrintedEstimator
    rw [hlevx, hsub]
    norm_num [T12Population, scalarPopulation]
  have hcorrectedScalar : T12CorrectedEstimator = fun S =>
      (1 / 8 : ℝ) * sampleCov (control S) (fun i => weightX i ^ 2) weightY +
        mean (control S) weightX * ((sampleCov (control S) weightX weightX)⁻¹ - 1) *
          sampleCov (control S) weightX weightY := by
    funext S
    unfold T12CorrectedEstimator
    rw [hlevx, hsub]
    norm_num [T12Population, scalarPopulation]
  have hactualMatrix : expectation 2 (fun S =>
      dot (xMean T12Population (control S))
        (armBetaHat T12Population (control S) T12Population.yC)) =
        (31085815448171 / 17062566567774 : ℝ) := by
    simp only [hbeta]
    exact hactual
  have hprintedMatrix : expectation 2 T12PrintedEstimator =
      (12010469 / 846720 : ℝ) := by
    rw [hprintedScalar]
    exact hprinted
  have hcorrectedMatrix : expectation 2 T12CorrectedEstimator =
      (31085815448171 / 17062566567774 : ℝ) := by
    rw [hcorrectedScalar]
    exact hcorrected

  -- Complement transport supplies zero mean; the certified T13 proof identifies
  -- the nuisance expectation without assuming any unproved printed formula.
  have hex : expectation 2 (fun S => xMean T12Population (control S) 0) = 0 := by
    change expectation 2 (fun S => mean (control S) weightX) = 0
    rw [SAP.P005a.Bridge.expectation_control (by decide : 2 ≤ 6)
      (fun A => mean A weightX)]
    exact (AronowAudit.P005.mean_unbiased (by decide : 0 < 6)
      (by decide : 0 < 4) (by decide : 4 ≤ 6) weightX).trans hx0
  have hfixed : expectation 2 (fun S => dot (xMean T12Population (control S))
      (populationSlope T12Population T12Population.yC)) = 0 := by
    rw [SAP.P005a.Bridge.expectation_control (by decide : 2 ≤ 6)
      (fun A => dot (xMean T12Population A)
        (populationSlope T12Population T12Population.yC))]
    exact AronowAudit.P005.Wave1.t13_dot_mean_E
      (SAP.P005a.Bridge.toPopulation T12Population) (by decide) (by decide)
      (by decide) hstd.1 _
  have hnu : expectation 2 T12ControlNuisance = expectation 2 (fun S =>
      dot (xMean T12Population (control S))
        (armBetaHat T12Population (control S) T12Population.yC)) :=
    (AronowAudit.P005.Wave1.corrected_control_bias_estimator_proof
      (SAP.P005a.Bridge.toPopulation T12Population) (by decide) (by decide)
      (by decide) hstd (fun S hS => (hreg S hS).2)).2.1
  have hnuValue : expectation 2 T12ControlNuisance =
      (31085815448171 / 17062566567774 : ℝ) := hnu.trans hactualMatrix

  -- The rational-coordinate identities are existing scale-cancellation results.
  have hbetaRat (A : Finset (Fin 6)) :
      dot (xMean T12Population A) (armBetaHat T12Population A T12Population.yC) =
      mean A weightA * sampleCov A weightA weightY / sampleCov A weightA weightA :=
    (hbeta A).trans
      (AronowAudit.P005.scalar_slope_product_scale A weightA weightY weightScale hs0)
  have hNRat (A : Finset (Fin 6)) :
      dot (xMean T12Population A) (armN T12Population A T12Population.yC) =
      (3 / 20 : ℝ) * mean A weightA * sampleCov A weightA weightY := by
    have h : dot (xMean T12Population A) (armN T12Population A T12Population.yC) =
        weightScale ^ 2 * mean A weightA * sampleCov A weightA weightY :=
      AronowAudit.P005.scalar_dot_armN weightA (fun _ => 0) weightY
        weightY weightScale A
    simpa only [hs] using h
  have hInvRat (A H : Finset (Fin 6)) :
      dot (xMean T12Population A)
        ((armL T12Population H)⁻¹ *ᵥ armN T12Population A T12Population.yC) =
      mean A weightA * sampleCov A weightA weightY / sampleCov H weightA weightA := by
    have hm : dot (xMean T12Population A)
        (((armL T12Population H)⁻¹ - 1) *ᵥ armN T12Population A T12Population.yC) =
        mean A weightA * sampleCov A weightA weightY / sampleCov H weightA weightA -
          (3 / 20 : ℝ) * mean A weightA * sampleCov A weightA weightY := by
      rw [hsub]
      have h : mean A weightX * ((sampleCov H weightX weightX)⁻¹ - 1) *
          sampleCov A weightX weightY =
          mean A weightA * sampleCov A weightA weightY / sampleCov H weightA weightA -
            weightScale ^ 2 * mean A weightA * sampleCov A weightA weightY :=
        AronowAudit.P005.scalar_inverse_product_scale A H weightA weightY weightScale hs0
      simpa only [hs] using h
    have hrel : dot (xMean T12Population A)
        (((armL T12Population H)⁻¹ - 1) *ᵥ armN T12Population A T12Population.yC) =
        dot (xMean T12Population A)
          ((armL T12Population H)⁻¹ *ᵥ armN T12Population A T12Population.yC) -
            dot (xMean T12Population A) (armN T12Population A T12Population.yC) := by
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dot, Pi.sub_apply,
        Fin.sum_univ_one]
      ring
    rw [hNRat] at hrel
    linarith

  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, hinj, ha2, hstd, hx0, ?_, hx2, ?_, hy2, hlo, hhi⟩
    · norm_num [design, Finset.card_powersetCard, Nat.choose]
    · rw [hx2]
      norm_num
    · simp [T12Population, scalarPopulation, popMean, mean]
  · refine ⟨hreg, ?_⟩
    intro S hS
    have hcN : (control S).Nonempty := Finset.card_pos.mp (by
      rw [(hcards S hS).2]
      decide)
    refine ⟨(hcards S hS).1, (hcards S hS).2, hL S, hL (control S),
      ?_, ?_, ?_⟩
    · rw [hLX]
      exact (hpositive S hS).1
    · rw [hLX]
      exact (hpositive S hS).2
    · exact AronowAudit.P005.arm_slope_decomposition
        (SAP.P005a.Bridge.toPopulation T12Population) hstd (control S) hcN
        T12Population.yC (hreg S hS).2
  · refine ⟨fun i => ⟨congrFun hlevx i, congrFun hlev i⟩, ?_⟩
    rw [hlevx]
    exact hx2
  · exact ⟨hex, hfixed, hnu, hactualMatrix, hnuValue⟩
  · refine ⟨hprintedMatrix, hcorrectedMatrix, ?_, ?_, ?_, ?_⟩
    · rw [hprintedMatrix, hnuValue]
      norm_num
    · exact hcorrectedMatrix.trans hnuValue.symm
    · norm_num
    · norm_num
  · refine ⟨by norm_num, ?_⟩
    intro S _
    refine ⟨hbetaRat (control S), hNRat (control S), hInvRat (control S) S, ?_⟩
    rw [hlev]
    exact AronowAudit.P005.sampleCov_scale_left (control S)
      (fun i => weightA i ^ 2) weightY (3 / 20)

end
end SAP.P005a.WH.W3
