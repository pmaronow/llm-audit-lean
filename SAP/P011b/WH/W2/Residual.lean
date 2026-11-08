import SAP.P011b.WH.W2.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.WH.W2

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

theorem fitted_eqW2 {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ)
    (b : Fin p → ℝ) (y : Fin n → ℝ) :
    fittedResidual m D (ols D) y = trueResidual m D b y - olsDeltaW2 m D b y := by
  ext i
  simp only [fittedResidual, trueResidual, olsDeltaW2, Matrix.mulVec_sub, Pi.sub_apply]
  ring

/-- Normalize the existing symmetric quadratic perturbation theorem exactly,
without replacing the true-error norm by a larger uniform bound. -/
theorem perturbation_boundW2 {n : ℕ} (hn : 0 < n) (G : Graph n)
    (c : ℝ) (hc : 0 ≤ c) (hd : ∀ i, (degree G i : ℝ) ≤ c)
    (e d : Fin n → ℝ) : perturbationErrorW2 G e d ≤ perturbationRHSW2 c e d := by
  have hnR : 0 < (n : ℝ) := by positivity
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
  have hop : AronowAudit.P011.operatorNorm (oracleMatrix G) ≤ 1 + c := by
    apply AronowAudit.P011.SpectralConfidence.operatorNorm_le_abs_row_sum _
      (AronowAudit.P011.SpectralConfidence.oracle_symmetric G) _ (by positivity)
    intro i
    simp_rw [abs_of_nonneg (AronowAudit.P011.SpectralConfidence.oracle_nonneg G i _)]
    rw [AronowAudit.P011.SpectralConfidence.oracle_row_sum]
    change (degree G i : ℝ) + 1 ≤ 1 + c
    linarith [hd i]
  have hnorm : l2 ((e - d) - e) = l2 d := by
    simp [l2, sub_sub_cancel_left]
  have hpert : |quadratic (oracleMatrix G) (e - d) - quadratic (oracleMatrix G) e| ≤
      AronowAudit.P011.operatorNorm (oracleMatrix G) * l2 d * (2 * l2 e + l2 d) := by
    have hh : |quadratic (oracleMatrix G) (e-d) - quadratic (oracleMatrix G) e| ≤
        AronowAudit.P011.operatorNorm (oracleMatrix G) * l2 ((e-d)-e) *
          (2*l2 e + l2 ((e-d)-e)) :=
      AronowAudit.P011.residual_perturbation (oracleMatrix G)
        (AronowAudit.P011.SpectralConfidence.oracle_symmetric G) (e-d) e
    simpa only [hnorm] using hh
  calc
    perturbationErrorW2 G e d ≤
        (AronowAudit.P011.operatorNorm (oracleMatrix G) * l2 d * (2*l2 e+l2 d)) / (n : ℝ) :=
      div_le_div_of_nonneg_right hpert hnR.le
    _ ≤ ((1+c) * l2 d * (2*l2 e+l2 d)) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hop (Real.sqrt_nonneg _))
        (by exact add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    _ = perturbationRHSW2 c e d := by
      unfold perturbationRHSW2
      field_simp [hs0, hnR.ne']
      rw [Real.sq_sqrt hnR.le]
      <;> ring

/-- A single finite mean model identifies the true errors with own-mean-centred
weighted outcomes. Assumption 2 supplies all their finite moments. -/
theorem true_error_boundW2 (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (p : ℕ) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : ℕ → Fin p → ℝ)
    (hm : ∀ k, MeanModel (F.model k) (D k) (b k)) :
    ∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i,
      |trueResidual (F.model k) (D k) (b k) y i| ≤ 2*c1 := by
  rcases h with ⟨_, _, _, _, _, _, hb, _, _, _⟩
  intro k
  have hL2 := AronowAudit.P011.ProbabilityCompletion.weighted_memLp
    (Bridge.toModel (F.model k)) c1 (hb k)
  have hh := AronowAudit.P011.ProbabilityCompletion.own_centred_bound
    (Bridge.toModel (F.model k)) c1 hL2 (hb k)
  filter_upwards [hh] with y hy i
  have he : trueResidual (F.model k) (D k) (b k) y i =
      weighted (F.model k) y i - expectation (F.model k) (fun z => weighted (F.model k) z i) :=
    AronowAudit.P011.Wave1.rps_true_eq (Bridge.toModel (F.model k)) (D k) (b k) (hm k) y i
  rw [he]
  exact hy i

/-- Concentration allows a different deterministic centring vector at every n;
correct specification makes that vector exactly the weighted mean. -/
theorem true_oracleW2 (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (p : ℕ) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : ℕ → Fin p → ℝ)
    (hm : ∀ k, MeanModel (F.model k) (D k) (b k)) :
    InProbability F (fun k y => quadratic (oracleMatrix (F.model k).G)
      (trueResidual (F.model k) (D k) (b k) y) / (F.size k : ℝ)) (scaledTrue F) := by
  let a : ∀ k, Fin (F.size k) → ℝ :=
    fun k i => expectation (F.model k) (fun y => weighted (F.model k) y i)
  have he (k : ℕ) (y : Fin (F.size k) → ℝ) :
      (fun i => AronowAudit.P011.Wave1.msr_shift (Bridge.toModel (F.model k)) (a k) i y) =
        trueResidual (F.model k) (D k) (b k) y := by
    ext i
    exact (AronowAudit.P011.Wave1.rps_true_eq
      (Bridge.toModel (F.model k)) (D k) (b k) (hm k) y i).symm
  have hz := true_error_boundW2 F c1 c2 c3 c4 h p D b hm
  have hh := AronowAudit.P011.Wave1.msr_quadratic_concentration
    (Bridge.toFamily F) c1 c2 c3 c4 h a (2*c1) (by linarith [h.2.1]) (by
      intro k
      change ∀ᵐ y ∂(F.model k).law, ∀ i,
        |AronowAudit.P011.Wave1.msr_shift (Bridge.toModel (F.model k)) (a k) i y| ≤ 2*c1
      filter_upwards [hz k] with y hy i
      rw [congrFun (he k y) i]
      exact hy i)
  change InProbability F (fun k y => quadratic (oracleMatrix (F.model k).G)
    (fun i => AronowAudit.P011.Wave1.msr_shift (Bridge.toModel (F.model k)) (a k) i y) /
      (F.size k : ℝ)) (fun k => scaledTrue F k + quadratic (oracleMatrix (F.model k).G)
        (fun i => expectation (F.model k) (fun y => weighted (F.model k) y i) - a k i) /
          (F.size k : ℝ)) at hh
  simp_rw [he] at hh
  simpa only [a, sub_self, quadratic, mul_zero, zero_mul, Finset.sum_const_zero,
    zero_div, add_zero] using hh

end
end SAP.P011b.WH.W2
