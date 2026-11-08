import SAP.P026a.Defs.WholeW2
import SAP.P026a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.WH.W2

open Finset
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The two small block regressions have the already exported normal equations
and nonsingular two-by-two Gram matrices. -/
theorem linear_valid : ∀ b,
    w2ValidFit w2LinearDesign (w2BlockWeight b) paperTableY (w2LinearBeta b) := by
  unfold w2ValidFit
  decide +kernel

/-- The full coefficient vector reconstructs the exported FE (Cov.) fitted values. -/
theorem feCov_predict (w : W2Allocation) (i : Fin 16) :
    w2Predict (w2FeCovDesign w) (w2FeCovBeta w) i = paperFeFitted w i := by
  by_cases hi : i.val < 6
  · have h6 : ¬ 6 ≤ i.val := by omega
    simp [w2Predict, w2FeCovDesign, w2FeCovBeta, paperFeFitted,
      paperTableCenteredT, paperTableCenteredX, w2Treatment, Fin.sum_univ_succ, hi, h6]
    ring
  · have h6 : 6 ≤ i.val := by omega
    simp [w2Predict, w2FeCovDesign, w2FeCovBeta, paperFeFitted,
      paperTableCenteredT, paperTableCenteredX, w2Treatment, Fin.sum_univ_succ, hi, h6]
    ring

/-- Reuse all four exported FE (Cov.) normal equations. -/
theorem feCov_normal (w : W2Allocation) : ∀ j : Fin 4,
    (∑ i, (1 : ℚ) * w2FeCovDesign w i j *
      (paperTableY i - w2Predict (w2FeCovDesign w) (w2FeCovBeta w) i)) = 0 := by
  have hn := (AronowAudit.P026.fe_normal_equations w).2
  change (∑ i, (paperTableY i-paperFeFitted w i)) = 0 ∧
    (∑ i, w2Treatment w i*(paperTableY i-paperFeFitted w i)) = 0 ∧
    (∑ i ∈ (univ : Finset (Fin 16)).filter (fun i => 6 ≤ i.val),
      (paperTableY i-paperFeFitted w i)) = 0 ∧
    (∑ i, paperTableX i*(paperTableY i-paperFeFitted w i)) = 0 at hn
  intro j
  simp_rw [feCov_predict]
  fin_cases j
  · simpa [w2FeCovDesign] using hn.1
  · simpa [w2FeCovDesign] using hn.2.1
  · change (∑ i, (1 : ℚ) * (if 6 ≤ i.val then 1 else 0) *
      (paperTableY i-paperFeFitted w i)) = 0
    simpa only [Finset.sum_filter, ite_mul, one_mul, zero_mul] using hn.2.2.1
  · simpa [w2FeCovDesign] using hn.2.2.2

theorem unit_marginal (a : Bool) (i : Fin 16) :
    inclusion paperTableUnitDesign a i =
      AronowAudit.P026.tableMarginal a (paperTableCluster i) :=
  AronowAudit.P026.table_marginal a (paperTableCluster i)

theorem cluster_marginal (a : Bool) (g : Fin 10) :
    inclusion paperTableDesign a g = AronowAudit.P026.tableMarginal a g :=
  AronowAudit.P026.table_marginal a g

/-- Identify the unit-level generalized estimators in equation [16] with the
cluster-residual formulas used in the existing moment certificates. -/
theorem generalized_identifications : ∀ w : W2Allocation,
    adjustedContrast paperTableUnitDesign 16 paperTableY paperTableY
      (fun _ i => paperTableLinearPrediction i) w = w2LinearEstimate w ∧
    adjustedContrast paperTableUnitDesign 16 paperTableY paperTableY
      (fun _ _ => 0) w = w2HTEstimate w ∧
    adjustedContrast paperTableUnitDesign 16 paperTableY paperTableY
      (fun _ _ => 1/2) w = w2PriorEstimate w := by
  simp only [adjustedContrast, adjustedSum, w2LinearEstimate, w2HTEstimate,
    w2PriorEstimate, htContrast, htSum, unit_marginal, cluster_marginal,
    Bridge.linear_residual_eq]
  decide +kernel

theorem real_rounds {x r : ℚ} (h : roundsToThree x r) : w2RealRounds (x : ℝ) r := by
  have hlo : ((r-1/2000 : ℚ) : ℝ) ≤ (x : ℝ) := Rat.cast_le.mpr h.1
  have hhi : (x : ℝ) < ((r+1/2000 : ℚ) : ℝ) := Rat.cast_lt.mpr h.2
  push_cast at hlo hhi
  exact ⟨hlo, hhi⟩

/-- Squared rational intervals really are the claimed real square-root intervals.
The nonnegative lower endpoint prevents the usual squared-rounding trap. -/
theorem sqrt_rounds {v r : ℚ} (h : sdRoundsToThree v r)
    (hr : 0 ≤ r - 1/2000) : w2RealRounds (Real.sqrt (v : ℝ)) r := by
  have hlo : (((r-1/2000)^2 : ℚ) : ℝ) ≤ (v : ℝ) := Rat.cast_le.mpr h.1
  have hhi : (v : ℝ) < (((r+1/2000)^2 : ℚ) : ℝ) := Rat.cast_lt.mpr h.2
  have hrlo : ((0 : ℚ) : ℝ) ≤ ((r-1/2000 : ℚ) : ℝ) := Rat.cast_le.mpr hr
  push_cast at hlo hhi hrlo
  have hrhi : 0 < (r : ℝ)+1/2000 := by linarith
  exact ⟨Real.le_sqrt_of_sq_le hlo, (Real.sqrt_lt' hrhi).2 hhi⟩

/-- Assemble all ten rows from eight rational rounding certificates. -/
theorem column_from_certificates (e v : W2Allocation → ℚ)
    (m s rm vv ev bv sv rv : ℚ)
    (ha : w2ATECertificate e m s rm vv)
    (hv : w2VarianceCertificate e v ev bv sv rv)
    (hs : 0 ≤ s-1/2000) (hrm : 0 ≤ rm-1/2000)
    (hsv : 0 ≤ sv-1/2000) (hrv : 0 ≤ rv-1/2000) :
    w2ColumnRounds e v (w2PrintedColumn m s rm vv ev bv sv rv) := by
  rcases ha with ⟨hm, hse, hrme, hvar⟩
  rcases hv with ⟨hev, hbv, hsev, hrmv⟩
  intro j
  fin_cases j
  · change w2RealRounds 0 0
    norm_num [w2RealRounds]
  · exact real_rounds hm
  · exact real_rounds hm
  · exact sqrt_rounds hse hs
  · exact sqrt_rounds hrme hrm
  · exact real_rounds hvar
  · exact real_rounds hev
  · exact real_rounds hbv
  · exact sqrt_rounds hsev hsv
  · exact sqrt_rounds hrmv hrv

/-- In the unbiased cases both RMSE rows equal their standard-deviation rows. -/
theorem unbiased_certificates (e v : W2Allocation → ℚ) (V Z s vv sv : ℚ)
    (hm : mean paperTableDesign e = 0)
    (hs : designVariance paperTableDesign e = V)
    (hev : mean paperTableDesign v = V)
    (hz : designVariance paperTableDesign v = Z)
    (hse : sdRoundsToThree V s) (hvar : roundsToThree V vv)
    (hsev : sdRoundsToThree Z sv) :
    w2ATECertificate e 0 s s vv ∧ w2VarianceCertificate e v vv 0 sv sv := by
  simp only [w2ATECertificate, w2VarianceCertificate, hm, hs, hev, hz, sub_self]
  norm_num only [zero_pow, add_zero]
  exact ⟨⟨by norm_num [roundsToThree], hse, hse, hvar⟩,
    hvar, by norm_num [roundsToThree], hsev, hsev⟩

end
end SAP.P026a.WH.W2
