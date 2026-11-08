import SAP.P011c.WH.W1.Leaves
import AronowAudit.P011.P011_CoverageCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c.WH.W1.P.T39_L1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

set_option maxHeartbeats 1000000

theorem result : SAP.P011c.WH.W1.T39_L1 := by
  classical
  intro F c hc hscale hclt V hV hclose α hα hα1
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let μ := fun k => (F.model k).law
  let X := fun k y => (F.size k : ℝ) * V k y
  have hmove : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k => (μ k).real {y | |X k y - scaledTrue F k| > ε}) atTop (𝓝 0) := by
    intro ε hε
    simpa [InProbability, probability, μ, X] using hclose ε hε
  have hcp : AronowAudit.P011.CoverageCompletion.RowCP μ X c :=
    AronowAudit.P011.CoverageCompletion.rowCP_moving_center μ X (scaledTrue F) c hmove hscale
  have hdcp : AronowAudit.P011.CoverageCompletion.RowCP μ (fun k _ => scaledTrue F k) c :=
    AronowAudit.P011.CoverageCompletion.rowCP_det μ _ _ hscale
  let z := normalQuantile α
  have hz : 0 < z := AronowAudit.P011.CoverageCompletion.quantile_positive α hα hα1
  let f : ℝ × ℝ → ℝ := fun u => z * Real.sqrt (max u.1 0) / Real.sqrt u.2
  have hf : ContinuousAt f (c, c) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact (Real.sqrt_pos.mpr hc).ne'
  have hfc : f (c, c) = z := by
    dsimp [f]
    rw [max_eq_left hc.le]
    exact mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hc).ne'
  let W := fun k y => f (X k y, scaledTrue F k)
  have hW : AronowAudit.P011.CoverageCompletion.RowCP μ W z := by
    simpa only [hfc] using
      AronowAudit.P011.CoverageCompletion.rowCP_continuous_pair μ X
        (fun k _ => scaledTrue F k) c c hcp hdcp f hf
  letI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  have hPhi : Continuous Phi := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact AronowAudit.P053.NormalCompletion.cdf_continuousAt (gaussianReal 0 1) t
  have hCD : ∀ t : ℝ, Tendsto
      (fun k => AronowAudit.P011.CoverageCompletion.rowCDF μ
        (fun k y => standardized (F.model k) y) k t) atTop (𝓝 (Phi t)) := by
    intro t
    simpa [AronowAudit.P011.CoverageCompletion.rowCDF, μ, probability] using hclt t
  have hZ (k : ℕ) : Measurable (standardized (F.model k)) := by
    have hbeta : Measurable (betaHat (F.model k)) := by
      unfold betaHat average weighted
      apply Measurable.div_const
      exact Finset.measurable_sum Finset.univ fun i _ =>
        measurable_const.mul (measurable_pi_apply i)
    exact (hbeta.sub measurable_const).div_const _
  have hlim := AronowAudit.P011.CoverageCompletion.row_random_width_interval
    μ (fun k => standardized (F.model k)) W hZ Phi hCD hPhi
    (monotone_cdf (μ := gaussianReal 0 1)) z hz hW
  have hmass : Phi z - Phi (-z) = 1 - α := by
    simpa [z, SAP.P011c.Phi, SAP.P011c.normalQuantile,
      AronowAudit.P011.Phi, AronowAudit.P011.normalQuantile] using
      AronowAudit.P011.CoverageCompletion.quantile_mass α hα hα1
  rw [hmass] at hlim
  have hpos : ∀ᶠ k in atTop, 0 < var (F.model k) (betaHat (F.model k)) :=
    SAP.P011c.WH.W1.variance_eventually_positive F c hc hscale
  have heq : (fun k => coverage (F.model k) (V k) α) =ᶠ[atTop]
      (fun k => (μ k).real {y |
        |standardized (F.model k) y| ≤ W k y}) := by
    filter_upwards [hpos] with k hk
    apply congrArg ((μ k).real)
    ext y
    change (|betaHat (F.model k) y - beta (F.model k)| ≤
        z * Real.sqrt (max (V k y) 0)) ↔
      (|standardized (F.model k) y| ≤ W k y)
    dsimp [W, f, X, scaledTrue]
    rw [AronowAudit.P011.CoverageCompletion.scaled_width _ _ _ _
        (by exact_mod_cast (F.positive k)), standardized,
      abs_div, abs_of_pos (Real.sqrt_pos.mpr hk)]
    exact (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hk)).symm
  exact (tendsto_congr' heq).mpr hlim

end
end SAP.P011c.WH.W1.P.T39_L1

theorem SAP.P011c.WH.W1.T39_L1_proof : SAP.P011c.WH.W1.T39_L1 :=
  SAP.P011c.WH.W1.P.T39_L1.result
