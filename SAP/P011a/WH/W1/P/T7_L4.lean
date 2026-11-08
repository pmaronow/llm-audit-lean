import SAP.P011a.WH.W1.Leaves
import AronowAudit.P011.P011_CoverageCompletion
import AronowAudit.P011.P011_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W1.P.T7_L4

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
local instance : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

lemma consistent_coverage (hclt : SAP.P011a.WholeCLT)
    (F : SAP.P011a.Family) (c1 c2 c3 c4 : ℝ)
    (h : SAP.P011a.WholeScaling F c1 c2 c3 c4)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (_hV : ∀ k, Measurable (V k))
    (hc : SAP.P011a.InProbability F (fun k y => (F.size k : ℝ) * V k y)
      (SAP.P011a.scaledTrue F)) :
    ∀ α : ℝ, 0 < α → α < 1 →
      Tendsto (fun k => SAP.P011a.coverage (F.model k) (V k) α)
        atTop (𝓝 (1 - α)) := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  have hc3 : 0 < c3 := h.c3_pos
  have hscale : Tendsto (SAP.P011a.scaledTrue F) atTop (𝓝 c3) := h.variance_limit
  let μ := fun k => (F.model k).law
  have hcp : AronowAudit.P011.CoverageCompletion.RowCP μ
      (fun k y => (F.size k : ℝ) * V k y) c3 :=
    AronowAudit.P011.CoverageCompletion.rowCP_moving_center μ _
      (SAP.P011a.scaledTrue F) c3 hc hscale
  have hdcp : AronowAudit.P011.CoverageCompletion.RowCP μ
      (fun k _ => SAP.P011a.scaledTrue F k) c3 :=
    AronowAudit.P011.CoverageCompletion.rowCP_det μ _ _ hscale
  intro α hα hα1
  let z := SAP.P011a.normalQuantile α
  have hz : 0 < z := AronowAudit.P011.CoverageCompletion.quantile_positive α hα hα1
  let f : ℝ × ℝ → ℝ := fun u => z * Real.sqrt (max u.1 0) / Real.sqrt u.2
  have hf : ContinuousAt f (c3, c3) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact (Real.sqrt_pos.mpr hc3).ne'
  have hfc : f (c3, c3) = z := by
    dsimp [f]
    rw [max_eq_left hc3.le]
    exact mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hc3).ne'
  let W := fun k y => f ((F.size k : ℝ) * V k y, SAP.P011a.scaledTrue F k)
  have hW : AronowAudit.P011.CoverageCompletion.RowCP μ W z := by
    simpa only [hfc] using
      AronowAudit.P011.CoverageCompletion.rowCP_continuous_pair μ _ _ c3 c3 hcp hdcp f hf
  have hPhi : Continuous SAP.P011a.Phi := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact AronowAudit.P053.NormalCompletion.cdf_continuousAt
      (gaussianReal 0 1) t
  have hZ (k : ℕ) : Measurable (SAP.P011a.wholeStandardized (F.model k)) :=
    by
      have hb : Measurable (betaHat (F.model k)) := by
        unfold betaHat average
        exact (Finset.measurable_sum Finset.univ fun i _ => by
          dsimp [SAP.P011a.weighted]
          exact measurable_const.mul (measurable_pi_apply i)).div_const _
      exact (hb.sub measurable_const).div_const _
  have hlim := AronowAudit.P011.CoverageCompletion.row_random_width_interval μ
    (fun k => SAP.P011a.wholeStandardized (F.model k)) W hZ SAP.P011a.Phi
    (fun t => by
      simpa [AronowAudit.P011.CoverageCompletion.rowCDF, μ, SAP.P011a.probability,
        SAP.P011a.wholeStandardized] using hclt F c1 c2 c3 c4 h t)
    hPhi (monotone_cdf (μ := gaussianReal 0 1)) z hz hW
  have hmass : SAP.P011a.Phi z - SAP.P011a.Phi (-z) = 1 - α := by
    change AronowAudit.P011.Phi (AronowAudit.P011.normalQuantile α) -
      AronowAudit.P011.Phi (-AronowAudit.P011.normalQuantile α) = 1 - α
    exact AronowAudit.P011.CoverageCompletion.quantile_mass α hα hα1
  rw [hmass] at hlim
  have hpos : ∀ᶠ k in atTop, 0 < var (F.model k) (betaHat (F.model k)) := by
    have he := hscale.eventually (Ioi_mem_nhds hc3)
    filter_upwards [he] with k hk
    change 0 < SAP.P011a.scaledTrue F k at hk
    dsimp [SAP.P011a.scaledTrue] at hk
    have hn : 0 < (F.size k : ℝ) := by exact_mod_cast F.positive k
    nlinarith
  have heq : (fun k => SAP.P011a.coverage (F.model k) (V k) α) =ᶠ[atTop]
      (fun k => (μ k).real
        {y | |SAP.P011a.wholeStandardized (F.model k) y| ≤ W k y}) := by
    filter_upwards [hpos] with k hk
    apply congrArg ((μ k).real)
    ext y
    change (|betaHat (F.model k) y-beta (F.model k)| ≤
        z * Real.sqrt (max (V k y) 0)) ↔
      (|SAP.P011a.wholeStandardized (F.model k) y| ≤ W k y)
    have hwidth : W k y =
        z * Real.sqrt (max (V k y) 0) /
          Real.sqrt (var (F.model k) (betaHat (F.model k))) := by
      dsimp [W, f]
      exact AronowAudit.P011.CoverageCompletion.scaled_width
        (F.size k : ℝ) (var (F.model k) (betaHat (F.model k))) (V k y) z
          (by exact_mod_cast F.positive k)
    rw [hwidth, SAP.P011a.wholeStandardized, abs_div,
      abs_of_pos (Real.sqrt_pos.mpr hk)]
    exact (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hk)).symm
  exact (tendsto_congr' heq).mpr hlim

lemma conservative_coverage (hclt : SAP.P011a.WholeCLT)
    (F : SAP.P011a.Family) (c1 c2 c3 c4 : ℝ)
    (h : SAP.P011a.WholeScaling F c1 c2 c3 c4)
    (V : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (hV : ∀ k, Measurable (V k))
    (hc : SAP.P011a.Conservative F V) : SAP.P011a.ConservativeCoverage F V := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let U := fun k y => min (V k y) (var (F.model k) (betaHat (F.model k)))
  have hU : ∀ k, Measurable (U k) := fun k => (hV k).min measurable_const
  have hUc : SAP.P011a.InProbability F
      (fun k y => (F.size k : ℝ) * U k y) (SAP.P011a.scaledTrue F) := by
    intro ε hε
    have heq : (fun k => probability (F.model k)
        {y | |(F.size k : ℝ) * U k y - SAP.P011a.scaledTrue F k| > ε}) =
        (fun k => probability (F.model k)
          {y | (F.size k : ℝ) *
            (var (F.model k) (betaHat (F.model k)) - V k y) > ε}) := by
      funext k
      apply congrArg (probability (F.model k))
      ext y
      dsimp [U, SAP.P011a.scaledTrue]
      rw [(AronowAudit.P011.truncation_identity (F.size k : ℝ) _ _
        (by positivity)).1]
      have hid : (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)) -
          (F.size k : ℝ) * V k y =
          (F.size k : ℝ) *
            (var (F.model k) (betaHat (F.model k)) - V k y) := by ring
      rw [hid]
      change ε < max ((F.size k : ℝ) *
          (var (F.model k) (betaHat (F.model k)) - V k y)) 0 ↔
        ε < (F.size k : ℝ) *
          (var (F.model k) (betaHat (F.model k)) - V k y)
      rw [lt_max_iff]
      simp only [show ¬ ε < 0 by linarith, or_false]
    rw [heq]
    exact hc ε hε
  have hlim := consistent_coverage hclt F c1 c2 c3 c4 h U hU hUc
  intro α hα hα1
  have hz : 0 ≤ SAP.P011a.normalQuantile α :=
    (AronowAudit.P011.CoverageCompletion.quantile_positive α hα hα1).le
  have hdom (k : ℕ) : SAP.P011a.coverage (F.model k) (U k) α ≤
      SAP.P011a.coverage (F.model k) (V k) α := by
    apply measureReal_mono (μ := (F.model k).law) ?_ (measure_ne_top _ _)
    intro y hy
    exact AronowAudit.P011.interval_containment _ _ _ _ hz (min_le_left _ _) hy
  have hbelow : atTop.IsBoundedUnder (· ≥ ·)
      (fun k => SAP.P011a.coverage (F.model k) (V k) α) :=
    isBoundedUnder_of ⟨0, fun k => measureReal_nonneg⟩
  have habove : atTop.IsBoundedUnder (· ≤ ·)
      (fun k => SAP.P011a.coverage (F.model k) (V k) α) := by
    refine isBoundedUnder_of ⟨1, fun k => ?_⟩
    simpa only [SAP.P011a.coverage, SAP.P011a.probability, measureReal_def,
      measure_univ, ENNReal.toReal_one] using
      measureReal_mono (μ := (F.model k).law) (Set.subset_univ
        {y | |betaHat (F.model k) y-beta (F.model k)| ≤
          SAP.P011a.normalQuantile α * Real.sqrt (max (V k y) 0)})
  apply (le_liminf_iff habove.isCoboundedUnder_flip hbelow).mpr
  intro y hy
  filter_upwards [(hlim α hα hα1).eventually_const_lt hy] with k hk
  exact hk.trans_le (hdom k)

end
end SAP.P011a.WH.W1.P.T7_L4

theorem SAP.P011a.WH.W1.T7_L4_proof : SAP.P011a.WH.W1.T7_L4 := by
  intro hclt F c1 c2 c3 c4 h V hV hc
  exact SAP.P011a.WH.W1.P.T7_L4.conservative_coverage hclt F c1 c2 c3 c4 h V hV hc
