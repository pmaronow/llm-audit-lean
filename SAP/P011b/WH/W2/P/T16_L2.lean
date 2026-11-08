import SAP.P011b.WH.W2.Leaves
import AronowAudit.P011.Wave1.Gap.GP011B3
import AronowAudit.P011.P011_CoverageCompletion
import AronowAudit.P011.P011_OracleCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

namespace SAP.P011b.WH.W2.P.T16_L2

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

end SAP.P011b.WH.W2.P.T16_L2

theorem SAP.P011b.WH.W2.T16_L2_proof : SAP.P011b.WH.W2.T16_L2 := by
  intro F c1 c2 c3 c4 hscale p D b hmean hD hrate
  have hscale0 := hscale
  rcases hscale with ⟨_, hc1, hc2, _, hc4, _, _, _, _, htheta⟩
  obtain ⟨Bx, hBx, hrows⟩ := hD
  let μ : ∀ k, MeasureTheory.Measure (Fin (F.size k) → ℝ) := fun k => (F.model k).law
  letI : ∀ k, IsProbabilityMeasure (μ k) := fun k => (F.model k).probability
  let S : ∀ k, (Fin (F.size k) → ℝ) → ℝ :=
    fun k y => Real.sqrt (F.size k : ℝ) * SAP.P011b.l2 (ols (D k) y - b k)
  let Δ : ∀ k, (Fin (F.size k) → ℝ) → (Fin (F.size k) → ℝ) :=
    fun k y => olsDeltaW2 (F.model k) (D k) (b k) y
  let d : ∀ k, (Fin (F.size k) → ℝ) → ℝ :=
    fun k y => SAP.P011b.l2 (Δ k y) / Real.sqrt (F.size k : ℝ)

  have hrate' : AronowAudit.P011.Tight (SAP.P011b.Bridge.toFamily F) S := by
    change AronowAudit.P011.Tight (SAP.P011b.Bridge.toFamily F) S
    exact hrate

  have hdeltaBound (k : ℕ) (y : Fin (F.size k) → ℝ) :
      SAP.P011b.l2 (Δ k y) ≤ (c4 * Bx) * S k y := by
    have hh := AronowAudit.P011.Wave1.rrn_error_norm_bounds
      (SAP.P011b.Bridge.toModel (F.model k)) (D k) (b k) (fun y => ols (D k) y)
      c4 Bx hc4.le hBx
      (fun i => le_of_lt (htheta k i)) (hrows k) y
    have hres :
        (fun i =>
          (SAP.P011b.fittedResidual (F.model k) (D k) (ols (D k)) y -
            SAP.P011b.trueResidual (F.model k) (D k) (b k) y) i) =
          -Δ k y := by
      funext i
      rw [SAP.P011b.WH.W2.fitted_eqW2 (F.model k) (D k) (b k) y]
      simp [Δ, SAP.P011b.olsDeltaW2]
    have hres' :
        AronowAudit.P011.fittedResidual (SAP.P011b.Bridge.toModel (F.model k))
            (D k) (fun y => ols (D k) y) y -
          AronowAudit.P011.trueResidual (SAP.P011b.Bridge.toModel (F.model k))
            (D k) (b k) y = -Δ k y := by
      funext i
      simpa [SAP.P011b.Bridge.toModel, SAP.P011b.fittedResidual,
        AronowAudit.P011.fittedResidual, SAP.P011b.trueResidual,
        AronowAudit.P011.trueResidual, Δ] using congrFun hres i
    have hn : SAP.P011b.l2 (Δ k y) ≤
        (c4 * Bx) * (Real.sqrt (F.size k : ℝ) *
          SAP.P011b.l2 (ols (D k) y - b k)) := by
      have hhneg := hh.2
      rw [hres'] at hhneg
      simpa [SAP.P011b.l2, AronowAudit.P011.l2, S, Δ] using hhneg
    simpa [S] using hn

  have hdeltaTight' : AronowAudit.P011.Tight (SAP.P011b.Bridge.toFamily F)
      (fun k y => SAP.P011b.l2 (Δ k y)) := by
    apply AronowAudit.P011.Wave1.rrn_tight_dominated
      (SAP.P011b.Bridge.toFamily F) S _ (c4 * Bx) (mul_nonneg hc4.le hBx) hrate'
    intro k
    exact Eventually.of_forall fun y => by
      have hnon : 0 ≤ SAP.P011b.l2 (Δ k y) := Real.sqrt_nonneg _
      have hsnon : 0 ≤ S k y := by
        dsimp [S]
        exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rw [abs_of_nonneg hnon, abs_of_nonneg hsnon]
      simpa [S, SAP.P011b.l2, AronowAudit.P011.l2] using hdeltaBound k y

  have hd' := AronowAudit.P011.Wave1.rrn_tight_div_sqrt
    (SAP.P011b.Bridge.toFamily F) (fun k y => SAP.P011b.l2 (Δ k y)) hdeltaTight'
  have hd : SAP.P011b.InProbability F d (fun _ => 0) := by
    change AronowAudit.P011.InProbability (SAP.P011b.Bridge.toFamily F)
      (fun k y => SAP.P011b.l2 (Δ k y) / Real.sqrt (F.size k : ℝ)) (fun _ => 0)
    exact hd'

  have htrueBound : ∀ k, ∀ᵐ y ∂(F.model k).law,
      SAP.P011b.l2 (SAP.P011b.trueResidual (F.model k) (D k) (b k) y) /
        Real.sqrt (F.size k : ℝ) ≤ 2 * c1 := by
    intro k
    filter_upwards [SAP.P011b.WH.W2.true_error_boundW2 F c1 c2 c3 c4 hscale0 p D b hmean k]
      with y hy
    have hb := AronowAudit.P011.Wave1.rrn_l2_div_bound (F.positive k) _ (2 * c1)
      (by positivity) hy
    simpa [SAP.P011b.l2, AronowAudit.P011.l2] using hb

  let f : ℝ × ℝ → ℝ := fun z => (1 + c2) * (4 * c1 * z.1 + z.1 ^ 2)
  have hf : ContinuousAt f (0, 0) := by
    dsimp [f]
    fun_prop

  have hpoly : AronowAudit.P011.CoverageCompletion.RowCP μ
      (fun k y => f (d k y, 0)) 0 := by
    have hdrow : AronowAudit.P011.CoverageCompletion.RowCP μ d 0 := by
      change AronowAudit.P011.CoverageCompletion.RowCP μ d 0
      intro ε hε
      have hh := hd ε hε
      change Tendsto (fun k => (F.model k).law.real {y | |d k y - 0| > ε}) atTop (𝓝 0)
      simpa [μ, SAP.P011b.probability, sub_zero] using hh
    have hzero : AronowAudit.P011.CoverageCompletion.RowCP μ (fun _ _ => (0 : ℝ)) 0 :=
      AronowAudit.P011.CoverageCompletion.rowCP_det μ (fun _ => (0 : ℝ)) 0
        tendsto_const_nhds
    have hh := AronowAudit.P011.CoverageCompletion.rowCP_continuous_pair μ d
      (fun _ _ => (0 : ℝ)) 0 0 hdrow hzero f hf
    simpa [f] using hh

  have hdom : ∀ k, ∀ᵐ y ∂(F.model k).law,
      |SAP.P011b.perturbationRHSW2 c2
          (SAP.P011b.trueResidual (F.model k) (D k) (b k) y) (Δ k y)| ≤
        f (d k y, 0) := by
    intro k
    have hn : 0 < F.size k := F.positive k
    have hnR : 0 < (F.size k : ℝ) := by exact_mod_cast hn
    have hsqrt : 0 < Real.sqrt (F.size k : ℝ) := Real.sqrt_pos.mpr hnR
    filter_upwards [htrueBound k] with y hy
    have hdnonneg : 0 ≤ d k y :=
      by
        dsimp [d]
        exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq :
        SAP.P011b.l2 (Δ k y) ^ 2 / (F.size k : ℝ) = (d k y) ^ 2 := by
      dsimp [d]
      rw [div_pow, Real.sq_sqrt hnR.le]
    have hprod :
        2 * (SAP.P011b.l2
          (SAP.P011b.trueResidual (F.model k) (D k) (b k) y) /
          Real.sqrt (F.size k : ℝ)) * d k y ≤ 4 * c1 * d k y := by
      have hmul := mul_le_mul_of_nonneg_right hy
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdnonneg)
      nlinarith
    have hcoef : 0 ≤ 1 + c2 := by linarith
    have hraw :
        SAP.P011b.perturbationRHSW2 c2
          (SAP.P011b.trueResidual (F.model k) (D k) (b k) y) (Δ k y) ≤
          f (d k y, 0) := by
      unfold SAP.P011b.perturbationRHSW2 f
      rw [hsq]
      have hprod' := mul_le_mul_of_nonneg_left hprod hcoef
      simp only [Prod.fst, Prod.snd, zero_mul, add_zero]
      nlinarith
    have hraw_nonneg : 0 ≤ SAP.P011b.perturbationRHSW2 c2
        (SAP.P011b.trueResidual (F.model k) (D k) (b k) y) (Δ k y) := by
      unfold SAP.P011b.perturbationRHSW2
      apply mul_nonneg (by linarith)
      apply add_nonneg
      · exact mul_nonneg
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
            (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
          hdnonneg
      · exact div_nonneg (sq_nonneg _) hnR.le
    rw [abs_of_nonneg hraw_nonneg]
    exact hraw

  have hresult := AronowAudit.P011.OracleCompletion.rowCP_dominated μ
    (fun k y => SAP.P011b.perturbationRHSW2 c2
      (SAP.P011b.trueResidual (F.model k) (D k) (b k) y) (Δ k y))
    (fun k y => f (d k y, 0)) hpoly hdom
  change AronowAudit.P011.CoverageCompletion.RowCP μ
    (fun k y => SAP.P011b.perturbationRHSW2 c2
      (SAP.P011b.trueResidual (F.model k) (D k) (b k) y) (Δ k y)) 0
  simpa [AronowAudit.P011.CoverageCompletion.RowCP,
    SAP.P011b.probability, μ, Δ] using hresult
