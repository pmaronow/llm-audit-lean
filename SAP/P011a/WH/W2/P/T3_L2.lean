import SAP.P011a.WH.W2.Leaves
import AronowAudit.P011.P011_SampleCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W2.P.T3_L2

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

theorem prove : SAP.P011a.WH.W2.T3_L2 := by
  intro F c1 c2 c3 c4 h
  classical
  let G : AronowAudit.P011.Family := SAP.P011a.Bridge.family F
  let m (k : ℕ) : AronowAudit.P011.Model (F.size k) :=
    SAP.P011a.Bridge.model (F.model k)
  let (k : ℕ) : IsProbabilityMeasure (m k).law := (m k).probability
  rcases h with ⟨hc1,hc2,hc3,hc4,hDep,hBound,hDeg,hScaled,hTheta⟩
  have hN : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  have hbeta (k : ℕ) : AronowAudit.P011.beta (m k) = SAP.P011a.beta (F.model k) := rfl
  have hBound' (k : ℕ) : ∀ᵐ y ∂(m k).law, ∀ i,
      |AronowAudit.P011.weighted (m k) y i-AronowAudit.P011.beta (m k)| ≤ c1 := by
    filter_upwards [hBound k] with y hy
    intro i
    change |AronowAudit.P011.weighted (SAP.P011a.Bridge.model (F.model k)) y i -
      AronowAudit.P011.beta (SAP.P011a.Bridge.model (F.model k))| ≤ c1
    rw [← SAP.P011a.Bridge.weighted_eq, hbeta k]
    exact hy i
  have hDep' (k : ℕ) : AronowAudit.P011.Dependency (m k) := by
    change AronowAudit.P011.VariableDependency (F.model k).law (F.model k).G
      (fun i y => y i)
    exact hDep k
  have hDeg' (k : ℕ) (i : Fin (F.size k)) :
      (AronowAudit.P011.degree (m k).G i : ℝ) ≤ c2 := by
    change (degree (F.model k).G i : ℝ) ≤ c2
    exact hDeg k i
  have hU2 (k : ℕ) : MemLp (AronowAudit.P011.U (m k)) 2 (m k).law :=
    AronowAudit.P011.SampleCompletion.U_memLp_two (m k) c1 (hBound' k)
  have hUV : Tendsto
      (fun k => ProbabilityTheory.variance (AronowAudit.P011.U (m k)) (m k).law)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => ProbabilityTheory.variance_nonneg _ _) (fun k => ?_)
      (hN.const_div_atTop ((1+c2)*c1^4))
    have hd (i : Fin (F.size k)) :
        (AronowAudit.P011.degree (m k).G i : ℝ)+1 ≤ 1+c2 := by
      linarith [hDeg' k i]
    have hv := AronowAudit.P011.SampleCompletion.U_variance_bound
      (F.positive k) (m k) c1 (1+c2) hc1.le (hDep' k) (hBound' k) hd
    unfold AronowAudit.P011.var AronowAudit.P011.expectation at hv
    rw [←ProbabilityTheory.variance_eq_integral (hU2 k).aemeasurable] at hv
    exact hv
  have hUC := AronowAudit.P011.OracleCompletion.rowCP_of_variance
    (fun k => (m k).law) (fun k => AronowAudit.P011.U (m k)) hU2 hUV
  have hMean (k : ℕ) : AronowAudit.P011.meanVariance (m k) +
      AronowAudit.P011.meanSpread (m k) =
      SAP.P011a.meanVariance (F.model k) + SAP.P011a.meanSpread (F.model k) := by
    rfl
  have hUC' : ∀ ε > (0:ℝ), Tendsto (fun k => (m k).law.real
      {y | |AronowAudit.P011.U (m k) y -
        (SAP.P011a.meanVariance (F.model k)+SAP.P011a.meanSpread (F.model k))| > ε})
      atTop (𝓝 0) := by
    have he (k : ℕ) : (∫ y, AronowAudit.P011.U (m k) y ∂(m k).law) =
        AronowAudit.P011.meanVariance (m k)+AronowAudit.P011.meanSpread (m k) :=
      AronowAudit.P011.SampleCompletion.U_mean (m k) c1 (hBound' k)
    simpa only [he, hMean] using hUC
  have hBV : Tendsto
      (fun k => ProbabilityTheory.variance (AronowAudit.P011.betaHat (m k)) (m k).law)
      atTop (𝓝 0) := by
    have hvar (k : ℕ) : SAP.P011a.var (F.model k) (SAP.P011a.betaHat (F.model k)) =
        AronowAudit.P011.var (m k) (AronowAudit.P011.betaHat (m k)) := rfl
    have heScaled (k : ℕ) : SAP.P011a.scaledTrue F k =
        (F.size k : ℝ) * AronowAudit.P011.var (m k)
          (AronowAudit.P011.betaHat (m k)) := by
      simp only [SAP.P011a.scaledTrue, hvar]
    have hs : Tendsto (fun k => (F.size k : ℝ) * AronowAudit.P011.var (m k)
        (AronowAudit.P011.betaHat (m k))) atTop (𝓝 c3) := by
      have hseq : (fun k => SAP.P011a.scaledTrue F k) =
          (fun k => (F.size k : ℝ) * AronowAudit.P011.var (m k)
            (AronowAudit.P011.betaHat (m k))) := by
        funext k
        exact heScaled k
      rw [← hseq]
      exact hScaled
    have hv := hs.div_atTop hN
    have he (k : ℕ) : ((F.size k : ℝ) * AronowAudit.P011.var (m k)
        (AronowAudit.P011.betaHat (m k)))/(F.size k:ℝ) =
        ProbabilityTheory.variance (AronowAudit.P011.betaHat (m k)) (m k).law := by
      rw [ProbabilityTheory.variance_eq_integral
        (AronowAudit.P011.ProbabilityCompletion.betaHat_measurable (m k)).aemeasurable]
      rw [AronowAudit.P011.var, AronowAudit.P011.expectation]
      simp only [AronowAudit.P011.expectation]
      have hn0 : (F.size k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (F.positive k)
      field_simp
    simpa only [he] using hv
  have hBC : AronowAudit.P011.CoverageCompletion.RowCP
      (fun k => (m k).law)
      (fun k y => AronowAudit.P011.betaHat (m k) y-AronowAudit.P011.beta (m k)) 0 := by
    simpa only [AronowAudit.P011.CoverageCompletion.RowCP, sub_zero,
      AronowAudit.P011.beta, AronowAudit.P011.expectation] using
      AronowAudit.P011.OracleCompletion.rowCP_of_variance
        (fun k => (m k).law) (fun k => AronowAudit.P011.betaHat (m k))
        (fun k => AronowAudit.P011.ProbabilityCompletion.betaHat_memLp (m k)
          (AronowAudit.P011.ProbabilityCompletion.weighted_memLp (m k) c1 (hBound' k))) hBV
  have hE : AronowAudit.P011.CoverageCompletion.RowCP
      (fun k => (m k).law)
      (fun k y => AronowAudit.P011.sampleVariance
          (AronowAudit.P011.weighted (m k) y)-AronowAudit.P011.U (m k) y) 0 := by
    have hh := AronowAudit.P011.CoverageCompletion.rowCP_continuous_pair
      (fun k => (m k).law)
      (fun k y => AronowAudit.P011.betaHat (m k) y-AronowAudit.P011.beta (m k))
      (fun _ _ => (0:ℝ)) 0 0 hBC
      (AronowAudit.P011.CoverageCompletion.rowCP_det _ (fun _ => (0:ℝ)) 0
        tendsto_const_nhds)
      (fun p : ℝ×ℝ => -(p.1)^2) (by fun_prop)
    have he (k : ℕ) (y : Fin (F.size k) → ℝ) :
        AronowAudit.P011.sampleVariance (AronowAudit.P011.weighted (m k) y)-
          AronowAudit.P011.U (m k) y =
        -(AronowAudit.P011.betaHat (m k) y-AronowAudit.P011.beta (m k))^2 := by
      rw [AronowAudit.P011.SampleCompletion.sample_center_identity (F.positive k)]
      ring
    simpa only [he, zero_pow (by decide : 2 ≠ 0), neg_zero] using hh
  have hfinal := AronowAudit.P011.OracleCompletion.row_moving_add_error
    (fun k => (m k).law)
    (fun k y => AronowAudit.P011.U (m k) y)
    (fun k y => AronowAudit.P011.sampleVariance
      (AronowAudit.P011.weighted (m k) y))
    (fun k => SAP.P011a.meanVariance (F.model k)+SAP.P011a.meanSpread (F.model k))
    hUC' hE
  intro ε hε
  have hh := hfinal ε hε
  have hsample (k : ℕ) (y : Fin (F.size k) → ℝ) :
      AronowAudit.P011.sampleVariance (AronowAudit.P011.weighted (m k) y) =
        SAP.P011a.sampleVariance (SAP.P011a.weighted (F.model k) y) := by
    rfl
  change Tendsto (fun k => (F.model k).law.real
    {y | |SAP.P011a.sampleVariance (SAP.P011a.weighted (F.model k) y) -
      (SAP.P011a.meanVariance (F.model k)+SAP.P011a.meanSpread (F.model k))| > ε})
    atTop (𝓝 0)
  have hlaw (k : ℕ) : (m k).law = (F.model k).law := rfl
  simpa only [hsample, ← SAP.P011a.Bridge.weighted_eq, hlaw] using hh

end
end SAP.P011a.WH.W2.P.T3_L2

theorem SAP.P011a.WH.W2.T3_L2_proof : SAP.P011a.WH.W2.T3_L2 :=
  SAP.P011a.WH.W2.P.T3_L2.prove
