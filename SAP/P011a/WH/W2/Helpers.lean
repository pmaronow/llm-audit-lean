import SAP.P011a.Defs.WholeW2
import SAP.P011a.Bridge
import AronowAudit.P011.Wave1.PropositionOne.N2
import AronowAudit.P011.Wave1.PropositionOne.N8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W2

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

theorem rowScaling_of_scaling {F : Family} {c1 c2 c3 c4 : ℝ}
    (h : Scaling F c1 c2 c3 c4) : RowScaling F c1 c2 c3 c4 := h.2

theorem whole_bias (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : RowScaling F c1 c2 c3 c4) (k : ℕ) :
    |meanBias (F.model k)| ≤ (1+c2)*c1^2 := by
  rcases h with ⟨hc1,_,_,_,hDep,hBound,hDeg,_,_⟩
  let m := Bridge.model (F.model k)
  have hL2 := AronowAudit.P011.ProbabilityCompletion.weighted_memLp m c1 (hBound k)
  have hu (i : Fin (F.size k)) : |delta (F.model k) i| ≤ c1 :=
    AronowAudit.P011.ProbabilityCompletion.own_mean_bound m c1 hL2 (hBound k) i
  have hq := AronowAudit.P011.MeanCompletion.quadratic_bound (F.model k).G c1 (1+c2)
    hc1.le (fun i => by change (degree (F.model k).G i : ℝ)+1 ≤ 1+c2; linarith [hDeg k i]) (delta (F.model k)) hu
  change |quadratic (oracleMatrix (F.model k).G) (delta (F.model k))| ≤
    (F.size k : ℝ)*(1+c2)*c1^2 at hq
  have hnR : 0 < (F.size k : ℝ) := by exact_mod_cast F.positive k
  unfold meanBias
  rw [abs_div, abs_of_pos hnR]
  exact (div_le_iff₀ hnR).mpr (by nlinarith [hq])

theorem whole_expectation : OracleExpectationWhole := by
  intro F c1 c2 c3 c4 h k
  rcases h with ⟨hc1,hc2,_,_,hDep,hBound,hDeg,_,_⟩
  exact AronowAudit.P011.ExpectationCompletion.finite_oracle_expectation_bound
    (F.positive k) (Bridge.model (F.model k)) c1 (1+c2) hc1.le (by linarith)
    (hDep k) (hBound k) (fun i => by
      change (degree (F.model k).G i : ℝ)+1 ≤ 1+c2; linarith [hDeg k i])

theorem whole_mean_conditions (hconv : OracleConvergenceWhole) : OracleMeanConditionsWhole := by
  intro F c1 c2 c3 c4 h
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let μ := fun k=>(F.model k).law
  let X := fun k y=>scaledOracle F k y-scaledTrue F k
  let b := fun k=>meanBias (F.model k)
  have hE : AronowAudit.P011.CoverageCompletion.RowCP μ (fun k y=>X k y-b k) 0 := by
    intro ε hε
    have hh := hconv F c1 c2 c3 c4 h ε hε
    have he (k : ℕ) (y : Fin (F.size k)→ℝ) : X k y-b k-0=
        (F.size k:ℝ)*V1 (F.model k).G (weighted (F.model k) y)-
          ((F.size k:ℝ)*var (F.model k) (betaHat (F.model k))+meanBias (F.model k)) := by
      dsimp [X,b,scaledOracle,scaledTrue]
      ring
    simpa only [he,μ,probability] using hh
  have hBound (k : ℕ) : |b k| ≤(1+c2)*c1^2 := whole_bias F c1 c2 c3 c4 h k
  have hBelow : IsBoundedUnder (·≥·) atTop b := by
    refine ⟨-((1+c2)*c1^2),?_⟩
    change ∀ᶠ k : ℕ in atTop,-((1+c2)*c1^2)≤b k
    exact Eventually.of_forall fun k=>(abs_le.mp (hBound k)).1
  have hAbove : IsBoundedUnder (·≤·) atTop b := by
    refine ⟨(1+c2)*c1^2,?_⟩
    change ∀ᶠ k : ℕ in atTop,b k≤(1+c2)*c1^2
    exact Eventually.of_forall fun k=>(abs_le.mp (hBound k)).2
  have hIff : InProbability F (scaledOracle F) (scaledTrue F)↔Tendsto b atTop (𝓝 0) := by
    constructor
    · intro hx
      have hx' : AronowAudit.P011.CoverageCompletion.RowCP μ X 0 := by simpa only [AronowAudit.P011.CoverageCompletion.RowCP,InProbability,probability,μ,X,sub_zero] using hx
      exact AronowAudit.P011.MeanCompletion.deterministic_centres μ X b hx' hE
    · intro hb
      have hx := AronowAudit.P011.CoverageCompletion.rowCP_moving_center μ X b 0
        (by simpa only [AronowAudit.P011.CoverageCompletion.RowCP,sub_zero] using hE) hb
      simpa only [AronowAudit.P011.CoverageCompletion.RowCP,InProbability,probability,μ,X,sub_zero] using hx
  have hCiff : Conservative F (fun k y=>V1 (F.model k).G (weighted (F.model k) y))↔0≤liminf b atTop := by
    have hh := AronowAudit.P011.MeanCompletion.conservative_centres μ X b hE hBelow hAbove
    have he (k : ℕ) (y : Fin (F.size k)→ℝ) :
        (F.size k:ℝ)*(var (F.model k) (betaHat (F.model k))-V1 (F.model k).G (weighted (F.model k) y))= -X k y := by
      dsimp [X,scaledOracle,scaledTrue]
      ring
    simpa only [Conservative,probability,μ,he] using hh
  refine ⟨hIff,hCiff,?_,?_⟩
  · intro hδ
    apply hIff.mpr
    have he : b=fun _=>(0:ℝ) := by
      funext k
      simp [b,meanBias,quadratic,hδ k]
    rw [he]
    exact tendsto_const_nhds
  · intro hPSD
    apply hCiff.mpr
    apply (le_liminf_iff hAbove.isCoboundedUnder_ge hBelow).mpr
    intro y hy
    filter_upwards [] with k
    have hb : 0≤b k := div_nonneg ((hPSD k).2 (delta (F.model k))) (Nat.cast_nonneg _)
    linarith


theorem residual_prediction_of_misspec (hmiss : ResidualMisspecificationWhole) :
    ResidualPredictionWhole := by
  intro F c1 c2 c3 c4 h p D γ γhat hmeas hmean hz herr A hv hm
  have hlim := hmiss F c1 c2 c3 c4 h p D γ γhat hmeas hz herr
  have hb (k : ℕ) (i : Fin (F.size k)) : expectation (F.model k)
      (fun y => weighted (F.model k) y i) - (F.model k).theta i*(D k *ᵥ γ) i = 0 := by
    have hw : expectation (F.model k) (fun y => weighted (F.model k) y i) =
        (F.model k).theta i*(D k *ᵥ γ) i :=
      AronowAudit.P011.Wave1.rps_weighted_mean (Bridge.model (F.model k))
        (D k) γ (hmean k) i
    rw [hw, sub_self]
  have ho : InProbability F (fun k y => (F.size k : ℝ)*VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (γhat k) y)) (scaledTrue F) := by
    intro ε hε
    simpa only [hb, quadratic, mul_zero, zero_mul, Finset.sum_const_zero,
      zero_div, sub_zero] using hlim ε hε
  exact ⟨ho, AronowAudit.P011.Wave1.rps_maximum_conservative (Bridge.family F)
    (fun k y => fittedResidual (F.model k) (D k) (γhat k) y) A hv hm ho⟩

theorem residual_root_of_prediction (hpred : ResidualPredictionWhole) :
    ResidualRootRateWhole := by
  intro F c1 c2 c3 c4 h p D γ γhat hmeas hmean hbound hrate A hv hm
  classical
  have hcopy := h
  obtain ⟨hc1,hc2,hc3,hc4,hDep,hBound,hDeg,hVar,hTheta⟩ := hcopy
  have hL2 (k : ℕ) (i : Fin (F.size k)) :=
    AronowAudit.P011.ProbabilityCompletion.weighted_memLp
      (Bridge.model (F.model k)) c1 (hBound k) i
  have hmom (k : ℕ) := AronowAudit.P011.Wave1.rrn_residual_moments
    (Bridge.model (F.model k)) (D k) γ (hmean k) (hL2 k)
  have hz (k : ℕ) : ∀ᵐ y ∂(F.model k).law,
      ∀ i, |trueResidual (F.model k) (D k) γ y i| ≤ 2*c1 := by
    have hb := AronowAudit.P011.ProbabilityCompletion.own_centred_bound
      (Bridge.model (F.model k)) c1 (hL2 k) (hBound k)
    filter_upwards [hb] with y hy
    intro i
    have he : trueResidual (F.model k) (D k) γ y i =
        weighted (F.model k) y i-expectation (F.model k) (fun z => weighted (F.model k) z i) :=
      AronowAudit.P011.Wave1.rps_true_eq (Bridge.model (F.model k)) (D k) γ (hmean k) y i
    rw [he]
    exact hy i
  obtain ⟨B₀,hB₀⟩ := hbound
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hD (k : ℕ) (i : Fin (F.size k)) : l2 (D k i) ≤ B :=
    (hB₀ k i).trans (le_max_left _ _)
  let S := fun k y => Real.sqrt (F.size k : ℝ)*l2 (γhat k y-γ)
  let E := fun k y => fittedResidual (F.model k) (D k) (γhat k) y -
    trueResidual (F.model k) (D k) γ y
  have hSpos (k : ℕ) (y : Fin (F.size k) → ℝ) : 0 ≤ S k y :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfinite (k : ℕ) (y : Fin (F.size k) → ℝ) :
      Real.sqrt (F.size k : ℝ)*maxAbs (E k y) ≤ (c4*B)*S k y ∧
        l2 (E k y) ≤ (c4*B)*S k y :=
    AronowAudit.P011.Wave1.rrn_error_norm_bounds (Bridge.model (F.model k))
      (D k) γ (γhat k) c4 B hc4.le hB (fun i => (hTheta k i).le) (hD k) y
  have hmax : Tight F (fun k y => Real.sqrt (F.size k : ℝ)*maxAbs (E k y)) := by
    apply AronowAudit.P011.Wave1.rrn_tight_dominated (Bridge.family F) S _
      (c4*B) (mul_nonneg hc4.le hB) hrate
    dsimp only [Bridge.family]
    intro k
    exact Eventually.of_forall fun y => by
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (show 0 ≤ maxAbs (E k y) from NNReal.coe_nonneg _)), abs_of_nonneg (hSpos k y)]
      exact (hfinite k y).1
  have hnorm : Tight F (fun k y => l2 (E k y)) := by
    apply AronowAudit.P011.Wave1.rrn_tight_dominated (Bridge.family F) S _
      (c4*B) (mul_nonneg hc4.le hB) hrate
    dsimp only [Bridge.family]
    intro k
    exact Eventually.of_forall fun y => by
      rw [abs_of_nonneg (show 0 ≤ l2 (E k y) from Real.sqrt_nonneg _), abs_of_nonneg (hSpos k y)]
      exact (hfinite k y).2
  have htrue : Tight F (fun k y =>
      l2 (trueResidual (F.model k) (D k) γ y)/Real.sqrt (F.size k : ℝ)) := by
    apply AronowAudit.P011.Wave1.rrn_tight_ae_bound (Bridge.family F) _ (2*c1) (by positivity)
    dsimp only [Bridge.family]
    intro k
    filter_upwards [hz k] with y hy
    rw [abs_of_nonneg (div_nonneg (show 0 ≤ l2 (trueResidual (F.model k) (D k) γ y) from Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact AronowAudit.P011.Wave1.rrn_l2_div_bound (F.positive k) _ (2*c1) (by positivity) hy
  have herr : InProbability F (fun k y => l2 (E k y)/Real.sqrt (F.size k : ℝ))
      (fun _ => 0) := AronowAudit.P011.Wave1.rrn_tight_div_sqrt (Bridge.family F) _ hnorm
  have hlast := hpred F c1 c2 c3 c4 h p D γ γhat hmeas hmean ⟨2*c1,hz⟩ herr A hv hm
  exact ⟨(fun k i => (hmom k).1 i), (fun k i j => (hmom k).2 i j),
    hmax, hnorm, htrue, hlast.1, hlast.2⟩

end
end SAP.P011a.WH.W2
