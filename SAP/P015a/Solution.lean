import SAP.P015a.Defs
import SAP.P015a.Bridge
import AronowAudit.P015.P015_Regression
import AronowAudit.P015.P015_PaperSpecializations
import AronowAudit.P015.P015_PaperDomains
import AronowAudit.P015.Wave1.Gap.FidP015
import SAP.P015a.WH.W1.Proofs.T12
import SAP.P015a.WH.W1.Proofs.T8

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
open AronowAudit.P015
universe u v
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

/-- The fixed-law arithmetic supplements the complete existing certificate. -/
theorem SAP.P015a.T1 : SAP.P015a.T1Statement := by
  apply SAP.P015a.Bridge.T1_correspondence.mpr
  refine ⟨RareCounterexample_checked, ?_⟩
  norm_num [fCondProb, fCondMean, fExpectation, fMass, fWeight, fEffective,
    rareLaw, binaryX, binaryD, Fin.sum_univ_succ]

theorem SAP.P015a.T2 : SAP.P015a.T2Statement.{u} := by
  apply SAP.P015a.Bridge.T2_correspondence.mpr
  refine ⟨MultivaluedCounterexample_checked, ?_⟩
  norm_num [fCondMean, fExpectation, fMass, fWeight, multiLaw, multiD,
    binaryX, Fin.sum_univ_succ]

theorem SAP.P015a.T3 : SAP.P015a.T3Statement := by
  apply SAP.P015a.Bridge.T3_correspondence.mpr
  refine ⟨FittedZeroCounterexample_checked, ?_⟩
  rw [FittedZeroCounterexample_checked.2.1.2.1]
  norm_num [funext_iff, Fin.forall_fin_succ]

theorem SAP.P015a.T4 : SAP.P015a.T4Statement.{u,v} := by
  apply SAP.P015a.Bridge.T4_correspondence.mpr
  refine ⟨PositivityCorrection_checked, ?_⟩
  intro Ω B _ _ _ _ P _ X D hX hD h₂ x hx
  have h := PositivityCorrection_checked.1 P X D hX hD h₂
  refine ⟨?_, ?_, ?_⟩
  · intro hv d d' hdd hp
    have hpos := (h.1 x hx).1 d d' hdd hp.1 hp.2
    rw [hv] at hpos
    exact lt_irrefl _ hpos
  · intro hbin
    haveI : IsProbabilityMeasure (cellLaw P X x) :=
      PositivityCompletion.cell_probability P X x hx
    have hp0 : cellProb P X D x 0 = 1-cellProb P X D x 1 :=
      PositivityCompletion.binary_probability_zero (cellLaw P X x) D hD
        (PositivityCompletion.cell_ae_of_ae P X x hbin)
    refine ⟨hp0, ?_⟩
    rw [(h.2.1 hbin x hx).2, hp0]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  · intro hw hi
    refine ⟨PositivityCompletion.effective_probability P X D hi hw, ?_⟩
    intro hbin hQ
    have he := h.2.2 hw hi x hx
    have hvne : cellVar P X D x ≠ 0 := by
      intro hv
      exact (ne_of_gt hQ) (he.2.1.mpr hv)
    have hvnon : 0 ≤ cellVar P X D x := integral_nonneg (fun _ => sq_nonneg _)
    have hvpos : 0 < cellVar P X D x := lt_of_le_of_ne hvnon hvne.symm
    have hp := (h.2.1 hbin x hx).2.mp hvpos
    have hr := he.2.2 hbin hp.1 hp.2
    refine ⟨hvpos, ?_, ?_⟩
    · rw [hr.2]
      exact hp.1
    · rw [hr.1]
      exact sub_pos.mpr hp.2

/-- Only the components with usable credit are assembled here. -/
theorem SAP.P015a.T5 : SAP.P015a.T5Statement := by
  apply SAP.P015a.Bridge.T5_correspondence.mpr
  exact ⟨⟨odds_score_counterexample,
    PaperSpecializations.odds_not_mle_calculus.2.1,
    PaperSpecializations.odds_gram_determinant.2.2.1,
    odds_model_details⟩, odds_multiplier⟩

theorem SAP.P015a.T6 : SAP.P015a.T6Statement := by
  apply SAP.P015a.Bridge.T6_correspondence.mpr
  have h := ProbitCounterexample_checked
  have hc : normalCDF probitA = 3/4 := h.1.2.2.2.2.1
  have h0 : normalCDF 0 = 1/2 := h.1.2.2.2.1
  refine ⟨h, ⟨⟨probitA, hc.ge⟩, ?_⟩, ?_⟩
  · refine ⟨0, ?_⟩
    intro x hx
    by_contra hn
    have hl := AnalyticCompletion.strictMono_normalCDF (lt_of_not_ge hn)
    rw [h0] at hl
    change 3/4 ≤ normalCDF x at hx
    linarith
  · intro v
    have hd := likelihood_directional_derivative_calculus probitW (fun _ => 8)
      probitSuccess normalCDF ![0,0,probitA] v
      (fun _ => (AnalyticCompletion.hasDerivAt_normalCDF _).differentiableAt)
      (fun _ => (AnalyticCompletion.normalCDF_bounds _).1)
      (fun _ => (AnalyticCompletion.normalCDF_bounds _).2)
    simpa only [AnalyticCompletion.scoreMultiplier_normalCDF] using hd

theorem SAP.P015a.T7 : SAP.P015a.T7Statement := by
  apply SAP.P015a.Bridge.T7_correspondence.mpr
  refine ⟨RootLinkCounterexample_checked, ?_, ?_,
    RootPotentialCompletion.unit_D_integrable, ?_⟩
  · intro θ
    refine ⟨rfl, ?_⟩
    intro i
    simp [rootZ, rootE, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · intro α β γ
    refine ⟨![α+β/2, β, γ+β/4], ?_⟩
    ext j
    fin_cases j <;> simp
  · intro a ε
    exact RootPotentialCompletion.unitY_integrable rootUnitLaw a ε rootUnitD measurable_fst.snd

theorem SAP.P015a.T8 : SAP.P015a.T8WholeStatement :=
  SAP.P015a.WH.W1.T8_whole

theorem SAP.P015a.T12 : SAP.P015a.T12WholeStatement :=
  SAP.P015a.WH.W1.T12_whole

theorem SAP.P015a.T13 : SAP.P015a.T13Statement := by
  exact SAP.P015a.Bridge.T13_correspondence.mpr corrected_logistic_taylor

theorem SAP.P015a.T16 : SAP.P015a.T16Statement := by
  apply SAP.P015a.Bridge.T16_correspondence.mpr
  refine ⟨log_points_numeric_correction, exponentiated_fitted_contrast,
    spending_mean_counterexample, ?_⟩
  norm_num [Matrix.det_fin_two, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

theorem SAP.P015a.T19 : SAP.P015a.T19Statement.{u,v} := by
  apply SAP.P015a.Bridge.T19_correspondence.mpr
  intro Ω B _ _ P _ D X hD hX h₂
  exact ⟨conditional_weight_variance P D X h₂ hX,
    fun hbin => binary_conditional_variance P D X hD hX hbin⟩
