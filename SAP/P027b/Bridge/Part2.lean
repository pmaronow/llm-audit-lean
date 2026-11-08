import SAP.P027b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b.Bridge
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

theorem strataFixed_proof (M : ℕ) (hM : 2 ≤ M) (y : (Fin M × Fin 2) → ℝ) :
    StrataFixed M hM y := by
  have h := AronowAudit.P027.strata_finite_formulas M hM y
  refine ⟨?_, h.2⟩
  intro ω
  have hw := h.1 ω
  refine ⟨hw.1,hw.2.1,hw.2.2,?_,rfl⟩
  change c2Estimator (strataDesign M (by omega)) y ω/(2*(M:ℝ))^2 =
    2*(htVarianceEstimator (strataDesign M (by omega)) y ω/(2*(M:ℝ))^2)
  rw [show c2Estimator (strataDesign M (by omega)) y ω/(2*(M:ℝ))^2 =
    ((M:ℝ)-1)/(2*M)*(y (ω.1,0)^2+y (ω.2,1)^2) from hw.2.2,
    show htVarianceEstimator (strataDesign M (by omega)) y ω/(2*(M:ℝ))^2 =
    ((M:ℝ)-1)/(4*M)*(y (ω.1,0)^2+y (ω.2,1)^2) from hw.2.1]
  ring

theorem strataModel_proof {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (M : ℕ) (hM : 2 ≤ M) (α : ℝ)
    (ε : (Fin M × Fin 2) → Ξ → ℝ) (hε : NoiseMoments μ ε 1) :
    StrataModel μ M hM α ε := by
  have hm := AronowAudit.P027.strata_model_moments μ M hM α ε hε
  have hr : strataC2BiasFormula M α-strataCSBiasFormula M α = ((M:ℝ)-2-2*α^2)/(2*M) ∧
      (strataC2BiasFormula M α < strataCSBiasFormula M α ↔ (M:ℝ) < 2*(1+α^2)) ∧
      (strataC2BiasFormula M α = strataCSBiasFormula M α ↔ (M:ℝ) = 2*(1+α^2)) ∧
      (strataCSBiasFormula M α < strataC2BiasFormula M α ↔ 2*(1+α^2) < (M:ℝ)) :=
    AronowAudit.P027.strata_bias_ranking M hM α
  have hratio := AronowAudit.P027.strata_ratio_formula M hM α
  have hMr : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hn : (M:ℝ) ≠ 0 := by linarith
  dsimp only [StrataModel]
  have hv : outcomeE μ (fun ξ => variance (strataDesign M (by omega)) (htMean (strataDesign M (by omega))
      (stratumOutcomes α ε ξ))) = ((M:ℝ)-1)/(2*M) := hm.1
  have hh : outcomeE μ (fun ξ => expect (strataDesign M (by omega))
      (fun ω => htVarianceEstimator (strataDesign M (by omega)) (stratumOutcomes α ε ξ) ω/(2*(M:ℝ))^2)) =
      ((M:ℝ)-1)/(2*M)*(1+α^2) := hm.2.1
  have hc : outcomeE μ (fun ξ => expect (strataDesign M (by omega))
      (fun ω => c2Estimator (strataDesign M (by omega)) (stratumOutcomes α ε ξ) ω/(2*(M:ℝ))^2)) =
      ((M:ℝ)-1)/M*(1+α^2) := hm.2.2.1
  have hs : outcomeE μ (fun ξ => expect (strataDesign M (by omega))
      (collapsedEstimator (stratumOutcomes α ε ξ))) = α^2+1/2 := hm.2.2.2.1
  rw [hv,hh,hc,hs]
  have bh : ((M:ℝ)-1)/(2*M)*(1+α^2)-((M:ℝ)-1)/(2*M) =
      ((M:ℝ)-1)/(2*M)*α^2 := by ring
  have bc : ((M:ℝ)-1)/M*(1+α^2)-((M:ℝ)-1)/(2*M) =
      strataC2BiasFormula M α := by unfold strataC2BiasFormula; ring
  have bs : α^2+1/2-((M:ℝ)-1)/(2*M) = strataCSBiasFormula M α := by
    unfold strataCSBiasFormula
    field_simp
    <;> ring
  rw [bh,bc,bs]
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,hr.1,?_,hr.2.1,hr.2.2.1,hr.2.2.2,?_,?_,hratio,?_⟩
  · exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (sq_nonneg α)
  · unfold strataC2BiasFormula
    exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (by positivity)
  · unfold strataCSBiasFormula
    positivity
  · rw [hr.1]
    field_simp
    <;> ring
  · rw [hr.2.1]
    unfold heterogeneity
    rw [div_lt_div_iff₀ (by linarith : 0 < (M:ℝ)-1) (by positivity : 0 < α^2+1/2)]
    constructor <;> intro h <;> nlinarith
  · field_simp
    <;> ring
  · field_simp
    <;> ring

theorem T15_proof : T15Statement := by
  refine ⟨strataFixed_proof,?_,?_⟩
  · intro Ξ _ μ _ M hM α ε hε
    exact strataModel_proof μ M hM α ε hε
  · exact AronowAudit.P027.strata_large_size_limits

theorem T17_proof : T17Statement := by
  refine ⟨?_,?_,AronowAudit.P027.heterogeneity_conversion_monotone,
    AronowAudit.P027.heterogeneity_conversion_limit,AronowAudit.P027.printed_icc_labels⟩
  · intro Ξ _ μ _ α S ε ε' h
    rcases h with ⟨hS,hSmean,hint,hε,hε',hmeans,hsecond,hcross⟩
    exact AronowAudit.P027.same_stratum_correlation μ α S ε ε'
      hS hSmean hint hε hε' hmeans hsecond hcross
  · intro α
    have hs := AronowAudit.P027.stratum_means_variance α
    have hc := AronowAudit.P027.heterogeneity_conversion α
    exact ⟨hs.1,hs.2.1,hs.2.2,hc⟩

end
end SAP.P027b.Bridge
