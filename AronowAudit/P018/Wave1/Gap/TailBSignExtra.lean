import AronowAudit.P018.Wave1.Gap.TailBSignPopulation

/-! Uniform fitted-moment conditions for the sign model. -/
noncomputable section
namespace AronowAudit.P018.Wave1.TailBSign
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
local instance tb05_extra_unit_probability : IsProbabilityMeasure signPairKernel.μ := tb05_standing.1

theorem tb05_coefficients_consistent {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (hK : Standing K) :
    inProbability (unitSampleLaw K) (fun N ω => coefficientError K ω) := by
  let R := singleRecord K
  let dir : ∀ N,(d : Dyad N) → Fin (R.T N d) → Bool := fun _ _ _ => false
  let v : ∀ N,(d : Dyad N) → Fin (R.T N d) → ℝ := fun _ _ _ => 1
  have hS : WeightedConsistency.Setting R K.X K.Y dir v 1 (populationGram K) :=
    GP0182B2b_singleSetting K hK
  have hreg := WeightedConsistency.m0_proof WeightedConsistency.g1_proof R hS.1
  have hker := WeightedConsistency.m1_proof R K.X K.Y dir v 1 (populationGram K) hS
  have hmom := WeightedConsistency.m2_proof WeightedConsistency.g1_proof
    R K.X K.Y dir v 1 (populationGram K) hS hker
  have hpop := WeightedConsistency.m3_proof R K.X K.Y dir v 1 (populationGram K) hS hreg hmom
  have hcent := WeightedConsistency.m4_proof R K.X K.Y dir v 1 (populationGram K) hS hreg hmom hpop
  have hgram := WeightedConsistency.m5_proof WeightedConsistency.g3_proof
    WeightedConsistency.g4_proof WeightedConsistency.g5_proof
    R K.X K.Y dir v 1 (populationGram K) hS hreg
  have hscore := WeightedConsistency.m6_proof WeightedConsistency.g3_proof
    WeightedConsistency.g4_proof WeightedConsistency.g5_proof
    R K.X K.Y dir v 1 (populationGram K) hS hreg hcent
  have hc := WeightedConsistency.m7_proof WeightedConsistency.g6_proof WeightedConsistency.g7_proof
    R K.X K.Y dir v 1 (populationGram K) hS hpop hgram hscore
  change inProbability (unitSampleLaw K) (fun N ω =>
    recordWeightedOLS (singleRecord K) (fun _ _ => 1) ω-populationBeta K) at hc
  simpa only [GP0182B2b_singleWeightedOLS,coefficientError] using hc

def tb05_betaHat (N : ℕ) (ω : Fin N → Bool × Bool) : Vec 2 :=
  sampleOLS (design signPairKernel ω) (response signPairKernel ω)
def tb05_prediction {N : ℕ} (ω : Fin N → Bool × Bool) (d : Dyad N) : ℝ :=
  dot (design signPairKernel ω d) (tb05_betaHat N ω)

def tb05_envelope : Vec 2 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun b => min 6 (3*‖b‖),by fun_prop⟩ 6 (by
    intro x y
    change |min 6 (3*‖x‖)-min 6 (3*‖y‖)| ≤ 6
    have hx : 0 ≤ min (6:ℝ) (3*‖x‖) := le_min (by norm_num) (by positivity)
    have hy : 0 ≤ min (6:ℝ) (3*‖y‖) := le_min (by norm_num) (by positivity)
    exact abs_le.2 ⟨by linarith [min_le_left (6:ℝ) (3*‖y‖)],
      by linarith [min_le_left (6:ℝ) (3*‖x‖)]⟩)

theorem tb05_envelope_nonneg (b : Vec 2) : 0 ≤ tb05_envelope b :=
  le_min (by norm_num) (by positivity)

theorem tb05_envelope_mean_zero :
    Tendsto (fun N => ∫ ω,tb05_envelope (tb05_betaHat N ω) ∂unitSampleLaw signPairKernel N)
      atTop (𝓝 0) := by
  have hc : inProbability (unitSampleLaw signPairKernel) tb05_betaHat := by
    change inProbability (unitSampleLaw signPairKernel) (fun N ω =>
      sampleOLS (design signPairKernel ω) (response signPairKernel ω))
    simpa only [coefficientError,tb05_population_beta,sub_zero,tb05_betaHat] using
      tb05_coefficients_consistent signPairKernel tb05_standing
  have hzero : weakLimit (unitSampleLaw signPairKernel) (fun _ _ => (0:Vec 2))
      (Measure.dirac (0:Vec 2)) := by
    refine ⟨fun _ => measurable_const.aemeasurable,inferInstance,fun g => ?_⟩
    simpa only [integral_const,probReal_univ,one_smul,integral_dirac] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => g 0) atTop (𝓝 (g 0)))
  have hweak := AronowAudit.Shared.MapTailB.TailB_weakLimit_perturbation
    (unitSampleLaw signPairKernel) (fun _ _ => (0:Vec 2)) tb05_betaHat _ hzero
    (fun _ => (measurable_of_countable _).aemeasurable)
    (by intro ε hε; simpa only [zero_sub,norm_neg] using hc ε hε)
  have he0 : tb05_envelope (0:Vec 2)=0 := by change min (6:ℝ) (3*‖(0:Vec 2)‖)=0; simp
  simpa only [integral_dirac,he0] using hweak.2.2 tb05_envelope

theorem tb05_model_response_bound {N : ℕ} (ω : Fin N → Bool × Bool) (d : Dyad N) :
    |response signPairKernel ω d| ≤ 2 := by
  have h := tb05_response_bound (tb05_w ω) (fun i => printed_sign_square (ω i).2) d
  dsimp only [response,signPairKernel,tb05_response,tb05_w] at h ⊢
  exact h

theorem tb05_prediction_envelope {N : ℕ} (ω : Fin N → Bool × Bool) (d : Dyad N) :
    |tb05_prediction ω d| ≤ tb05_envelope (tb05_betaHat N ω) := by
  have h6 : |tb05_prediction ω d| ≤ 6 := by
    have he : tb05_prediction ω d=response signPairKernel ω d-
        fittedResidual (design signPairKernel ω) (response signPairKernel ω) d := by
      dsimp [tb05_prediction,tb05_betaHat,fittedResidual]
      ring
    rw [he]
    calc
      _ ≤ |response signPairKernel ω d|+
          |fittedResidual (design signPairKernel ω) (response signPairKernel ω) d| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le
          (response signPairKernel ω d) (-(fittedResidual (design signPairKernel ω) (response signPairKernel ω) d))
      _ ≤ 6 := by linarith [tb05_model_response_bound ω d,tb05_model_fitted_residual_bound ω d]
  have hx : |1+tb05_z ω (firstUnit d)*tb05_z ω (secondUnit d)| ≤ 2 := by
    have ht : (tb05_z ω (firstUnit d)*tb05_z ω (secondUnit d))^2=1 := by
      dsimp only [tb05_z]
      rw [mul_pow,printed_sign_square,printed_sign_square]; ring
    rcases sq_eq_one_iff.1 ht with ht | ht <;> rw [ht] <;> norm_num
  have hb (j : Fin 2) : |tb05_betaHat N ω j| ≤ ‖tb05_betaHat N ω‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (tb05_betaHat N ω) j
  have h3 : |tb05_prediction ω d| ≤ 3*‖tb05_betaHat N ω‖ := by
    change |dot (design signPairKernel ω d) (tb05_betaHat N ω)| ≤ _
    have he : dot (design signPairKernel ω d) (tb05_betaHat N ω) =
        tb05_betaHat N ω 0+(1+tb05_z ω (firstUnit d)*tb05_z ω (secondUnit d))*tb05_betaHat N ω 1 := by
      simp [design,signPairKernel,dot,tb05_z,Fin.sum_univ_two]
    rw [he]
    calc
      _ ≤ |tb05_betaHat N ω 0|+|1+tb05_z ω (firstUnit d)*tb05_z ω (secondUnit d)| *|tb05_betaHat N ω 1| := by
        simpa only [abs_mul] using abs_add_le (tb05_betaHat N ω 0)
          ((1+tb05_z ω (firstUnit d)*tb05_z ω (secondUnit d))*tb05_betaHat N ω 1)
      _ ≤ 3*‖tb05_betaHat N ω‖ := by
        have hm := mul_le_mul_of_nonneg_right hx (abs_nonneg (tb05_betaHat N ω 1))
        linarith [hb 0,hb 1]
  exact le_min h6 h3

theorem tb05_fitted_product_error {N : ℕ} (ω : Fin N → Bool × Bool) (d f : Dyad N) :
    |fittedResidual (design signPairKernel ω) (response signPairKernel ω) d*
      fittedResidual (design signPairKernel ω) (response signPairKernel ω) f-
      response signPairKernel ω d*response signPairKernel ω f| ≤
      6*tb05_envelope (tb05_betaHat N ω) := by
  have hM := tb05_envelope_nonneg (tb05_betaHat N ω)
  let e := fittedResidual (design signPairKernel ω) (response signPairKernel ω)
  let y := response signPairKernel ω
  let p := tb05_prediction ω
  have he : e d*e f-y d*y f=e d*(-p f)+(-p d)*y f := by
    dsimp [e,y,p,tb05_prediction,tb05_betaHat,fittedResidual]
    ring
  change |e d*e f-y d*y f| ≤ _
  rw [he]
  calc
    _ ≤ |e d| *|p f|+|p d| *|y f| := by simpa only [abs_mul,abs_neg] using abs_add_le (e d*(-p f)) ((-p d)*y f)
    _ ≤ 4*tb05_envelope (tb05_betaHat N ω)+tb05_envelope (tb05_betaHat N ω)*2 := by
      gcongr
      · exact tb05_model_fitted_residual_bound ω d
      · exact tb05_prediction_envelope ω f
      · exact tb05_prediction_envelope ω d
      · exact tb05_model_response_bound ω f
    _ = _ := by ring

theorem tb05_fitted_moment_error {N : ℕ} (d f : Dyad N) :
    |(∫ ω,fittedResidual (design signPairKernel ω) (response signPairKernel ω) d*
      fittedResidual (design signPairKernel ω) (response signPairKernel ω) f ∂unitSampleLaw signPairKernel N)-
      (∫ ω,response signPairKernel ω d*response signPairKernel ω f ∂unitSampleLaw signPairKernel N)| ≤
      6*(∫ ω,tb05_envelope (tb05_betaHat N ω) ∂unitSampleLaw signPairKernel N) := by
  rw [← integral_sub (printed_finite_integrable _ _) (printed_finite_integrable _ _)]
  calc
    _ ≤ ∫ ω,|fittedResidual (design signPairKernel ω) (response signPairKernel ω) d*
        fittedResidual (design signPairKernel ω) (response signPairKernel ω) f-
        response signPairKernel ω d*response signPairKernel ω f| ∂unitSampleLaw signPairKernel N :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω,6*tb05_envelope (tb05_betaHat N ω) ∂unitSampleLaw signPairKernel N :=
      integral_mono (printed_finite_integrable _ _) (printed_finite_integrable _ _)
        (fun ω => tb05_fitted_product_error ω d f)
    _ = _ := integral_const_mul _ _


theorem tb05_response_product {N : ℕ} (d f : Dyad N) :
    (∫ ω,response signPairKernel ω d*response signPairKernel ω f ∂unitSampleLaw signPairKernel N)=
      if d=f then 2 else if overlap d f then 1 else 0 := by
  let h : (Bool × Bool) × (Bool × Bool) → ℝ := fun uv => signValue uv.1.2+signValue uv.2.2
  have hrow (u : Bool × Bool) : GP0182B2b_rowIntegral (μ := signPairKernel.μ) h u=signValue u.2 := by
    rw [GP0182B2b_rowIntegral,tb05_unit_integral]
    rcases u with ⟨z,w⟩
    cases w <;> norm_num [tb05_average,h,signValue]
  have h0 : (∫ u,h u ∂signPairKernel.μ.prod signPairKernel.μ)=0 := by
    rw [tb05_units_integral]
    norm_num [tb05_average,h,signValue]
  have h2 : (∫ u,h u^2 ∂signPairKernel.μ.prod signPairKernel.μ)=2 := by
    rw [tb05_units_integral]
    norm_num [tb05_average,h,signValue]
  have h1 : (∫ u,(GP0182B2b_rowIntegral (μ := signPairKernel.μ) h u)^2 ∂signPairKernel.μ)=1 := by
    simp only [hrow]
    rw [tb05_unit_integral]
    norm_num [tb05_average,signValue]
  have hp := GP0182B2b_dyad_product signPairKernel.μ h (measurable_of_countable _)
    (printed_finite_L2 _ _) (fun u v => add_comm _ _) d f
  change (∫ ω,h (ω (firstUnit d),ω (secondUnit d))*h (ω (firstUnit f),ω (secondUnit f))
    ∂Measure.pi (fun _ : Fin N => signPairKernel.μ))=_
  simpa only [h0,h1,h2,zero_pow (by decide : 2 ≠ 0)] using hp

theorem tb05_fitted_moments_nonzero : ∀ᶠ N : ℕ in atTop,
    (∀ d : Dyad N,(∫ ω,(fittedResidual (design signPairKernel ω) (response signPairKernel ω) d)^2
      ∂unitSampleLaw signPairKernel N) ≠ 0) ∧
    (∀ d f : Dyad N,f ∈ neighbors d →
      (∫ ω,fittedResidual (design signPairKernel ω) (response signPairKernel ω) d*
        fittedResidual (design signPairKernel ω) (response signPairKernel ω) f
        ∂unitSampleLaw signPairKernel N) ≠ 0) := by
  filter_upwards [tb05_envelope_mean_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/12))]
    with N hN
  constructor
  · intro d hz
    have hb := tb05_fitted_moment_error d d
    rw [tb05_response_product,if_pos rfl] at hb
    simp only [pow_two] at hz
    rw [hz] at hb
    norm_num at hb
    linarith
  · intro d f hf hz
    have hf' := (Finset.mem_filter.1 hf).2
    have hb := tb05_fitted_moment_error d f
    have ho : overlap d f := hf'.2
    rw [tb05_response_product,if_neg (Ne.symm hf'.1),if_pos ho,hz] at hb
    norm_num at hb
    linarith

theorem tb05_triple_regressor_moment :
    meanMat (Measure.pi (fun _ : Fin 3 => signPairKernel.μ)) (fun u =>
      outer (signPairKernel.X (u 0) (u 1)) (signPairKernel.X (u 0) (u 2))) =
        !![1,1;1,1] := by
  let h : (Bool × Bool) × (Bool × Bool) → ℝ := fun uv => 1+signValue uv.1.1*signValue uv.2.1
  let P := Measure.pi (fun _ : Fin 3 => signPairKernel.μ)
  let X : Fin 3 → (Fin 3 → Bool × Bool) → Bool × Bool := fun i ω => ω i
  have hind : iIndepFun X P := iIndepFun_pi (fun _ => aemeasurable_id)
  have hX (i : Fin 3) : MeasurePreserving (X i) P signPairKernel.μ := measurePreserving_eval _ i
  have hrow (u : Bool × Bool) : GP0182B2b_rowIntegral (μ := signPairKernel.μ) h u=1 := by
    rw [GP0182B2b_rowIntegral,tb05_unit_integral]
    rcases u with ⟨z,w⟩
    cases z <;> norm_num [tb05_average,h,signValue]
  have hmean : (∫ u,h u ∂signPairKernel.μ.prod signPairKernel.μ)=1 := by
    rw [tb05_units_integral]
    norm_num [tb05_average,h,signValue]
  have hp01 : (∫ ω,h (ω 0,ω 1) ∂P)=1 :=
    (GP0182B2b_kernel_pair_integral X hind hX (measurable_of_countable _) (by decide : (0:Fin 3) ≠ 1)).trans hmean
  have hp02 : (∫ ω,h (ω 0,ω 2) ∂P)=1 :=
    (GP0182B2b_kernel_pair_integral X hind hX (measurable_of_countable _) (by decide : (0:Fin 3) ≠ 2)).trans hmean
  have hshared : (∫ ω,h (ω 0,ω 1)*h (ω 0,ω 2) ∂P)=1 := by
    have hs := GP0182B2b_kernel_shared_product_integral X hind hX
      (K := h) (measurable_of_countable _) (printed_finite_L2 _ _)
      (by decide : (0:Fin 3) ≠ 1) (by decide : (0:Fin 3) ≠ 2) (by decide : (1:Fin 3) ≠ 2)
    simpa only [hrow,one_pow,integral_const,probReal_univ,smul_eq_mul,one_mul] using hs
  ext a b
  fin_cases a <;> fin_cases b
  · change (∫ _ : Fin 3 → Bool × Bool,(1:ℝ)*1 ∂P)=1
    simp
  · change (∫ ω : Fin 3 → Bool × Bool,1*h (ω 0,ω 2) ∂P)=1
    simpa only [one_mul] using hp02
  · change (∫ ω : Fin 3 → Bool × Bool,h (ω 0,ω 1)*1 ∂P)=1
    simpa only [mul_one] using hp01
  · change (∫ ω : Fin 3 → Bool × Bool,h (ω 0,ω 1)*h (ω 0,ω 2) ∂P)=1
    exact hshared

theorem tb05_proposition_extra : Proposition1Extra signPairKernel := by
  refine ⟨tb05_proposition_extra_bounded,?_,?_,tb05_fitted_moments_nonzero⟩
  · intro a b
    rw [tb05_population_gram]
    fin_cases a <;> fin_cases b <;> norm_num
  · intro a b
    rw [tb05_triple_regressor_moment]
    fin_cases a <;> fin_cases b <;> norm_num

end AronowAudit.P018.Wave1.TailBSign
