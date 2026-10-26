import AronowAudit.Shared.MapTailB.RowLimits
import AronowAudit.Shared.MapTailB.Gaussian
import AronowAudit.P018.Wave1.Gap.GP0182B2b
import AronowAudit.P018.Wave1.Gap.TailBSignScaling
import AronowAudit.P018.Wave1.Gap.TailBSignFit

/-! Exact finite algebra for the two-sign degenerate-inference model. -/

noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace TailBSign

local instance tb05_fair_probability : IsProbabilityMeasure fairLaw := printed_fair_probability
local instance tb05_unit_probability : IsProbabilityMeasure signPairKernel.μ := by
  change IsProbabilityMeasure (fairLaw.prod fairLaw)
  infer_instance

theorem tb05_bool_integral (f : Bool → ℝ) :
    (∫ b, f b ∂fairLaw) = (f false + f true) / 2 := by
  rw [integral_fintype (printed_finite_integrable fairLaw f)]
  norm_num [fairLaw, Measure.real, PMF.toMeasure_uniformOfFintype_apply,
    Fintype.sum_bool, Fintype.card_bool]
  ring

def tb05_average (f : Bool × Bool → ℝ) : ℝ :=
  (f (false,false) + f (false,true) + f (true,false) + f (true,true)) / 4

theorem tb05_unit_integral (f : Bool × Bool → ℝ) :
    (∫ u, f u ∂signPairKernel.μ) = tb05_average f := by
  change (∫ u, f u ∂fairLaw.prod fairLaw) = _
  rw [integral_prod (μ := fairLaw) (ν := fairLaw) f (printed_finite_integrable _ f)]
  simp only [tb05_bool_integral, tb05_average]
  ring

theorem tb05_units_integral (f : (Bool × Bool) × (Bool × Bool) → ℝ) :
    (∫ uv, f uv ∂signPairKernel.μ.prod signPairKernel.μ) =
      tb05_average (fun u => tb05_average (fun v => f (u,v))) := by
  rw [integral_prod (μ := signPairKernel.μ) (ν := signPairKernel.μ) f
    (printed_finite_integrable _ f)]
  simp only [tb05_unit_integral]

theorem tb05_population_gram : populationGram signPairKernel = !![1,1;1,2] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [populationGram, meanMat, outer]
  all_goals rw [tb05_units_integral]
  all_goals norm_num [tb05_average, signPairKernel, signValue]

theorem tb05_population_inverse :
    (populationGram signPairKernel)⁻¹ = (!![2,-1;-1,1] : Mat 2) := by
  apply Matrix.inv_eq_left_inv
  rw [tb05_population_gram]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem tb05_population_beta : populationBeta signPairKernel = 0 := by
  have hm : meanVec (signPairKernel.μ.prod signPairKernel.μ)
      (fun uv => score (signPairKernel.X uv.1 uv.2) (signPairKernel.Y uv.1 uv.2)) = 0 := by
    ext a
    fin_cases a <;> simp only [meanVec]
    all_goals rw [tb05_units_integral]
    all_goals norm_num [tb05_average, signPairKernel, score, signValue]
  simp only [populationBeta, hm, Matrix.mulVec_zero]

theorem tb05_population_residual (u v : Bool × Bool) :
    populationResidual signPairKernel u v = signValue u.2 + signValue v.2 := by
  rw [populationResidual, tb05_population_beta]
  simp [signPairKernel, dot]

theorem tb05_projection (u : Bool × Bool) :
    projection signPairKernel u = ![signValue u.2, signValue u.2] := by
  ext a
  fin_cases a <;> rcases u with ⟨z,w⟩ <;> cases z <;> cases w <;>
    simp only [projection, meanVec]
  all_goals rw [tb05_unit_integral]
  all_goals simp only [tb05_average, populationScore, tb05_population_residual]
  all_goals norm_num [signPairKernel, score, signValue]

theorem tb05_projection_gamma : projectionGamma signPairKernel = !![1,1;1,1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [projectionGamma, meanMat]
  all_goals rw [tb05_unit_integral]
  all_goals norm_num [tb05_average, tb05_projection, outer, signValue]

theorem tb05_limiting_target : limitingTarget signPairKernel = !![4,0;0,0] := by
  rw [limitingTarget, tb05_population_inverse, tb05_projection_gamma]
  norm_num [sandwich, Matrix.mul_apply, Fin.sum_univ_two,
    funext_iff, Fin.forall_fin_two]

theorem tb05_standing : Standing signPairKernel := by
  refine ⟨inferInstance, measurable_of_countable _, measurable_of_countable _, ?_, ?_,
    ⟨0, fun _ _ => rfl⟩, ?_⟩
  · intro u v
    constructor
    · simp only [signPairKernel, mul_comm]
    · exact add_comm _ _
  · refine ⟨2, by norm_num, Filter.Eventually.of_forall ?_⟩
    rintro ⟨⟨z,w⟩,⟨z',w'⟩⟩
    cases z <;> cases w <;> cases z' <;> cases w' <;>
      norm_num [signPairKernel, signValue, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        Fin.forall_fin_two]
  · rw [tb05_population_gram]
    norm_num [Matrix.det_fin_two]


theorem tb05_true_target_quad {N : ℕ} (hN : 3 ≤ N) (c : Vec 2) :
    dot c ((trueTarget signPairKernel N).mulVec c) =
      4*(N:ℝ)/((N:ℝ)-1)*(c 0)^2 - 8/((N:ℝ)-1)*c 0*c 1 +
        4/((N:ℝ)-1)*(c 1)^2 := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hn1 : (N:ℝ)-1 ≠ 0 := by
    have : (3:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [GP0182B2b_trueTarget_scalar signPairKernel tb05_standing c (by omega)]
  simp only [tb05_population_inverse, GP0182B2b_rowIntegral, populationScore,
    tb05_population_residual]
  rw [tb05_units_integral, tb05_unit_integral]
  simp only [tb05_average, tb05_unit_integral]
  norm_num [tb05_average, signPairKernel, dot, score, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, signValue]
  dsimp [Dreal]
  field_simp [hn,hn1]
  <;> ring

theorem tb05_true_target_symmetric (N : ℕ) : (trueTarget signPairKernel N).IsSymm := by
  have hv : (varMat (unitSampleLaw signPairKernel N) (scoreSum signPairKernel))ᵀ =
      varMat (unitSampleLaw signPairKernel N) (scoreSum signPairKernel) := by
    ext a b
    exact covariance_comm _ _
  have hb : (!![2,-1;-1,1] : Mat 2)ᵀ = !![2,-1;-1,1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  change (trueTarget signPairKernel N)ᵀ = _
  simp only [trueTarget, sandwich, tb05_population_inverse, Matrix.transpose_smul,
    Matrix.transpose_mul, hv, hb, Matrix.mul_assoc]

theorem tb05_true_target {N : ℕ} (hN : 3 ≤ N) : trueTarget signPairKernel N =
    !![4*(N:ℝ)/((N:ℝ)-1),-4/((N:ℝ)-1);-4/((N:ℝ)-1),4/((N:ℝ)-1)] := by
  have h0 := tb05_true_target_quad hN ![1,0]
  have h1 := tb05_true_target_quad hN ![0,1]
  have h2 := tb05_true_target_quad hN ![1,1]
  have hs := (tb05_true_target_symmetric N).apply 0 1
  norm_num [dot, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1 h2
  ext a b
  fin_cases a <;> fin_cases b <;> dsimp <;> ring_nf at h0 h1 h2 ⊢ <;> linarith


theorem tb05_absolute_consistency :
    inProbability (unitSampleLaw signPairKernel) (fun N ω =>
      (N:ℝ) • sampleVariance members (design signPairKernel ω) (response signPairKernel ω)-
        (!![4,0;0,0] : Mat 2)) := by
  have hc := GP0182B2b_variance_consistency signPairKernel tb05_standing
  let B : Mat 2 := !![1,-1;-1,1]
  have hi : Tendsto (fun N : ℕ => 4*((N:ℝ)-1)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        (by simpa only [sub_eq_add_neg] using
          (tendsto_atTop_add_const_right atTop (-1:ℝ) tendsto_natCast_atTop_atTop))).const_mul (4:ℝ)
  have hs := WeightedConsistency.inProbability_deterministic (unitSampleLaw signPairKernel)
    (fun N => 4*((N:ℝ)-1)⁻¹) hi
  have hb : ∀ᶠ N : ℕ in atTop, ∀ ω : Fin N → Bool × Bool,
      ‖trueTarget signPairKernel N-(!![4,0;0,0] : Mat 2)‖ ≤
        (‖B‖+1)*‖4*((N:ℝ)-1)⁻¹‖ := by
    filter_upwards [eventually_ge_atTop 3] with N hN
    intro ω
    have hn : (N:ℝ)-1 ≠ 0 := by
      have : (3:ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have he : trueTarget signPairKernel N-(!![4,0;0,0] : Mat 2) =
        (4*((N:ℝ)-1)⁻¹) • B := by
      rw [tb05_true_target hN]
      ext i j
      fin_cases i <;> fin_cases j <;> dsimp [B] <;> field_simp <;> ring
    rw [he,norm_smul]
    nlinarith [norm_nonneg (4*((N:ℝ)-1)⁻¹)]
  have hd := WeightedConsistency.inProbability_of_norm_bound
    (unitSampleLaw signPairKernel) hs (‖B‖+1) (by positivity) hb
  simpa only [sub_add_sub_cancel] using
    WeightedConsistency.inProbability_add (unitSampleLaw signPairKernel) hc hd


def tb05_z {N : ℕ} (ω : Fin N → Bool × Bool) (i : Fin N) : ℝ := signValue (ω i).1
def tb05_w {N : ℕ} (ω : Fin N → Bool × Bool) (i : Fin N) : ℝ := signValue (ω i).2

theorem tb05_model_fitted_residual_bound {N : ℕ} (ω : Fin N → Bool × Bool) (d : Dyad N) :
    |fittedResidual (design signPairKernel ω) (response signPairKernel ω) d| ≤ 4 := by
  have h := tb05_all_sample_residual_bound (tb05_z ω) (tb05_w ω)
      (fun i => printed_sign_square (ω i).1) (fun i => printed_sign_square (ω i).2) d
  dsimp only [tb05_design,tb05_response,design,response,signPairKernel,tb05_z,tb05_w] at h ⊢
  exact h

theorem tb05_proposition_extra_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ᵐ ω ∂unitSampleLaw signPairKernel N,
      ∀ d, |fittedResidual (design signPairKernel ω) (response signPairKernel ω) d| ≤ C := by
  exact ⟨4,by norm_num,fun N => Filter.Eventually.of_forall
    (fun ω d => tb05_model_fitted_residual_bound ω d)⟩

/-- The deterministic second-order expansion of the fitted sandwich variance estimate
for the slope in the literal model. After multiplication by N², the remainder is
O(N^-1/2), uniformly on bounded sets of the three normalized sign sums. -/
theorem tb05_model_second_order_remainder (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ω : Fin N → Bool × Bool), 2 ≤ N →
      (Real.sqrt N)⁻¹ ≤ 1/(2*(R^2+2)) →
      |(∑ i,tb05_z ω i)/Real.sqrt N| ≤ R → |(∑ i,tb05_w ω i)/Real.sqrt N| ≤ R →
      |(∑ i,tb05_z ω i*tb05_w ω i)/Real.sqrt N| ≤ R →
      |(N:ℝ)^2*sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1-
        4*(((∑ i,tb05_z ω i)/Real.sqrt N)^2+
          ((∑ i,tb05_z ω i*tb05_w ω i)/Real.sqrt N)^2-1)| ≤ C/Real.sqrt N := by
  obtain ⟨C,hC,hbound⟩ := tb05_slope_second_order_bounded_sums R hR
  refine ⟨C,hC,?_⟩
  intro N ω hN hx hz hw hzw
  have h := hbound N (tb05_z ω) (tb05_w ω)
      (fun i => printed_sign_square (ω i).1) (fun i => printed_sign_square (ω i).2)
      hN hx hz hw hzw
  dsimp only [tb05_design,tb05_response,design,response,signPairKernel,tb05_z,tb05_w] at h ⊢
  exact h

/-- The sample-size restrictions in the bounded-sums expansion hold eventually,
so only the three normalized sign sums restrict the random event. -/
theorem tb05_model_second_order_eventual (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ ω : Fin N → Bool × Bool,
      |(∑ i,tb05_z ω i)/Real.sqrt N| ≤ R → |(∑ i,tb05_w ω i)/Real.sqrt N| ≤ R →
      |(∑ i,tb05_z ω i*tb05_w ω i)/Real.sqrt N| ≤ R →
      |(N:ℝ)^2*sampleVariance members (design signPairKernel ω) (response signPairKernel ω) 1 1-
        4*(((∑ i,tb05_z ω i)/Real.sqrt N)^2+
          ((∑ i,tb05_z ω i*tb05_w ω i)/Real.sqrt N)^2-1)| ≤ C/Real.sqrt N := by
  obtain ⟨C,hC,hbound⟩ := tb05_model_second_order_remainder R hR
  refine ⟨C,hC,?_⟩
  have hi : Tendsto (fun N : ℕ => (Real.sqrt (N:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hd : (0:ℝ) < 1/(2*(R^2+2)) := by positivity
  filter_upwards [eventually_ge_atTop 2,hi.eventually (gt_mem_nhds hd)] with N hN hx
  intro ω hz hw hzw
  exact hbound N ω hN hx.le hz hw hzw

end TailBSign
end AronowAudit.P018.Wave1
