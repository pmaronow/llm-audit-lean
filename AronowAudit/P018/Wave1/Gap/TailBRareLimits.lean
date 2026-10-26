import AronowAudit.P018.Wave1.Gap.TailBRarePopulation
import AronowAudit.Shared.MapTailB.PairLimitTools

/-! The distributional and sandwich limits of the actual rare repeated model. -/
noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.Shared.MapTailB
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

local instance tb09_rare_limits_probability : IsProbabilityMeasure rareLaw := TailB_rare_probability
local instance tb09_rare_limits_rows_probability : ∀ N,IsProbabilityMeasure (repeatedLaw rareRepeated N) :=
  fun N => by change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => rareLaw)); infer_instance

def tb09_rare_G (N : ℕ) (w : Fin N → RareUnit) : Mat 2 := (Dreal N)⁻¹ • repeatedGram rareRepeated w
def tb09_rare_A (N : ℕ) (w : Fin N → RareUnit) : Mat 2 := (tb09_rare_G N w)⁻¹
def tb09_rare_sN (N : ℕ) (w : Fin N → RareUnit) : Vec 2 :=
  (Dreal N)⁻¹ • ∑ d : Dyad N,tb09_rare_score (w (firstUnit d),w (secondUnit d))
def tb09_rare_V : Mat 2 :=
  !![4+rareLimitSlopeVariance,-rareLimitSlopeVariance;-rareLimitSlopeVariance,rareLimitSlopeVariance]
def tb09_rare_fittedMeat (N : ℕ) (w : Fin N → RareUnit) : Mat 2 :=
  ((N:ℝ)/(Dreal N)^2) • meat members (repeatedBlockScore rareRepeated (repeatedOLS rareRepeated w) w)

theorem tb09_rare_Qdet : tb09_rare_Qmat.det ≠ 0 := by
  have hq := tb09_rare_Q_pos
  norm_num [tb09_rare_Qmat,Matrix.det_fin_two]
  nlinarith

theorem tb09_rare_Qinverse : tb09_rare_Qmat⁻¹=
    (!![(1+rareQ)/(2*rareQ),-1/(2*rareQ);-1/(2*rareQ),1/(2*rareQ)] : Mat 2) := by
  apply Matrix.inv_eq_left_inv
  have hq := tb09_rare_Q_pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tb09_rare_Qmat,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply] <;>
    field_simp [hq] <;> ring

theorem tb09_rare_s2_bound (uv : RareUnit × RareUnit) : |(rareS uv.1 uv.2)^2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_one_iff_abs_le_one _).mpr
  rw [abs_of_pos (TailB_rare_s_bounds _ _).1]
  exact (TailB_rare_s_bounds _ _).2

theorem tb09_rare_normalized_gram {N : ℕ} (hN : 2 ≤ N) (w : Fin N → RareUnit) :
    tb09_rare_G N w =
      !![2,2;2,2+2*GP0182B2b_dyadAverage (fun uv => (rareS uv.1 uv.2)^2) w] := by
  have hd := (TailB_rare_D_pos hN).ne'
  rw [tb09_rare_G,TailB_rare_gram]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GP0182B2b_dyadAverage,TailB_rare_S,TailB_rare_s] <;> field_simp [hd] <;> ring

theorem tb09_rare_gram_limit :
    inProbability (repeatedLaw rareRepeated) (fun N w => tb09_rare_G N w-tb09_rare_Qmat) := by
  let P := repeatedLaw rareRepeated
  letI tb09_rare_gram_rows_probability : ∀ N,IsProbabilityMeasure (P N) :=
    tb09_rare_limits_rows_probability
  let φ : ℝ → Mat 2 := fun t => !![2,2;2,2+2*t]
  have hq := tb09_pair_lln rareLaw (fun uv => (rareS uv.1 uv.2)^2)
    (measurable_of_countable _) ⟨1,tb09_rare_s2_bound⟩
  have hq' : inProbability P (fun N w =>
      GP0182B2b_dyadAverage (fun uv => (rareS uv.1 uv.2)^2) w-rareQ) := hq
  have hh := WeightedConsistency.inProbability_continuousAt P (φ := φ)
    (by unfold φ; fun_prop) hq'
  apply WeightedConsistency.inProbability_eventually_eq P (hf := hh)
  filter_upwards [eventually_ge_atTop 2] with N hN w
  rw [tb09_rare_normalized_gram hN]
  rfl

theorem tb09_rare_bread_limit :
    inProbability (repeatedLaw rareRepeated) (fun N w => tb09_rare_A N w-tb09_rare_Qmat⁻¹) :=
  (WeightedConsistency.g7_proof tb09_rare_Qmat tb09_rare_Qdet).2
    (repeatedLaw rareRepeated) tb09_rare_G tb09_rare_gram_limit

theorem tb09_rare_record_score {N : ℕ} (w : Fin N → RareUnit) (d : Dyad N) :
    (∑ t,score (repeatedX rareRepeated w d t) (repeatedY rareRepeated w d t))=
      tb09_rare_score (w (firstUnit d),w (secondUnit d)) := by
  change (∑ t : Fin 2,_) = _
  ext j
  fin_cases j <;>
    norm_num [Fin.sum_univ_succ,score,repeatedX,repeatedY,TailB_rare_X,TailB_rare_Y,
      tb09_rare_score,tb09_rare_u,tb09_rare_W,Finset.sum_apply] <;> ring

theorem tb09_rare_population_beta (N : ℕ) : repeatedBeta rareRepeated N=0 := by
  have hp (j : Fin 2) : MemLp (fun uv => tb09_rare_score uv j) 2 (rareLaw.prod rareLaw) :=
    tb09_pair_memLp rareLaw _ (measurable_of_countable _)
      (fun uv => (norm_le_pi_norm (tb09_rare_score uv) j).trans (tb09_rare_score_bound uv)) 2
  have hz : meanVec (repeatedLaw rareRepeated N) (fun w =>
      ∑ d : Dyad N,∑ t,score (repeatedX rareRepeated w d t) (repeatedY rareRepeated w d t))=0 := by
    ext j
    simp only [meanVec,tb09_rare_record_score,Finset.sum_apply,Pi.zero_apply]
    have hi (d : Dyad N) : Integrable (fun w : Fin N → RareUnit =>
        tb09_rare_score (w (firstUnit d),w (secondUnit d)) j) (repeatedLaw rareRepeated N) :=
      (GP0182B2b_kernel_pair_memLp _ (iIndepFun_pi (fun _ => aemeasurable_id))
        (fun i => measurePreserving_eval (fun _ : Fin N => rareLaw) i) (hp j)
        (WeightedConsistency.firstUnit_ne_secondUnit d)).integrable one_le_two
    rw [integral_finsetSum _ (fun d _ => hi d)]
    have he (d : Dyad N) : (∫ w : Fin N → RareUnit,
        tb09_rare_score (w (firstUnit d),w (secondUnit d)) j ∂repeatedLaw rareRepeated N)=0 :=
      (GP0182B2b_kernel_pair_integral _ (iIndepFun_pi (fun _ => aemeasurable_id))
        (fun i => measurePreserving_eval (fun _ : Fin N => rareLaw) i)
        (measurable_of_countable _) (WeightedConsistency.firstUnit_ne_secondUnit d)).trans
        (tb09_rare_score_mean j)
    simp only [he,Finset.sum_const_zero]
  unfold repeatedBeta
  rw [hz,Matrix.mulVec_zero]

theorem tb09_rare_score_lln : inProbability (repeatedLaw rareRepeated) tb09_rare_sN := by
  apply tb09_inProbability_pi
  intro j
  have hh := tb09_pair_lln rareLaw (fun uv => tb09_rare_score uv j)
    (measurable_of_countable _) ⟨8,fun uv =>
      (norm_le_pi_norm (tb09_rare_score uv) j).trans (tb09_rare_score_bound uv)⟩
  simp only [tb09_rare_score_mean,sub_zero,GP0182B2b_dyadAverage] at hh
  convert hh using 1
  · rfl
  · funext N w
    simp only [tb09_rare_sN,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]

theorem tb09_rare_OLS_normalized {N : ℕ} (hN : 2 ≤ N) (w : Fin N → RareUnit) :
    (tb09_rare_A N w).mulVec (tb09_rare_sN N w)=repeatedOLS rareRepeated w := by
  have hd := (TailB_rare_D_pos hN).ne'
  dsimp [tb09_rare_A,tb09_rare_G,tb09_rare_sN]
  rw [matrix_inverse_scale_total _ _ (inv_ne_zero hd),inv_inv,
    Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,mul_inv_cancel₀ hd,one_smul]
  simp only [repeatedOLS,tb09_rare_record_score]
  congr 1

theorem tb09_rare_coefficients_consistent :
    inProbability (repeatedLaw rareRepeated) (fun N w => repeatedOLS rareRepeated w) := by
  have hh := WeightedConsistency.inProbability_product_null (repeatedLaw rareRepeated)
    (fun (A : Mat 2) (s : Vec 2) => A.mulVec s) 2 (by norm_num)
    (WeightedConsistency.norm_mulVec_le (k := 2)) tb09_rare_A tb09_rare_Qmat⁻¹ tb09_rare_sN
    tb09_rare_bread_limit tb09_rare_score_lln
  apply WeightedConsistency.inProbability_eventually_eq _ (hf := hh)
  filter_upwards [eventually_ge_atTop 2] with N hN w
  exact tb09_rare_OLS_normalized hN w

theorem tb09_rare_block_at {N : ℕ} (w : Fin N → RareUnit) (d : Dyad N) (b : Vec 2) :
    repeatedBlockScore rareRepeated b w d =
      tb09_rare_score (w (firstUnit d),w (secondUnit d))-
        (!![2,2;2,2+2*(TailB_rare_s w d)^2] : Mat 2).mulVec b := by
  change (∑ t : Fin 2,_) = _
  ext j
  fin_cases j <;>
    norm_num [repeatedBlockScore,Fin.sum_univ_succ,score,repeatedX,repeatedY,TailB_rare_X,TailB_rare_Y,
      tb09_rare_score,tb09_rare_u,tb09_rare_W,TailB_rare_s,dot,Matrix.mulVec,dotProduct,Finset.sum_apply] <;> ring

theorem tb09_rare_block_change {N : ℕ} (w : Fin N → RareUnit) (d : Dyad N) (b : Vec 2) :
    ‖tb09_rare_score (w (firstUnit d),w (secondUnit d))-repeatedBlockScore rareRepeated b w d‖ ≤ 8*‖b‖ := by
  rw [tb09_rare_block_at,sub_sub_cancel]
  have hs := tb09_rare_s2_bound (w (firstUnit d),w (secondUnit d))
  have hm : ‖(!![2,2;2,2+2*(TailB_rare_s w d)^2] : Mat 2)‖ ≤ 4 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 4)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 4)).mpr
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [TailB_rare_s] at *
    rw [abs_of_nonneg (by positivity)]
    nlinarith [(sq_le_one_iff_abs_le_one _).mpr hs]
  calc
    _ ≤ 2*‖(!![2,2;2,2+2*(TailB_rare_s w d)^2] : Mat 2)‖*‖b‖ :=
      WeightedConsistency.norm_mulVec_le _ _
    _ ≤ 2*4*‖b‖ := by gcongr
    _ = _ := by ring

theorem tb09_rare_meat_limit : inProbability (repeatedLaw rareRepeated)
    (fun N w => tb09_rare_fittedMeat N w-(4:ℝ) • tb09_rare_Γ) := by
  have hb := (TailB_bounded_pair_score_limit rareLaw tb09_rare_score (measurable_of_countable _)
    tb09_rare_score_symmetric ⟨8,tb09_rare_score_bound⟩ tb09_rare_score_mean).1
  have he : (fun j l => ∫ u,(∫ v,tb09_rare_score (u,v) j ∂rareLaw)*
      (∫ v,tb09_rare_score (u,v) l ∂rareLaw) ∂rareLaw)=tb09_rare_Γ := by
    have hh (u) (j) : (∫ v,tb09_rare_score (u,v) j ∂rareLaw)=tb09_rare_g u j :=
      congrFun (tb09_rare_score_projection u) j
    simp_rw [hh]
    exact tb09_rare_projection_second
  rw [he] at hb
  have hs := tb09_pair_meat_substitution rareLaw tb09_rare_score
    (fun N w => repeatedBlockScore rareRepeated (repeatedOLS rareRepeated w) w)
    (fun N w => repeatedOLS rareRepeated w) 8 8 (by norm_num) (by norm_num)
    tb09_rare_score_bound (fun N _ w d => tb09_rare_block_change w d _)
    tb09_rare_coefficients_consistent
  have hh := WeightedConsistency.inProbability_add (repeatedLaw rareRepeated) hs hb
  simpa only [tb09_rare_fittedMeat,sub_add_sub_cancel] using hh

theorem tb09_rare_limit_covariance :
    sandwich tb09_rare_Qmat⁻¹ ((4:ℝ) • tb09_rare_Γ)=tb09_rare_V := by
  rw [tb09_rare_Qinverse]
  have hq := tb09_rare_Q_pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sandwich,tb09_rare_Γ,tb09_rare_V,rareLimitSlopeVariance,
      Matrix.mul_apply,Fin.sum_univ_succ] <;> field_simp [hq] <;> ring

theorem tb09_rare_scaled_sandwich {N : ℕ} (hN : 2 ≤ N) (w : Fin N → RareUnit) :
    (N:ℝ) • repeatedVariance rareRepeated w =
      sandwich (tb09_rare_A N w) (tb09_rare_fittedMeat N w) := by
  have hd := (TailB_rare_D_pos hN).ne'
  have ha : tb09_rare_A N w=Dreal N • (repeatedGram rareRepeated w)⁻¹ := by
    dsimp [tb09_rare_A,tb09_rare_G]
    rw [matrix_inverse_scale_total _ _ (inv_ne_zero hd),inv_inv]
  rw [ha]
  simp only [tb09_rare_fittedMeat,repeatedVariance,sandwich,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  congr 1
  field_simp [hd]

theorem tb09_rare_variance_limit : inProbability (repeatedLaw rareRepeated)
    (fun N w => (N:ℝ) • repeatedVariance rareRepeated w-tb09_rare_V) := by
  have hj := tb09_inProbability_prod (repeatedLaw rareRepeated)
    tb09_rare_A tb09_rare_fittedMeat tb09_rare_Qmat⁻¹ ((4:ℝ) • tb09_rare_Γ)
    tb09_rare_bread_limit tb09_rare_meat_limit
  let ψ : Mat 2 × Mat 2 → Mat 2 := fun z => sandwich z.1 z.2
  have hh := WeightedConsistency.inProbability_continuousAt (repeatedLaw rareRepeated)
    (φ := ψ) (by unfold ψ sandwich; fun_prop) hj
  apply WeightedConsistency.inProbability_eventually_eq _ (hf := hh)
  filter_upwards [eventually_ge_atTop 2] with N hN w
  change sandwich (tb09_rare_A N w) (tb09_rare_fittedMeat N w)-
    sandwich tb09_rare_Qmat⁻¹ ((4:ℝ) • tb09_rare_Γ) = _
  rw [← tb09_rare_scaled_sandwich hN,tb09_rare_limit_covariance]

theorem tb09_rare_gaussian_limit : ∃ ν : Measure (Vec 2),
    centeredNormalLaw ν tb09_rare_V ∧ weakLimit (repeatedLaw rareRepeated)
      (fun N w => Real.sqrt N • (repeatedOLS rareRepeated w-repeatedBeta rareRepeated N)) ν := by
  have he : (fun j l => ∫ u,(∫ v,tb09_rare_score (u,v) j ∂rareLaw)*
      (∫ v,tb09_rare_score (u,v) l ∂rareLaw) ∂rareLaw)=tb09_rare_Γ := by
    have hh (u) (j) : (∫ v,tb09_rare_score (u,v) j ∂rareLaw)=tb09_rare_g u j :=
      congrFun (tb09_rare_score_projection u) j
    simp_rw [hh]
    exact tb09_rare_projection_second
  obtain ⟨G,hG,hX⟩ := (TailB_bounded_pair_score_limit rareLaw tb09_rare_score
    (measurable_of_countable _) tb09_rare_score_symmetric
    ⟨8,tb09_rare_score_bound⟩ tb09_rare_score_mean).2
  rw [he] at hG
  let X := fun N (w : Fin N → RareUnit) => (Real.sqrt N/Dreal N) •
    ∑ d : Dyad N,tb09_rare_score (w (firstUnit d),w (secondUnit d))
  have hw := tb09_weak_mulVec rareLaw X tb09_rare_A
    (fun N => measurable_of_countable _) (fun N => measurable_of_countable _)
    G tb09_rare_Qmat⁻¹ hX tb09_rare_bread_limit
  have hn := tb09_normal_linear G ((4:ℝ) • tb09_rare_Γ) tb09_rare_Qmat⁻¹ hG
  have hs : (tb09_rare_Qmat⁻¹).transpose=tb09_rare_Qmat⁻¹ := by
    rw [tb09_rare_Qinverse]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hc : tb09_rare_Qmat⁻¹*((4:ℝ) • tb09_rare_Γ)*(tb09_rare_Qmat⁻¹).transpose=tb09_rare_V := by
    rw [hs]
    exact tb09_rare_limit_covariance
  rw [hc] at hn
  refine ⟨G.map (fun z => tb09_rare_Qmat⁻¹.mulVec z),hn,?_⟩
  apply tb09_weak_eventually_eq (repeatedLaw rareRepeated) _ _ _ hw
    (fun N => (measurable_of_countable _).aemeasurable)
  filter_upwards [eventually_ge_atTop 2] with N hN w
  rw [tb09_rare_population_beta,sub_zero]
  have hx : X N w=Real.sqrt N • tb09_rare_sN N w := by
    dsimp [X,tb09_rare_sN]
    rw [smul_smul,div_eq_mul_inv]
  rw [hx,Matrix.mulVec_smul,tb09_rare_OLS_normalized hN]

/-- P018-T19, with its original sample law and totalized estimators. -/
theorem TailB_infinite_moments_counterexample : (IsProbabilityMeasure rareLaw ∧ RepeatedStanding rareRepeated ∧
    (∀ N : ℕ, 2 ≤ N → ∀ ω : Fin N → RareUnit, (repeatedGram rareRepeated ω).det > 0 ∧
      (∀ d : Dyad N, ∀ t : Fin 2, |repeatedY rareRepeated ω d t -
        dot (repeatedX rareRepeated ω d t) (repeatedOLS rareRepeated ω)| ≤ 8)) ∧
    (∀ N : ℕ, 3 ≤ N →
      (∫⁻ ω, ENNReal.ofReal ((repeatedOLS rareRepeated ω 1)^2) ∂ repeatedLaw rareRepeated N) = ∞ ∧
      (∫⁻ ω, ENNReal.ofReal |repeatedOLS rareRepeated ω 1| ∂ repeatedLaw rareRepeated N) = ∞) ∧
    (∀ N : ℕ, 4 ≤ N →
      (∫⁻ ω, ENNReal.ofReal (max ((repeatedVariance rareRepeated ω) 1 1) 0) ∂ repeatedLaw rareRepeated N) = ∞ ∧
      (∫⁻ ω, ENNReal.ofReal (max (-((repeatedVariance rareRepeated ω) 1 1)) 0) ∂ repeatedLaw rareRepeated N) < ∞) ∧
    (0 < rareLimitSlopeVariance ∧
      inProbability (repeatedLaw rareRepeated) (fun N ω =>
        (N : ℝ) • repeatedVariance rareRepeated ω - (!![4+rareLimitSlopeVariance,-rareLimitSlopeVariance;-rareLimitSlopeVariance,rareLimitSlopeVariance] : Mat 2)) ∧
      ∃ ν : Measure (Vec 2), centeredNormalLaw ν (!![4+rareLimitSlopeVariance,-rareLimitSlopeVariance;-rareLimitSlopeVariance,rareLimitSlopeVariance]) ∧
        weakLimit (repeatedLaw rareRepeated)
          (fun N ω => Real.sqrt N • (repeatedOLS rareRepeated ω - repeatedBeta rareRepeated N)) ν)) := by
  obtain ⟨hp,hS,hfinite,hcoef,hsand⟩ := TailB_rare_finite_pathologies
  exact ⟨hp,hS,hfinite,hcoef,hsand,tb09_rare_limit_variance_pos,
    tb09_rare_variance_limit,tb09_rare_gaussian_limit⟩

end AronowAudit.P018.Wave1
