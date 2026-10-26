import AronowAudit.P001.P001_Foundations
import Mathlib.Topology.Instances.Matrix

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidablePlaceboFTest (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Empirical cell frequencies of the twelve-atom experiment. -/
def placeboFTest_frequency {Ω : Type*} (Z : ℕ → Ω → Fin 12) (n : ℕ) (ω : Ω)
    (j : Fin 12) : ℝ :=
  (∑ i ∈ Finset.range n, if Z i ω = j then (1 : ℝ) else 0) / (n : ℝ)

lemma placeboFTest_integral (g : Fin 12 → ℝ) :
    (∫ j, g j ∂finiteLawMeasure placeboLaw) = fmean placeboLaw g := by
  rw [finiteLawMeasure, integral_finsetSum_measure]
  · simp [integral_smul_measure, fmean, ENNReal.toReal_ofReal, placeboLaw.nonneg]
  · intro i hi
    exact (integrable_dirac (by simp)).smul_measure (by finiteness)

lemma placeboFTest_frequency_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
    (hiid : IID μ Z) (hlaw : μ.map (Z 0) = finiteLawMeasure placeboLaw) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => placeboFTest_frequency Z n ω) atTop
      (nhds placeboLaw.weight) := by
  have hcell (j : Fin 12) : ∀ᵐ ω ∂μ,
      Tendsto (fun n => placeboFTest_frequency Z n ω j) atTop
        (nhds (placeboLaw.weight j)) := by
    let g : Fin 12 → ℝ := fun k => if k = j then 1 else 0
    have hg : Measurable g := measurable_of_finite _
    have hI : Integrable (g ∘ Z 0) μ := by
      apply (MemLp.of_bound (hg.comp (hiid.1 0)).aestronglyMeasurable 1 ?_).integrable le_rfl
      exact ae_of_all μ (fun ω => by simp [g]; split_ifs <;> norm_num)
    have he : (∫ ω, g (Z 0 ω) ∂μ) = placeboLaw.weight j := by
      rw [← integral_map (hiid.1 0).aemeasurable hg.aestronglyMeasurable, hlaw,
        placeboFTest_integral]
      simp [fmean, g]
    have h := strong_law_ae_real (fun i => g ∘ Z i) hI
      (fun i k hik => (hiid.2.1.indepFun hik).comp hg hg)
      (fun i => (hiid.2.2 i).comp hg)
    simpa only [placeboFTest_frequency, Function.comp_def, g, he] using h
  filter_upwards [ae_all_iff.mpr hcell] with ω hω
  exact tendsto_pi_nhds.mpr hω

/-- Weighted regression algebra, defined on all real cell-weight vectors. -/
def placeboFTest_gram {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b => ∑ j, q j * R j a * R j b

def placeboFTest_cross {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) : Fin k → ℝ := fun a => ∑ j, q j * R j a * placeboD j

def placeboFTest_coef {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) : Fin k → ℝ :=
  (placeboFTest_gram R q)⁻¹.mulVec (placeboFTest_cross R q)

def placeboFTest_risk {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) : ℝ :=
  ∑ j, q j * (placeboD j - ∑ a, R j a * placeboFTest_coef R q a)^2

lemma placeboFTest_gram_continuous {k : ℕ} (R : Fin 12 → Fin k → ℝ) :
    Continuous (placeboFTest_gram R) := by
  unfold placeboFTest_gram
  fun_prop

lemma placeboFTest_coef_continuousAt {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) (h : (placeboFTest_gram R q).det ≠ 0) :
    ContinuousAt (placeboFTest_coef R) q := by
  have hi : ContinuousAt (fun q => (placeboFTest_gram R q)⁻¹) q :=
    (continuousAt_matrix_inv _ (by simpa only [Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ h))).comp (placeboFTest_gram_continuous R).continuousAt
  unfold placeboFTest_coef
  apply continuousAt_pi.mpr
  intro a
  change ContinuousAt (fun q => ∑ b, (placeboFTest_gram R q)⁻¹ a b *
    placeboFTest_cross R q b) q
  apply tendsto_finsetSum
  intro b hb
  exact ((continuous_apply b).continuousAt.comp
    ((continuous_apply a).continuousAt.comp hi)).mul (by
      unfold placeboFTest_cross
      apply tendsto_finsetSum
      intro j hj
      exact ((continuous_apply j).continuousAt.mul_const _).mul_const _)

lemma placeboFTest_risk_continuousAt {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) (h : (placeboFTest_gram R q).det ≠ 0) :
    ContinuousAt (placeboFTest_risk R) q := by
  have hc := placeboFTest_coef_continuousAt R q h
  unfold placeboFTest_risk
  apply tendsto_finsetSum
  intro j hj
  apply (continuous_apply j).continuousAt.mul
  apply ContinuousAt.pow
  apply continuousAt_const.sub
  apply tendsto_finsetSum
  intro a ha
  exact continuousAt_const.mul ((continuous_apply a).continuousAt.comp hc)


lemma placeboFTest_sum_frequency {Ω : Type*} (Z : ℕ → Ω → Fin 12)
    (n : ℕ) (ω : Ω) (g : Fin 12 → ℝ) :
    (∑ j, placeboFTest_frequency Z n ω j * g j) =
      (∑ i : Fin n, g (Z i.val ω)) / (n : ℝ) := by
  simp only [placeboFTest_frequency, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp
  exact (Fin.sum_univ_eq_sum_range (fun i => g (Z i ω)) n).symm

lemma placeboFTest_sum_cells {Ω : Type*} (Z : ℕ → Ω → Fin 12)
    (n : ℕ) (hn : (n : ℝ) ≠ 0) (ω : Ω) (g : Fin 12 → ℝ) :
    (∑ i : Fin n, g (Z i.val ω)) =
      (n : ℝ) * ∑ j, placeboFTest_frequency Z n ω j * g j := by
  rw [placeboFTest_sum_frequency, mul_div_cancel₀ _ hn]

lemma placeboFTest_inv_smul {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ)
    (hG : IsUnit G.det) (c : ℝ) (hc : c ≠ 0) :
    (c • G)⁻¹ = c⁻¹ • G⁻¹ := by
  simpa only [Units.smul_def, Units.val_mk0, Units.val_inv_eq_inv_val] using
    Matrix.inv_smul' G (Units.mk0 c hc) hG

lemma placeboFTest_sample_gram {Ω : Type*} {k : ℕ}
    (Z : ℕ → Ω → Fin 12) (R : Fin 12 → Fin k → ℝ)
    (n : ℕ) (hn : (n : ℝ) ≠ 0) (ω : Ω) :
    (Matrix.transpose (fun i : Fin n => R (Z i.val ω))) *
      (Matrix.of (fun i : Fin n => R (Z i.val ω))) =
      (n : ℝ) • placeboFTest_gram R (placeboFTest_frequency Z n ω) := by
  ext a b
  simpa only [Matrix.mul_apply, Matrix.transpose, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    placeboFTest_gram, mul_assoc] using
    placeboFTest_sum_cells Z n hn ω (fun j => R j a * R j b)

lemma placeboFTest_sample_coef {Ω : Type*} {k : ℕ}
    (Z : ℕ → Ω → Fin 12) (R : Fin 12 → Fin k → ℝ)
    (n : ℕ) (hn : (n : ℝ) ≠ 0) (ω : Ω)
    (hG : IsUnit (placeboFTest_gram R (placeboFTest_frequency Z n ω)).det) :
    olsCoef (fun i : Fin n => R (Z i.val ω)) (fun i => placeboD (Z i.val ω)) =
      placeboFTest_coef R (placeboFTest_frequency Z n ω) := by
  have hgram := placeboFTest_sample_gram Z R n hn ω
  have hcross : (Matrix.transpose (fun i : Fin n => R (Z i.val ω))).mulVec
      (fun i => placeboD (Z i.val ω)) =
      (n : ℝ) • placeboFTest_cross R (placeboFTest_frequency Z n ω) := by
    ext a
    simpa only [Matrix.mulVec, dotProduct, Matrix.transpose, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply,
      smul_eq_mul, placeboFTest_cross, mul_assoc] using
      placeboFTest_sum_cells Z n hn ω (fun j => R j a * placeboD j)
  unfold olsCoef
  erw [hgram, hcross]
  rw [placeboFTest_inv_smul _ hG _ hn,
    Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rfl

/-- Restricted regressors, including the intercept. -/
def placeboFTest_restricted (j : Fin 12) : Fin 2 → ℝ := ![1, placeboX j]

lemma placeboFTest_population_gram :
    placeboFTest_gram placeboRegressor placeboLaw.weight =
      !![1,0,2/3; 0,2/3,0; 2/3,0,11/12] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [placeboFTest_gram, placeboRegressor, placeboLaw, placeboX, placeboW,
      placeboZ, Fin.sum_univ_succ]

lemma placeboFTest_population_inverse :
    (placeboFTest_gram placeboRegressor placeboLaw.weight)⁻¹ =
      !![33/17,0,-24/17; 0,3/2,0; -24/17,0,36/17] := by
  rw [placeboFTest_population_gram]
  apply Matrix.inv_eq_left_inv
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

lemma placeboFTest_population_coef :
    placeboFTest_coef placeboRegressor placeboLaw.weight = ![29/68,0,4/17] := by
  unfold placeboFTest_coef
  rw [placeboFTest_population_inverse]
  ext a
  fin_cases a <;>
    norm_num [Matrix.mulVec, dotProduct, placeboFTest_cross, placeboRegressor,
      placeboLaw, placeboX, placeboW, placeboZ, placeboD, Fin.sum_univ_succ]

lemma placeboFTest_restricted_gram :
    placeboFTest_gram placeboFTest_restricted placeboLaw.weight = !![1,0; 0,2/3] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [placeboFTest_gram, placeboFTest_restricted, placeboLaw, placeboX,
      Fin.sum_univ_succ]

lemma placeboFTest_restricted_inverse :
    (placeboFTest_gram placeboFTest_restricted placeboLaw.weight)⁻¹ = !![1,0; 0,3/2] := by
  rw [placeboFTest_restricted_gram]
  apply Matrix.inv_eq_left_inv
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

lemma placeboFTest_restricted_coef :
    placeboFTest_coef placeboFTest_restricted placeboLaw.weight = ![7/12,0] := by
  unfold placeboFTest_coef
  rw [placeboFTest_restricted_inverse]
  ext a
  fin_cases a <;>
    norm_num [Matrix.mulVec, dotProduct, placeboFTest_cross, placeboFTest_restricted,
      placeboLaw, placeboX, placeboD, Fin.sum_univ_succ]

lemma placeboFTest_population_risks :
    placeboFTest_risk placeboFTest_restricted placeboLaw.weight = 35/144 ∧
      placeboFTest_risk placeboRegressor placeboLaw.weight = 59/272 := by
  unfold placeboFTest_risk
  rw [placeboFTest_population_coef, placeboFTest_restricted_coef]
  norm_num [placeboRegressor, placeboFTest_restricted, placeboLaw, placeboX,
    placeboW, placeboZ, placeboD, Fin.sum_univ_succ]


lemma placeboFTest_sample_rss {Ω : Type*} {k : ℕ}
    (Z : ℕ → Ω → Fin 12) (R : Fin 12 → Fin (k+1) → ℝ)
    (n : ℕ) (hn : (n : ℝ) ≠ 0) (ω : Ω)
    (hG : IsUnit (placeboFTest_gram R (placeboFTest_frequency Z n ω)).det) :
    olsRSS (fun i : Fin n => R (Z i.val ω)) (fun i => placeboD (Z i.val ω))
      (olsCoef (fun i : Fin n => R (Z i.val ω)) (fun i => placeboD (Z i.val ω))) =
      (n : ℝ) * placeboFTest_risk R (placeboFTest_frequency Z n ω) := by
  rw [placeboFTest_sample_coef Z R n hn ω hG]
  exact placeboFTest_sum_cells Z n hn ω
    (fun j => (placeboD j - ∑ a, R j a *
      placeboFTest_coef R (placeboFTest_frequency Z n ω) a)^2)

lemma placeboFTest_full_design (j : Fin 12) :
    (fun a : Fin 3 => Fin.cases 1 (fun b => Fin.addCases
      (motive := fun _ => ℝ) (fun _ : Fin 1 => placeboX j)
      (fun _ : Fin 1 => placeboW j) b) a) = placeboRegressor j := by
  ext a
  fin_cases a <;> rfl

lemma placeboFTest_restricted_design (j : Fin 12) :
    (Fin.cases 1 (fun _ : Fin 1 => placeboX j) : Fin 2 → ℝ) =
      placeboFTest_restricted j := by
  ext a
  fin_cases a <;> rfl

lemma placeboFTest_sampleF_formula {Ω : Type*}
    (Z : ℕ → Ω → Fin 12) (n : ℕ) (hn : (n : ℝ) ≠ 0) (ω : Ω)
    (hR : IsUnit (placeboFTest_gram placeboFTest_restricted
      (placeboFTest_frequency Z n ω)).det)
    (hF : IsUnit (placeboFTest_gram placeboRegressor
      (placeboFTest_frequency Z n ω)).det) :
    placeboSampleF Z n ω / (n : ℝ) =
      (1 - 3 / (n : ℝ)) *
        (placeboFTest_risk placeboFTest_restricted (placeboFTest_frequency Z n ω) -
          placeboFTest_risk placeboRegressor (placeboFTest_frequency Z n ω)) /
        placeboFTest_risk placeboRegressor (placeboFTest_frequency Z n ω) := by
  unfold placeboSampleF placeboFStatistic
  simp only [placeboFTest_full_design, placeboFTest_restricted_design]
  rw [placeboFTest_sample_rss Z placeboFTest_restricted n hn ω hR,
    placeboFTest_sample_rss Z placeboRegressor n hn ω hF]
  norm_num only [Nat.cast_one, div_one, Nat.reduceAdd, Nat.cast_ofNat]
  by_cases hr : placeboFTest_risk placeboRegressor (placeboFTest_frequency Z n ω) = 0
  · simp [hr]
  · field_simp
    <;> ring

lemma placeboFTest_determinants :
    (placeboFTest_gram placeboFTest_restricted placeboLaw.weight).det = 2/3 ∧
      (placeboFTest_gram placeboRegressor placeboLaw.weight).det = 17/54 := by
  rw [placeboFTest_population_gram, placeboFTest_restricted_gram]
  norm_num [Matrix.det_fin_two, Matrix.det_fin_three]

lemma placeboFTest_sampleF_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
    (hiid : IID μ Z) (hlaw : μ.map (Z 0) = finiteLawMeasure placeboLaw) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleF Z n ω / (n : ℝ)) atTop
      (nhds (64/531)) := by
  have hR : (placeboFTest_gram placeboFTest_restricted placeboLaw.weight).det ≠ 0 := by
    rw [placeboFTest_determinants.1]; norm_num
  have hF : (placeboFTest_gram placeboRegressor placeboLaw.weight).det ≠ 0 := by
    rw [placeboFTest_determinants.2]; norm_num
  filter_upwards [placeboFTest_frequency_limit μ Z hiid hlaw] with ω hω
  have hrr := (placeboFTest_risk_continuousAt placeboFTest_restricted _ hR).tendsto.comp hω
  have hrf := (placeboFTest_risk_continuousAt placeboRegressor _ hF).tendsto.comp hω
  rw [placeboFTest_population_risks.1] at hrr
  rw [placeboFTest_population_risks.2] at hrf
  have hRdet := ((placeboFTest_gram_continuous placeboFTest_restricted).matrix_det.tendsto
    placeboLaw.weight).comp hω
  have hFdet := ((placeboFTest_gram_continuous placeboRegressor).matrix_det.tendsto
    placeboLaw.weight).comp hω
  have hn : Tendsto (fun n : ℕ => 1 - 3/(n : ℝ)) atTop (nhds (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (3 : ℝ))).div_atTop
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlim := (hn.mul (hrr.sub hrf)).div hrf (by norm_num : (59/272 : ℝ) ≠ 0)
  norm_num at hlim
  apply hlim.congr'
  filter_upwards [hRdet.eventually (eventually_ne_nhds hR),
    hFdet.eventually (eventually_ne_nhds hF), eventually_gt_atTop (0 : ℕ)] with n hr hf hn
  exact (placeboFTest_sampleF_formula Z n (by exact_mod_cast hn.ne') ω
    (isUnit_iff_ne_zero.mpr hr) (isUnit_iff_ne_zero.mpr hf)).symm


/-- The empirical sandwich meat, with the fitted empirical residuals. -/
def placeboFTest_meat {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b => ∑ j, q j * R j a *
    (placeboD j - ∑ c, R j c * placeboFTest_coef R q c)^2 * R j b

def placeboFTest_sandwich {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (placeboFTest_gram R q)⁻¹ * placeboFTest_meat R q * (placeboFTest_gram R q)⁻¹

lemma placeboFTest_sandwich_continuousAt {k : ℕ} (R : Fin 12 → Fin k → ℝ)
    (q : Fin 12 → ℝ) (h : (placeboFTest_gram R q).det ≠ 0) :
    ContinuousAt (placeboFTest_sandwich R) q := by
  have hc := placeboFTest_coef_continuousAt R q h
  have hi : ContinuousAt (fun q => (placeboFTest_gram R q)⁻¹) q :=
    (continuousAt_matrix_inv _ (by simpa only [Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ h))).comp (placeboFTest_gram_continuous R).continuousAt
  have hm : ContinuousAt (placeboFTest_meat R) q := by
    apply continuousAt_pi.mpr
    intro a
    apply continuousAt_pi.mpr
    intro b
    unfold placeboFTest_meat
    apply tendsto_finsetSum
    intro j hj
    apply ContinuousAt.mul_const
    apply ContinuousAt.mul
    · exact (continuous_apply j).continuousAt.mul_const _
    · apply ContinuousAt.pow
      apply continuousAt_const.sub
      apply tendsto_finsetSum
      intro c hcc
      exact continuousAt_const.mul ((continuous_apply c).continuousAt.comp hc)
  exact (hi.mul hm).mul hi

lemma placeboFTest_population_sandwich :
    placeboFTest_sandwich placeboRegressor placeboLaw.weight 2 2 = 135315/334084 := by
  unfold placeboFTest_sandwich placeboFTest_meat
  rw [placeboFTest_population_inverse, placeboFTest_population_coef]
  norm_num [Matrix.mul_apply, Matrix.vecMul, dotProduct, placeboRegressor, placeboLaw, placeboX,
    placeboW, placeboZ, placeboD, Fin.sum_univ_succ]

lemma placeboFTest_sample_cov {Ω : Type*} {k : ℕ}
    (Z : ℕ → Ω → Fin 12) (R : Fin 12 → Fin (k+1) → ℝ)
    (n : ℕ) (hn : (n : ℝ) ≠ 0) (ω : Ω)
    (hG : IsUnit (placeboFTest_gram R (placeboFTest_frequency Z n ω)).det) :
    robustCov (fun i : Fin n => R (Z i.val ω))
      ((fun i : Fin n => placeboD (Z i.val ω)) -
        (Matrix.of (fun i : Fin n => R (Z i.val ω))).mulVec
          (olsCoef (fun i : Fin n => R (Z i.val ω)) (fun i => placeboD (Z i.val ω)))) =
      (n : ℝ)⁻¹ • placeboFTest_sandwich R (placeboFTest_frequency Z n ω) := by
  rw [placeboFTest_sample_coef Z R n hn ω hG]
  have hmeat : ((Matrix.transpose (fun i : Fin n => R (Z i.val ω))) *
      Matrix.diagonal (fun i : Fin n => ((fun i => placeboD (Z i.val ω)) i -
        (Matrix.of (fun i : Fin n => R (Z i.val ω))).mulVec
          (placeboFTest_coef R (placeboFTest_frequency Z n ω)) i)^2)) *
        (Matrix.of (fun i : Fin n => R (Z i.val ω))) =
      (n : ℝ) • placeboFTest_meat R (placeboFTest_frequency Z n ω) := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul,
      placeboFTest_meat]
    have hs := placeboFTest_sum_cells Z n hn ω
      (fun j => R j a * (placeboD j - ∑ c, R j c *
        placeboFTest_coef R (placeboFTest_frequency Z n ω) c)^2 * R j b)
    convert hs using 1
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold robustCov
  erw [placeboFTest_sample_gram Z R n hn ω, hmeat]
  rw [placeboFTest_inv_smul _ hG _ hn]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_inv_cancel₀ hn, mul_one]
  rfl

lemma placeboFTest_sampleWald_formula {Ω : Type*}
    (Z : ℕ → Ω → Fin 12) (n : ℕ) (hn : (n : ℝ) ≠ 0) (ω : Ω)
    (hF : IsUnit (placeboFTest_gram placeboRegressor
      (placeboFTest_frequency Z n ω)).det) :
    placeboSampleWald Z n ω / (n : ℝ) =
      (placeboFTest_coef placeboRegressor (placeboFTest_frequency Z n ω) 2)^2 /
        placeboFTest_sandwich placeboRegressor (placeboFTest_frequency Z n ω) 2 2 := by
  unfold placeboSampleWald
  change (olsCoef (fun i : Fin n => placeboRegressor (Z i.val ω))
      (fun i => placeboD (Z i.val ω)) 2)^2 /
    robustCov (fun i : Fin n => placeboRegressor (Z i.val ω))
      ((fun i : Fin n => placeboD (Z i.val ω)) -
        (Matrix.of (fun i : Fin n => placeboRegressor (Z i.val ω))).mulVec
          (olsCoef (fun i : Fin n => placeboRegressor (Z i.val ω))
            (fun i => placeboD (Z i.val ω)))) 2 2 / (n : ℝ) = _
  rw [placeboFTest_sample_cov Z placeboRegressor n hn ω hF,
    placeboFTest_sample_coef Z placeboRegressor n hn ω hF]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [div_div, mul_right_comm _ _ (n : ℝ), inv_mul_cancel₀ hn, one_mul]

lemma placeboFTest_sampleWald_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
    (hiid : IID μ Z) (hlaw : μ.map (Z 0) = finiteLawMeasure placeboLaw) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleWald Z n ω / (n : ℝ)) atTop
      (nhds (18496/135315)) := by
  have hF : (placeboFTest_gram placeboRegressor placeboLaw.weight).det ≠ 0 := by
    rw [placeboFTest_determinants.2]; norm_num
  filter_upwards [placeboFTest_frequency_limit μ Z hiid hlaw] with ω hω
  have hcoef := ((continuous_apply (2 : Fin 3)).continuousAt.comp
    (placeboFTest_coef_continuousAt placeboRegressor _ hF)).tendsto.comp hω
  have hcov := ((continuous_apply (2 : Fin 3)).continuousAt.comp
    ((continuous_apply (2 : Fin 3)).continuousAt.comp
      (placeboFTest_sandwich_continuousAt placeboRegressor _ hF))).tendsto.comp hω
  dsimp only [Function.comp_def] at hcoef hcov
  rw [placeboFTest_population_coef] at hcoef
  norm_num only [Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero] at hcoef
  rw [placeboFTest_population_sandwich] at hcov
  have hdet := ((placeboFTest_gram_continuous placeboRegressor).matrix_det.tendsto
    placeboLaw.weight).comp hω
  have hlim := (hcoef.pow 2).div hcov (by norm_num : (135315/334084 : ℝ) ≠ 0)
  norm_num at hlim
  apply hlim.congr'
  filter_upwards [hdet.eventually (eventually_ne_nhds hF),
    eventually_gt_atTop (0 : ℕ)] with n hf hn
  exact (placeboFTest_sampleWald_formula Z n (by exact_mod_cast hn.ne') ω
    (isUnit_iff_ne_zero.mpr hf)).symm


lemma placeboFTest_divergence {T : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hT : Tendsto (fun n => T n / (n : ℝ)) atTop (nhds c)) :
    Tendsto T atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_pos hc hT
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact mul_div_cancel₀ _ (by exact_mod_cast hn.ne')

lemma placeboFTest_reject_of_divergence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → ℝ)
    (hT : ∀ n, Measurable (T n))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => T n ω) atTop atTop)
    (critical : ℕ → ℝ) (C : ℝ) (hc : ∀ᶠ n in atTop, critical n ≤ C) :
    Tendsto (fun n => prob μ {ω | critical n < T n ω}) atTop (nhds 1) := by
  let A : ℕ → Set Ω := fun n => {ω | critical n < T n ω}
  have hA : ∀ n, MeasurableSet (A n) := fun n => measurableSet_lt measurable_const (hT n)
  have hh : ∀ᵐ ω ∂μ, Tendsto (fun n => (A n).indicator (fun _ => (1 : ℝ)) ω)
      atTop (nhds (1 : ℝ)) := by
    filter_upwards [hlim] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω.eventually_gt_atTop C, hc] with n ht hc
    exact (Set.indicator_of_mem (lt_of_le_of_lt hc ht) (fun _ => (1 : ℝ))).symm
  have h := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (fun n => (measurable_const.indicator (hA n)).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n => ae_of_all μ (fun ω => by
      simp only [Set.indicator, Real.norm_eq_abs]
      split_ifs <;> norm_num)) hh
  simpa only [integral_indicator (hA _), integral_const, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one, measure_univ, ENNReal.toReal_one, prob, A,
    Measure.real] using h

lemma placeboFTest_sampleF_measurable {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℕ → Ω → Fin 12) (hZ : ∀ i, Measurable (Z i)) (n : ℕ) :
    Measurable (placeboSampleF Z n) := by
  let t : (Fin n → Fin 12) → ℝ := fun s => placeboFStatistic
    (fun i => fun _ : Fin 1 => placeboX (s i))
    (fun i => fun _ : Fin 1 => placeboW (s i)) (fun i => placeboD (s i))
  exact (measurable_of_finite t).comp (measurable_pi_lambda (fun i : Fin n => hZ i.val))

lemma placeboFTest_sampleWald_measurable {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℕ → Ω → Fin 12) (hZ : ∀ i, Measurable (Z i)) (n : ℕ) :
    Measurable (placeboSampleWald Z n) := by
  let t : (Fin n → Fin 12) → ℝ := fun s =>
    let P : Matrix (Fin n) (Fin 3) ℝ := fun i => placeboRegressor (s i)
    let D : Fin n → ℝ := fun i => placeboD (s i)
    let b := olsCoef P D
    (b 2)^2 / robustCov P (D - P.mulVec b) 2 2
  exact (measurable_of_finite t).comp (measurable_pi_lambda (fun i : Fin n => hZ i.val))

lemma placeboFTest_sampleF_reject_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
    (hiid : IID μ Z) (hlaw : μ.map (Z 0) = finiteLawMeasure placeboLaw)
    (critical : ℕ → ℝ) (C : ℝ) (hc : ∀ᶠ n in atTop, critical n ≤ C) :
    Tendsto (fun n => prob μ {ω | critical n < placeboSampleF Z n ω})
      atTop (nhds 1) := by
  apply placeboFTest_reject_of_divergence μ (placeboSampleF Z)
    (placeboFTest_sampleF_measurable Z hiid.1) _ critical C hc
  filter_upwards [placeboFTest_sampleF_limit μ Z hiid hlaw] with ω hω
  exact placeboFTest_divergence (by norm_num : (0 : ℝ) < 64/531) hω

lemma placeboFTest_sampleWald_reject {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
    (hiid : IID μ Z) (hlaw : μ.map (Z 0) = finiteLawMeasure placeboLaw) (c : ℝ) :
    Tendsto (fun n => prob μ {ω | c < placeboSampleWald Z n ω})
      atTop (nhds 1) := by
  apply placeboFTest_reject_of_divergence μ (placeboSampleWald Z)
    (placeboFTest_sampleWald_measurable Z hiid.1) _ (fun _ => c) c (Eventually.of_forall fun _ => le_rfl)
  filter_upwards [placeboFTest_sampleWald_limit μ Z hiid hlaw] with ω hω
  exact placeboFTest_divergence (by norm_num : (0 : ℝ) < 18496/135315) hω


/-- A common probability space for all denominator degrees of freedom. -/
def placeboFTest_normalProduct : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance placeboFTest_normalProduct_probability : IsProbabilityMeasure placeboFTest_normalProduct := by
  unfold placeboFTest_normalProduct
  infer_instance

def placeboFTest_referenceCoupling (v : ℕ) (z : ℕ → ℝ) : ℝ :=
  (z 0)^2 / ((∑ i : Fin v, (z (i.val + 1))^2) / (v : ℝ))

lemma placeboFTest_normal_coordinates (i : ℕ) :
    IdentDistrib (fun z : ℕ → ℝ => z i) id placeboFTest_normalProduct (gaussianReal 0 1) := by
  refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
  simp [placeboFTest_normalProduct, Measure.infinitePi_map_eval]

lemma placeboFTest_referenceCoupling_limit :
    ∀ᵐ z ∂placeboFTest_normalProduct,
      Tendsto (fun v => placeboFTest_referenceCoupling v z) atTop (nhds ((z 0)^2)) := by
  let Y : ℕ → (ℕ → ℝ) → ℝ := fun i z => (z (i+1))^2
  have hid (i : ℕ) := (placeboFTest_normal_coordinates (i+1)).comp
    (by fun_prop : Measurable (fun x : ℝ => x^2))
  have hi : Integrable (Y 0) placeboFTest_normalProduct :=
    (hid 0).symm.integrable_snd ((memLp_id_gaussianReal 2).integrable_sq)
  have he : (∫ z, Y 0 z ∂placeboFTest_normalProduct) = 1 := by
    calc (∫ z, Y 0 z ∂placeboFTest_normalProduct)
      _ = ∫ x : ℝ, x^2 ∂gaussianReal 0 1 := (hid 0).integral_eq
      _ = 1 := by
        have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
        rw [variance_eq_integral measurable_id'.aemeasurable] at hv
        simpa using hv
  have hind : iIndepFun (fun i (z : ℕ → ℝ) => z i) placeboFTest_normalProduct :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  have hY : iIndepFun Y placeboFTest_normalProduct :=
    (hind.precomp Nat.succ_injective).comp (fun _ (x : ℝ) => x^2)
      (fun _ => (by fun_prop : Measurable (fun x : ℝ => x^2)))
  have h := strong_law_ae_real Y hi (fun i j hij => hY.indepFun hij)
    (fun i => (hid i).trans (hid 0).symm)
  rw [he] at h
  filter_upwards [h] with z hz
  have hh := (tendsto_const_nhds (x := (z 0)^2)).div hz (by norm_num : (1 : ℝ) ≠ 0)
  have hsum (v : ℕ) : (∑ i : Fin v, (z (i.val+1))^2) =
      ∑ i ∈ Finset.range v, (z (i+1))^2 :=
    Fin.sum_univ_eq_sum_range (fun i => (z (i+1))^2) v
  simp_rw [placeboFTest_referenceCoupling, hsum]
  change Tendsto (fun n => (z 0)^2 / ((∑ i ∈ Finset.range n, Y i z) / (n : ℝ)))
    atTop (nhds ((z 0)^2 / 1)) at hh
  simpa only [div_one, Y] using hh

lemma placeboFTest_referenceCoupling_law (v : ℕ) :
    placeboFTest_normalProduct.map (placeboFTest_referenceCoupling v) = fReference 1 v := by
  have hind : iIndepFun (fun i (z : ℕ → ℝ) => z i) placeboFTest_normalProduct :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  have hm : placeboFTest_normalProduct.map (fun z (i : Fin (v+1)) => z i.val) =
      Measure.pi (fun _ : Fin (v+1) => gaussianReal 0 1) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun i => (measurable_pi_apply i.val).aemeasurable)
      (hind.precomp Fin.val_injective)]
    simp [placeboFTest_normalProduct, Measure.infinitePi_map_eval]
  unfold fReference
  rw [Nat.add_comm 1 v, ← hm]
  rw [Measure.map_map (by
    simp only [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    simp
    fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp [placeboFTest_referenceCoupling, Fin.sum_univ_succ]

/-- Almost-sure convergence of a real sequence gives a common high-probability upper bound. -/
lemma placeboFTest_uniform_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ → Ω → ℝ)
    (hT : ∀ n, Measurable (T n)) (t : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => T n ω) atTop (nhds (t ω)))
    (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, ∀ n, 1 - α < prob μ {ω | T n ω ≤ C} := by
  let A : ℕ → Set Ω := fun m => {ω | ∀ n, T n ω ≤ (m : ℝ)}
  have hA : ∀ m, MeasurableSet (A m) := by
    intro m
    change MeasurableSet {ω | ∀ n, T n ω ≤ (m : ℝ)}
    convert MeasurableSet.iInter (fun n => measurableSet_le (hT n)
      (measurable_const (a := (m : ℝ)))) using 1
    ext ω
    simp
  have hmono : Monotone A := by
    intro a b hab ω hω n
    exact (hω n).trans (by exact_mod_cast hab)
  have hu : ∀ᵐ ω ∂μ, ω ∈ ⋃ m, A m := by
    filter_upwards [hlim] with ω hω
    obtain ⟨C, hC⟩ := hω.bddAbove_range
    obtain ⟨m, hm⟩ := exists_nat_gt C
    exact Set.mem_iUnion.mpr ⟨m, fun n => (hC (Set.mem_range_self n)).trans hm.le⟩
  have hμ : μ (⋃ m, A m) = 1 := by
    rw [← measure_univ (μ := μ)]
    apply measure_congr
    filter_upwards [hu] with ω hω
    simp [hω]
  have hm := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hμ] at hm
  have hreal := (ENNReal.continuousAt_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).tendsto.comp hm
  simp only [Function.comp_def, ENNReal.toReal_one] at hreal
  obtain ⟨m, hm⟩ := (hreal.eventually (lt_mem_nhds (by linarith : 1 - α < (1 : ℝ)))).exists
  refine ⟨(m : ℝ), fun n => hm.trans_le ?_⟩
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (fun ω hω => hω n))

lemma placeboFTest_critical_bounded (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (critical : ℕ → ℝ)
    (hcritical : ∀ n : ℕ, 3 < n →
      prob (fReference 1 (n-3)) (Set.Iic (critical n)) = 1-α) :
    ∃ C : ℝ, ∀ᶠ n in atTop, critical n ≤ C := by
  obtain ⟨C, hC⟩ := placeboFTest_uniform_bound placeboFTest_normalProduct
    placeboFTest_referenceCoupling (fun n => by unfold placeboFTest_referenceCoupling; fun_prop)
    (fun z => (z 0)^2) placeboFTest_referenceCoupling_limit α hα.1
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (3 : ℕ)] with n hn
  by_contra hnc
  have hle : C ≤ critical n := le_of_lt (lt_of_not_ge hnc)
  have hp : 1-α < prob (fReference 1 (n-3)) (Set.Iic C) := by
    rw [← placeboFTest_referenceCoupling_law (n-3), prob,
      Measure.map_apply (by unfold placeboFTest_referenceCoupling; fun_prop) measurableSet_Iic]
    exact hC (n-3)
  have hm : prob (fReference 1 (n-3)) (Set.Iic C) ≤
      prob (fReference 1 (n-3)) (Set.Iic (critical n)) := by
    apply ENNReal.toReal_mono
    · rw [← placeboFTest_referenceCoupling_law (n-3)]
      exact measure_ne_top _ _
    · exact measure_mono (Set.Iic_subset_Iic.mpr hle)
  rw [hcritical n hn] at hm
  linarith


theorem placebo_linear_test_counterexample_proof {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → Fin 12)
  (hiid : IID μ Z) (hlaw : μ.map (Z 0)=finiteLawMeasure placeboLaw) :
  FCondIndep placeboLaw placeboW placeboD placeboX ∧
  FCondIndep placeboLaw (fun i => (2+placeboZ i,3+placeboZ i)) placeboD placeboX ∧
  placeboMoment.det=17/54 ∧
  (∀ a b c : ℝ, placeboRisk (29/68) 0 (4/17) ≤ placeboRisk a b c ∧
    (placeboRisk a b c=placeboRisk (29/68) 0 (4/17) ↔ a=29/68 ∧ b=0 ∧ c=4/17)) ∧
  (∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleF Z n ω/(n : ℝ)) atTop (nhds (64/531))) ∧
  (∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleWald Z n ω/(n : ℝ)) atTop (nhds (18496/135315))) ∧
  (∀ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 → ∀ critical : ℕ → ℝ,
    (∀ n : ℕ, 3 < n → prob (fReference 1 (n-3)) (Set.Iic (critical n))=1-α) →
    Tendsto (fun n => prob μ {ω | critical n < placeboSampleF Z n ω}) atTop (nhds 1)) ∧
  (∀ c : ℝ, Tendsto (fun n => prob μ {ω | c < placeboSampleWald Z n ω}) atTop (nhds 1)) ∧
  240*placeboRisk (7/12) 0 0=175/3 ∧
  240*placeboRisk (29/68) 0 (4/17)=885/17 ∧
  ((240*placeboRisk (7/12) 0 0-240*placeboRisk (29/68) 0 (4/17))/
    (240*placeboRisk (29/68) 0 (4/17)/(240-3))=5056/177) := by
  rcases placebo_full_finite_counterexample with
    ⟨hCI,hPO,hPos,hVar,hDet,hUnique,hRestricted,hRR,hRF,hImproves,hNonzero⟩
  refine ⟨hCI,hPO,hDet,hUnique,placeboFTest_sampleF_limit μ Z hiid hlaw,
    placeboFTest_sampleWald_limit μ Z hiid hlaw,?_,
    placeboFTest_sampleWald_reject μ Z hiid hlaw,?_,?_,?_⟩
  · intro α hα critical hcritical
    obtain ⟨C,hC⟩ := placeboFTest_critical_bounded α hα critical hcritical
    exact placeboFTest_sampleF_reject_bounded μ Z hiid hlaw critical C hC
  · rw [hRR]; norm_num
  · rw [hRF]; norm_num
  · rw [hRR,hRF]; norm_num

lemma placeboFTest_sq_fiber_finite (a : ℝ) : {x : ℝ | x^2 = a}.Finite := by
  by_cases h : ∃ x : ℝ, x^2 = a
  · obtain ⟨x,hx⟩ := h
    apply (Set.toFinite ({x,-x} : Set ℝ)).subset
    intro y hy
    have hh : y^2 = x^2 := hy.trans hx.symm
    simpa [sq_eq_sq_iff_eq_or_eq_neg] using hh
  · have he : {x : ℝ | x^2 = a} = ∅ := by ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]; exact fun hx => h ⟨x,hx⟩
    rw [he]; exact finite_empty

def placeboFTest_referenceProduct (v : ℕ) : Measure (ℝ × (Fin v → ℝ)) :=
  (gaussianReal 0 1).prod (Measure.pi (fun _ : Fin v => gaussianReal 0 1))

def placeboFTest_referenceRatio (v : ℕ) (z : ℝ × (Fin v → ℝ)) : ℝ :=
  z.1^2 / ((∑ i, (z.2 i)^2) / (v : ℝ))

lemma placeboFTest_reference_product_law (v : ℕ) :
    (placeboFTest_referenceProduct v).map (placeboFTest_referenceRatio v) = fReference 1 v := by
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (v+1) => gaussianReal 0 1) 0).map_eq
  change (Measure.pi (fun _ : Fin (v+1) => gaussianReal 0 1)).map
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (v+1) => ℝ) 0) =
    placeboFTest_referenceProduct v at he
  rw [← he, Measure.map_map (by unfold placeboFTest_referenceRatio; fun_prop) (by fun_prop)]
  unfold fReference
  rw [Nat.add_comm 1 v]
  congr 1
  funext z
  simp [placeboFTest_referenceRatio, Fin.sum_univ_succ,
    MeasurableEquiv.piFinSuccAbove, Fin.tail]

lemma placeboFTest_reference_noAtoms (v : ℕ) (hv : 0 < v) (t : ℝ) :
    fReference 1 v {t} = 0 := by
  let placeboFTest_gaussianNull : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hz : ∀ᵐ y ∂(Measure.pi (fun _ : Fin v => gaussianReal 0 1)),
      (∑ i, (y i)^2) / (v : ℝ) ≠ 0 := by
    have he : (Measure.pi (fun _ : Fin v => gaussianReal 0 1)).map
        (fun y => y ⟨0,hv⟩) = gaussianReal 0 1 := by
      exact (measurePreserving_eval (fun _ : Fin v => gaussianReal 0 1) ⟨0,hv⟩).map_eq
    have hne : ∀ᵐ y ∂(Measure.pi (fun _ : Fin v => gaussianReal 0 1)), y ⟨0,hv⟩ ≠ 0 := by
      have hp : ∀ᵐ x ∂(Measure.pi (fun _ : Fin v => gaussianReal 0 1)).map
          (fun y => y ⟨0,hv⟩), x ≠ (0 : ℝ) := by
        rw [he]
        exact ae_iff.mpr (by simp)
      exact (ae_map_iff (f := fun y : Fin v → ℝ => y ⟨0,hv⟩)
        (p := fun x : ℝ => x ≠ 0) (measurable_pi_apply _).aemeasurable (by measurability)).mp hp
    filter_upwards [hne] with y hy
    apply div_ne_zero _ (by exact_mod_cast hv.ne')
    have hpos := Finset.single_le_sum (fun i _ => sq_nonneg (y i))
      (Finset.mem_univ (⟨0,hv⟩ : Fin v))
    exact ne_of_gt (lt_of_lt_of_le (sq_pos_of_ne_zero hy) hpos)
  have hmeas : Measurable (placeboFTest_referenceRatio v) := by
    unfold placeboFTest_referenceRatio; fun_prop
  have hset : MeasurableSet {x | x ∉ placeboFTest_referenceRatio v ⁻¹' {t}} :=
    (hmeas (measurableSet_singleton t)).compl
  rw [← placeboFTest_reference_product_law v, Measure.map_apply
    (by unfold placeboFTest_referenceRatio; fun_prop) (measurableSet_singleton t)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  rw [placeboFTest_referenceProduct, Measure.ae_prod_iff_ae_ae hset]
  -- Interchange the factors so the denominator is fixed first.
  rw [Measure.ae_ae_comm hset]
  filter_upwards [hz] with y hy
  have hf : {x : ℝ | x^2 / ((∑ i, (y i)^2) / (v : ℝ)) = t}.Finite := by
    have he : {x : ℝ | x^2 / ((∑ i, (y i)^2) / (v : ℝ)) = t} =
        {x : ℝ | x^2 = t * ((∑ i, (y i)^2) / (v : ℝ))} := by
      ext x; exact div_eq_iff hy
    rw [he]
    exact placeboFTest_sq_fiber_finite _
  exact (measure_eq_zero_iff_ae_notMem.mp (hf.measure_zero _))


lemma placeboFTest_reference_quantile (v : ℕ) (hv : 0 < v) :
    ∃ c : ℝ, prob (fReference 1 v) (Set.Iic c) = 1/2 := by
  let ν := fReference 1 v
  let placeboFTest_reference_probability : IsProbabilityMeasure ν := by
    rw [show ν = (placeboFTest_normalProduct.map (placeboFTest_referenceCoupling v)) from
      (placeboFTest_referenceCoupling_law v).symm]
    infer_instance
  let placeboFTest_reference_null : NullSingletonClass ν :=
    ⟨fun t => placeboFTest_reference_noAtoms v hv t⟩
  have hcont : Continuous (fun x : ℝ => prob ν (Iic x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hc := ((integrable_const (1 : ℝ) (μ := ν)).integrableOn (s := Iic (x+1))).continuousOn_Iic_primitive_Iic
    have hh := (hc x (by simp)).continuousAt (Iic_mem_nhds (by linarith : x < x+1))
    simpa [prob, Measure.real] using hh
  have he (x : ℝ) : ProbabilityTheory.cdf ν x = prob ν (Iic x) := ProbabilityTheory.cdf_eq_real ν x
  have hbot := tendsto_cdf_atBot ν
  have htop := tendsto_cdf_atTop ν
  have hfun : (fun x => (ProbabilityTheory.cdf ν) x) = (fun x => prob ν (Iic x)) := funext he
  rw [show (ProbabilityTheory.cdf ν : ℝ → ℝ) = (fun x => prob ν (Iic x)) from hfun] at hbot htop
  obtain ⟨a,ha⟩ := (hbot.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))).exists
  obtain ⟨b,hb⟩ := (htop.eventually (lt_mem_nhds (by norm_num : (1/2 : ℝ) < 1))).exists
  exact intermediate_value_univ a b hcont ⟨ha.le,hb.le⟩


instance placeboFTest_finiteLaw_probability : IsProbabilityMeasure (finiteLawMeasure placeboLaw) := by
  constructor
  have hs : (∑ i : Fin 12, ENNReal.ofReal (placeboLaw.weight i)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => placeboLaw.nonneg i), placeboLaw.total]
    norm_num
  simpa [finiteLawMeasure] using hs

def placeboFTest_Xv (j : Fin 12) : Fin 1 → ℝ := fun _ => placeboX j

def placeboFTest_Wv (j : Fin 12) : Fin 1 → ℝ := fun _ => placeboW j

/-- The conditional average over the four atoms with the given X value. -/
def placeboFTest_cellAverage (g : Fin 12 → ℝ) (x : Fin 1 → ℝ) : ℝ :=
  3 * ∑ j, if placeboX j = x 0 then placeboLaw.weight j * g j else 0

lemma placeboFTest_cellAverage_measurable (g : Fin 12 → ℝ) :
    Measurable (placeboFTest_cellAverage g) := by
  unfold placeboFTest_cellAverage
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.piecewise
    (measurableSet_eq_fun measurable_const (measurable_pi_apply 0)) measurable_const

lemma placeboFTest_cellAverage_balance (g : Fin 12 → ℝ) (S : Set (Fin 1 → ℝ)) :
    fmean placeboLaw (fun j => if placeboFTest_Xv j ∈ S then
      placeboFTest_cellAverage g (placeboFTest_Xv j) else 0) =
    fmean placeboLaw (fun j => if placeboFTest_Xv j ∈ S then g j else 0) := by
  unfold fmean placeboFTest_cellAverage placeboFTest_Xv
  by_cases hm : (fun _ : Fin 1 => (-1 : ℝ)) ∈ S <;>
    by_cases hz : (fun _ : Fin 1 => (0 : ℝ)) ∈ S <;>
      by_cases hp : (fun _ : Fin 1 => (1 : ℝ)) ∈ S <;>
        norm_num [fmean, placeboFTest_cellAverage, placeboFTest_Xv,
          placeboLaw, placeboX, Fin.sum_univ_succ, hm, hz, hp] <;> ring

lemma placeboFTest_integral_lift {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 12) (hZ : Measurable Z)
    (hlaw : μ.map Z = finiteLawMeasure placeboLaw) (g : Fin 12 → ℝ) :
    (∫ ω, g (Z ω) ∂μ) = fmean placeboLaw g := by
  rw [← integral_map hZ.aemeasurable (measurable_of_finite g).aestronglyMeasurable,
    hlaw, placeboFTest_integral]

lemma placeboFTest_setIntegral_lift {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 12) (hZ : Measurable Z)
    (hlaw : μ.map Z = finiteLawMeasure placeboLaw) (g : Fin 12 → ℝ)
    (S : Set (Fin 1 → ℝ)) (hS : MeasurableSet S) :
    (∫ ω in (fun ω => placeboFTest_Xv (Z ω)) ⁻¹' S, g (Z ω) ∂μ) =
      fmean placeboLaw (fun j => if placeboFTest_Xv j ∈ S then g j else 0) := by
  have hs : MeasurableSet ((fun ω => placeboFTest_Xv (Z ω)) ⁻¹' S) := by
    exact ((measurable_of_finite placeboFTest_Xv).comp hZ) hS
  rw [← integral_indicator hs]
  exact placeboFTest_integral_lift μ Z hZ hlaw
    (fun j => if placeboFTest_Xv j ∈ S then g j else 0)

lemma placeboFTest_condExp_lift {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → Fin 12) (hZ : Measurable Z)
    (hlaw : μ.map Z = finiteLawMeasure placeboLaw) (g : Fin 12 → ℝ) :
    (fun ω => placeboFTest_cellAverage g (placeboFTest_Xv (Z ω))) =ᵐ[μ]
      μ[(fun ω => g (Z ω)) | MeasurableSpace.comap (fun ω => placeboFTest_Xv (Z ω)) inferInstance] := by
  have hmp : MeasurePreserving Z μ (finiteLawMeasure placeboLaw) := ⟨hZ,hlaw⟩
  have hg : Integrable (fun ω => g (Z ω)) μ := (hmp.integrable_comp (measurable_of_finite g).aestronglyMeasurable).mpr
      (Integrable.of_finite (μ := finiteLawMeasure placeboLaw))
  have hb : Integrable (fun ω => placeboFTest_cellAverage g (placeboFTest_Xv (Z ω))) μ :=
    (hmp.integrable_comp (measurable_of_finite
      (fun j => placeboFTest_cellAverage g (placeboFTest_Xv j))).aestronglyMeasurable).mpr
        (Integrable.of_finite (μ := finiteLawMeasure placeboLaw))
  have hm := ((measurable_of_finite placeboFTest_Xv).comp hZ).comap_le
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hg
  · intro s hs hμs
    exact hb.integrableOn
  · intro s hs hμs
    obtain ⟨S,hS,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    change (∫ ω in (fun ω => placeboFTest_Xv (Z ω)) ⁻¹' S,
      (fun j => placeboFTest_cellAverage g (placeboFTest_Xv j)) (Z ω) ∂μ) = _
    exact (placeboFTest_setIntegral_lift μ Z hZ hlaw
      (fun j => placeboFTest_cellAverage g (placeboFTest_Xv j)) S hS).trans
        ((placeboFTest_cellAverage_balance g S).trans
          (placeboFTest_setIntegral_lift μ Z hZ hlaw g S hS).symm)
  · exact ((placeboFTest_cellAverage_measurable g).comp
      (comap_measurable _)).stronglyMeasurable.aestronglyMeasurable

set_option maxHeartbeats 1600000 in
lemma placeboFTest_cellAverage_factor (A : Set (Fin 1 → ℝ)) (B : Set ℝ) (j : Fin 12) :
    placeboFTest_cellAverage (fun k => if placeboFTest_Wv k ∈ A ∧ placeboD k ∈ B then 1 else 0)
      (placeboFTest_Xv j) =
    placeboFTest_cellAverage (fun k => if placeboFTest_Wv k ∈ A then 1 else 0) (placeboFTest_Xv j) *
      placeboFTest_cellAverage (fun k => if placeboD k ∈ B then 1 else 0) (placeboFTest_Xv j) := by
  have hx : placeboX j = -1 ∨ placeboX j = 0 ∨ placeboX j = 1 := by
    fin_cases j <;> norm_num [placeboX]
  unfold placeboFTest_cellAverage placeboFTest_Xv placeboFTest_Wv
  rcases hx with hx | hx | hx <;>
    simp only [hx] <;>
      norm_num [placeboLaw, placeboX, placeboW, placeboZ, placeboD, Fin.sum_univ_succ]
  all_goals
    by_cases hAm : (fun _ : Fin 1 => (-(1/2) : ℝ)) ∈ A <;>
      by_cases hAz : (fun _ : Fin 1 => (1/2 : ℝ)) ∈ A <;>
        by_cases hAp : (fun _ : Fin 1 => (3/2 : ℝ)) ∈ A <;>
          by_cases hBz : (0 : ℝ) ∈ B <;>
            by_cases hBo : (1 : ℝ) ∈ B <;>
              norm_num [hAm, hAz, hAp, hBz, hBo]

lemma placeboFTest_CI_lift {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → Fin 12) (hZ : Measurable Z)
    (hlaw : μ.map Z = finiteLawMeasure placeboLaw) :
    CI μ (fun ω => placeboFTest_Xv (Z ω)) ((measurable_of_finite placeboFTest_Xv).comp hZ)
      (fun ω => placeboFTest_Wv (Z ω)) (fun ω => placeboD (Z ω)) := by
  intro A B hA hB
  filter_upwards [placeboFTest_condExp_lift μ Z hZ hlaw
      (fun k => if placeboFTest_Wv k ∈ A ∧ placeboD k ∈ B then 1 else 0),
    placeboFTest_condExp_lift μ Z hZ hlaw (fun k => if placeboFTest_Wv k ∈ A then 1 else 0),
    placeboFTest_condExp_lift μ Z hZ hlaw (fun k => if placeboD k ∈ B then 1 else 0)] with ω hAB ha hb
  rw [← hAB, ← ha, ← hb]
  exact placeboFTest_cellAverage_factor A B (Z ω)

/-- The canonical iid sample space of the twelve-atom law. -/
def placeboFTest_sampleSpace : Measure (ℕ → Fin 12) :=
  Measure.infinitePi (fun _ : ℕ => finiteLawMeasure placeboLaw)

instance placeboFTest_sampleSpace_probability : IsProbabilityMeasure placeboFTest_sampleSpace := by
  unfold placeboFTest_sampleSpace
  infer_instance

lemma placeboFTest_sampleSpace_iid :
    IID placeboFTest_sampleSpace (fun i (ω : ℕ → Fin 12) => ω i) := by
  refine ⟨fun i => measurable_pi_apply i, ?_, ?_⟩
  · exact iIndepFun_infinitePi (X := fun _ (x : Fin 12) => x) (fun _ => measurable_id)
  · intro i
    refine ⟨(measurable_pi_apply i).aemeasurable,
      (measurable_pi_apply 0).aemeasurable, ?_⟩
    simp [placeboFTest_sampleSpace, Measure.infinitePi_map_eval]

lemma placeboFTest_sampleSpace_law :
    placeboFTest_sampleSpace.map (fun ω => ω 0) = finiteLawMeasure placeboLaw := by
  exact Measure.infinitePi_map_eval _ _

lemma placeboFTest_vector_iid {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : ℕ → Ω → Fin 12) (hZ : IID μ Z) :
    IID μ (fun i ω => (placeboFTest_Xv (Z i ω),placeboFTest_Wv (Z i ω),placeboD (Z i ω))) := by
  let g : Fin 12 → (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ := fun j =>
    (placeboFTest_Xv j,placeboFTest_Wv j,placeboD j)
  have hg : Measurable g := measurable_of_finite _
  exact ⟨fun i => hg.comp (hZ.1 i),
    hZ.2.1.comp (fun _ => g) (fun _ => hg),fun i => (hZ.2.2 i).comp hg⟩

lemma placeboFTest_vector_rank {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → Fin 12) (hZ : Measurable Z) (hlaw : μ.map Z = finiteLawMeasure placeboLaw) :
    IsUnit (Matrix.det ((fun j k : Fin (1+1+1) => mean μ (fun ω =>
      (Fin.cases 1 ((fun b : Fin 2 => Fin.addCases (motive := fun _ => ℝ)
        (placeboFTest_Xv (Z ω)) (placeboFTest_Wv (Z ω)) b)) j)*
      (Fin.cases 1 ((fun b : Fin 2 => Fin.addCases (motive := fun _ => ℝ)
        (placeboFTest_Xv (Z ω)) (placeboFTest_Wv (Z ω)) b)) k))) :
      Matrix (Fin (1+1+1)) (Fin (1+1+1)) ℝ)) := by
  have he : ((fun j k : Fin 3 => mean μ (fun ω =>
      (Fin.cases 1 ((fun b : Fin 2 => Fin.addCases (motive := fun _ => ℝ)
        (placeboFTest_Xv (Z ω)) (placeboFTest_Wv (Z ω)) b)) j)*
      (Fin.cases 1 ((fun b : Fin 2 => Fin.addCases (motive := fun _ => ℝ)
        (placeboFTest_Xv (Z ω)) (placeboFTest_Wv (Z ω)) b)) k))) :
      Matrix (Fin 3) (Fin 3) ℝ) = placeboMoment := by
    have hd (j : Fin 12) (a : Fin 3) :
        Fin.cases 1 (fun b : Fin 2 => Fin.addCases (motive := fun _ => ℝ)
          (placeboFTest_Xv j) (placeboFTest_Wv j) b) a = placeboRegressor j a := by
      fin_cases a <;> rfl
    ext a b
    simp only [mean, hd]
    exact placeboFTest_integral_lift μ Z hZ hlaw
      (fun j => placeboRegressor j a * placeboRegressor j b)
  rw [he, placebo_full_finite_counterexample.2.2.2.2.1]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

lemma placeboFTest_vector_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → Fin 12) (hZ : Measurable Z) :
    (∀ k, MemLp (fun ω => placeboFTest_Xv (Z ω) k) 2 μ) ∧
    (∀ k, MemLp (fun ω => placeboFTest_Wv (Z ω) k) 2 μ) := by
  constructor
  · intro k
    apply MemLp.of_bound (((measurable_of_finite placeboX).comp hZ).aestronglyMeasurable) 1
    apply ae_of_all
    intro ω
    have h (j : Fin 12) : ‖placeboX j‖ ≤ 1 := by
      fin_cases j <;> norm_num [placeboX]
    exact h (Z ω)
  · intro k
    apply MemLp.of_bound (((measurable_of_finite placeboW).comp hZ).aestronglyMeasurable) 2
    apply ae_of_all
    intro ω
    have h (j : Fin 12) : ‖placeboW j‖ ≤ 2 := by
      fin_cases j <;> norm_num [placeboW,placeboX,placeboZ]
    exact h (Z ω)


theorem printed_placebo_f_test_size_refuted :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K L : ℕ} (hL : 0 < L) (X : ℕ → Ω → Fin K → ℝ) (W : ℕ → Ω → Fin L → ℝ) (D : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,W i ω,D i ω))) (hX : Measurable (X 0))
   (hCI : CI μ (X 0) hX (W 0) (D 0)) (hbinary : ∀ i ω,D i ω=0 ∨ D i ω=1)
   (hX2 : ∀ k,MemLp (fun ω => X 0 ω k) 2 μ) (hW2 : ∀ k,MemLp (fun ω => W 0 ω k) 2 μ)
   (hRank : IsUnit (Matrix.det ((fun j k : Fin (K+L+1) => mean μ (fun ω =>
     (Fin.cases 1 (Fin.addCases (X 0 ω) (W 0 ω)) j)*
     (Fin.cases 1 (Fin.addCases (X 0 ω) (W 0 ω)) k))) : Matrix (Fin (K+L+1)) (Fin (K+L+1)) ℝ)))
   (α : ℝ) (hα : α∈Set.Ioo (0 : ℝ) 1) (critical : ℕ → ℝ)
   (hcritical : ∀ n,K+L+1 < n → prob (fReference L (n-(K+L+1))) (Set.Iic (critical n))=1-α),
   Filter.limsup (fun (n : ℕ) => prob μ {ω | critical n < placeboFStatistic (firstSample X n ω)
     (firstSample W n ω) (firstSample D n ω)}) atTop  ≤  α) := by
  intro hprinted
  let μ := placeboFTest_sampleSpace
  let Z : ℕ → (ℕ → Fin 12) → Fin 12 := fun i ω => ω i
  let X : ℕ → (ℕ → Fin 12) → Fin 1 → ℝ := fun i ω => placeboFTest_Xv (Z i ω)
  let W : ℕ → (ℕ → Fin 12) → Fin 1 → ℝ := fun i ω => placeboFTest_Wv (Z i ω)
  let D : ℕ → (ℕ → Fin 12) → ℝ := fun i ω => placeboD (Z i ω)
  have hiid : IID μ Z := placeboFTest_sampleSpace_iid
  have hlaw : μ.map (Z 0) = finiteLawMeasure placeboLaw := placeboFTest_sampleSpace_law
  have hX : Measurable (X 0) := (measurable_of_finite placeboFTest_Xv).comp (hiid.1 0)
  have hCI : CI μ (X 0) hX (W 0) (D 0) := placeboFTest_CI_lift μ (Z 0) (hiid.1 0) hlaw
  have hbinary : ∀ i ω, D i ω = 0 ∨ D i ω = 1 := by
    have hd (j : Fin 12) : placeboD j = 0 ∨ placeboD j = 1 := by
      fin_cases j <;> norm_num [placeboD]
    exact fun i ω => hd (Z i ω)
  have hMom := placeboFTest_vector_moments μ (Z 0) (hiid.1 0)
  let critical : ℕ → ℝ := fun n => if hn : 3 < n then
    (placeboFTest_reference_quantile (n-3) (by omega)).choose else 0
  have hcritical : ∀ n : ℕ, 3 < n →
      prob (fReference 1 (n-3)) (Iic (critical n)) = 1-(1/2 : ℝ) := by
    intro n hn
    simpa only [critical, dif_pos hn, show (1 : ℝ)-(1/2) = 1/2 by norm_num] using
      (placeboFTest_reference_quantile (n-3) (by omega)).choose_spec
  have hsize := hprinted μ (K := 1) (L := 1) (by decide) X W D
    (placeboFTest_vector_iid μ Z hiid) hX hCI hbinary hMom.1 hMom.2
    (placeboFTest_vector_rank μ (Z 0) (hiid.1 0) hlaw)
    (1/2) (by norm_num) critical hcritical
  have hrej : Tendsto (fun n => prob μ {ω | critical n < placeboSampleF Z n ω})
      atTop (nhds 1) := by
    obtain ⟨C,hC⟩ := placeboFTest_critical_bounded (1/2) (by norm_num) critical hcritical
    exact placeboFTest_sampleF_reject_bounded μ Z hiid hlaw critical C hC
  change Filter.limsup (fun n => prob μ {ω | critical n < placeboSampleF Z n ω}) atTop ≤ (1/2 : ℝ) at hsize
  rw [hrej.limsup_eq] at hsize
  norm_num at hsize

end
end AronowAudit.P001.Wave1
