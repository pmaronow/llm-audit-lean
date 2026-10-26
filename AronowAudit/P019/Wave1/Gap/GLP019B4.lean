import AronowAudit.P019.Wave1.Gap.GP019B5b
import AronowAudit.P019.Wave1.Gap.GP019B3b
import Mathlib.Probability.CramerWold
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

namespace AronowAudit.P019.Wave1

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped BigOperators Topology RealInnerProductSpace ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

abbrev frc_law := uniformFin 128 (by norm_num)
abbrev frc_gaussian (n : ℕ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
def frc_v (j : Fin 5) : ℝ := if j.val < 4 then 4 else 2

lemma frc_v_pos (j : Fin 5) : 0 < frc_v j := by
  unfold frc_v; split_ifs <;> norm_num

lemma frc_contrast_eq (j : Fin 5) (ω : Fin 128) :
    frc_law.contrastInfluence (fun t => ((sequentialStudy j).V t : ℝ))
      ((sequentialStudy j).cell true true) ((sequentialStudy j).cell false true) ω =
      sequentialPsi j ω := by
  let S := sequentialStudy j
  have hs := (fisher_sequential_finite_proof.1 j).1
  have hp := regularity_probabilities S hs.2.2.2
  let q := S.law.prob (fun t => S.Y t = true)
  let m := S.law.ce (fun t => (S.W t : ℝ)) (fun t => S.Y t = true)
  have hq : q ≠ 0 := (hp.2 true).ne'
  have hg : S.gamma ≠ 0 := (hp.1 true).ne'
  have hg0 : 1-S.gamma ≠ 0 := by
    have h := (hp.1 false).ne'; rw [prob_false] at h; exact h
  have hmz (z : Bool) : S.listMean z true = m + bitVal z := by
    rw [list_mean_identified S hs.2.1 hs.2.2.1 z true
      (hs.2.2.2.1 z true).1.ne', monotone_yes_mean S hs.1 hq]
    simp [m]
  have hc1 : S.law.prob (S.cell true true) = q*S.gamma := by
    rw [cell_probability S hs.2.2.1 true true]; dsimp [q, Study.gamma]; ring
  have hc0 : S.law.prob (S.cell false true) = q*(1-S.gamma) := by
    rw [cell_probability S hs.2.2.1 false true, prob_false]; dsimp [q, Study.gamma]; ring
  rw [← fisher_sequential_finite_proof.2.2.1 j ω]
  change S.law.contrastInfluence (fun t => (S.V t : ℝ))
    (S.cell true true) (S.cell false true) ω = S.betaPsi ω
  symm
  change bitVal (S.Y ω)/q*((bitVal (S.Z ω)-S.gamma)/(S.gamma*(1-S.gamma)))*
    ((S.W ω : ℝ)-m) =
    (if S.cell true true ω then (S.V ω : ℝ)-S.listMean true true else 0)/
      S.law.prob (S.cell true true) -
    (if S.cell false true ω then (S.V ω : ℝ)-S.listMean false true else 0)/
      S.law.prob (S.cell false true)
  rw [hc1, hc0, hmz true, hmz false]
  have hω : 0 < S.law.mass ω := by norm_num [S, sequentialStudy, uniformFin]
  cases hy : S.Y ω
  · simp [bitVal, Study.cell, hy]
  · have hx := hs.1 ω hω hy
    rw [hs.2.1 ω hω]
    cases hz : S.Z ω <;> simp [bitVal, Study.cell, hy, hx, hz] <;> field_simp <;> ring

lemma frc_variance_consistency (j : Fin 5) :
    ∀ᵐ ω ∂t19_product frc_law, Tendsto (fun (n : ℕ) =>
      (n : ℝ) * (sequentialStudy j).betaVarianceHat (t19_sample n ω) 0)
      atTop (nhds (frc_v j)) := by
  let S := sequentialStudy j
  have hs := (fisher_sequential_finite_proof.1 j).1
  have hm := contrast_influence_moments S.law (fun t => (S.V t : ℝ))
    (S.cell true true) (S.cell false true)
    (hs.2.2.2.1 true true).1.ne' (hs.2.2.2.1 false true).1.ne'
    (by intro t ht hf; exact Bool.false_ne_true (hf.1.symm.trans ht.1))
  have hv : S.law.variance (S.law.contrastInfluence (fun t => (S.V t : ℝ))
      (S.cell true true) (S.cell false true)) = frc_v j := by
    have hf : S.law.contrastInfluence (fun t => (S.V t : ℝ))
        (S.cell true true) (S.cell false true) = sequentialPsi j :=
      funext (frc_contrast_eq j)
    rw [hf]
    change frc_law.variance (sequentialPsi j) = _
    rw [FiniteLaw.variance, sequential_influence_centered]
    simpa [frc_v, pow_two] using sequential_influence_matrix j j
  have h := GP019B3b_varianceHat_ae S.law (fun t => (S.V t : ℝ))
    (S.cell true true) (S.cell false true)
    (hs.2.2.2.1 true true).1 (hs.2.2.2.1 false true).1 0
  rw [← hm.2, hv] at h
  exact h

lemma frc_ratio_remainder (j : Fin 5) :
    TendstoInMeasure (t19_product frc_law) (fun (n : ℕ) ω =>
      Real.sqrt n * ((sequentialStudy j).betaHat (t19_sample n ω) 0 0 - 1) -
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, sequentialPsi j (ω i)) atTop (fun _ => 0) := by
  let S := sequentialStudy j
  have hs := (fisher_sequential_finite_proof.1 j).1
  have h := AronowAudit.P015.ConvergenceCompletion.sub_limit _
    (GP019B3b_ratio_remainder S.law (fun t => (S.V t : ℝ)) (S.cell true true)
      (hs.2.2.2.1 true true).1 0)
    (GP019B3b_ratio_remainder S.law (fun t => (S.V t : ℝ)) (S.cell false true)
      (hs.2.2.2.1 false true).1 0)
  have hβ : S.listMean true true - S.listMean false true = 1 :=
    (fisher_sequential_finite_proof.1 j).2
  have he (ω : ℕ → Fin 128) (n : ℕ) :
      (∑ i : Fin n, (if S.cell true true (ω i) then
        (S.V (ω i) : ℝ) - S.law.ce (fun t => (S.V t : ℝ)) (S.cell true true) else 0) /
        S.law.prob (S.cell true true)) -
      (∑ i : Fin n, (if S.cell false true (ω i) then
        (S.V (ω i) : ℝ) - S.law.ce (fun t => (S.V t : ℝ)) (S.cell false true) else 0) /
        S.law.prob (S.cell false true)) = ∑ i : Fin n, sequentialPsi j (ω i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => frc_contrast_eq j (ω i)
  convert h using 1 <;> try rfl
  all_goals try { simp only [sub_zero] }
  case e'_7 =>
    funext n ω
    change _ = Real.sqrt n *
      (S.cellMean (t19_sample n ω) true true 0 - S.listMean true true) - _ -
        (Real.sqrt n * (S.cellMean (t19_sample n ω) false true 0 - S.listMean false true) - _)
    rw [← he ω n, ← hβ]
    change Real.sqrt n * (S.betaHat (t19_sample n ω) 0 0 -
      (S.listMean true true - S.listMean false true)) - _ = _
    unfold Study.betaHat
    ring

lemma frc_gaussian_eval {n : ℕ} (j : Fin n) :
    HasLaw (fun e : Fin n → ℝ => e j) (gaussianReal 0 1) (frc_gaussian n) :=
  (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) j).hasLaw

lemma frc_gaussian_linear {n : ℕ} (a : Fin n → ℝ) :
    HasLaw (fun e : Fin n → ℝ => ∑ j, a j * e j)
      (gaussianReal 0 (∑ j, (a j)^2).toNNReal) (frc_gaussian n) := by
  have hi : iIndepFun (fun j (e : Fin n → ℝ) => e j) (frc_gaussian n) := by
    simpa only [id_eq] using iIndepFun_pi
      (μ := fun _ : Fin n => gaussianReal 0 1)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have hG := (hi.comp (fun j x => a j * x) (fun _ => by fun_prop)).hasGaussianLaw_fun_sum
    (fun j => ((frc_gaussian_eval j).hasGaussianLaw).fun_smul (a j))
  simp only [smul_eq_mul] at hG
  have hm : (∫ e, ∑ j, a j * e j ∂frc_gaussian n) = 0 := by
    rw [integral_finset_sum]
    · simp only [integral_const_mul, (frc_gaussian_eval _).integral_eq,
        integral_id_gaussianReal, mul_zero, Finset.sum_const_zero]
    · intro j _; exact ((frc_gaussian_eval j).hasGaussianLaw.fun_smul (a j)).integrable
  have hv : Var[fun e : Fin n → ℝ => ∑ j, a j * e j; frc_gaussian n] = ∑ j, (a j)^2 := by
    have hh (j : Fin n) : Var[fun x : ℝ => a j*x; gaussianReal 0 1] = (a j)^2 := by
      simpa only [id_eq, variance_id_gaussianReal, NNReal.coe_one, mul_one] using
        variance_const_mul (a j) id (gaussianReal 0 1)
    have h := variance_sum_pi (μ := fun _ : Fin n => gaussianReal 0 1)
      (X := fun j x => a j * x)
      (fun j => (memLp_id_gaussianReal 2).const_mul (a j))
    convert h using 1
    · congr 1; ext e; simp
    · exact (Finset.sum_congr rfl fun j _ => hh j).symm
  exact ⟨hG.aemeasurable, by rw [hG.map_eq_gaussianReal, hm, hv]⟩

def frc_z (n : ℕ) (ω : ℕ → Fin 128) (j : Fin 5) : ℝ :=
  ((sequentialStudy j).betaHat (t19_sample n ω) 0 0 - 1) /
    Real.sqrt ((sequentialStudy j).betaVarianceHat (t19_sample n ω) 0)

lemma frc_studentized_remainder (j : Fin 5) :
    TendstoInMeasure (t19_product frc_law) (fun (n : ℕ) ω => frc_z n ω j -
      ((Real.sqrt n)⁻¹ * ∑ i : Fin n, sequentialPsi j (ω i)) / Real.sqrt (frc_v j))
      atTop (fun _ => 0) := by
  let d : ℕ → (ℕ → Fin 128) → ℝ := fun n ω =>
    (Real.sqrt ((n : ℝ) * (sequentialStudy j).betaVarianceHat (t19_sample n ω) 0))⁻¹
  have hd : ∀ᵐ ω ∂t19_product frc_law, Tendsto (fun n => d n ω)
      atTop (nhds (Real.sqrt (frc_v j))⁻¹) := by
    filter_upwards [frc_variance_consistency j] with ω hω
    exact hω.sqrt.inv₀ (Real.sqrt_pos.mpr (frc_v_pos j)).ne'
  have hdm (n : ℕ) : Measurable (d n) := t19_stat_measurable n (fun s =>
    (Real.sqrt ((n : ℝ) * (sequentialStudy j).betaVarianceHat s 0))⁻¹)
  have hdi := tendstoInMeasure_of_tendsto_ae (fun n => (hdm n).aestronglyMeasurable) hd
  have hR := AronowAudit.P015.ConvergenceCompletion.mul_limit _ (frc_ratio_remainder j) hdi
  have hL := t19_small_product frc_law (sequentialPsi j) (sequential_influence_centered j)
    (fun n ω => d n ω - (Real.sqrt (frc_v j))⁻¹)
    (fun n => (hdm n).sub_const _)
    (by filter_upwards [hd] with ω hω; simpa using hω.sub_const (Real.sqrt (frc_v j))⁻¹)
  have hh := AronowAudit.P015.ConvergenceCompletion.add_limit _ hR hL
  simp only [zero_mul, add_zero] at hh
  apply t19_transfer_inMeasure (t19_product frc_law)
    (fun n => ((t19_stat_measurable n (fun s =>
      Real.sqrt n * ((sequentialStudy j).betaHat s 0 0 - 1) -
        (Real.sqrt n)⁻¹ * ∑ i, sequentialPsi j (s i))).mul (hdm n)).add
      ((t19_stat_measurable n (fun s => (Real.sqrt n)⁻¹ * ∑ i, sequentialPsi j (s i))).mul
        ((hdm n).sub_const _)))
    (fun n => t19_stat_measurable n (fun s =>
      ((sequentialStudy j).betaHat s 0 0-1) / Real.sqrt ((sequentialStudy j).betaVarianceHat s 0) -
        ((Real.sqrt n)⁻¹ * ∑ i, sequentialPsi j (s i)) / Real.sqrt (frc_v j))) hh
  apply ae_of_all
  intro ω
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnS : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  dsimp only [d, frc_z, Pi.add_apply, Pi.mul_apply]
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  simp only [mul_inv_rev, div_eq_mul_inv]
  linear_combination
    (((sequentialStudy j).betaHat (t19_sample n ω) 0 0 - 1) *
      (Real.sqrt ((sequentialStudy j).betaVarianceHat (t19_sample n ω) 0))⁻¹) *
        (mul_inv_cancel₀ hnS)

def frc_coeff (a : Fin 5 → ℝ) (j : Fin 5) : ℝ :=
  if j.val < 4 then a j / Real.sqrt 2 else
    (a 0 + a 1 + a 2 + a 3) / Real.sqrt 2 + a 4

lemma frc_correlated_linear (a e : Fin 5 → ℝ) :
    (∑ j, a j * correlatedNormals e j) = ∑ j, frc_coeff a j * e j := by
  norm_num [Fin.sum_univ_succ, correlatedNormals, frc_coeff]
  ring

def frc_influence (a : Fin 5 → ℝ) (ω : Fin 128) : ℝ :=
  ∑ j, (a j / Real.sqrt (frc_v j)) * sequentialPsi j ω

lemma frc_influence_mean (a : Fin 5 → ℝ) : frc_law.mean (frc_influence a) = 0 := by
  unfold frc_influence
  rw [mean_sum]
  simp_rw [mean_const_mul, sequential_influence_centered, mul_zero]
  simp

lemma frc_influence_variance (a : Fin 5 → ℝ) :
    frc_law.variance (frc_influence a) = ∑ j, (frc_coeff a j)^2 := by
  have he : (fun ω => (frc_influence a ω)^2) =
      (fun ω => ∑ j : Fin 5, ∑ k : Fin 5,
        (a j / Real.sqrt (frc_v j) * (a k / Real.sqrt (frc_v k))) *
          (sequentialPsi j ω * sequentialPsi k ω)) := by
    funext ω
    simp only [frc_influence, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [FiniteLaw.variance, frc_influence_mean, he, mean_sum]
  simp_rw [mean_sum, mean_const_mul, sequential_influence_matrix]
  norm_num [Fin.sum_univ_succ, frc_v, frc_coeff, Real.sqrt_eq_iff_mul_self_eq]
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp <;> ring_nf <;> simp only [hs] <;> ring

lemma frc_projection_limit (a : Fin 5 → ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω => ∑ j, a j * frc_z n ω j) atTop
      (fun e => ∑ j, a j * correlatedNormals e j)
      (fun _ => t19_product frc_law) (frc_gaussian 5) := by
  have h := t19_average_clt frc_law (frc_influence a) (frc_influence_mean a)
  rw [frc_influence_variance] at h
  have hl : HasLaw (fun e => ∑ j, a j * correlatedNormals e j)
      (gaussianReal 0 (∑ j, (frc_coeff a j)^2).toNNReal) (frc_gaussian 5) := by
    simpa only [frc_correlated_linear] using frc_gaussian_linear (frc_coeff a)
  have h' : TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i : Fin n, frc_influence a (ω i)) atTop
      (fun e => ∑ j, a j * correlatedNormals e j)
      (fun _ => t19_product frc_law) (frc_gaussian 5) := by
    refine ⟨h.forall_aemeasurable, hl.aemeasurable, ?_⟩
    simpa only [Measure.map_id, hl.map_eq] using h.tendsto
  have hr := AronowAudit.P015.ConvergenceCompletion.sum_limit (t19_product frc_law)
    (fun j n ω => a j * (frc_z n ω j -
      ((Real.sqrt n)⁻¹ * ∑ i : Fin n, sequentialPsi j (ω i)) / Real.sqrt (frc_v j)))
    (fun _ => 0) (fun j => by
      simpa only [mul_zero] using AronowAudit.P015.ConvergenceCompletion.mul_limit _
        (AronowAudit.P015.ConvergenceCompletion.constant_limit _ (a j))
        (frc_studentized_remainder j))
  have hdiff : TendstoInMeasure (t19_product frc_law)
      (fun (n : ℕ) ω => (∑ j, a j * frc_z n ω j) -
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, frc_influence a (ω i)) atTop (fun _ => 0) := by
    convert hr using 1
    · funext n ω
      simp only [frc_influence, Finset.sum_comm (s := Finset.univ (α := Fin n)),
        Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, div_eq_mul_inv]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [← Finset.mul_sum]
      ring
    · simp
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ h' hdiff
    (fun n => (t19_stat_measurable n (fun s => ∑ j,
      a j * (((sequentialStudy j).betaHat s 0 0-1) /
        Real.sqrt ((sequentialStudy j).betaVarianceHat s 0)))).aemeasurable)

lemma frc_correlated_continuous : Continuous correlatedNormals := by
  apply continuous_pi
  intro j
  unfold correlatedNormals
  by_cases hj : j.val < 4 <;> simp only [hj, if_true, if_false] <;> fun_prop

lemma frc_joint_limit :
    TendstoInDistribution (fun n ω => frc_z n ω) atTop correlatedNormals
      (fun _ => t19_product frc_law) (frc_gaussian 5) := by
  have h : TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (frc_z n ω)) atTop
      (fun e => WithLp.toLp 2 (correlatedNormals e))
      (fun _ => t19_product frc_law) (frc_gaussian 5) := by
    apply TendstoInDistribution.of_inner
    · exact ((PiLp.continuous_toLp _ _).measurable.comp
        frc_correlated_continuous.measurable).aemeasurable
    · intro n
      exact ((PiLp.continuous_toLp _ _).measurable.comp
        (Measurable.of_eval fun j => t19_stat_measurable n (fun s =>
          ((sequentialStudy j).betaHat s 0 0-1) /
            Real.sqrt ((sequentialStudy j).betaVarianceHat s 0)))).aemeasurable
    · intro t
      simpa only [PiLp.inner_apply, Real.inner_apply, mul_comm] using
        frc_projection_limit (fun j => t j)
  simpa only [Function.comp_def, WithLp.ofLp_toLp] using
    h.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : Fin 5 => ℝ))


local instance frc_uniform_probability :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

local instance frc_exponential_probability : IsProbabilityMeasure (expMeasure (1/2)) :=
  isProbabilityMeasure_expMeasure (by norm_num)

local instance frc_normal_atomless : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num)

def frc_p (x : ℝ) : ℝ := 2 * normalCDF (-|x|)
def frc_g (x : ℝ) : ℝ := -2 * Real.log (frc_p x)

@[fun_prop] lemma frc_p_continuous : Continuous frc_p := by
  have hc : Continuous normalCDF := by
    have h := continuous_iff_continuousAt.mpr
      (AronowAudit.P053.NormalCompletion.cdf_continuousAt (gaussianReal 0 1))
    exact h.congr (fun x => (npu_cdf_eq x).symm)
  exact continuous_const.mul (hc.comp continuous_abs.neg)

lemma frc_p_pos (x : ℝ) : 0 < frc_p x := mul_pos (by norm_num) (npu_cdf_pos _)

lemma frc_p_le_one (x : ℝ) : frc_p x ≤ 1 := by
  have h := npu_strictMono.monotone (neg_nonpos.mpr (abs_nonneg x))
  have h0 : normalCDF 0 = 1/2 := by
    rw [npu_cdf_eq, AronowAudit.P053.NormalCompletion.normal_cdf_zero]
  rw [h0] at h
  unfold frc_p
  linarith

@[fun_prop] lemma frc_g_continuous : Continuous frc_g :=
  continuous_const.mul (frc_p_continuous.log (fun x => (frc_p_pos x).ne'))

lemma frc_g_nonneg (x : ℝ) : 0 ≤ frc_g x := by
  have h := Real.log_nonpos (frc_p_pos x).le (frc_p_le_one x)
  unfold frc_g; linarith

lemma frc_g_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : frc_g x ≤ frc_g y := by
  have hy := hx.trans hxy
  have h : frc_p y ≤ frc_p x := by
    unfold frc_p
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    exact mul_le_mul_of_nonneg_left (npu_strictMono.monotone (neg_le_neg hxy)) (by norm_num)
  have hlog := Real.log_le_log (frc_p_pos y) h
  unfold frc_g
  linarith

lemma frc_g_large : ∃ b : ℝ, 0 < b ∧ 6 < frc_g b := by
  have he0 : 0 < Real.exp (-4 : ℝ) := Real.exp_pos _
  have he1 : Real.exp (-4 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  obtain ⟨q, hq⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq (gaussianReal 0 1)
    (p := Real.exp (-4)/2) (by positivity) (by linarith)
  have hq0 : q < 0 := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [hq, AronowAudit.P053.NormalCompletion.normal_cdf_zero]
    linarith
  refine ⟨-q, neg_pos.mpr hq0, ?_⟩
  have hp : frc_p (-q) = Real.exp (-4) := by
    simp only [frc_p, abs_of_pos (neg_pos.mpr hq0), neg_neg, npu_cdf_eq, hq]
    ring
  rw [frc_g, hp, Real.log_exp]
  norm_num

lemma frc_p_law :
    (gaussianReal 0 1).map frc_p = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  apply Measure.eq_of_cdf
  refine StieltjesFunction.ext fun t => ?_
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply frc_p_continuous.measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  by_cases ht1 : t ≤ 1
  · have hi : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 t := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨hut, hu0, _⟩; exact ⟨hu0, hut⟩
      · rintro ⟨hu0, hut⟩; exact ⟨hut, hu0, hut.trans ht1⟩
    rw [hi, Real.volume_Icc]
    by_cases ht0 : 0 < t
    · by_cases hlt1 : t < 1
      · rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ t-0)]
        change ((gaussianReal 0 1) {g | 2 * normalCDF (-|g|) ≤ t}).toReal = t-0
        simpa only [sub_zero] using normal_pvalue_uniform_proof t ht0 hlt1
      · have ht : t = 1 := le_antisymm ht1 (le_of_not_gt hlt1)
        subst t
        have he : frc_p ⁻¹' Set.Iic 1 = Set.univ := by
          ext x; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
          exact frc_p_le_one x
        rw [he, measure_univ]
        norm_num
    · have he : frc_p ⁻¹' Set.Iic t = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
        exact not_le.mpr (lt_of_le_of_lt (le_of_not_gt ht0) (frc_p_pos x))
      rw [he, measure_empty, ENNReal.ofReal_eq_zero.mpr (by linarith)]
  · have he : frc_p ⁻¹' Set.Iic t = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
      exact (frc_p_le_one x).trans (le_of_not_ge ht1)
    have hi : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 := by
      apply Set.inter_eq_right.mpr
      intro x hx
      exact hx.2.trans (le_of_not_ge ht1)
    rw [he, hi, measure_univ, Real.volume_Icc]
    norm_num

lemma frc_g_law : HasLaw frc_g (expMeasure (1/2)) (gaussianReal 0 1) := by
  have hp : HasLaw frc_p (volume.restrict (Set.Icc (0 : ℝ) 1)) (gaussianReal 0 1) :=
    ⟨frc_p_continuous.measurable.aemeasurable, frc_p_law⟩
  have hl : HasLaw (fun u : ℝ => -2*Real.log u) (expMeasure (1/2))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨ufi_log_measurable.aemeasurable, ufi_uniform_log_law⟩
  exact hl.comp hp

local instance frc_holder_four : ENNReal.HolderTriple 4 4 2 := ⟨by
  have h : (4 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ * 2⁻¹ := by
    simpa only [show (2 : ℝ≥0∞)*2 = 4 by norm_num] using
      (ENNReal.mul_inv (a := 2) (b := 2) (by norm_num) (by norm_num))
  simp only [h, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]⟩

lemma frc_exponential_memLp : MemLp id 2 (expMeasure (1/2)) := by
  have h4 (j : Fin 2) : MemLp (fun e : Fin 2 → ℝ => e j) 4 (frc_gaussian 2) :=
    (frc_gaussian_eval j).memLp (memLp_id_gaussianReal 4)
  have h2 (j : Fin 2) : MemLp (fun e : Fin 2 → ℝ => (e j)^2) 2 (frc_gaussian 2) := by
    simpa only [pow_two] using (h4 j).fun_mul (h4 j)
  have hsum : MemLp (fun e : Fin 2 → ℝ => ∑ j, (e j)^2) 2 (frc_gaussian 2) :=
    memLp_finsetSum _ (fun j _ => h2 j)
  rw [← ufi_normal_pair_law]
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    (Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).pow_const 2)).aemeasurable).mpr hsum

lemma frc_exponential_mean : (∫ x : ℝ, x ∂expMeasure (1/2)) = 2 := by
  change (∫ x : ℝ, x ∂gammaMeasure 1 (1/2)) = 2
  rw [StatLean.MultipleTesting.integral_id_gammaMeasure (by norm_num) (by norm_num)]
  norm_num

lemma frc_exponential_second : (∫ x : ℝ, x^2 ∂expMeasure (1/2)) = 8 := by
  have h := StatLean.MultipleTesting.variance_gammaMeasure
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1/2)
  have h1 : Integrable (fun x : ℝ => x) (expMeasure (1/2)) :=
    frc_exponential_memLp.integrable (by norm_num)
  have h2 : Integrable (fun x : ℝ => x^2) (expMeasure (1/2)) :=
    frc_exponential_memLp.integrable_sq
  have h3 : Integrable (fun x : ℝ => x^2-4*x) (expMeasure (1/2)) :=
    h2.sub (h1.const_mul 4)
  have he (x : ℝ) : (x - (1 : ℝ)/(1/2))^2 = x^2 - 4*x + 4 := by ring
  change (∫ x : ℝ, (x - (1 : ℝ)/(1/2))^2 ∂expMeasure (1/2)) = _ at h
  simp_rw [he] at h
  rw [integral_add h3 (integrable_const 4),
    integral_sub h2 (h1.const_mul 4), integral_const_mul,
    frc_exponential_mean, integral_const] at h
  norm_num at h
  linarith

lemma frc_g_memLp : MemLp frc_g 2 (gaussianReal 0 1) :=
  frc_g_law.memLp frc_exponential_memLp

lemma frc_g_mean : (∫ x, frc_g x ∂gaussianReal 0 1) = 2 :=
  frc_g_law.integral_eq.trans frc_exponential_mean

lemma frc_g_second : (∫ x, (frc_g x)^2 ∂gaussianReal 0 1) = 8 := by
  exact (frc_g_law.integral_comp (by fun_prop : AEStronglyMeasurable
    (fun x : ℝ => x^2) (expMeasure (1/2)))).trans frc_exponential_second

lemma frc_vector_weakLimit :
    WeakLimit frc_law
      (fun _ s j => ((sequentialStudy j).betaHat s 0 0-1) /
        Real.sqrt ((sequentialStudy j).betaVarianceHat s 0))
      ((frc_gaussian 5).map correlatedNormals) := by
  intro f hf hbound
  obtain ⟨C, hC⟩ := hbound
  let F : BoundedContinuousFunction (Fin 5 → ℝ) ℝ :=
    ⟨⟨f, hf⟩, ⟨2*C, fun x y => (dist_le_norm_add_norm _ _).trans (by
      simpa only [Real.norm_eq_abs, two_mul] using add_le_add (hC x) (hC y))⟩⟩
  have hh := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    frc_joint_limit.forall_aemeasurable frc_joint_limit.aemeasurable_limit).mp frc_joint_limit F
  change Tendsto (fun (n : ℕ) => ∫ ω, f (frc_z n ω) ∂t19_product frc_law)
    atTop (nhds (∫ e, f (correlatedNormals e) ∂frc_gaussian 5)) at hh
  rw [integral_map frc_correlated_continuous.measurable.aemeasurable hf.measurable.aestronglyMeasurable]
  convert hh using 1
  funext n
  exact (t19_sample_integral frc_law n (fun s => f (fun j =>
    ((sequentialStudy j).betaHat s 0 0-1) /
      Real.sqrt ((sequentialStudy j).betaVarianceHat s 0)))).symm

lemma frc_fisher_transform (e : Fin 5 → ℝ) :
    fisherStatistic (fun j => normalPValue (e j) 0 1) = ∑ j, frc_g (e j) := by
  simp [fisherStatistic, frc_g, frc_p, normalPValue, Finset.mul_sum]

lemma frc_fisher_weakLimit :
    WeakLimit frc_law (fun _ s => fisherStatistic
      (fun j => normalPValue ((sequentialStudy j).betaHat s 0 0) 1
        ((sequentialStudy j).betaVarianceHat s 0))) sequentialFisherLimit := by
  let F : (Fin 5 → ℝ) → ℝ := fun e => ∑ j, frc_g (e j)
  have hF : Continuous F := by dsimp only [F]; fun_prop
  have h := frc_joint_limit.continuous_comp hF
  have hm : HasLaw (F ∘ correlatedNormals) sequentialFisherLimit (frc_gaussian 5) := by
    refine ⟨hF.measurable.aemeasurable.comp_measurable frc_correlated_continuous.measurable, ?_⟩
    unfold sequentialFisherLimit
    congr 1
    funext e
    exact (frc_fisher_transform (correlatedNormals e)).symm
  haveI : IsProbabilityMeasure sequentialFisherLimit := hm.isProbabilityMeasure_iff.mp inferInstance
  have h' := t19_distribution_hasLaw h hm
  apply t19_weakLimit
  convert h' using 1
  funext n ω
  change _ = ∑ j, frc_g (frc_z n ω j)
  simp only [fisherStatistic, frc_g, frc_p, frc_z, normalPValue, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _), neg_div, Finset.mul_sum]

def frc_row (j : Fin 5) : Fin 5 → ℝ := frc_coeff (Pi.single j 1)

lemma frc_row_eval (j : Fin 5) (e : Fin 5 → ℝ) :
    (∑ k, frc_row j k * e k) = correlatedNormals e j := by
  simpa [frc_row, Pi.single_apply] using (frc_correlated_linear (Pi.single j 1) e).symm

def frc_rho (j k : Fin 5) : ℝ :=
  if j.val < 4 ∧ k.val < 4 then 1/2 else (Real.sqrt 2)⁻¹

lemma frc_row_dot (j k : Fin 5) :
    (∑ l, frc_row j l * frc_row k l) = if j = k then 1 else frc_rho j k := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  fin_cases j <;> fin_cases k <;>
    norm_num [frc_row, frc_coeff, frc_rho, Pi.single_apply, Fin.sum_univ_succ] <;>
      field_simp <;> ring_nf <;> simp only [hs] <;> norm_num

lemma frc_row_norm (j : Fin 5) : (∑ l, (frc_row j l)^2) = 1 := by
  simpa [pow_two] using frc_row_dot j j

lemma frc_normal_margin (j : Fin 5) :
    HasLaw (fun e => correlatedNormals e j) (gaussianReal 0 1) (frc_gaussian 5) := by
  simpa only [frc_row_eval, frc_row_norm, Real.toNNReal_one] using frc_gaussian_linear (frc_row j)

lemma frc_margin_memLp (j : Fin 5) :
    MemLp (fun e => frc_g (correlatedNormals e j)) 2 (frc_gaussian 5) :=
  (frc_normal_margin j).memLp_comp frc_g_memLp

lemma frc_margin_mean (j : Fin 5) :
    (∫ e, frc_g (correlatedNormals e j) ∂frc_gaussian 5) = 2 :=
  ((frc_normal_margin j).integral_comp frc_g_continuous.measurable.aestronglyMeasurable).trans
    frc_g_mean

lemma frc_margin_variance (j : Fin 5) :
    Var[fun e => frc_g (correlatedNormals e j); frc_gaussian 5] = 4 := by
  rw [variance_eq_sub (frc_margin_memLp j), frc_margin_mean]
  have h := (frc_normal_margin j).integral_comp
    (frc_g_continuous.pow 2).measurable.aestronglyMeasurable
  change (∫ e, (frc_g (correlatedNormals e j))^2 ∂frc_gaussian 5) = _ at h
  simp only [Pi.pow_apply] at h ⊢
  rw [h, frc_g_second]
  norm_num

lemma frc_norm_linear {n : ℕ} (a b : Fin n → ℝ) (u v : ℝ) :
    (∑ j, (u*a j + v*b j)^2) =
      u^2 * (∑ j, (a j)^2) + 2*u*v*(∑ j, a j*b j) + v^2*(∑ j, (b j)^2) := by
  calc
    _ = ∑ j, (u^2*(a j)^2 + 2*u*v*(a j*b j) + v^2*(b j)^2) := by
      apply Finset.sum_congr rfl; intro j _; ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

lemma frc_pair_measurable {n : ℕ} (a b : Fin n → ℝ) :
    Measurable (fun e : Fin n → ℝ => (∑ j, a j*e j, ∑ j, b j*e j)) := by
  apply Measurable.prodMk
  · apply Finset.measurable_sum
    intro j _
    exact measurable_const.mul (measurable_pi_apply j)
  · apply Finset.measurable_sum
    intro j _
    exact measurable_const.mul (measurable_pi_apply j)

/-- A Gaussian pair is determined by its Gram matrix. -/
lemma frc_pair_eq {m n : ℕ} (a b : Fin m → ℝ) (c d : Fin n → ℝ)
    (ha : (∑ j, (a j)^2) = ∑ j, (c j)^2)
    (hb : (∑ j, (b j)^2) = ∑ j, (d j)^2)
    (hab : (∑ j, a j*b j) = ∑ j, c j*d j) :
    (frc_gaussian m).map (fun e => (∑ j, a j*e j, ∑ j, b j*e j)) =
      (frc_gaussian n).map (fun e => (∑ j, c j*e j, ∑ j, d j*e j)) := by
  apply Measure.ext_of_charFunDual
  funext L
  have hL (x y : ℝ) : L (x,y) = L (1,0)*x + L (0,1)*y := by
    have he : (x,y) = x • ((1 : ℝ),0) + y • (0,(1 : ℝ)) := by ext <;> simp
    rw [he, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  have he {r : ℕ} (f g : Fin r → ℝ) :
      L ∘ (fun e : Fin r → ℝ => (∑ j, f j*e j, ∑ j, g j*e j)) =
        (fun e => ∑ j, (L (1,0)*f j + L (0,1)*g j)*e j) := by
    funext e
    rw [Function.comp_apply, hL, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map L.measurable (frc_pair_measurable a b),
    Measure.map_map L.measurable (frc_pair_measurable c d), he a b, he c d,
    (frc_gaussian_linear _).map_eq, (frc_gaussian_linear _).map_eq,
    frc_norm_linear, frc_norm_linear, ha, hb, hab]

abbrev frc_normal := gaussianReal 0 1

lemma frc_product_linear (c d : ℝ) (hn : c^2+d^2=1) :
    HasLaw (fun p : ℝ × ℝ => c*p.1+d*p.2) frc_normal (frc_normal.prod frc_normal) := by
  have hp := (measurePreserving_piFinTwo (fun _ : Fin 2 => frc_normal)).symm.hasLaw
  have hl := frc_gaussian_linear (![c,d] : Fin 2 → ℝ)
  norm_num [Fin.sum_univ_succ, hn] at hl
  convert hl.comp hp using 1
  funext p
  rfl

def frc_h (c d t : ℝ) : ℝ := ∫ a, frc_g (c*t+d*a) ∂frc_normal

lemma frc_h_memLp (c d : ℝ) (hn : c^2+d^2=1) : MemLp (frc_h c d) 2 frc_normal := by
  have hf : MemLp (fun p : ℝ × ℝ => frc_g (c*p.1+d*p.2)) 2
      (frc_normal.prod frc_normal) := (frc_product_linear c d hn).memLp_comp frc_g_memLp
  have hi : Integrable (frc_h c d) frc_normal := (hf.integrable (by norm_num)).integral_prod_left
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr
  apply hf.integrable_sq.integral_prod_left.mono'
    (hi.aestronglyMeasurable.pow 2)
  filter_upwards [hf.integrable_sq.prod_right_ae, (hf.integrable (by norm_num)).prod_right_ae]
    with t ht2 ht1
  have hsec : MemLp (fun a => frc_g (c*t+d*a)) 2 frc_normal :=
    (memLp_two_iff_integrable_sq ht1.aestronglyMeasurable).mpr ht2
  have hv := variance_nonneg (fun a => frc_g (c*t+d*a)) frc_normal
  rw [variance_eq_sub hsec] at hv
  change |(∫ a, frc_g (c*t+d*a) ∂frc_normal)^2| ≤
    ∫ a, (frc_g (c*t+d*a))^2 ∂frc_normal
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [Pi.pow_apply] using (sub_nonneg.mp hv)

lemma frc_h_mean (c d : ℝ) (hn : c^2+d^2=1) :
    (∫ t, frc_h c d t ∂frc_normal) = 2 := by
  have hl := (frc_product_linear c d hn).memLp_comp frc_g_memLp
  have hi : Integrable (fun p : ℝ × ℝ => frc_g (c*p.1+d*p.2))
      (frc_normal.prod frc_normal) := hl.integrable (by norm_num)
  unfold frc_h
  calc
    _ = ∫ p : ℝ × ℝ, frc_g (c*p.1+d*p.2) ∂frc_normal.prod frc_normal :=
      (integral_prod _ hi).symm
    _ = 2 := ((frc_product_linear c d hn).integral_comp
      frc_g_continuous.measurable.aestronglyMeasurable).trans frc_g_mean

def frc_common (c d : ℝ) (e : Fin 3 → ℝ) : ℝ × ℝ :=
  (c*e 0+d*e 1, c*e 0+d*e 2)

lemma frc_common_margin (c d : ℝ) (hn : c^2+d^2=1) (b : Bool) :
    HasLaw (fun e : Fin 3 → ℝ => if b then (frc_common c d e).1 else (frc_common c d e).2)
      frc_normal (frc_gaussian 3) := by
  cases b
  · convert frc_gaussian_linear (![c,0,d] : Fin 3 → ℝ) using 1 <;>
      norm_num [Fin.sum_univ_succ, frc_common, hn]
  · convert frc_gaussian_linear (![c,d,0] : Fin 3 → ℝ) using 1 <;>
      norm_num [Fin.sum_univ_succ, frc_common, hn]

lemma frc_common_cross (c d : ℝ) (hn : c^2+d^2=1) :
    (∫ e, frc_g (frc_common c d e).1 * frc_g (frc_common c d e).2 ∂frc_gaussian 3) =
      ∫ t, (frc_h c d t)^2 ∂frc_normal := by
  have h1 := (frc_common_margin c d hn true).memLp_comp frc_g_memLp
  have h2 := (frc_common_margin c d hn false).memLp_comp frc_g_memLp
  simp [Function.comp_def] at h1 h2
  have hi : Integrable (fun e : Fin 3 → ℝ =>
      frc_g (frc_common c d e).1 * frc_g (frc_common c d e).2) (frc_gaussian 3) :=
    h1.integrable_mul h2
  let mp := (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => frc_normal) 0).symm
  rw [← mp.integral_comp']
  change (∫ p : ℝ × (Fin 2 → ℝ), frc_g (c*p.1+d*p.2 0) * frc_g (c*p.1+d*p.2 1)
    ∂frc_normal.prod (frc_gaussian 2)) = _
  have hip : Integrable (fun p : ℝ × (Fin 2 → ℝ) =>
      frc_g (c*p.1+d*p.2 0) * frc_g (c*p.1+d*p.2 1))
      (frc_normal.prod (frc_gaussian 2)) := mp.integrable_comp_of_integrable hi
  rw [integral_prod _ hip]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  change (∫ e : Fin 2 → ℝ, frc_g (c*t+d*e 0) * frc_g (c*t+d*e 1) ∂frc_gaussian 2) = _
  simpa only [Fin.prod_univ_two, Fintype.card_fin, frc_h] using
    (integral_fintype_prod_eq_pow (ι := Fin 2) (μ := frc_normal) (fun a => frc_g (c*t+d*a)))

lemma frc_common_covariance (c d : ℝ) (hn : c^2+d^2=1) :
    cov[fun e => frc_g (frc_common c d e).1, fun e => frc_g (frc_common c d e).2;
      frc_gaussian 3] = Var[frc_h c d; frc_normal] := by
  have h1 := (frc_common_margin c d hn true).memLp_comp frc_g_memLp
  have h2 := (frc_common_margin c d hn false).memLp_comp frc_g_memLp
  have hm1 := (frc_common_margin c d hn true).integral_comp
    frc_g_continuous.measurable.aestronglyMeasurable
  have hm2 := (frc_common_margin c d hn false).integral_comp
    frc_g_continuous.measurable.aestronglyMeasurable
  simp [Function.comp_def, frc_g_mean] at h1 h2 hm1 hm2
  rw [covariance_eq_sub h1 h2, variance_eq_sub (frc_h_memLp c d hn)]
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [frc_common_cross c d hn, hm1, hm2, frc_h_mean c d hn]
  norm_num


lemma frc_h_strict (c d : ℝ) (hn : c^2+d^2=1) (hc : 0 < c) (hd : 0 ≤ d) :
    0 < Var[frc_h c d; frc_normal] := by
  have hf := (frc_product_linear c d hn).memLp_comp frc_g_memLp
  have hhalf : frc_normal.real (Set.Ici (0 : ℝ)) = 1/2 := by
    change ((gaussianReal 0 1) (Set.Ici 0)).toReal = 1/2
    rw [npu_mass_Ici, npu_cdf_eq, AronowAudit.P053.NormalCompletion.normal_cdf_zero]
    norm_num
  have hbound : ∀ᵐ t ∂frc_normal, 0 ≤ t → frc_g (c*t)/2 ≤ frc_h c d t := by
    filter_upwards [(hf.integrable (by norm_num)).prod_right_ae] with t ht ht0
    calc
      _ = ∫ _a in Set.Ici (0 : ℝ), frc_g (c*t) ∂frc_normal := by
        rw [setIntegral_const]
        change _ = frc_normal.real (Set.Ici (0 : ℝ)) • frc_g (c*t)
        rw [hhalf, smul_eq_mul]; ring
      _ ≤ ∫ a in Set.Ici (0 : ℝ), frc_g (c*t+d*a) ∂frc_normal := by
        apply integral_mono_ae (integrable_const _) ht.restrict
        filter_upwards [ae_restrict_mem measurableSet_Ici] with a ha
        apply frc_g_mono (mul_nonneg hc.le ht0)
        exact le_add_of_nonneg_right (mul_nonneg hd ha)
      _ ≤ _ := setIntegral_le_integral ht (ae_of_all _ fun a => frc_g_nonneg _)
  by_contra hnot
  have hz : Var[frc_h c d; frc_normal] = 0 :=
    le_antisymm (le_of_not_gt hnot) (variance_nonneg _ _)
  have hconst := ae_eq_integral_of_variance_eq_zero (frc_h_memLp c d hn) hz
  rw [frc_h_mean c d hn] at hconst
  obtain ⟨b, hb0, hb⟩ := frc_g_large
  let t0 : ℝ := b/c
  have ht0 : 0 < t0 := div_pos hb0 hc
  have hp : frc_normal (Set.Icc t0 (t0+1)) ≠ 0 := by
    intro hzero
    have hvol := (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)) hzero
    rw [Real.volume_Icc] at hvol
    norm_num at hvol
  obtain ⟨t, ht, hbt, hct⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp
    (ae_restrict_of_ae (hbound.and hconst))
  have hbt' := hbt (ht0.le.trans ht.1)
  have hmul : b ≤ c*t := by
    have h := (div_le_iff₀ hc).mp ht.1
    simpa only [mul_comm] using h
  have hmono := frc_g_mono hb0.le hmul
  linarith

lemma frc_covariance_common (j k : Fin 5) (c d : ℝ)
    (hn : c^2+d^2=1) (hdot : (∑ l, frc_row j l * frc_row k l) = c^2) :
    cov[fun e => frc_g (correlatedNormals e j), fun e => frc_g (correlatedNormals e k);
      frc_gaussian 5] = Var[frc_h c d; frc_normal] := by
  have ha : (∑ l, (frc_row j l)^2) = ∑ l, (![c,d,0] : Fin 3 → ℝ) l ^ 2 := by
    rw [frc_row_norm]
    norm_num [Fin.sum_univ_succ]
    exact hn.symm
  have hb : (∑ l, (frc_row k l)^2) = ∑ l, (![c,0,d] : Fin 3 → ℝ) l ^ 2 := by
    rw [frc_row_norm]
    norm_num [Fin.sum_univ_succ]
    exact hn.symm
  have hab : (∑ l, frc_row j l*frc_row k l) =
      ∑ l, (![c,d,0] : Fin 3 → ℝ) l * (![c,0,d] : Fin 3 → ℝ) l := by
    rw [hdot]
    norm_num [Fin.sum_univ_succ, pow_two]
  have hpair : (frc_gaussian 5).map (fun e => (correlatedNormals e j, correlatedNormals e k)) =
      (frc_gaussian 3).map (frc_common c d) := by
    have h := frc_pair_eq (frc_row j) (frc_row k) (![c,d,0]) (![c,0,d]) ha hb hab
    convert h using 1
    · congr 1; funext e; rw [frc_row_eval, frc_row_eval]
    · congr 1; funext e; norm_num [Fin.sum_univ_succ, frc_common]
  calc
    _ = cov[fun p : ℝ × ℝ => frc_g p.1, fun p => frc_g p.2;
        (frc_gaussian 5).map (fun e => (correlatedNormals e j, correlatedNormals e k))] :=
      (covariance_map_fun (by fun_prop) (by fun_prop) (by
        exact (((measurable_pi_apply j).comp frc_correlated_continuous.measurable).prodMk
          ((measurable_pi_apply k).comp frc_correlated_continuous.measurable)).aemeasurable)).symm
    _ = cov[fun p : ℝ × ℝ => frc_g p.1, fun p => frc_g p.2;
        (frc_gaussian 3).map (frc_common c d)] := by rw [hpair]
    _ = cov[fun e => frc_g (frc_common c d e).1, fun e => frc_g (frc_common c d e).2;
        frc_gaussian 3] := covariance_map_fun (by fun_prop) (by fun_prop)
          (by unfold frc_common; fun_prop)
    _ = _ := frc_common_covariance c d hn

lemma frc_rho_bounds (j k : Fin 5) : 0 < frc_rho j k ∧ frc_rho j k ≤ 1 := by
  unfold frc_rho
  split_ifs
  · norm_num
  · have hs0 : 0 < Real.sqrt 2 := by positivity
    have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have hs1 : 1 ≤ Real.sqrt 2 := by nlinarith
    exact ⟨inv_pos.mpr hs0, (inv_le_one₀ hs0).mpr hs1⟩

lemma frc_pair_nonneg (j k : Fin 5) (hjk : j ≠ k) :
    0 ≤ cov[fun e => frc_g (correlatedNormals e j), fun e => frc_g (correlatedNormals e k);
      frc_gaussian 5] := by
  have hr := frc_rho_bounds j k
  have hn : (Real.sqrt (frc_rho j k))^2 + (Real.sqrt (1-frc_rho j k))^2 = 1 := by
    rw [Real.sq_sqrt hr.1.le, Real.sq_sqrt (sub_nonneg.mpr hr.2)]
    ring
  have hd : (∑ l, frc_row j l*frc_row k l) = (Real.sqrt (frc_rho j k))^2 := by
    rw [frc_row_dot, if_neg hjk, Real.sq_sqrt hr.1.le]
  rw [frc_covariance_common j k _ _ hn hd]
  exact variance_nonneg _ _

lemma frc_pair_strict :
    0 < cov[fun e => frc_g (correlatedNormals e 0), fun e => frc_g (correlatedNormals e 1);
      frc_gaussian 5] := by
  have hn : (Real.sqrt (1/2 : ℝ))^2 + (Real.sqrt (1/2 : ℝ))^2 = 1 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/2)]
    norm_num
  have hd : (∑ l, frc_row 0 l*frc_row 1 l) = (Real.sqrt (1/2 : ℝ))^2 := by
    rw [frc_row_dot]
    norm_num [frc_rho, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [frc_covariance_common 0 1 _ _ hn hd]
  exact frc_h_strict _ _ hn (by positivity) (Real.sqrt_nonneg _)

def frc_T (e : Fin 5 → ℝ) : ℝ := ∑ j, frc_g (correlatedNormals e j)

@[fun_prop] lemma frc_T_continuous : Continuous frc_T := by
  apply continuous_finset_sum
  intro j _
  exact frc_g_continuous.comp ((continuous_apply j).comp frc_correlated_continuous)

lemma frc_T_memLp : MemLp frc_T 2 (frc_gaussian 5) :=
  memLp_finsetSum _ (fun j _ => frc_margin_memLp j)

lemma frc_T_law : HasLaw frc_T sequentialFisherLimit (frc_gaussian 5) := by
  refine ⟨frc_T_continuous.measurable.aemeasurable, ?_⟩
  unfold sequentialFisherLimit
  congr 1
  funext e
  exact (frc_fisher_transform (correlatedNormals e)).symm

lemma frc_limit_memLp : MemLp id 2 sequentialFisherLimit := by
  rw [← frc_T_law.map_eq]
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    frc_T_continuous.measurable.aemeasurable).mpr frc_T_memLp

lemma frc_continuousVariance {Q : Measure ℝ} [IsProbabilityMeasure Q] (h : MemLp id 2 Q) :
    continuousVariance Q = Var[id; Q] := by
  simpa only [continuousVariance, id_eq, Pi.pow_apply] using (variance_eq_sub h).symm

lemma frc_limit_variance : 20 < continuousVariance sequentialFisherLimit := by
  let C : Fin 5 → Fin 5 → ℝ := fun j k =>
    cov[fun e => frc_g (correlatedNormals e j), fun e => frc_g (correlatedNormals e k); frc_gaussian 5]
  have hdiag (j : Fin 5) : C j j = 4 := by
    dsimp only [C]
    rw [covariance_self (frc_margin_memLp j).aemeasurable, frc_margin_variance]
  have hle (j k : Fin 5) : (if j=k then (4 : ℝ) else 0) ≤ C j k := by
    by_cases hjk : j=k
    · subst k; simp [hdiag]
    · simpa only [if_neg hjk] using frc_pair_nonneg j k hjk
  have hs : (∑ j : Fin 5, ∑ k : Fin 5, if j=k then (4 : ℝ) else 0) < ∑ j, ∑ k, C j k := by
    apply Finset.sum_lt_sum (fun j _ => Finset.sum_le_sum (fun k _ => hle j k))
    refine ⟨0, Finset.mem_univ _, ?_⟩
    apply Finset.sum_lt_sum (fun k _ => hle 0 k)
    exact ⟨1, Finset.mem_univ _, by simpa only [Fin.zero_ne_one, if_false] using frc_pair_strict⟩
  have htwenty : (∑ j : Fin 5, ∑ k : Fin 5, if j=k then (4 : ℝ) else 0) = 20 := by
    norm_num [Fin.sum_univ_succ]
  rw [htwenty] at hs
  have hv : Var[frc_T; frc_gaussian 5] = ∑ j, ∑ k, C j k :=
    variance_fun_sum frc_margin_memLp
  haveI : IsProbabilityMeasure sequentialFisherLimit :=
    frc_T_law.isProbabilityMeasure_iff.mp inferInstance
  rw [frc_continuousVariance frc_limit_memLp, ← frc_T_law.map_eq,
    variance_map aemeasurable_id frc_T_law.aemeasurable]
  change 20 < Var[frc_T; frc_gaussian 5]
  rwa [hv]

lemma frc_chi_eq : chiSquareTen = StatLean.MultipleTesting.chiSquared 10 := by
  exact StatLean.MultipleTesting.map_sum_sq_eq_chiSquared
    (n := 10) (by norm_num) (frc_gaussian 10)
    (fun j (e : Fin 10 → ℝ) => e j)
    (fun j => measurable_pi_apply j)
    (fun j => (frc_gaussian_eval j).map_eq)
    (by simpa only [id_eq] using (iIndepFun_pi
      (μ := fun _ : Fin 10 => frc_normal) (X := fun _ => (id : ℝ → ℝ))
      (fun _ => measurable_id.aemeasurable)))

lemma frc_chi_memLp : MemLp id 2 chiSquareTen := by
  have h4 (j : Fin 10) : MemLp (fun e : Fin 10 → ℝ => e j) 4 (frc_gaussian 10) :=
    (frc_gaussian_eval j).memLp (memLp_id_gaussianReal 4)
  have h2 (j : Fin 10) : MemLp (fun e : Fin 10 → ℝ => (e j)^2) 2 (frc_gaussian 10) := by
    simpa only [pow_two] using (h4 j).fun_mul (h4 j)
  have hsum : MemLp (fun e : Fin 10 → ℝ => ∑ j, (e j)^2) 2 (frc_gaussian 10) :=
    memLp_finsetSum _ (fun j _ => h2 j)
  unfold chiSquareTen
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    (Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).pow_const 2)).aemeasurable).mpr
      hsum

lemma frc_chi_variance : continuousVariance chiSquareTen = 20 := by
  have hm := StatLean.MultipleTesting.integral_id_chiSquared (k := 10) (by norm_num)
  have hc := StatLean.MultipleTesting.variance_chiSquared (k := 10) (by norm_num)
  rw [← frc_chi_eq] at hm hc
  haveI : IsProbabilityMeasure chiSquareTen := by unfold chiSquareTen; infer_instance
  rw [frc_continuousVariance frc_chi_memLp, variance_eq_integral aemeasurable_id]
  change (∫ x : ℝ, (x - ∫ y : ℝ, y ∂chiSquareTen)^2 ∂chiSquareTen) = 20
  rw [hm]
  convert hc using 1 <;> norm_num

/-- The ordered 128-atom model satisfies every per-list assumption, but
its actual Fisher limit has variance strictly greater than the reference. -/
theorem fisher_reference_counterexample_proof :
    (∀ j : Fin 5, (sequentialStudy j).standing ∧ (sequentialStudy j).beta = 1) ∧
    WeakLimit (uniformFin 128 (by norm_num))
      (fun _ s j => ((sequentialStudy j).betaHat s 0 0-1) /
        Real.sqrt ((sequentialStudy j).betaVarianceHat s 0))
      ((Measure.pi (fun _ : Fin 5 => gaussianReal 0 1)).map correlatedNormals) ∧
    WeakLimit (uniformFin 128 (by norm_num)) (fun _ s => fisherStatistic
      (fun j => normalPValue ((sequentialStudy j).betaHat s 0 0) 1
        ((sequentialStudy j).betaVarianceHat s 0))) sequentialFisherLimit ∧
    Integrable (fun x : ℝ => x) sequentialFisherLimit ∧
    Integrable (fun x : ℝ => x^2) sequentialFisherLimit ∧
    20 < continuousVariance sequentialFisherLimit ∧ sequentialFisherLimit ≠ chiSquareTen := by
  haveI : IsProbabilityMeasure sequentialFisherLimit :=
    frc_T_law.isProbabilityMeasure_iff.mp inferInstance
  refine ⟨fisher_sequential_finite_proof.1, frc_vector_weakLimit, frc_fisher_weakLimit,
    frc_limit_memLp.integrable (by norm_num), frc_limit_memLp.integrable_sq, frc_limit_variance, ?_⟩
  intro heq
  have h := frc_limit_variance
  rw [heq, frc_chi_variance] at h
  exact (lt_irrefl _ h)

end
end AronowAudit.P019.Wave1
