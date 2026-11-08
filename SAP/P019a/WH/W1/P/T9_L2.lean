import SAP.P019a.WH.W1.Leaves
import AronowAudit.P019.Wave1.Gap.GLP019B4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1.P.T9_L2

open SAP.P019a SAP.P019a.Bridge SAP.P019a.WH.W1
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
open AronowAudit.P019.Wave1
noncomputable section
open Classical

local instance whole_gaussian_five_probability : IsProbabilityMeasure wholeGaussianFive := by
  unfold wholeGaussianFive
  infer_instance

local instance uniform_probability : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

lemma margin_hasLaw (j : Fin 5) :
    HasLaw (fun e : Fin 5 → ℝ => correlatedNormals e j) (gaussianReal 0 1) wholeGaussianFive := by
  simpa only [SAP.P019a.Bridge.correlatedNormals_eq, wholeGaussianFive, frc_gaussian] using
    (frc_normal_margin j)

lemma margin_memLp (j : Fin 5) :
    MemLp (fun e : Fin 5 → ℝ => correlatedNormals e j) 2 wholeGaussianFive :=
  (margin_hasLaw j).memLp (memLp_id_gaussianReal 2)

lemma margin_mean (j : Fin 5) :
    (∫ e, correlatedNormals e j ∂wholeGaussianFive) = 0 := by
  have h := (margin_hasLaw j).integral_comp
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x) (gaussianReal 0 1))
  change (∫ e, correlatedNormals e j ∂wholeGaussianFive) =
    ∫ x, x ∂gaussianReal 0 1 at h
  rw [integral_id_gaussianReal] at h
  exact h

lemma margin_second (j : Fin 5) :
    (∫ e, (correlatedNormals e j)^2 ∂wholeGaussianFive) = 1 := by
  have h := (margin_hasLaw j).integral_comp
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2) (gaussianReal 0 1))
  change (∫ e, (correlatedNormals e j)^2 ∂wholeGaussianFive) =
    ∫ x, x^2 ∂gaussianReal 0 1 at h
  have hv : Var[id; gaussianReal 0 1] = 1 := by
    simpa using (variance_id_gaussianReal (μ := 0) (v := 1))
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at hv
  simp only [id_eq] at hv
  rw [integral_id_gaussianReal] at hv
  norm_num at hv
  exact h.trans hv

lemma coordinate_memLp (i : Fin 5) :
    MemLp (fun e : Fin 5 → ℝ => e i) 2 wholeGaussianFive := by
  simpa [wholeGaussianFive, frc_gaussian] using
    (frc_gaussian_eval i).memLp (memLp_id_gaussianReal 2)

lemma coordinate_mean (i : Fin 5) :
    (∫ e : Fin 5 → ℝ, e i ∂wholeGaussianFive) = 0 := by
  have h := (frc_gaussian_eval i).integral_comp
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x) (gaussianReal 0 1))
  change (∫ e : Fin 5 → ℝ, e i ∂wholeGaussianFive) =
    ∫ x, x ∂gaussianReal 0 1 at h
  rw [integral_id_gaussianReal] at h
  exact h

lemma coordinate_second (i : Fin 5) :
    (∫ e : Fin 5 → ℝ, (e i)^2 ∂wholeGaussianFive) = 1 := by
  have h := (frc_gaussian_eval i).integral_comp
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2) (gaussianReal 0 1))
  change (∫ e : Fin 5 → ℝ, (e i)^2 ∂wholeGaussianFive) =
    ∫ x, x^2 ∂gaussianReal 0 1 at h
  have hv : Var[id; gaussianReal 0 1] = 1 := by
    simpa using (variance_id_gaussianReal (μ := 0) (v := 1))
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at hv
  simp only [id_eq] at hv
  rw [integral_id_gaussianReal] at hv
  norm_num at hv
  exact h.trans hv

lemma coordinate_covariance (i k : Fin 5) :
    cov[fun e : Fin 5 → ℝ => e i, fun e => e k; wholeGaussianFive] =
      if i = k then 1 else 0 := by
  by_cases hik : i = k
  · subst k
    rw [if_pos rfl, covariance_eq_sub (coordinate_memLp i) (coordinate_memLp i)]
    simp only [Pi.mul_apply, ← pow_two, coordinate_second, coordinate_mean]
    norm_num
  · rw [if_neg hik]
    have hI : iIndepFun (fun i : Fin 5 => fun e : Fin 5 → ℝ => e i) wholeGaussianFive := by
      simpa only [wholeGaussianFive, frc_gaussian, id_eq] using
        (iIndepFun_pi (μ := fun _ : Fin 5 => gaussianReal 0 1)
          (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable))
    exact (hI.indepFun hik).covariance_eq_zero (coordinate_memLp i) (coordinate_memLp k)

lemma whole_covariance_eq_covariance (j k : Fin 5) :
    wholeCovariance wholeGaussianFive (fun e => correlatedNormals e j)
      (fun e => correlatedNormals e k) =
        cov[fun e => correlatedNormals e j, fun e => correlatedNormals e k; wholeGaussianFive] := by
  unfold wholeCovariance
  symm
  exact covariance_eq_sub (margin_memLp j) (margin_memLp k)

lemma covariance_first_four (j k : Fin 5) (hj : j.val < 4) (hk : k.val < 4)
    (hjk : j ≠ k) :
    cov[fun e : Fin 5 → ℝ => correlatedNormals e j,
      fun e => correlatedNormals e k; wholeGaussianFive] = 1/2 := by
  have hjf : (fun e : Fin 5 → ℝ => correlatedNormals e j) = fun e => (Real.sqrt 2)⁻¹ * (e j + e 4) := by
    funext e
    simp [correlatedNormals, hj, div_eq_mul_inv]
    ring
  have hkf : (fun e : Fin 5 → ℝ => correlatedNormals e k) = fun e => (Real.sqrt 2)⁻¹ * (e k + e 4) := by
    funext e
    simp [correlatedNormals, hk, div_eq_mul_inv]
    ring
  have hi : j ≠ 4 := by omega
  have hk4 : k ≠ 4 := by omega
  rw [hjf, hkf, covariance_const_mul_left, covariance_const_mul_right]
  rw [show (fun e : Fin 5 → ℝ => e j + e 4) =
    (fun e => e j) + (fun e => e 4) by rfl]
  rw [show (fun e : Fin 5 → ℝ => e k + e 4) =
    (fun e => e k) + (fun e => e 4) by rfl]
  rw [covariance_add_left (coordinate_memLp j) (coordinate_memLp 4)
    ((coordinate_memLp k).add (coordinate_memLp 4))]
  rw [covariance_add_right (coordinate_memLp j) (coordinate_memLp k) (coordinate_memLp 4)]
  rw [covariance_add_right (coordinate_memLp 4) (coordinate_memLp k) (coordinate_memLp 4)]
  rw [coordinate_covariance j k, coordinate_covariance j 4,
    coordinate_covariance 4 k, coordinate_covariance 4 4]
  simp only [if_neg hjk, if_neg hi, if_neg (Ne.symm hk4), if_pos rfl]
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [hs]
  norm_num

lemma covariance_with_fifth (j : Fin 5) (hj : j.val < 4) :
    cov[fun e : Fin 5 → ℝ => correlatedNormals e j,
      fun e => correlatedNormals e 4; wholeGaussianFive] = 1/Real.sqrt 2 := by
  have hjf : (fun e : Fin 5 → ℝ => correlatedNormals e j) = fun e => (Real.sqrt 2)⁻¹ * (e j + e 4) := by
    funext e
    simp [correlatedNormals, hj, div_eq_mul_inv]
    ring
  have h4f : (fun e : Fin 5 → ℝ => correlatedNormals e 4) = fun e => e 4 := by
    funext e
    simp [correlatedNormals]
  rw [hjf, h4f, covariance_const_mul_left]
  rw [show (fun e : Fin 5 → ℝ => e j + e 4) =
    (fun e => e j) + (fun e => e 4) by rfl]
  rw [covariance_add_left (coordinate_memLp j) (coordinate_memLp 4) (coordinate_memLp 4)]
  rw [coordinate_covariance j 4, coordinate_covariance 4 4]
  have hj4 : j ≠ (4 : Fin 5) := by omega
  simp [hj4]

end
end SAP.P019a.WH.W1.P.T9_L2

open SAP.P019a.WH.W1.P.T9_L2
open SAP.P019a SAP.P019a.Bridge SAP.P019a.WH.W1
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
open AronowAudit.P019.Wave1

local instance whole_gaussian_five_probability : IsProbabilityMeasure wholeGaussianFive := by
  unfold wholeGaussianFive
  infer_instance

local instance uniform_probability : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

theorem SAP.P019a.WH.W1.T9_L2_proof : SAP.P019a.WH.W1.T9_L2 := by
  classical
  constructor
  · intro j
    refine ⟨margin_hasLaw j, ?_, ?_, margin_mean j, ?_, ?_⟩
    · exact (margin_memLp j).integrable (by norm_num)
    · exact (margin_memLp j).integrable_sq
    · change (∫ e, (correlatedNormals e j)^2 ∂wholeGaussianFive) -
        (∫ e, correlatedNormals e j ∂wholeGaussianFive)^2 = 1
      rw [margin_second j, margin_mean j]
      norm_num
    · let T : (n : ℕ) → (Fin n → Fin 128) → ℝ := fun n s =>
        frc_p (((sequentialStudy j).betaHat s 0 0 - 1) /
          Real.sqrt ((sequentialStudy j).betaVarianceHat s 0))
      have hlim : TendstoInDistribution (fun n ω => T n (t19_sample n ω)) atTop id
          (fun _ => t19_product frc_law) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        have hcomp := frc_joint_limit.continuous_comp
          (frc_p_continuous.comp (continuous_apply j))
        have hp : HasLaw frc_p (volume.restrict (Set.Icc (0 : ℝ) 1)) (gaussianReal 0 1) :=
          ⟨frc_p_continuous.measurable.aemeasurable, frc_p_law⟩
        have hm : HasLaw (fun e : Fin 5 → ℝ => frc_p (correlatedNormals e j))
            (volume.restrict (Set.Icc (0 : ℝ) 1)) (frc_gaussian 5) := hp.comp (frc_normal_margin j)
        have hdist := t19_distribution_hasLaw hcomp hm
        convert hdist using 1
        funext n ω
        simp [T, frc_z, sequential_betaHat_eq, sequential_betaVarianceHat_eq]
      have hweak := frc_weakLimit T (volume.restrict (Set.Icc (0 : ℝ) 1)) hlim
      have hweakSAP : WeakLimit (uniformFin 128 (by norm_num)) T
          (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        rw [weakLimit_eq]
        simpa only [uniformFin_eq, frc_law] using hweak
      change WeakLimit (uniformFin 128 (by norm_num))
        (fun n s => normalPValue ((sequentialStudy j).betaHat s 0 0) 1
          ((sequentialStudy j).betaVarianceHat s 0)) (volume.restrict (Set.Icc (0 : ℝ) 1))
      convert hweakSAP using 1
      funext n s
      simp only [T, normalPValue_eq, AronowAudit.P019.normalPValue, frc_p]
      congr 1
      rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [neg_div]
  · intro j k hjk
    by_cases hj : j.val < 4
    · by_cases hk : k.val < 4
      · rw [whole_covariance_eq_covariance, covariance_first_four j k hj hk hjk]
        simp [hj, hk]
      · have hk4 : k = 4 := by
          apply Fin.ext
          omega
        rw [hk4, whole_covariance_eq_covariance, covariance_with_fifth j hj]
        simp [hj, hk4]
    · have hj4 : j = 4 := by
        apply Fin.ext
        omega
      have hk : k.val < 4 := by
        have hk4 : k ≠ (4 : Fin 5) := by
          intro heq
          exact hjk (hj4.trans heq.symm)
        omega
      rw [hj4, SAP.P019a.WH.W1.wholeCovariance_comm, whole_covariance_eq_covariance,
        covariance_with_fifth k hk]
      simp [hj, hk, hj4]

