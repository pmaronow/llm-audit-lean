import AronowAudit.P019.Wave1.Gap.GP019B3b
import Mathlib.Probability.CramerWold
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
The corrected Fisher theorem under the full joint assignment premise. Finite
assignment factorization proves orthogonality, including on each latent fibre.
The joint limit is obtained by Cramér–Wold on the common IID product space.
-/
namespace AronowAudit.P019.Wave1

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped BigOperators Topology RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

variable {Ω : Type*} [Fintype Ω]

/-- The assignment premise extends from pattern indicators to products of
arbitrary functions of the five Boolean assignments. -/
lemma fc_assignment_factor (P : FiniteLaw Ω) (S : Fin 5 → Study Ω)
    (hj : jointAssignmentStable P S)
    (f : (Fin 5 → ℕ) → (Fin 5 → Bool) → (Fin 5 → Bool) → ℝ)
    (r : Fin 5 → Bool → ℝ) :
    P.mean (fun ω => f (fun j => (S j).W ω) (fun j => (S j).X ω)
      (fun j => (S j).Y ω) * ∏ j, r j ((S j).Z ω)) =
    P.mean (fun ω => f (fun j => (S j).W ω) (fun j => (S j).X ω)
      (fun j => (S j).Y ω)) *
      ∏ j, ∑ b : Bool, P.prob (fun ω => (S j).Z ω = b) * r j b := by
  have he (ω : Ω) : f (fun j => (S j).W ω) (fun j => (S j).X ω)
      (fun j => (S j).Y ω) * ∏ j, r j ((S j).Z ω) =
      ∑ a : Fin 5 → Bool, (if ∀ j, (S j).Z ω = a j then
        f (fun j => (S j).W ω) (fun j => (S j).X ω) (fun j => (S j).Y ω)
        else 0) * ∏ j, r j (a j) := by
    have heq (a : Fin 5 → Bool) : (∀ j, (S j).Z ω = a j) ↔
        (fun j => (S j).Z ω) = a := funext_iff.symm
    simp_rw [heq, ite_mul, zero_mul]
    simp
  simp_rw [he]
  rw [mean_sum]
  simp_rw [mean_mul_const, hj f]
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_mul_distrib]
  ring

lemma fc_two_assignment_factors (j k : Fin 5) (hjk : j ≠ k)
    (r t : Bool → ℝ) (a : Fin 5 → Bool) :
    (∏ i, if i = j then r (a i) else if i = k then t (a i) else 1) =
      r (a j) * t (a k) := by
  have he (i : Fin 5) :
      (if i = j then r (a i) else if i = k then t (a i) else 1) =
      (if i = j then r (a i) else 1) * (if i = k then t (a i) else 1) := by
    by_cases h1 : i = j <;> by_cases h2 : i = k <;> simp_all
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

/-- A latent multiplier times two distinct centered assignments has mean zero.
This also applies to a multiplier restricted to one exact latent fibre. -/
lemma fc_centered_assignment (P : FiniteLaw Ω) (S : Fin 5 → Study Ω)
    (hsame : ∀ j, (S j).law = P) (hj : jointAssignmentStable P S)
    (j k : Fin 5) (hjk : j ≠ k)
    (f : (Fin 5 → ℕ) → (Fin 5 → Bool) → (Fin 5 → Bool) → ℝ) :
    P.mean (fun ω => f (fun i => (S i).W ω) (fun i => (S i).X ω)
      (fun i => (S i).Y ω) *
      (bitVal ((S j).Z ω) - (S j).gamma) *
      (bitVal ((S k).Z ω) - (S k).gamma)) = 0 := by
  let r : Fin 5 → Bool → ℝ := fun i b =>
    if i = j then bitVal b - (S j).gamma else
      if i = k then bitVal b - (S k).gamma else 1
  have h := fc_assignment_factor P S hj f r
  have hprod (a : Fin 5 → Bool) : (∏ i, r i (a i)) =
      (bitVal (a j) - (S j).gamma) * (bitVal (a k) - (S k).gamma) :=
    fc_two_assignment_factors j k hjk (fun b => bitVal b - (S j).gamma)
      (fun b => bitVal b - (S k).gamma) a
  simp_rw [hprod] at h
  have hz : (∑ b : Bool, P.prob (fun ω => (S j).Z ω = b) * r j b) = 0 := by
    simp [r, bitVal]
    rw [prob_false]
    have hg : P.prob (fun ω => (S j).Z ω = true) = (S j).gamma := by
      simp only [Study.gamma, hsame]
    rw [hg]
    ring
  rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, mul_zero] at h
  convert h using 1
  congr 1
  funext ω
  ring

def fc_latent_coefficient (S : Study Ω) (w : ℕ) (y : Bool) : ℝ :=
  bitVal y / S.law.prob (fun t => S.Y t = true) *
    ((w : ℝ) - S.law.ce (fun t => (S.W t : ℝ)) (fun t => S.Y t = true)) /
    (S.gamma * (1 - S.gamma))

lemma fc_psi_factor (S : Study Ω) (ω : Ω) :
    S.betaPsi ω = fc_latent_coefficient S (S.W ω) (S.Y ω) *
      (bitVal (S.Z ω) - S.gamma) := by
  unfold Study.betaPsi fc_latent_coefficient
  ring

lemma fc_cross (P : FiniteLaw Ω) (S : Fin 5 → Study Ω)
    (hsame : ∀ j, (S j).law = P) (hj : jointAssignmentStable P S)
    (j k : Fin 5) (hjk : j ≠ k) :
    P.mean (fun ω => (S j).betaPsi ω * (S k).betaPsi ω) = 0 := by
  have h := fc_centered_assignment P S hsame hj j k hjk
    (fun w _ y => fc_latent_coefficient (S j) (w j) (y j) *
      fc_latent_coefficient (S k) (w k) (y k))
  convert h using 1
  congr 1
  funext ω
  simp only [fc_psi_factor]
  ring

lemma fc_cross_fibre (P : FiniteLaw Ω) (S : Fin 5 → Study Ω)
    (hsame : ∀ j, (S j).law = P) (hj : jointAssignmentStable P S)
    (j k : Fin 5) (hjk : j ≠ k) (ω : Ω) :
    P.ce (fun t => (S j).betaPsi t * (S k).betaPsi t) (latentVectorFibre S ω) = 0 := by
  have h := fc_centered_assignment P S hsame hj j k hjk
    (fun w x y => if ∀ i, w i = (S i).W ω ∧ x i = (S i).X ω ∧ y i = (S i).Y ω then
      fc_latent_coefficient (S j) (w j) (y j) *
        fc_latent_coefficient (S k) (w k) (y k) else 0)
  have hn : P.mean (fun t => if latentVectorFibre S ω t then
      (S j).betaPsi t * (S k).betaPsi t else 0) = 0 := by
    convert h using 1
    congr 1
    funext t
    by_cases ht : latentVectorFibre S ω t
    · rw [if_pos ht, if_pos (show ∀ i, (S i).W t = (S i).W ω ∧
          (S i).X t = (S i).X ω ∧ (S i).Y t = (S i).Y ω from ht)]
      simp only [fc_psi_factor]
      ring
    · rw [if_neg ht, if_neg (show ¬ (∀ i, (S i).W t = (S i).W ω ∧
          (S i).X t = (S i).X ω ∧ (S i).Y t = (S i).Y ω) from ht)]
      ring
  rw [FiniteLaw.ce, hn, zero_div]

/-- The coefficient consistently estimated by n times the actual variance. -/
def fc_variance (S : Study Ω) : ℝ :=
  S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true true) / S.law.prob (S.cell true true) +
    S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false true) / S.law.prob (S.cell false true)

lemma fc_variance_pos (S : Study Ω) (hs : S.standing) : 0 < fc_variance S :=
  add_pos (div_pos (hs.2.2.2.1 true true).2 (hs.2.2.2.1 true true).1)
    (div_pos (hs.2.2.2.1 false true).2 (hs.2.2.2.1 false true).1)

lemma fc_psi_contrast (S : Study Ω) (hs : S.standing) (ω : Ω)
    (hω : 0 < S.law.mass ω) :
    S.betaPsi ω = S.law.contrastInfluence (fun t => (S.V t : ℝ))
      (S.cell true true) (S.cell false true) ω := by
  let m := S.law.ce (fun t => (S.W t : ℝ)) (fun t => S.Y t = true)
  have hq := (regularity_probabilities S hs.2.2.2).2 true
  have hm (z : Bool) : S.listMean z true = m + bitVal z := by
    rw [list_mean_identified S hs.2.1 hs.2.2.1 z true
      (hs.2.2.2.1 z true).1.ne', monotone_yes_mean S hs.1 hq.ne']
    simp [m]
  have hp1 : S.law.prob (S.cell true true) =
      S.law.prob (fun t => S.Y t = true) * S.gamma := by
    rw [cell_probability S hs.2.2.1 true true]
    unfold Study.gamma
    ring
  have hp0 : S.law.prob (S.cell false true) =
      S.law.prob (fun t => S.Y t = true) * (1 - S.gamma) := by
    rw [cell_probability S hs.2.2.1 false true, prob_false]
    unfold Study.gamma
    ring
  rw [← placebo_influence_residual S hs ω hω]
  change _ = (if S.cell true true ω then (S.V ω : ℝ) - S.listMean true true else 0) /
      S.law.prob (S.cell true true) -
    (if S.cell false true ω then (S.V ω : ℝ) - S.listMean false true else 0) /
      S.law.prob (S.cell false true)
  rw [hp1, hp0, hm, hm]
  cases hy : S.Y ω <;> cases hz : S.Z ω <;>
    simp [bitVal, Study.cell, hy, hz, m, div_eq_mul_inv, mul_inv_rev] <;> ring


def fc_influence (S : Study Ω) : Ω → ℝ :=
  S.law.contrastInfluence (fun t => (S.V t : ℝ)) (S.cell true true) (S.cell false true)

def fc_normalized (S : Study Ω) (ω : Ω) : ℝ :=
  fc_influence S ω / Real.sqrt (fc_variance S)

lemma fc_influence_moments (S : Study Ω) (hs : S.standing) :
    S.law.mean (fc_influence S) = 0 ∧
      S.law.mean (fun ω => (fc_influence S ω)^2) = fc_variance S := by
  have h := contrast_influence_moments S.law (fun t => (S.V t : ℝ))
    (S.cell true true) (S.cell false true)
    (hs.2.2.2.1 true true).1.ne' (hs.2.2.2.1 false true).1.ne'
    (by intro ω ht hf; exact Bool.false_ne_true (hf.1.symm.trans ht.1))
  refine ⟨h.1, ?_⟩
  simpa only [fc_influence, fc_variance, FiniteLaw.variance, h.1,
    zero_pow (by decide : 2 ≠ 0), sub_zero] using h.2

lemma fc_normalized_mean (S : Study Ω) (hs : S.standing) :
    S.law.mean (fc_normalized S) = 0 := by
  change S.law.mean (fun ω => fc_influence S ω / Real.sqrt (fc_variance S)) = 0
  rw [mean_div_const, (fc_influence_moments S hs).1, zero_div]

lemma fc_normalized_cross (P : FiniteLaw Ω) (S : Fin 5 → Study Ω)
    (hsame : ∀ j, (S j).law = P) (hs : ∀ j, (S j).standing)
    (hj : jointAssignmentStable P S) (j k : Fin 5) :
    P.mean (fun ω => fc_normalized (S j) ω * fc_normalized (S k) ω) =
      if j = k then 1 else 0 := by
  by_cases heq : j = k
  · subst k
    rw [if_pos rfl, ← hsame j]
    have he (ω : Ω) : fc_normalized (S j) ω * fc_normalized (S j) ω =
        (fc_influence (S j) ω)^2 / (Real.sqrt (fc_variance (S j)))^2 := by
      unfold fc_normalized
      ring
    simp_rw [he]
    rw [mean_div_const, (fc_influence_moments (S j) (hs j)).2,
      Real.sq_sqrt (fc_variance_pos (S j) (hs j)).le,
      div_self (fc_variance_pos (S j) (hs j)).ne']
  · rw [if_neg heq]
    have hcross : P.mean (fun ω => fc_influence (S j) ω * fc_influence (S k) ω) = 0 := by
      rw [← fc_cross P S hsame hj j k heq]
      apply mean_congr_support
      intro ω hω
      rw [fc_psi_contrast (S j) (hs j) ω (by simpa only [hsame] using hω),
        fc_psi_contrast (S k) (hs k) ω (by simpa only [hsame] using hω)]
      rfl
    simp only [fc_normalized, div_mul_div_comm]
    rw [mean_div_const, hcross, zero_div]

lemma fc_projection_moments (P : FiniteLaw Ω) (S : Fin 5 → Study Ω)
    (hsame : ∀ j, (S j).law = P) (hs : ∀ j, (S j).standing)
    (hj : jointAssignmentStable P S) (a : Fin 5 → ℝ) :
    P.mean (fun ω => ∑ j, a j * fc_normalized (S j) ω) = 0 ∧
    P.variance (fun ω => ∑ j, a j * fc_normalized (S j) ω) = ∑ j, (a j)^2 := by
  have hm : P.mean (fun ω => ∑ j, a j * fc_normalized (S j) ω) = 0 := by
    rw [mean_sum]
    have hz (j : Fin 5) : P.mean (fc_normalized (S j)) = 0 := by
      rw [← hsame j]
      exact fc_normalized_mean (S j) (hs j)
    simp_rw [mean_const_mul, hz, mul_zero]
    simp
  refine ⟨hm, ?_⟩
  have he (ω : Ω) : (∑ j, a j * fc_normalized (S j) ω)^2 =
      ∑ j, ∑ k, (a j * a k) * (fc_normalized (S j) ω * fc_normalized (S k) ω) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [FiniteLaw.variance, hm, zero_pow (by decide : 2 ≠ 0), sub_zero]
  simp_rw [he, mean_sum, mean_const_mul, fc_normalized_cross P S hsame hs hj]
  simp [pow_two]

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

lemma fc_linear_remainder (S : Study Ω) (hs : S.standing) :
    TendstoInMeasure (t19_product S.law) (fun (n : ℕ) ω =>
      Real.sqrt n * (S.betaHat (t19_sample n ω) 0 0 - 1) -
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, fc_influence S (ω i))
      atTop (fun _ => 0) := by
  have hβ : S.beta = 1 := placebo_one_identity S hs.1 hs.2.1 hs.2.2.1
    (hs.2.2.2.1 false true).1.ne' (hs.2.2.2.1 true true).1.ne'
  have hR := AronowAudit.P015.ConvergenceCompletion.sub_limit _
    (GP019B3b_ratio_remainder S.law (fun t => (S.V t : ℝ))
      (S.cell true true) (hs.2.2.2.1 true true).1 0)
    (GP019B3b_ratio_remainder S.law (fun t => (S.V t : ℝ))
      (S.cell false true) (hs.2.2.2.1 false true).1 0)
  rw [← hβ]
  convert hR using 1
  · funext n ω
    simp only [fc_influence, FiniteLaw.contrastInfluence, Finset.sum_sub_distrib]
    change Real.sqrt n *
        ((GP019B3b_sampleMean (fun t => (S.V t : ℝ)) (S.cell true true) (t19_sample n ω) 0 -
          GP019B3b_sampleMean (fun t => (S.V t : ℝ)) (S.cell false true) (t19_sample n ω) 0) -
          (S.law.ce (fun t => (S.V t : ℝ)) (S.cell true true) -
          S.law.ce (fun t => (S.V t : ℝ)) (S.cell false true))) - _ = _
    ring
  · simp only [sub_zero]

lemma fc_variance_ae (S : Study Ω) (hs : S.standing) :
    ∀ᵐ ω ∂t19_product S.law, Tendsto (fun n : ℕ =>
      (n : ℝ) * S.betaVarianceHat (t19_sample n ω) 0) atTop (nhds (fc_variance S)) :=
  GP019B3b_varianceHat_ae S.law (fun t => (S.V t : ℝ))
    (S.cell true true) (S.cell false true)
    (hs.2.2.2.1 true true).1 (hs.2.2.2.1 false true).1 0

/-- Each actual studentized statistic differs negligibly from its normalized
influence sum. This uses the actual divisor-count-minus-one sample variances. -/
lemma fc_studentized_remainder (S : Study Ω) (hs : S.standing) :
    TendstoInMeasure (t19_product S.law) (fun (n : ℕ) ω =>
      (S.betaHat (t19_sample n ω) 0 0 - 1) /
          Real.sqrt (S.betaVarianceHat (t19_sample n ω) 0) -
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, fc_normalized S (ω i))
      atTop (fun _ => 0) := by
  let b : ℕ → (ℕ → Ω) → ℝ := fun n ω =>
    (Real.sqrt ((n : ℝ) * S.betaVarianceHat (t19_sample n ω) 0))⁻¹
  let d : ℝ := (Real.sqrt (fc_variance S))⁻¹
  have hb (n : ℕ) : Measurable (b n) :=
    t19_stat_measurable n (fun s => (Real.sqrt ((n : ℝ) * S.betaVarianceHat s 0))⁻¹)
  have hbAE : ∀ᵐ ω ∂t19_product S.law, Tendsto (fun n => b n ω) atTop (nhds d) := by
    filter_upwards [fc_variance_ae S hs] with ω hω
    exact hω.sqrt.inv₀ (Real.sqrt_pos.mpr (fc_variance_pos S hs)).ne'
  have hbP := tendstoInMeasure_of_tendsto_ae (fun n => (hb n).aestronglyMeasurable) hbAE
  have hR := AronowAudit.P015.ConvergenceCompletion.mul_limit _ (fc_linear_remainder S hs) hbP
  have hsmall := t19_small_product S.law (fc_influence S) (fc_influence_moments S hs).1
    (fun n ω => b n ω - d) (fun n => (hb n).sub measurable_const) (by
      filter_upwards [hbAE] with ω hω
      simpa only [sub_self] using hω.sub_const d)
  have hsum := AronowAudit.P015.ConvergenceCompletion.add_limit _ hR hsmall
  simp only [zero_mul, add_zero] at hsum
  apply t19_transfer_inMeasure (t19_product S.law)
    (fun n => t19_stat_measurable n (fun s =>
      (Real.sqrt n * (S.betaHat s 0 0 - 1) -
        (Real.sqrt n)⁻¹ * ∑ i, fc_influence S (s i)) *
          (Real.sqrt ((n : ℝ) * S.betaVarianceHat s 0))⁻¹ +
        ((Real.sqrt n)⁻¹ * ∑ i, fc_influence S (s i)) *
          ((Real.sqrt ((n : ℝ) * S.betaVarianceHat s 0))⁻¹ - d)))
    (fun n => t19_stat_measurable n (fun s =>
      (S.betaHat s 0 0 - 1) / Real.sqrt (S.betaVarianceHat s 0) -
        (Real.sqrt n)⁻¹ * ∑ i, fc_normalized S (s i))) hsum
  exact Filter.Eventually.of_forall (fun ω => by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnS : Real.sqrt (n : ℝ) ≠ 0 := by positivity
    dsimp only [b, d]
    simp only [Real.sqrt_mul (Nat.cast_nonneg n), mul_inv_rev,
      fc_normalized, div_eq_mul_inv]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    field_simp [hnS]
    <;> ring)

lemma fc_gaussian_projection (a : EuclideanSpace ℝ (Fin 5)) :
    HasLaw (fun x : EuclideanSpace ℝ (Fin 5) => ⟪x, a⟫)
      (gaussianReal 0 (∑ j, (a j)^2).toNNReal)
      (stdGaussian (EuclideanSpace ℝ (Fin 5))) := by
  refine ⟨(by fun_prop), ?_⟩
  have h := IsGaussian.map_eq_gaussianReal
    (μ := stdGaussian (EuclideanSpace ℝ (Fin 5))) (innerSL ℝ a)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq] at h
  convert h using 1
  congr 1
  funext x
  exact (real_inner_comm x a).symm

lemma fc_joint_clt (P : FiniteLaw Ω) (S : Fin 5 → Study Ω)
    (hsame : ∀ j, (S j).law = P) (hs : ∀ j, (S j).standing)
    (hj : jointAssignmentStable P S) :
    TendstoInDistribution (fun (n : ℕ) ω =>
      WithLp.toLp 2 (fun j => ((S j).betaHat (t19_sample n ω) 0 0 - 1) /
        Real.sqrt ((S j).betaVarianceHat (t19_sample n ω) 0)))
      atTop id (fun _ => t19_product P) (stdGaussian (EuclideanSpace ℝ (Fin 5))) := by
  apply TendstoInDistribution.of_inner measurable_id.aemeasurable
    (fun n => ((measurable_of_finite (fun s : Fin n → Ω =>
      WithLp.toLp 2 (fun j => ((S j).betaHat s 0 0 - 1) /
        Real.sqrt ((S j).betaVarianceHat s 0)))).comp (t19_sample_measurable n)).aemeasurable)
  intro a
  let f : Ω → ℝ := fun ω => ∑ j, a j * fc_normalized (S j) ω
  have hm := fc_projection_moments P S hsame hs hj (fun j => a j)
  have hc := t19_average_clt P f hm.1
  rw [hm.2] at hc
  have hl := fc_gaussian_projection a
  have hc' : TendstoInDistribution (fun (n : ℕ) ω =>
      (Real.sqrt n)⁻¹ * ∑ i : Fin n, f (ω i)) atTop
      (fun x : EuclideanSpace ℝ (Fin 5) => ⟪x, a⟫)
      (fun _ => t19_product P) (stdGaussian (EuclideanSpace ℝ (Fin 5))) :=
    ⟨hc.forall_aemeasurable, hl.aemeasurable, by
      simpa only [Measure.map_id, hl.map_eq] using hc.tendsto⟩
  have hr := AronowAudit.P015.ConvergenceCompletion.sum_limit (t19_product P)
    (fun j n ω => a j *
      (((S j).betaHat (t19_sample n ω) 0 0 - 1) /
        Real.sqrt ((S j).betaVarianceHat (t19_sample n ω) 0) -
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, fc_normalized (S j) (ω i)))
    (fun _ => 0) (fun j => by
      have h := fc_studentized_remainder (S j) (hs j)
      rw [hsame j] at h
      simpa only [mul_zero] using AronowAudit.P015.ConvergenceCompletion.mul_limit _
        (AronowAudit.P015.ConvergenceCompletion.constant_limit _ (a j)) h)
  have hrem : TendstoInMeasure (t19_product P) (fun (n : ℕ) ω =>
      ⟪WithLp.toLp 2 (fun j => ((S j).betaHat (t19_sample n ω) 0 0 - 1) /
          Real.sqrt ((S j).betaVarianceHat (t19_sample n ω) 0)), a⟫ -
        (Real.sqrt n)⁻¹ * ∑ i : Fin n, f (ω i)) atTop (fun _ => 0) := by
    convert hr using 1
    · funext n ω
      simp only [PiLp.inner_apply, Real.inner_apply, f,
        mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        ring
      · apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
    · simp
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ hc' hrem
    (fun n => ((measurable_of_finite (fun s : Fin n → Ω =>
      ⟪WithLp.toLp 2 (fun j => ((S j).betaHat s 0 0 - 1) /
        Real.sqrt ((S j).betaVarianceHat s 0)), a⟫)).comp (t19_sample_measurable n)).aemeasurable)

/-- Bounded continuous test functions transfer the common-product limit back
to the finite weighted-sum predicate defining weak convergence. -/
lemma fc_weakLimit {E A : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace A] (P : FiniteLaw Ω)
    (T : (n : ℕ) → (Fin n → Ω) → E) (μ : Measure A) [IsProbabilityMeasure μ]
    (Z : A → E) (Q : Measure E)
    (h : TendstoInDistribution (fun (n : ℕ) ω => T n (t19_sample n ω))
      atTop Z (fun _ => t19_product P) μ) (hZ : HasLaw Z Q μ) : WeakLimit P T Q := by
  intro f hf hbound
  obtain ⟨C, hC⟩ := hbound
  let F : BoundedContinuousFunction E ℝ :=
    ⟨⟨f, hf⟩, ⟨2*C, fun x y => (dist_le_norm_add_norm _ _).trans (by
      simpa only [Real.norm_eq_abs, two_mul] using add_le_add (hC x) (hC y))⟩⟩
  have hh := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    h.forall_aemeasurable h.aemeasurable_limit).mp h F
  change Tendsto (fun n => ∫ ω, f (T n (t19_sample n ω)) ∂t19_product P)
    atTop (nhds (∫ x, f (Z x) ∂μ)) at hh
  rw [show (∫ x, f (Z x) ∂μ) = ∫ x, f x ∂Q from
    hZ.integral_comp hf.measurable.aestronglyMeasurable] at hh
  convert hh using 1
  funext n
  exact (t19_sample_integral P n (fun s => f (T n s))).symm

lemma fc_gaussian_pi_law :
    HasLaw (WithLp.ofLp : EuclideanSpace ℝ (Fin 5) → Fin 5 → ℝ)
      (Measure.pi (fun _ : Fin 5 => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin 5))) := by
  refine ⟨(PiLp.continuous_ofLp 2 (fun _ : Fin 5 => ℝ)).measurable.aemeasurable, ?_⟩
  rw [← map_pi_eq_stdGaussian,
    Measure.map_map (PiLp.continuous_ofLp 2 (fun _ : Fin 5 => ℝ)).measurable
      (PiLp.continuous_toLp 2 (fun _ : Fin 5 => ℝ)).measurable]
  simp only [Function.comp_def, WithLp.ofLp_toLp, Measure.map_id']

local instance fc_uniform_probability :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

local instance fc_normal_atomless : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

def fc_p (x : ℝ) : ℝ := 2 * normalCDF (-|x|)

lemma fc_p_pos (x : ℝ) : 0 < fc_p x :=
  mul_pos (by norm_num) (npu_cdf_pos _)

lemma fc_p_le_one (x : ℝ) : fc_p x ≤ 1 := by
  have h := npu_strictMono.monotone (show -|x| ≤ 0 by linarith [abs_nonneg x])
  have hzero : normalCDF 0 = 1/2 := by
    rw [npu_cdf_eq]
    exact AronowAudit.P053.NormalCompletion.normal_cdf_zero
  rw [hzero] at h
  dsimp only [fc_p]
  linarith

lemma fc_p_continuous : Continuous fc_p := by
  have hΦ : Continuous normalCDF := by
    have he : normalCDF = cdf (gaussianReal 0 1) := funext npu_cdf_eq
    rw [he, continuous_iff_continuousAt]
    exact AronowAudit.P053.NormalCompletion.cdf_continuousAt _
  exact continuous_const.mul (hΦ.comp continuous_abs.neg)

lemma fc_uniform_cdf (x : ℝ) :
    cdf (volume.restrict (Set.Icc (0 : ℝ) 1)) x = max (min x 1) 0 := by
  rw [cdf_eq_real]
  change ((volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic x)).toReal = _
  rw [Measure.restrict_apply measurableSet_Iic]
  have he : Set.Iic x ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 (min x 1) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
    tauto
  rw [he, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal']

lemma fc_p_uniform :
    (gaussianReal 0 1).map fc_p = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  apply Measure.eq_of_cdf
  refine StieltjesFunction.ext fun t => ?_
  rw [fc_uniform_cdf, cdf_eq_real]
  change (((gaussianReal 0 1).map fc_p) (Set.Iic t)).toReal = _
  rw [Measure.map_apply fc_p_continuous.measurable measurableSet_Iic]
  by_cases ht0 : t ≤ 0
  · have he : fc_p ⁻¹' Set.Iic t = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_le_of_lt ht0 (fc_p_pos x))
    rw [he, measure_empty, ENNReal.toReal_zero, min_eq_left (by linarith), max_eq_right ht0]
  · have ht0' : 0 < t := lt_of_not_ge ht0
    by_cases ht1 : 1 ≤ t
    · have he : fc_p ⁻¹' Set.Iic t = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        exact (fc_p_le_one x).trans ht1
      rw [he, measure_univ, ENNReal.toReal_one, min_eq_right ht1, max_eq_left (by norm_num)]
    · have ht1' : t < 1 := lt_of_not_ge ht1
      rw [min_eq_left ht1'.le, max_eq_left ht0'.le]
      exact normal_pvalue_uniform_proof t ht0' ht1'

lemma fc_pvector_law :
    HasLaw (fun x : Fin 5 → ℝ => fun j => fc_p (x j))
      (Measure.pi (fun _ : Fin 5 => volume.restrict (Set.Icc (0 : ℝ) 1)))
      (Measure.pi (fun _ : Fin 5 => gaussianReal 0 1)) := by
  refine ⟨(continuous_pi (fun j => fc_p_continuous.comp (continuous_apply j))).measurable.aemeasurable, ?_⟩
  rw [Measure.pi_map_pi (fun _ => fc_p_continuous.measurable.aemeasurable)]
  simp only [fc_p_uniform]

/-- Compose log with the positive normal p-map before applying CMT. -/
lemma fc_fisher_continuous :
    Continuous (fun x : Fin 5 → ℝ => fisherStatistic (fun j => fc_p (x j))) := by
  apply continuous_const.mul
  apply continuous_finset_sum
  intro j _
  exact (fc_p_continuous.comp (continuous_apply j)).log (fun x => (fc_p_pos (x j)).ne')

lemma fc_fisher_law :
    HasLaw (fun x : Fin 5 → ℝ => fisherStatistic (fun j => fc_p (x j)))
      chiSquareTen (Measure.pi (fun _ : Fin 5 => gaussianReal 0 1)) := by
  have hF : HasLaw fisherStatistic chiSquareTen
      (Measure.pi (fun _ : Fin 5 => volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    ⟨(show Measurable fisherStatistic by unfold fisherStatistic; fun_prop).aemeasurable,
      uniform_fisher_identity_proof⟩
  exact hF.comp fc_pvector_law

lemma fc_pvalue_point (e v : ℝ) : normalPValue e 1 v = fc_p ((e - 1) / Real.sqrt v) := by
  simp only [normalPValue, fc_p, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), neg_div]

end
noncomputable section
open Classical
variable {Ω : Type*} [Fintype Ω]

theorem fisher_corrected_proof (P : FiniteLaw Ω) (S : Fin 5 → Study Ω)
    (hsame : ∀ j, (S j).law = P) (hs : ∀ j, (S j).standing)
    (hj : jointAssignmentStable P S) :
    (∀ j, (S j).beta = 1) ∧
    (∀ j k : Fin 5, j ≠ k → ∀ ω,
      P.prob (latentVectorFibre S ω) ≠ 0 →
        P.ce (fun t => (S j).betaPsi t * (S k).betaPsi t) (latentVectorFibre S ω) = 0) ∧
    (∀ j k : Fin 5, j ≠ k → P.mean (fun ω => (S j).betaPsi ω * (S k).betaPsi ω) = 0) ∧
    WeakLimit P (fun _ s j => ((S j).betaHat s 0 0-1) /
      Real.sqrt ((S j).betaVarianceHat s 0))
        (Measure.pi (fun _ : Fin 5 => gaussianReal 0 1)) ∧
    WeakLimit P (fun _ s j => normalPValue ((S j).betaHat s 0 0) 1
      ((S j).betaVarianceHat s 0))
        (Measure.pi (fun _ : Fin 5 => volume.restrict (Set.Icc (0 : ℝ) 1))) ∧
    WeakLimit P (fun _ s => fisherStatistic (fun j =>
      normalPValue ((S j).betaHat s 0 0) 1 ((S j).betaVarianceHat s 0))) chiSquareTen := by
  refine ⟨(fun j => placebo_one_identity (S j) (hs j).1 (hs j).2.1 (hs j).2.2.1
    ((hs j).2.2.2.1 false true).1.ne' ((hs j).2.2.2.1 true true).1.ne'),
    (fun j k hjk ω _ => fc_cross_fibre P S hsame hj j k hjk ω),
    (fun j k hjk => fc_cross P S hsame hj j k hjk), ?_⟩
  letI fc_discrete : MeasurableSpace Ω := ⊤
  haveI fc_singleton : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩
  have hc := fc_joint_clt P S hsame hs hj
  have hz := hc.continuous_comp (g := (WithLp.ofLp : EuclideanSpace ℝ (Fin 5) → Fin 5 → ℝ))
    (PiLp.continuous_ofLp 2 (fun _ : Fin 5 => ℝ))
  have hp := hc.continuous_comp
    (g := fun x : EuclideanSpace ℝ (Fin 5) => fun j => fc_p (x j))
    (continuous_pi (fun j => fc_p_continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) j)))
  have hf := hc.continuous_comp
    (g := fun x : EuclideanSpace ℝ (Fin 5) => fisherStatistic (fun j => fc_p (x j)))
    (fc_fisher_continuous.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 5 => ℝ)))
  refine ⟨fc_weakLimit P _ _ _ _ hz fc_gaussian_pi_law, ?_, ?_⟩
  · have hw := fc_weakLimit P
      (fun _ s j => fc_p (((S j).betaHat s 0 0 - 1) /
        Real.sqrt ((S j).betaVarianceHat s 0))) _ _ _ hp
      (fc_pvector_law.comp fc_gaussian_pi_law)
    simpa only [fc_pvalue_point] using hw
  · have hw := fc_weakLimit P
      (fun _ s => fisherStatistic (fun j => fc_p (((S j).betaHat s 0 0 - 1) /
        Real.sqrt ((S j).betaVarianceHat s 0)))) _ _ _ hf
      (fc_fisher_law.comp fc_gaussian_pi_law)
    simpa only [fc_pvalue_point] using hw

end
end AronowAudit.P019.Wave1
