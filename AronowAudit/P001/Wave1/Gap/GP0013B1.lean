import AronowAudit.P001.P001_Foundations
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

/-!
Draft by dd-GP0013B1; no Lean executable was run.

Record order: 6, 7, 8, 10, 13, 14.  The report distinguishes the completed
proof text from records blocked on shared proof modules.  No held probabilistic
declaration is used as proof credit.
-/

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGP0013B1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-! ## Record 6: functional_delta_nondegenerate_correction

The exact duplicate wrapper requires the new empirical-CDF delta proof, which
is not present in this worktree.  The held declaration and its supporting
declaration cannot provide that proof.  See REPORT.md; no replacement premise
for the missing Donsker/bridge machinery is introduced here.
-/

/-! ## Record 7: kolmogorov_embedding_preserves_cdf

The same dependency blocks this exact duplicate wrapper.  Despite its name,
the target includes the full empirical-process and scalar Gaussian limits.
-/

/-! ## Record 8: general_gram_rate_stability

For this rate result it is enough to prove the weaker finite-sample estimate
E ||G-I||_F² ≤ zeta2*K/n.  This avoids a dependency on the separate sharp
finite-sample Gram-deviation theorem.  A measurable Frobenius event suffices:
monotonicity of outer measure does not require measurability of the larger
all-vector good event.
-/

private def general_gram_frob {K : ℕ} (G : Matrix (Fin K) (Fin K) ℝ) : ℝ :=
  ∑ j, ∑ k, (G j k - if j = k then 1 else 0)^2

private lemma general_gram_frob_nonneg {K : ℕ}
    (G : Matrix (Fin K) (Fin K) ℝ) : 0 ≤ general_gram_frob G := by
  exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))

private lemma general_gram_product_bound {K : ℕ} (z : Fin K → ℝ)
    (j k : Fin K) : |z j * z k| ≤ ∑ l, (z l)^2 := by
  have hj : (z j)^2 ≤ ∑ l, (z l)^2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (z l)) (Finset.mem_univ j)
  have hk : (z k)^2 ≤ ∑ l, (z l)^2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (z l)) (Finset.mem_univ k)
  rw [abs_mul]
  nlinarith [sq_nonneg (|z j| - |z k|), sq_abs (z j), sq_abs (z k)]

private lemma general_gram_quadratic_identity {K : ℕ} {Ω : Type*}
    (p : Fin K → Polynomial ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (v : Fin K → ℝ) :
    (∑ j, ∑ k, v j * sampleGram p X n ω j k * v k) =
      (∑ i ∈ Finset.range n, (∑ k, v k * (p k).eval (X i ω))^2)/(n : ℝ) := by
  classical
  simp only [sampleGram, div_eq_mul_inv]
  calc
    (∑ j, ∑ k, v j * ((∑ i ∈ Finset.range n,
        (p j).eval (X i ω) * (p k).eval (X i ω)) * (n : ℝ)⁻¹) * v k) =
      ∑ j, ∑ k, ∑ i ∈ Finset.range n,
        (v j * (p j).eval (X i ω)) *
          (v k * (p k).eval (X i ω)) * (n : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ i ∈ Finset.range n, ∑ j, ∑ k,
        (v j * (p j).eval (X i ω)) *
          (v k * (p k).eval (X i ω)) * (n : ℝ)⁻¹ := by
          calc
            _ = ∑ j, ∑ i ∈ Finset.range n, ∑ k,
                (v j * (p j).eval (X i ω)) *
                  (v k * (p k).eval (X i ω)) * (n : ℝ)⁻¹ := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_comm]
            _ = _ := by rw [Finset.sum_comm]
    _ = (∑ i ∈ Finset.range n,
        (∑ k, v k * (p k).eval (X i ω))^2) * (n : ℝ)⁻¹ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          simp only [← Finset.sum_mul, ← Finset.mul_sum, pow_two]

private lemma general_gram_frob_controls_quadratic {K : ℕ}
    (G : Matrix (Fin K) (Fin K) ℝ) (hG : general_gram_frob G ≤ 1/4)
    (v : Fin K → ℝ) :
    (1/2 : ℝ) * (∑ k, (v k)^2) ≤ ∑ j, ∑ k, v j * G j k * v k := by
  classical
  let A : Matrix (Fin K) (Fin K) ℝ := fun j k => G j k - if j = k then 1 else 0
  let S : ℝ := ∑ k, (v k)^2
  let D : ℝ := ∑ j, ∑ k, A j k * (v j * v k)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hCS : D^2 ≤ general_gram_frob G * S^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin K × Fin K))
      (fun jk => A jk.1 jk.2) (fun jk => v jk.1 * v jk.2)
    have hVV : (∑ j, ∑ k, (v j * v k)^2) = S^2 := by
      simp only [S, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    simpa only [Fintype.sum_prod_type, D, general_gram_frob, A, hVV] using h
  have hD : -(S/2) ≤ D := by
    have hmult := mul_le_mul_of_nonneg_right hG (sq_nonneg S)
    have hDS : D^2 ≤ S^2/4 := by nlinarith
    have habs : |D| ≤ S/2 := by
      apply (sq_le_sq₀ (abs_nonneg D) (div_nonneg hS (by norm_num : (0 : ℝ) ≤ 2))).mp
      nlinarith [sq_abs D]
    exact (abs_le.mp habs).1
  have hdecomp : (∑ j, ∑ k, v j * G j k * v k) = S + D := by
    have he (j k : Fin K) : v j * G j k * v k =
        (if j = k then v j * v k else 0) + A j k * (v j * v k) := by
      dsimp [A]
      split_ifs <;> ring
    simp_rw [he, Finset.sum_add_distrib]
    simp [S, D, pow_two]
  rw [hdecomp]
  change (1/2 : ℝ) * S ≤ S + D
  linarith

private lemma general_gram_frob_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (p : Fin K → Polynomial ℝ)
    (horth : ∀ j k, mean μ (fun ω =>
      (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) = if j = k then 1 else 0)
    (ζ : ℝ) (hrow : ∀ᵐ ω ∂μ, (∑ k, ((p k).eval (X 0 ω))^2) ≤ ζ)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ω => general_gram_frob (sampleGram p X n ω)) μ ∧
    (∫ ω, general_gram_frob (sampleGram p X n ω) ∂μ) ≤ (ζ * (K : ℝ)-K)/(n : ℝ) := by
  classical
  let Y : Fin K → Fin K → ℕ → Ω → ℝ :=
    fun j k i ω => (p j).eval (X i ω) * (p k).eval (X i ω)
  let S : Ω → ℝ := fun ω => ∑ k, ((p k).eval (X 0 ω))^2
  have hYm (j k : Fin K) (i : ℕ) : Measurable (Y j k i) := by
    exact ((p j).continuous.measurable.comp (hiid.1 i)).mul
      ((p k).continuous.measurable.comp (hiid.1 i))
  have hYiid (j k : Fin K) : IID μ (Y j k) := by
    let f : ℝ → ℝ := fun x => (p j).eval x * (p k).eval x
    have hf : Measurable f := (p j).continuous.measurable.mul (p k).continuous.measurable
    exact ⟨hYm j k, hiid.2.1.comp (fun _ => f) (fun _ => hf),
      fun i => (hiid.2.2 i).comp (u := f) hf⟩
  have hY2 (j k : Fin K) : MemLp (Y j k 0) 2 μ := by
    apply (memLp_const ζ).mono' (hYm j k 0).aestronglyMeasurable
    filter_upwards [hrow] with ω hω
    rw [Real.norm_eq_abs]
    exact (general_gram_product_bound (fun l => (p l).eval (X 0 ω)) j k).trans hω
  have hYsq (j k : Fin K) : Integrable (fun ω => (Y j k 0 ω)^2) μ :=
    (hY2 j k).integrable_sq
  have hS2 : MemLp S 2 μ := by
    simpa only [S, Y, pow_two] using
      (memLp_finsetSum (Finset.univ : Finset (Fin K)) (fun k _ => hY2 k k))
  have hS1 : Integrable S μ := hS2.integrable one_le_two
  have hES : (∫ ω, S ω ∂μ) = (K : ℝ) := by
    have hd (k : Fin K) : (∫ ω, ((p k).eval (X 0 ω))^2 ∂μ) = 1 := by
      have h := horth k k
      rw [if_pos rfl] at h
      simpa only [mean, pow_two] using h
    dsimp [S]
    rw [integral_finsetSum _ (fun k _ => by
      simpa only [Y, pow_two] using (hY2 k k).integrable one_le_two)]
    simp only [Finset.mem_univ, hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hESsq : (∫ ω, (S ω)^2 ∂μ) ≤ ζ * (K : ℝ) := by
    calc
      (∫ ω, (S ω)^2 ∂μ) ≤ ∫ ω, ζ * S ω ∂μ := by
        apply integral_mono_ae hS2.integrable_sq (hS1.const_mul ζ)
        filter_upwards [hrow] with ω hω
        have hS0 : 0 ≤ S ω := Finset.sum_nonneg (fun k _ => sq_nonneg _)
        change S ω ≤ ζ at hω
        nlinarith
      _ = ζ * (K : ℝ) := by rw [integral_const_mul, hES]
  have hG2 (j k : Fin K) : MemLp (fun ω => sampleGram p X n ω j k) 2 μ := by
    exact sample_mean_memLp μ (Y j k) (hYiid j k) (hY2 j k) n
  have hcenter (j k : Fin K) : Integrable
      (fun ω => (sampleGram p X n ω j k - if j = k then 1 else 0)^2) μ :=
    ((hG2 j k).sub (memLp_const _)).integrable_sq
  have hcenter_mean (j k : Fin K) :
      (∫ ω, (sampleGram p X n ω j k - if j = k then 1 else 0)^2 ∂μ) =
        var μ (Y j k 0)/(n : ℝ) := by
    have hmom := iid_sample_mean_finite_moments μ (Y j k) (hYiid j k) (hY2 j k) n hn
    have hmean : mean μ (fun ω => sampleGram p X n ω j k) =
        if j = k then 1 else 0 := hmom.1.trans (horth j k)
    rw [← hmean]
    change (∫ ω, (sampleMean (Y j k) n ω - mean μ (sampleMean (Y j k) n))^2 ∂μ) = _
    exact (variance_eq_integral (hG2 j k).aestronglyMeasurable.aemeasurable).symm.trans hmom.2
  have hYvar (j k : Fin K) : var μ (Y j k 0) =
      (∫ ω, (Y j k 0 ω)^2 ∂μ) - if j = k then 1 else 0 := by
    change variance (Y j k 0) μ = _
    rw [variance_eq_sub (hY2 j k)]
    have he : (∫ ω, Y j k 0 ω ∂μ) = if j = k then 1 else 0 := horth j k
    rw [he]
    split_ifs <;> norm_num
  have hFint : Integrable (fun ω => general_gram_frob (sampleGram p X n ω)) μ := by
    exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hcenter j k))
  refine ⟨hFint, ?_⟩
  have hsumY : (∑ j, ∑ k, ∫ ω, (Y j k 0 ω)^2 ∂μ) = ∫ ω, (S ω)^2 ∂μ := by
    calc
      (∑ j, ∑ k, ∫ ω, (Y j k 0 ω)^2 ∂μ) =
          ∫ ω, ∑ j, ∑ k, (Y j k 0 ω)^2 ∂μ := by
        rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hYsq j k))]
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_finsetSum _ (fun k _ => hYsq j k)]
      _ = ∫ ω, (S ω)^2 ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro ω
        simp only [Y, S, pow_two, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
  calc
    (∫ ω, general_gram_frob (sampleGram p X n ω) ∂μ) =
        ∑ j, ∑ k, var μ (Y j k 0)/(n : ℝ) := by
      unfold general_gram_frob
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hcenter j k))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun k _ => hcenter j k)]
      simp_rw [hcenter_mean]
    _ = ((∑ j, ∑ k, ∫ ω, (Y j k 0 ω)^2 ∂μ) - (K : ℝ))/(n : ℝ) := by
      simp_rw [← Finset.sum_div, hYvar, Finset.sum_sub_distrib]
      simp
    _ = ((∫ ω, (S ω)^2 ∂μ) - (K : ℝ))/(n : ℝ) := by
      rw [hsumY]
    _ ≤ (ζ * (K : ℝ)-K)/(n : ℝ) :=
      div_le_div_of_nonneg_right (sub_le_sub_right hESsq _) (Nat.cast_nonneg n)

private lemma general_gram_deviation_le_half {K : ℕ} (hK : 0 < K)
    (G : Matrix (Fin K) (Fin K) ℝ) (hG : general_gram_frob G ≤ 1/4) :
    gramDeviation G ≤ 1/2 := by
  classical
  let H : Matrix (Fin K) (Fin K) ℝ :=
    fun j k => 2 * (if j = k then 1 else 0) - G j k
  have hHF : general_gram_frob H = general_gram_frob G := by
    unfold general_gram_frob
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [H]
    split_ifs <;> ring
  have hunit (v : Fin K → ℝ) (hv : (∑ k, (v k)^2) = 1) :
      |(∑ j, ∑ k, v j * G j k * v k) - 1| ≤ 1/2 := by
    have hlo := general_gram_frob_controls_quadratic G hG v
    have hhi := general_gram_frob_controls_quadratic H (by rw [hHF]; exact hG) v
    have hHq : (∑ j, ∑ k, v j * H j k * v k) =
        2 - (∑ j, ∑ k, v j * G j k * v k) := by
      have he (j k : Fin K) : v j * H j k * v k =
          (if j = k then 2 * (v j * v k) else 0) - v j * G j k * v k := by
        dsimp [H]
        split_ifs <;> ring
      simp_rw [he, Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Finset.mul_sum]
      have hv' : (∑ k, v k * v k) = 1 := by simpa only [pow_two] using hv
      rw [hv', mul_one]
    rw [hv] at hlo hhi
    rw [hHq] at hhi
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold gramDeviation
  apply csSup_le
  · let e : Fin K → ℝ := fun k => if k = ⟨0, hK⟩ then 1 else 0
    refine ⟨|(∑ j, ∑ k, e j * G j k * e k) - 1|, e, ?_, rfl⟩
    simp [e]
  · rintro r ⟨v, hv, rfl⟩
    exact hunit v hv

/-- The sharp fixed-n estimate is proved here from the same elementary moment
calculation.  This is a helper for record 14, not an application of its held
general-polynomial counterpart. -/
lemma general_gram_finite_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ} (hK : 0 < K)
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (p : Fin K → Polynomial ℝ)
    (horth : ∀ j k, mean μ (fun ω =>
      (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) = if j = k then 1 else 0)
    (ζ : ℝ) (hrow : ∀ᵐ ω ∂μ, (∑ k, ((p k).eval (X 0 ω))^2) ≤ ζ)
    (n : ℕ) (hn : 0 < n) :
    prob μ {ω | 1/2 < gramDeviation (sampleGram p X n ω)} ≤
      4 * (ζ * (K : ℝ)-K)/(n : ℝ) := by
  let F : Ω → ℝ := fun ω => general_gram_frob (sampleGram p X n ω)
  have hmom := general_gram_frob_moment μ X hiid p horth ζ hrow n hn
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => general_gram_frob_nonneg (sampleGram p X n ω)))
    hmom.1 (1/4 : ℝ)
  have hbad : prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤
      4 * (ζ * (K : ℝ)-K)/(n : ℝ) := by
    change (1/4 : ℝ) * prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤ ∫ ω, F ω ∂μ at hmarkov
    calc
      prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤ 4 * ((ζ * (K : ℝ)-K)/(n : ℝ)) := by
        linarith [hmom.2]
      _ = 4 * (ζ * (K : ℝ)-K)/(n : ℝ) := by ring
  have hsub : {ω | 1/2 < gramDeviation (sampleGram p X n ω)} ⊆
      {ω | (1/4 : ℝ) ≤ F ω} := by
    intro ω hω
    by_contra hnot
    have hsmall : general_gram_frob (sampleGram p X n ω) ≤ 1/4 :=
      (lt_of_not_ge hnot).le
    exact (not_lt_of_ge (general_gram_deviation_le_half hK _ hsmall)) hω
  have hm : prob μ {ω | 1/2 < gramDeviation (sampleGram p X n ω)} ≤
      prob μ {ω | (1/4 : ℝ) ≤ F ω} := measureReal_mono hsub
  exact hm.trans hbad

example : type_of% @AronowAudit.P001.general_polynomial_gram_probability_bound :=
  general_gram_finite_probability_bound

private lemma general_gram_good_probability_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (p : Fin K → Polynomial ℝ)
    (horth : ∀ j k, mean μ (fun ω =>
      (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) = if j = k then 1 else 0)
    (ζ : ℝ) (hrow : ∀ᵐ ω ∂μ, (∑ k, ((p k).eval (X 0 ω))^2) ≤ ζ)
    (n : ℕ) (hn : 0 < n) :
    1 - 4 * (ζ * (K : ℝ)/(n : ℝ)) ≤ prob μ {ω | ∀ v : Fin K → ℝ,
      (1/2 : ℝ) * (∑ k, (v k)^2) ≤
        (∑ i ∈ Finset.range n, (∑ k, v k * (p k).eval (X i ω))^2)/(n : ℝ)} := by
  let F : Ω → ℝ := fun ω => general_gram_frob (sampleGram p X n ω)
  have hXm : ∀ i, Measurable (X i) := hiid.1
  have hFm : Measurable F := by
    dsimp [F, general_gram_frob, sampleGram]
    fun_prop
  have hmom := general_gram_frob_moment μ X hiid p horth ζ hrow n hn
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => general_gram_frob_nonneg (sampleGram p X n ω)))
    hmom.1 (1/4 : ℝ)
  have hbad : prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤ 4 * (ζ * (K : ℝ)/(n : ℝ)) := by
    change (1/4 : ℝ) * prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤ ∫ ω, F ω ∂μ at hmarkov
    have hweak : (∫ ω, F ω ∂μ) ≤ ζ * (K : ℝ)/(n : ℝ) := by
      exact hmom.2.trans (div_le_div_of_nonneg_right
        (sub_le_self _ (Nat.cast_nonneg K)) (Nat.cast_nonneg n))
    linarith
  have hmeas : MeasurableSet {ω | (1/4 : ℝ) ≤ F ω} :=
    measurableSet_le measurable_const hFm
  have hcomp : prob μ {ω | F ω < (1/4 : ℝ)} =
      1 - prob μ {ω | (1/4 : ℝ) ≤ F ω} := by
    have he : {ω | F ω < (1/4 : ℝ)} = {ω | (1/4 : ℝ) ≤ F ω}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [he]
    exact probReal_compl_eq_one_sub hmeas
  have hsub : {ω | F ω < (1/4 : ℝ)} ⊆ {ω | ∀ v : Fin K → ℝ,
      (1/2 : ℝ) * (∑ k, (v k)^2) ≤
        (∑ i ∈ Finset.range n, (∑ k, v k * (p k).eval (X i ω))^2)/(n : ℝ)} := by
    intro ω hω v
    rw [← general_gram_quadratic_identity p X n ω v]
    exact general_gram_frob_controls_quadratic (sampleGram p X n ω) hω.le v
  have hmono : prob μ {ω | F ω < (1/4 : ℝ)} ≤ prob μ {ω | ∀ v : Fin K → ℝ,
      (1/2 : ℝ) * (∑ k, (v k)^2) ≤
        (∑ i ∈ Finset.range n, (∑ k, v k * (p k).eval (X i ω))^2)/(n : ℝ)} :=
    measureReal_mono hsub
  rw [hcomp] at hmono
  linarith

theorem general_gram_rate_stability_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (p : ℕ → Polynomial ℝ)
   (horth : ∀ j k,mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω))=if j=k then 1 else 0)
   (J : ℕ → ℕ) (zeta2 : ℕ → ℝ)
   (hrow : ∀ n,∀ᵐ ω ∂μ,(∑ k : Fin (J n+1),((p k).eval (X 0 ω))^2) ≤ zeta2 n)
   (hrate : Tendsto (fun (n : ℕ) => zeta2 n*((J n+1 : ℕ) : ℝ)/(n : ℝ)) atTop (nhds 0)) :
   Tendsto (fun (n : ℕ) => prob μ {ω | ∀ v : Fin (J n+1) → ℝ,
     (1/2 : ℝ)*(∑ k,(v k)^2) ≤
       (∑ i∈Finset.range n,(∑ k : Fin (J n+1),v k*(p k).eval (X i ω))^2)/(n : ℝ)})
     atTop (nhds 1) := by
  have hlo : Tendsto (fun n : ℕ =>
      1 - 4 * (zeta2 n * ((J n+1 : ℕ) : ℝ)/(n : ℝ))) atTop (nhds 1) := by
    have hm := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4)).mul hrate
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hm
    simpa only [mul_zero, sub_zero] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have horth' (j k : Fin (J n+1)) :
        mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω)) =
          if j = k then 1 else 0 := by
      simpa only [Fin.ext_iff] using horth j.val k.val
    exact general_gram_good_probability_lower μ X hiid
      (fun k : Fin (J n+1) => p k) horth' (zeta2 n) (hrow n) n hn
  · exact Filter.Eventually.of_forall (fun n => measureReal_le_one)

example : type_of% @AronowAudit.P001.general_gram_rate_stability :=
  general_gram_rate_stability_proof

/-! ## Record 10: sieve_consistency_full_interval_support

Blocked on the new stable-Gram consistency proof, absent here.  The existing
wrapper inherits an unproved supporting declaration and is not used.
-/

/-! ## Record 13: uniform_cubic_gram_rate_stability

The preceding general rate proof is available.  The remaining dependency is
the uniform-interval row bound for an arbitrary successive-degree orthonormal
family, including affine transport and sign uniqueness.  Analytic facts about
the explicit shifted Legendre polynomials alone are not that row-bound theorem.
-/

/-- The explicitly specified real shifted Legendre polynomial, with the sign
convention of the pinned Mathlib integer polynomial. -/
private def uniform_cubic_shifted (k : ℕ) : Polynomial ℝ :=
  (Polynomial.shiftedLegendre k).map (Int.castRingHom ℝ)

/-- H-SHIFTED-LEGENDRE, as a plain proposition about the specified polynomials.
This definition asserts no theorem and contains no Gram conclusion. -/
private def uniform_cubic_legendre_input : Prop :=
  (∀ j k : ℕ,
    (∫ t in Set.Icc (0 : ℝ) 1,
      (uniform_cubic_shifted j).eval t * (uniform_cubic_shifted k).eval t) =
        if j = k then 1/(2*(k : ℝ)+1) else 0) ∧
  (∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) 1, |(uniform_cubic_shifted k).eval t| ≤ 1)

private def uniform_cubic_normalized (k : ℕ) : Polynomial ℝ :=
  Polynomial.C (Real.sqrt (2*(k : ℝ)+1)) * uniform_cubic_shifted k

private lemma uniform_cubic_normalized_degree (k : ℕ) :
    (uniform_cubic_normalized k).degree = k := by
  have hpos : 0 < 2*(k : ℝ)+1 := by positivity
  have hu : IsUnit (Real.sqrt (2*(k : ℝ)+1)) :=
    isUnit_iff_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
  rw [uniform_cubic_normalized, Polynomial.degree_C_mul_of_isUnit hu,
    uniform_cubic_shifted,
    Polynomial.degree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℝ) from
      Int.cast_injective), Polynomial.degree_shiftedLegendre]

private lemma uniform_cubic_normalized_orthogonal
    (hLegendre : uniform_cubic_legendre_input) (j k : ℕ) :
    (∫ t in Set.Icc (0 : ℝ) 1,
      (uniform_cubic_normalized j).eval t * (uniform_cubic_normalized k).eval t) =
        if j = k then 1 else 0 := by
  have he : (fun t : ℝ =>
      (uniform_cubic_normalized j).eval t * (uniform_cubic_normalized k).eval t) =
      (fun t : ℝ => (Real.sqrt (2*(j : ℝ)+1) * Real.sqrt (2*(k : ℝ)+1)) *
        ((uniform_cubic_shifted j).eval t * (uniform_cubic_shifted k).eval t)) := by
    funext t
    simp only [uniform_cubic_normalized, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [he, integral_const_mul, hLegendre.1 j k]
  by_cases hjk : j = k
  · subst j
    rw [if_pos rfl, if_pos rfl]
    have hpos : 0 < 2*(k : ℝ)+1 := by positivity
    rw [← pow_two, Real.sq_sqrt hpos.le]
    field_simp [hpos.ne']
  · simp only [if_neg hjk, mul_zero]

private lemma uniform_cubic_normalized_sq_le
    (hLegendre : uniform_cubic_legendre_input) (k : ℕ)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((uniform_cubic_normalized k).eval x)^2 ≤ 2*(k : ℝ)+1 := by
  have hbound := hLegendre.2 k x hx
  have hsq : ((uniform_cubic_shifted k).eval x)^2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg ((uniform_cubic_shifted k).eval x))
      (by norm_num : (0 : ℝ) ≤ 1)).mpr hbound
    simpa only [sq_abs, one_pow] using h
  have hpos : 0 ≤ 2*(k : ℝ)+1 := by positivity
  simp only [uniform_cubic_normalized, Polynomial.eval_mul, Polynomial.eval_C,
    mul_pow, Real.sq_sqrt hpos]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hpos

private lemma uniform_cubic_odd_sum (K : ℕ) :
    (∑ k : Fin K, (2*(k.val : ℝ)+1)) = (K : ℝ)^2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

/-- This proves the K² bound for the canonical normalized family.  Applying it
to the arbitrary family in the frozen targets still requires the polynomial
sign-uniqueness argument; that dependency is not assumed here. -/
private lemma uniform_cubic_canonical_row_bound
    (hLegendre : uniform_cubic_legendre_input) (K : ℕ)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑ k : Fin K, ((uniform_cubic_normalized k).eval x)^2) ≤ (K : ℝ)^2 := by
  calc
    (∑ k : Fin K, ((uniform_cubic_normalized k).eval x)^2) ≤
        ∑ k : Fin K, (2*(k.val : ℝ)+1) :=
      Finset.sum_le_sum (fun k _ => uniform_cubic_normalized_sq_le hLegendre k x hx)
    _ = (K : ℝ)^2 := uniform_cubic_odd_sum K

/-! ## Record 14: uniform_polynomial_gram_bound

The sharp fixed-n Gram-deviation estimate is supplied by
general_gram_finite_probability_bound above.  The arbitrary-family polynomial
sign-uniqueness dependency still prevents the final target from being stated
as a proved theorem.
-/

private lemma uniform_polynomial_unit_support {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (hx : μ.map X = uniformLaw 0 1) : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1 := by
  have hs : ∀ᵐ x ∂uniformLaw 0 1, x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [uniformLaw_zero_one_eq_restrict]
    exact ae_restrict_mem measurableSet_Icc
  apply ae_of_ae_map hX.aemeasurable
  rw [hx]
  exact hs

/-- Conditional canonical-family case, retained as a proved helper rather than
silently replacing the arbitrary p in the frozen target with Legendre p. -/
private lemma uniform_polynomial_canonical_probability_bound {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hLegendre : uniform_cubic_legendre_input)
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (hx : μ.map (X 0) = uniformLaw 0 1)
    (K n : ℕ) (hK : 0 < K) (hn : 0 < n) :
    prob μ {ω | 1/2 < gramDeviation
      (sampleGram (fun k : Fin K => uniform_cubic_normalized k) X n ω)} ≤
        4*((K : ℝ)^3-K)/n := by
  let p : Fin K → Polynomial ℝ := fun k => uniform_cubic_normalized k
  have horth (j k : Fin K) : mean μ (fun ω =>
      (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) = if j = k then 1 else 0 := by
    let f : ℝ → ℝ := fun x => (p j).eval x * (p k).eval x
    have hf : StronglyMeasurable f :=
      ((p j).continuous.mul (p k).continuous).stronglyMeasurable
    have hi := integral_map_of_stronglyMeasurable (μ := μ) (hiid.1 0) hf
    change (∫ ω, f (X 0 ω) ∂μ) = _
    rw [← hi, hx, uniformLaw_zero_one_eq_restrict]
    simpa only [f, p, Fin.ext_iff] using uniform_cubic_normalized_orthogonal hLegendre j k
  have hrow : ∀ᵐ ω ∂μ, (∑ k, ((p k).eval (X 0 ω))^2) ≤ (K : ℝ)^2 := by
    filter_upwards [uniform_polynomial_unit_support μ (X 0) (hiid.1 0) hx] with ω hω
    exact uniform_cubic_canonical_row_bound hLegendre K (X 0 ω) hω
  have hb := general_gram_finite_probability_bound μ hK X hiid p horth
    ((K : ℝ)^2) hrow n hn
  have halg : 4*((K : ℝ)^2*(K : ℝ)-K)/(n : ℝ) = 4*((K : ℝ)^3-K)/n := by ring
  simpa only [halg, p] using hb

end

end AronowAudit.P001.Wave1
