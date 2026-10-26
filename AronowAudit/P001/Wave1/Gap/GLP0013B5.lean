import AronowAudit.P001.P001_Foundations
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGLP0013B5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! Frobenius second moments and Markov's inequality. -/

private def p001t6gram_frob {K : ℕ} (G : Matrix (Fin K) (Fin K) ℝ) : ℝ :=
  ∑ j, ∑ k, (G j k - if j = k then 1 else 0)^2

private lemma p001t6gram_frob_nonneg {K : ℕ}
    (G : Matrix (Fin K) (Fin K) ℝ) : 0 ≤ p001t6gram_frob G := by
  exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))

private lemma p001t6gram_product_bound {K : ℕ} (z : Fin K → ℝ)
    (j k : Fin K) : |z j * z k| ≤ ∑ l, (z l)^2 := by
  have hj : (z j)^2 ≤ ∑ l, (z l)^2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (z l)) (Finset.mem_univ j)
  have hk : (z k)^2 ≤ ∑ l, (z l)^2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (z l)) (Finset.mem_univ k)
  rw [abs_mul]
  nlinarith [sq_nonneg (|z j| - |z k|), sq_abs (z j), sq_abs (z k)]


private lemma p001t6gram_frob_controls_quadratic {K : ℕ}
    (G : Matrix (Fin K) (Fin K) ℝ) (hG : p001t6gram_frob G ≤ 1/4)
    (v : Fin K → ℝ) :
    (1/2 : ℝ) * (∑ k, (v k)^2) ≤ ∑ j, ∑ k, v j * G j k * v k := by
  classical
  let A : Matrix (Fin K) (Fin K) ℝ := fun j k => G j k - if j = k then 1 else 0
  let S : ℝ := ∑ k, (v k)^2
  let D : ℝ := ∑ j, ∑ k, A j k * (v j * v k)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hCS : D^2 ≤ p001t6gram_frob G * S^2 := by
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
    simpa only [Fintype.sum_prod_type, D, p001t6gram_frob, A, hVV] using h
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

private lemma p001t6gram_frob_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (p : Fin K → Polynomial ℝ)
    (horth : ∀ j k, mean μ (fun ω =>
      (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) = if j = k then 1 else 0)
    (ζ : ℝ) (hrow : ∀ᵐ ω ∂μ, (∑ k, ((p k).eval (X 0 ω))^2) ≤ ζ)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ω => p001t6gram_frob (sampleGram p X n ω)) μ ∧
    (∫ ω, p001t6gram_frob (sampleGram p X n ω) ∂μ) ≤ (ζ * (K : ℝ)-K)/(n : ℝ) := by
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
    exact (p001t6gram_product_bound (fun l => (p l).eval (X 0 ω)) j k).trans hω
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
  have hFint : Integrable (fun ω => p001t6gram_frob (sampleGram p X n ω)) μ := by
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
    (∫ ω, p001t6gram_frob (sampleGram p X n ω) ∂μ) =
        ∑ j, ∑ k, var μ (Y j k 0)/(n : ℝ) := by
      unfold p001t6gram_frob
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

private lemma p001t6gram_deviation_le_half {K : ℕ} (hK : 0 < K)
    (G : Matrix (Fin K) (Fin K) ℝ) (hG : p001t6gram_frob G ≤ 1/4) :
    gramDeviation G ≤ 1/2 := by
  classical
  let H : Matrix (Fin K) (Fin K) ℝ :=
    fun j k => 2 * (if j = k then 1 else 0) - G j k
  have hHF : p001t6gram_frob H = p001t6gram_frob G := by
    unfold p001t6gram_frob
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [H]
    split_ifs <;> ring
  have hunit (v : Fin K → ℝ) (hv : (∑ k, (v k)^2) = 1) :
      |(∑ j, ∑ k, v j * G j k * v k) - 1| ≤ 1/2 := by
    have hlo := p001t6gram_frob_controls_quadratic G hG v
    have hhi := p001t6gram_frob_controls_quadratic H (by rw [hHF]; exact hG) v
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

/-- The fixed-n probability bound follows from the same elementary moment calculation. -/
theorem general_polynomial_gram_probability_bound_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K : ℕ} (hK : 0 < K) (X : ℕ → Ω → ℝ) (hiid : IID μ X)
   (p : Fin K → Polynomial ℝ)
   (horth : ∀ j k,mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω))=if j=k then 1 else 0)
   (ζ2 : ℝ) (hrow : ∀ᵐ ω ∂μ,(∑ k,((p k).eval (X 0 ω))^2) ≤ ζ2)
   (n : ℕ) (hn : 0 < n) :
   prob μ {ω | 1/2 < gramDeviation (sampleGram p X n ω)} ≤ 4*(ζ2*(K : ℝ)-K)/(n : ℝ) := by
  let F : Ω → ℝ := fun ω => p001t6gram_frob (sampleGram p X n ω)
  have hmom := p001t6gram_frob_moment μ X hiid p horth ζ2 hrow n hn
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => p001t6gram_frob_nonneg (sampleGram p X n ω)))
    hmom.1 (1/4 : ℝ)
  have hbad : prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤
      4 * (ζ2 * (K : ℝ)-K)/(n : ℝ) := by
    change (1/4 : ℝ) * prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤ ∫ ω, F ω ∂μ at hmarkov
    calc
      prob μ {ω | (1/4 : ℝ) ≤ F ω} ≤ 4 * ((ζ2 * (K : ℝ)-K)/(n : ℝ)) := by
        linarith [hmom.2]
      _ = 4 * (ζ2 * (K : ℝ)-K)/(n : ℝ) := by ring
  have hsub : {ω | 1/2 < gramDeviation (sampleGram p X n ω)} ⊆
      {ω | (1/4 : ℝ) ≤ F ω} := by
    intro ω hω
    by_contra hnot
    have hsmall : p001t6gram_frob (sampleGram p X n ω) ≤ 1/4 :=
      (lt_of_not_ge hnot).le
    exact (not_lt_of_ge (p001t6gram_deviation_le_half hK _ hsmall)) hω
  have hm : prob μ {ω | 1/2 < gramDeviation (sampleGram p X n ω)} ≤
      prob μ {ω | (1/4 : ℝ) ≤ F ω} := measureReal_mono hsub
  exact hm.trans hbad

/-! Compact support, conditional moments, and least-squares bounds. -/

private lemma p001t6consistent_compact_lp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (a b : ℝ) (hs : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (f : ℝ → ℝ)
    (hf : Measurable f) (hc : ContinuousOn f (Set.Icc a b)) (r : ℝ≥0∞) :
    MemLp (fun ω => f (X ω)) r μ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact MemLp.of_bound (hf.comp hX).aestronglyMeasurable C (hs.mono (fun ω hω => hC _ hω))

private lemma p001t6consistent_condvar {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (U : Ω → ℝ) (hU : MemLp U 2 μ) (V : ℝ)
    (hvar : ∀ A : Set ℝ, MeasurableSet A →
      (∫ ω in X ⁻¹' A, (U ω)^2 ∂μ) ≤ V * prob μ (X ⁻¹' A)) :
    μ[(fun ω => (U ω)^2) | MeasurableSpace.comap X inferInstance] ≤ᵐ[μ] fun _ => V := by
  have hle := hX.comap_le
  have hsm := stronglyMeasurable_condExp (μ := μ) (m := MeasurableSpace.comap X inferInstance)
    (f := fun ω => (U ω)^2)
  apply ae_of_ae_trim hle
  apply ae_le_of_forall_setIntegral_le (integrable_condExp.trim hle hsm) (integrable_const V)
  intro B hB _
  rw [← setIntegral_trim hle hsm hB, setIntegral_condExp hle hU.integrable_sq hB,
    ← setIntegral_trim hle stronglyMeasurable_const hB]
  obtain ⟨A, hA, rfl⟩ := hB
  simpa only [setIntegral_const, smul_eq_mul, prob, measureReal_def, mul_comm] using hvar A hA

private lemma p001t6consistent_weighted_second {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (U : Ω → ℝ) (hU : MemLp U 2 μ) (V : ℝ)
    (hvar : ∀ A : Set ℝ, MeasurableSet A →
      (∫ ω in X ⁻¹' A, (U ω)^2 ∂μ) ≤ V * prob μ (X ⁻¹' A))
    (w : ℝ → ℝ) (hw : Measurable w) (C : ℝ)
    (hbound : ∀ᵐ ω ∂μ, ‖w (X ω)‖ ≤ C) :
    (∫ ω, (w (X ω)*U ω)^2 ∂μ) ≤ V * ∫ ω, (w (X ω))^2 ∂μ := by
  let W : Ω → ℝ := fun ω => (w (X ω))^2
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  have hWm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] W :=
    ((hw.comp hXm).pow_const 2).stronglyMeasurable
  have hWbound : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ C^2 := by
    filter_upwards [hbound] with ω hω
    change ‖(w (X ω))^2‖ ≤ _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hω 2
  have hCE := p001t6consistent_condvar μ X hX U hU V hvar
  have hWU : Integrable (fun ω => W ω*(U ω)^2) μ :=
    hU.integrable_sq.bdd_mul (hWm.mono hX.comap_le).aestronglyMeasurable hWbound
  have hWC : Integrable (fun ω => W ω*μ[(fun ω => (U ω)^2) | MeasurableSpace.comap X inferInstance] ω) μ :=
    integrable_condExp.bdd_mul (hWm.mono hX.comap_le).aestronglyMeasurable hWbound
  have hWi : Integrable W μ :=
    (MemLp.of_bound (hWm.mono hX.comap_le).aestronglyMeasurable (C^2) hWbound (p := 1)).integrable le_rfl
  have hpull := condExp_mul_of_stronglyMeasurable_left hWm hWU hU.integrable_sq
  have he : (∫ ω, W ω*(U ω)^2 ∂μ) =
      ∫ ω, W ω*μ[(fun ω => (U ω)^2) | MeasurableSpace.comap X inferInstance] ω ∂μ := by
    rw [← integral_condExp hX.comap_le (f := fun ω => W ω*(U ω)^2)]
    apply integral_congr_ae
    simpa only [Pi.mul_def] using hpull
  calc
    (∫ ω, (w (X ω)*U ω)^2 ∂μ) = ∫ ω, W ω*(U ω)^2 ∂μ := by
      congr 1; funext ω; dsimp [W]; ring
    _ = _ := he
    _ ≤ ∫ ω, V*W ω ∂μ := by
      apply integral_mono_ae hWC (hWi.const_mul V)
      filter_upwards [hCE] with ω hω
      exact (mul_le_mul_of_nonneg_left hω (sq_nonneg _)).trans_eq (mul_comm _ _)
    _ = V*∫ ω, (w (X ω))^2 ∂μ := integral_const_mul _ _

private lemma p001t6consistent_span (p : ℕ → Polynomial ℝ)
    (hdeg : ∀ k, (p k).natDegree = k) (hp0 : p 0 ≠ 0) (d : ℕ)
    (q : Polynomial ℝ) (hq : q.natDegree ≤ d) :
    ∃ b : Fin (d+1) → ℝ, q = ∑ k, b k • p k := by
  have hpne (k : ℕ) : p k ≠ 0 := by
    by_cases hk : k = 0
    · simpa [hk] using hp0
    · intro hz
      have hh := hdeg k
      rw [hz, Polynomial.natDegree_zero] at hh
      exact hk hh.symm
  let S : Polynomial.Sequence ℝ := ⟨p, fun k => by
    rw [Polynomial.degree_eq_natDegree (hpne k), hdeg k]⟩
  have hspan := S.span_degreeLE (m := d) (fun k _ => isUnit_iff_ne_zero.mpr
    (Polynomial.leadingCoeff_ne_zero.mpr (hpne k)))
  have hrange : S '' Set.Iic d = Set.range (fun k : Fin (d+1) => p k) := by
    ext r
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, by simpa only [Set.mem_Iic, Nat.lt_succ_iff] using hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, Nat.le_of_lt_succ k.isLt, rfl⟩
  rw [hrange] at hspan
  have hmem : q ∈ Submodule.span ℝ (Set.range (fun k : Fin (d+1) => p k)) := by
    rw [hspan, Polynomial.mem_degreeLE]
    exact (Polynomial.degree_le_natDegree).trans (by exact_mod_cast hq)
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  exact ⟨b, hb.symm⟩

private lemma p001t6consistent_empirical_bound {n K : ℕ} (hn : 0 < n)
    (P : Matrix (Fin n) (Fin K) ℝ) (α : Fin K → ℝ) (r u : Fin n → ℝ)
    (η c : ℝ) (hη : 0 ≤ η) (hc : 0 < c)
    (hr : ∀ i, |r i| ≤ η)
    (hgram : c*(∑ k, (α k)^2) ≤ (∑ i, (P.mulVec α i)^2)/(n : ℝ))
    (hmin : (∑ i, (u i+r i-P.mulVec α i)^2) ≤ ∑ i, (u i+r i)^2) :
    (∑ k, (α k)^2) ≤ 16/c^2*(∑ k, ((∑ i, P i k*u i)/(n : ℝ))^2)+8/c*η^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let D := ∑ i, (P.mulVec α i)^2
  let A := ∑ k, (α k)^2
  let s : Fin K → ℝ := fun k => (∑ i, P i k*u i)/(n : ℝ)
  let T := ∑ k, (s k)^2
  have hsum : (∑ i, (u i+r i-P.mulVec α i)^2) =
      (∑ i, (u i+r i)^2)+D-((∑ i, 2*u i*P.mulVec α i)+(∑ i, 2*r i*P.mulVec α i)) := by
    dsimp [D]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrem : (∑ i, 2*r i*P.mulVec α i) ≤ D/2+2*(n : ℝ)*η^2 := by
    have hpt (i : Fin n) : 2*r i*P.mulVec α i ≤ (P.mulVec α i)^2/2+2*η^2 := by
      have hs : (r i)^2 ≤ η^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hη).mpr (hr i)
      nlinarith [sq_nonneg (P.mulVec α i-2*r i)]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpt i)
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    dsimp [D]
    nlinarith [hh]
  have hcross : (∑ i, 2*u i*P.mulVec α i)/(n : ℝ) = 2*∑ k, α k*s k := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_div, s]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hyoung : 2*∑ k, α k*s k ≤ c/4*A+4/c*T := by
    have hpt (k : Fin K) : 2*α k*s k ≤ c/4*(α k)^2+4/c*(s k)^2 := by
      calc
        2*α k*s k ≤ ((c/4*(α k)^2)*c+4*(s k)^2)/c :=
          (le_div_iff₀ hc).mpr (by nlinarith [sq_nonneg (c*α k-4*s k)])
        _ = _ := by field_simp <;> ring
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hpt k)
    simpa only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, A, T] using hh
  have hbase : c/4*A ≤ 4/c*T+2*η^2 := by
    have hmin' : D ≤ (∑ i, 2*u i*P.mulVec α i)+(∑ i, 2*r i*P.mulVec α i) := by
      rw [hsum] at hmin
      linarith
    have hscaled := (div_le_div_of_nonneg_right hmin' hnR.le).trans
      (div_le_div_of_nonneg_right (add_le_add (le_refl _) hrem) hnR.le)
    rw [add_div, hcross] at hscaled
    have hcanc : (D/2+2*(n : ℝ)*η^2)/(n : ℝ) = (D/(n : ℝ))/2+2*η^2 := by
      field_simp <;> ring
    rw [hcanc] at hscaled
    change c*A ≤ D/(n : ℝ) at hgram
    nlinarith
  calc
    A ≤ (4/c*T+2*η^2)/(c/4) := (le_div_iff₀ (div_pos hc (by norm_num))).mpr (by nlinarith [hbase])
    _ = 16/c^2*T+8/c*η^2 := by field_simp <;> ring

private lemma p001t6consistent_risk_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (a b : ℝ) (hs : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (m : ℝ → ℝ) (hmm : Measurable m) (hm : ContinuousOn m (Set.Icc a b))
    (p : ℕ → Polynomial ℝ) (hdeg : ∀ k, (p k).natDegree = k)
    (horth : ∀ j k, mean μ (fun ω => (p j).eval (X ω)*(p k).eval (X ω)) = if j=k then 1 else 0)
    {n d : ℕ} (hn : 0 < n) (x y : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc a b)
    (f q : Polynomial ℝ) (hf : f.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (hmin : ∀ t : Polynomial ℝ, t.natDegree ≤ d →
      (∑ i, (y i-f.eval (x i))^2) ≤ ∑ i, (y i-t.eval (x i))^2)
    (η c : ℝ) (hη : 0 ≤ η) (hc : 0 < c)
    (happrox : ∀ t ∈ Set.Icc a b, |m t-q.eval t| ≤ η)
    (hgram : ∀ v : Fin (d+1) → ℝ, c*(∑ k, (v k)^2) ≤
      (∑ i, (∑ k, v k*(p k).eval (x i))^2)/(n : ℝ)) :
    (∫ t, (f.eval t-m t)^2 ∂(μ.map X)) ≤
      32/c^2*(∑ k : Fin (d+1), ((∑ i, (p k).eval (x i)*(y i-m (x i)))/(n : ℝ))^2)+
        (16/c+2)*η^2 := by
  have hp0 : p 0 ≠ 0 := by
    intro hz
    have hh := horth 0 0
    simp [hz, mean] at hh
  obtain ⟨bf, hbf⟩ := p001t6consistent_span p hdeg hp0 d f hf
  obtain ⟨bq, hbq⟩ := p001t6consistent_span p hdeg hp0 d q hq
  let α := bf-bq
  let P : Matrix (Fin n) (Fin (d+1)) ℝ := fun i k => (p k).eval (x i)
  let r : Fin n → ℝ := fun i => m (x i)-q.eval (x i)
  let u : Fin n → ℝ := fun i => y i-m (x i)
  have heval (t : ℝ) : f.eval t-q.eval t = ∑ k, α k*(p k).eval t := by
    rw [hbf, hbq]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul, α,
      Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hPα (i : Fin n) : P.mulVec α i = f.eval (x i)-q.eval (x i) := by
    rw [heval]
    dsimp [P, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hα := p001t6consistent_empirical_bound hn P α r u η c hη hc
    (fun i => happrox _ (hx i)) (by simpa only [P, Matrix.mulVec, dotProduct, mul_comm] using hgram α)
    (by simpa only [u, r, hPα, sub_sub_sub_cancel_right, sub_add_sub_cancel] using hmin q hq)
  have hnorm : (∫ ω, (f.eval (X ω)-q.eval (X ω))^2 ∂μ) = ∑ k, (α k)^2 := by
    simp_rw [heval]
    have hp (k : Fin (d+1)) := p001t6consistent_compact_lp μ X hX a b hs
      (fun x => (p k).eval x) (p k).continuous.measurable (p k).continuous.continuousOn (2 : ℝ≥0∞)
    have hi (j k : Fin (d+1)) : Integrable
        (fun ω => α j*α k*((p j).eval (X ω)*(p k).eval (X ω))) μ :=
      ((hp j).integrable_mul (hp k)).const_mul _
    simp only [pow_two, Finset.sum_mul_sum]
    simp_rw [show ∀ j k ω, (α j*(p j).eval (X ω))*(α k*(p k).eval (X ω)) =
      α j*α k*((p j).eval (X ω)*(p k).eval (X ω)) by intros; ring]
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
    simp_rw [integral_finsetSum _ (fun k _ => hi _ k), integral_const_mul]
    have hh (j k : Fin (d+1)) : (∫ ω, (p j).eval (X ω)*(p k).eval (X ω) ∂μ) =
        if j=k then 1 else 0 := by simpa only [mean, Fin.ext_iff] using horth j k
    simp [hh, pow_two]
  have hf2 := p001t6consistent_compact_lp μ X hX a b hs (fun x => f.eval x)
    f.continuous.measurable f.continuous.continuousOn (2 : ℝ≥0∞)
  have hq2 := p001t6consistent_compact_lp μ X hX a b hs (fun x => q.eval x)
    q.continuous.measurable q.continuous.continuousOn (2 : ℝ≥0∞)
  have hm2 := p001t6consistent_compact_lp μ X hX a b hs m hmm hm (2 : ℝ≥0∞)
  have hR : (∫ ω, (f.eval (X ω)-m (X ω))^2 ∂μ) ≤ 2*(∑ k, (α k)^2)+2*η^2 := by
    calc
      (∫ ω, (f.eval (X ω)-m (X ω))^2 ∂μ) ≤
          ∫ ω, 2*(f.eval (X ω)-q.eval (X ω))^2+2*η^2 ∂μ := by
        apply integral_mono_ae (hf2.sub hm2).integrable_sq
          (((hf2.sub hq2).integrable_sq.const_mul 2).add (integrable_const _))
        filter_upwards [hs] with ω hω
        have hb : (m (X ω)-q.eval (X ω))^2 ≤ η^2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hη).mpr (happrox _ hω)
        change (f.eval (X ω)-m (X ω))^2 ≤ 2*(f.eval (X ω)-q.eval (X ω))^2+2*η^2
        nlinarith [sq_nonneg (f.eval (X ω)-q.eval (X ω)+(m (X ω)-q.eval (X ω)))]
      _ = _ := by rw [integral_add (show Integrable (fun ω => 2*(f.eval (X ω)-q.eval (X ω))^2) μ from (hf2.sub hq2).integrable_sq.const_mul 2) (integrable_const _),
        integral_const_mul, hnorm]; simp
  have hmap : AEStronglyMeasurable (fun t => (f.eval t-m t)^2) (μ.map X) := by fun_prop
  rw [integral_map hX.aemeasurable hmap]
  dsimp [P, u] at hα
  calc
    _ ≤ 2*(∑ k, (α k)^2)+2*η^2 := hR
    _ ≤ 2*(16/c^2*(∑ k : Fin (d+1), ((∑ i, (p k).eval (x i)*(y i-m (x i)))/(n : ℝ))^2)+8/c*η^2)+2*η^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hα (by norm_num : (0 : ℝ) ≤ 2)) (le_refl _)
    _ = _ := by ring

theorem sieve_consistency_stable_gram_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X Y : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
   (a b V : ℝ) (hab : a  <  b) (hV : 0  ≤  V) (hY2 : MemLp (Y 0) 2 μ)
   (fX : ℝ → ℝ) (hfX : HasPDF (μ.map (X 0)) fX)
   (hfullsupport : paperSupport fX=Set.Icc a b)
   (hsupp : ∀ᵐ ω ∂μ, X 0 ω ∈ Set.Icc a b)
   (m : ℝ → ℝ) (hm : ContinuousOn m (Set.Icc a b)) (hcef : IsCEF μ (X 0) (Y 0) m)
   (hvar : ∀ A : Set ℝ, MeasurableSet A →
     (∫ ω in (X 0) ⁻¹' A, (Y 0 ω-m (X 0 ω))^2 ∂μ)  ≤  V * prob μ ((X 0) ⁻¹' A))
   (p : ℕ → Polynomial ℝ) (hdeg : ∀ k, (p k).natDegree = k)
   (horth : ∀ j k, mean μ (fun ω => (p j).eval (X 0 ω)*(p k).eval (X 0 ω)) = if j=k then 1 else 0)
   (J : ℕ → ℕ) (hJ : Tendsto J atTop atTop)
   (hrate : Tendsto (fun (n : ℕ) => ((J n+1 : ℕ) : ℝ)/n) atTop (nhds 0))
   (c : ℝ) (hc : 0  <  c)
   (hgram : Tendsto (fun (n : ℕ) => prob μ {ω | ∀ v : Fin (J n+1) → ℝ,
     c*(∑ k, (v k)^2)  ≤  (∑ i ∈ Finset.range n,
       (∑ k : Fin (J n+1), v k*(p k).eval (X i ω))^2)/(n : ℝ)}) atTop (nhds 1))
   (fit : ℕ → Ω → Polynomial ℝ) (hfit : IsSieveLS X Y J fit) :
   CP μ (fun n ω => ∫ x, ((fit n ω).eval x-m x)^2 ∂(μ.map (X 0))) 0 := by
  have hX (i : ℕ) : Measurable (X i) := (hiid.1 i).fst
  have hY (i : ℕ) : Measurable (Y i) := (hiid.1 i).snd
  have hXi : IID μ X := ⟨hX, hiid.2.1.comp (fun _ => Prod.fst) (fun _ => measurable_fst),
    fun i => (hiid.2.2 i).comp (u := Prod.fst) measurable_fst⟩
  have hmall := p001t6consistent_compact_lp μ (X 0) (hX 0) a b hsupp m hcef.1 hm (2 : ℝ≥0∞)
  let U : ℕ → Ω → ℝ := fun i ω => Y i ω-m (X i ω)
  have hU2 : MemLp (U 0) 2 μ := hY2.sub hmall
  have hres := cef_residual_orthogonality_correction μ (X 0) (hX 0) (Y 0) hY2 m hcef hmall
  let Z : ℕ → ℕ → Ω → ℝ := fun k i ω => (p k).eval (X i ω)*U i ω
  have hZi (k : ℕ) : IID μ (Z k) := by
    let f : ℝ × ℝ → ℝ := fun xy => (p k).eval xy.1*(xy.2-m xy.1)
    have hf : Measurable f := ((p k).continuous.measurable.comp measurable_fst).mul
      (measurable_snd.sub (hcef.1.comp measurable_fst))
    exact ⟨fun i => hf.comp (hiid.1 i), hiid.2.1.comp (fun _ => f) (fun _ => hf),
      fun i => (hiid.2.2 i).comp (u := f) hf⟩
  have hZ2 (k : ℕ) : MemLp (Z k 0) 2 μ := by
    have hw := p001t6consistent_compact_lp μ (X 0) (hX 0) a b hsupp
      (fun x => (p k).eval x) (p k).continuous.measurable (p k).continuous.continuousOn (∞ : ℝ≥0∞)
    exact hw.mul hU2
  have hZ0 (k : ℕ) : mean μ (Z k 0) = 0 := by
    have hw := p001t6consistent_compact_lp μ (X 0) (hX 0) a b hsupp
      (fun x => (p k).eval x) (p k).continuous.measurable (p k).continuous.continuousOn (2 : ℝ≥0∞)
    have hh := hres.2.2 (fun x => (p k).eval x) (p k).continuous.measurable hw
    change covariance (fun ω => (p k).eval (X 0 ω)) (U 0) μ = 0 at hh
    rw [covariance_eq_sub hw hU2] at hh
    change mean μ (Z k 0)-mean μ (fun ω => (p k).eval (X 0 ω))*mean μ (U 0) = 0 at hh
    have hu : mean μ (U 0) = 0 := hres.2.1
    simpa only [hu, mul_zero, sub_zero] using hh
  have hZv (k : ℕ) : var μ (Z k 0) ≤ V := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (p k).continuous.continuousOn
    have hb : ∀ᵐ ω ∂μ, ‖(p k).eval (X 0 ω)‖ ≤ C := hsupp.mono (fun ω hω => hC _ hω)
    have hh := p001t6consistent_weighted_second μ (X 0) (hX 0) (U 0) hU2 V hvar
      (fun x => (p k).eval x) (p k).continuous.measurable C hb
    have hd : (∫ ω, ((p k).eval (X 0 ω))^2 ∂μ) = 1 := by
      simpa [mean, pow_two] using horth k k
    rw [hd, mul_one] at hh
    change variance (Z k 0) μ ≤ V
    rw [variance_eq_sub (hZ2 k)]
    change (∫ ω, (Z k 0 ω)^2 ∂μ)-(∫ ω, Z k 0 ω ∂μ)^2 ≤ V
    have hz : (∫ ω, Z k 0 ω ∂μ) = 0 := hZ0 k
    rw [hz]
    simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero] using hh
  let T : ℕ → Ω → ℝ := fun n ω => ∑ k : Fin (J n+1), (sampleMean (Z k) n ω)^2
  have hTnonneg (n : ℕ) (ω : Ω) : 0 ≤ T n ω := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hTint (n : ℕ) : Integrable (T n) μ :=
    integrable_finsetSum _ (fun k _ => (sample_mean_memLp μ (Z k) (hZi k) (hZ2 k) n).integrable_sq)
  have hTmean (n : ℕ) (hn : 0 < n) : (∫ ω, T n ω ∂μ) ≤ V*((J n+1 : ℕ) : ℝ)/(n : ℝ) := by
    have hentry (k : Fin (J n+1)) :
        (∫ ω, (sampleMean (Z k) n ω)^2 ∂μ) ≤ V/(n : ℝ) := by
      have hmom := iid_sample_mean_finite_moments μ (Z k) (hZi k) (hZ2 k) n hn
      have hm0 : mean μ (sampleMean (Z k) n) = 0 := hmom.1.trans (hZ0 k)
      have hnorm := (variance_eq_integral
        (sample_mean_memLp μ (Z k) (hZi k) (hZ2 k) n).aestronglyMeasurable.aemeasurable).symm
      change (∫ ω, (sampleMean (Z k) n ω-mean μ (sampleMean (Z k) n))^2 ∂μ) =
        var μ (sampleMean (Z k) n) at hnorm
      rw [hm0] at hnorm
      simp only [sub_zero] at hnorm
      rw [hnorm, hmom.2]
      exact div_le_div_of_nonneg_right (hZv k) (Nat.cast_nonneg n)
    dsimp [T]
    rw [integral_finsetSum _ (fun (k : Fin (J n+1)) _ =>
      (sample_mean_memLp μ (Z k) (hZi k) (hZ2 k) n).integrable_sq)]
    calc
      _ ≤ ∑ _ : Fin (J n+1), V/(n : ℝ) := Finset.sum_le_sum (fun k _ => hentry k)
      _ = _ := by simp; ring
  have hTtail (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => prob μ {ω | δ ≤ T n ω}) atTop (nhds 0) := by
    have hupp : ∀ᶠ n : ℕ in atTop, prob μ {ω | δ ≤ T n ω} ≤
        (V/δ)*(((J n+1 : ℕ) : ℝ)/(n : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hh := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ (hTnonneg n)) (hTint n) δ
      change δ*prob μ {ω | δ ≤ T n ω} ≤ ∫ ω, T n ω ∂μ at hh
      have hb : prob μ {ω | δ ≤ T n ω} ≤ (V*((J n+1 : ℕ) : ℝ)/(n : ℝ))/δ :=
        (le_div_iff₀ hδ).mpr (by nlinarith [hTmean n hn])
      exact hb.trans_eq (by ring)
    exact squeeze_zero' (Eventually.of_forall (fun n => ENNReal.toReal_nonneg)) hupp
      (by simpa using tendsto_const_nhds.mul hrate)
  let Good : ℕ → Set Ω := fun n => {ω | ∀ v : Fin (J n+1) → ℝ,
    c*(∑ k, (v k)^2) ≤ (∑ i ∈ Finset.range n,
      (∑ k : Fin (J n+1), v k*(p k).eval (X i ω))^2)/(n : ℝ)}
  have hGood (n : ℕ) : MeasurableSet (Good n) := by
    let R : Ω → Matrix (Fin n) (Fin (J n+1)) ℝ := fun ω i k => (p k).eval (X i ω)
    have hRm : Measurable R := by
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro k
      exact (p k).continuous.measurable.comp (hX i)
    have hclosed : IsClosed {P : Matrix (Fin n) (Fin (J n+1)) ℝ | ∀ v : Fin (J n+1) → ℝ,
        c*(∑ k, (v k)^2) ≤ (∑ i, (P.mulVec v i)^2)/(n : ℝ)} := by
      simp only [Set.setOf_forall]
      apply isClosed_iInter
      intro v
      exact isClosed_le continuous_const (by unfold Matrix.mulVec dotProduct; fun_prop)
    have heq : Good n = R ⁻¹' {P | ∀ v : Fin (J n+1) → ℝ,
        c*(∑ k, (v k)^2) ≤ (∑ i, (P.mulVec v i)^2)/(n : ℝ)} := by
      ext ω
      change (∀ v : Fin (J n+1) → ℝ, c*(∑ k, (v k)^2) ≤
        (∑ i ∈ Finset.range n, (∑ k : Fin (J n+1), v k*(p k).eval (X i ω))^2)/(n : ℝ)) ↔
        ∀ v : Fin (J n+1) → ℝ, c*(∑ k, (v k)^2) ≤ (∑ i, ((R ω).mulVec v i)^2)/(n : ℝ)
      have hrow (v : Fin (J n+1) → ℝ) (i : Fin n) :
          (R ω).mulVec v i = ∑ k : Fin (J n+1), v k*(p k).eval (X i ω) := by
        dsimp [R, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
      have hsum (v : Fin (J n+1) → ℝ) : (∑ i, ((R ω).mulVec v i)^2) =
          ∑ i ∈ Finset.range n, (∑ k : Fin (J n+1), v k*(p k).eval (X i ω))^2 := by
        simp_rw [hrow]
        exact Fin.sum_univ_eq_sum_range
          (fun i : ℕ => (∑ k : Fin (J n+1), v k*(p k).eval (X i ω))^2) n
      simp only [hsum]
    rw [heq]
    exact hclosed.measurableSet.preimage hRm
  have hbad : Tendsto (fun n => prob μ (Good n)ᶜ) atTop (nhds 0) := by
    have he (n : ℕ) : prob μ (Good n)ᶜ = 1-prob μ (Good n) := by
      simpa [prob, measureReal_def] using measureReal_compl (μ := μ) (hGood n)
    simp_rw [he]
    simpa only [Good, sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hgram
  have hsall : ∀ᵐ ω ∂μ, ∀ i : ℕ, X i ω ∈ Set.Icc a b := by
    apply ae_all_iff.mpr
    intro i
    exact (hXi.2.2 i).symm.ae_mem_snd measurableSet_Icc hsupp
  let S : Set Ω := {ω | ∀ i : ℕ, X i ω ∈ Set.Icc a b}
  have hSzero : prob μ Sᶜ = 0 := by
    change (μ Sᶜ).toReal = 0
    have hh : μ Sᶜ = 0 := by
      change μ {ω | ¬∀ i : ℕ, X i ω ∈ Set.Icc a b} = 0
      exact ae_iff.mp hsall
    simp [hh]
  intro ε hε
  let L : ℝ := 16/c+2
  have hL : 0 < L := by dsimp [L]; positivity
  let η : ℝ := Real.sqrt (ε/(4*L))
  have hη : 0 < η := Real.sqrt_pos.mpr (div_pos hε (by positivity))
  have hηsq : η^2 = ε/(4*L) := Real.sq_sqrt (by positivity)
  obtain ⟨q, hq⟩ := weierstrass_approximation a b hab.le m hm η hη
  let δ : ℝ := ε*c^2/64
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbound : ∀ᶠ n : ℕ in atTop,
      prob μ {ω | ε ≤ dist (∫ x, ((fit n ω).eval x-m x)^2 ∂(μ.map (X 0))) 0} ≤
        prob μ (Good n)ᶜ+prob μ {ω | δ ≤ T n ω} := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), (tendsto_atTop.1 hJ) q.natDegree] with n hn hnq
    have hsub : {ω | ε ≤ dist (∫ x, ((fit n ω).eval x-m x)^2 ∂(μ.map (X 0))) 0} ⊆
        ((Good n)ᶜ ∪ {ω | δ ≤ T n ω}) ∪ Sᶜ := by
      intro ω hω
      by_cases hSω : ω ∈ S
      swap
      · exact Or.inr hSω
      by_cases hg : ω ∈ Good n
      swap
      · exact Or.inl (Or.inl hg)
      by_cases hT : δ ≤ T n ω
      · exact Or.inl (Or.inr hT)
      have hmin : ∀ t : Polynomial ℝ, t.natDegree ≤ J n →
          (∑ i : Fin n, (Y i ω-(fit n ω).eval (X i ω))^2) ≤
            ∑ i : Fin n, (Y i ω-t.eval (X i ω))^2 := by
        intro t ht
        rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (Y i ω-(fit n ω).eval (X i ω))^2) n,
          Fin.sum_univ_eq_sum_range (fun i : ℕ => (Y i ω-t.eval (X i ω))^2) n]
        exact (hfit n ω).2 t ht
      have hg' : ∀ v : Fin (J n+1) → ℝ, c*(∑ k, (v k)^2) ≤
          (∑ i : Fin n, (∑ k : Fin (J n+1), v k*(p k).eval (X i ω))^2)/(n : ℝ) := by
        intro v
        rw [Fin.sum_univ_eq_sum_range
          (fun i : ℕ => (∑ k : Fin (J n+1), v k*(p k).eval (X i ω))^2) n]
        exact hg v
      have hr := p001t6consistent_risk_bound μ (X 0) (hX 0) a b hsupp m hcef.1 hm p hdeg horth
        hn (fun i : Fin n => X i ω) (fun i : Fin n => Y i ω) (fun i => hSω i)
        (fit n ω) q (hfit n ω).1 hnq hmin η c hη.le hc (fun t ht => (hq t ht).le) hg'
      have hTident : (∑ k : Fin (J n+1),
          ((∑ i : Fin n, (p k).eval (X i ω)*(Y i ω-m (X i ω)))/(n : ℝ))^2) = T n ω := by
        have hh (k : Fin (J n+1)) :
            (∑ i : Fin n, (p k).eval (X i ω)*(Y i ω-m (X i ω))) =
            ∑ i ∈ Finset.range n, (p k).eval (X i ω)*(Y i ω-m (X i ω)) :=
          Fin.sum_univ_eq_sum_range (fun i : ℕ => (p k).eval (X i ω)*(Y i ω-m (X i ω))) n
        simp only [T, sampleMean, Z, U, hh]
      rw [hTident] at hr
      have hω' : ε ≤ ∫ x, ((fit n ω).eval x-m x)^2 ∂(μ.map (X 0)) := by
        have hnn : 0 ≤ ∫ x, ((fit n ω).eval x-m x)^2 ∂(μ.map (X 0)) :=
          integral_nonneg (fun x : ℝ => sq_nonneg ((fit n ω).eval x-m x))
        simpa only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, abs_of_nonneg hnn] using hω
      have hnoise : 32/c^2*T n ω < ε/2 := by
        have hnum : 32/c^2*δ = ε/2 := by dsimp [δ]; field_simp <;> ring
        exact (mul_lt_mul_of_pos_left (lt_of_not_ge hT) (by positivity)).trans_eq hnum
      have hbias : (16/c+2)*η^2 = ε/4 := by
        change L*η^2 = ε/4
        rw [hηsq]
        field_simp [hL.ne'] <;> ring
      rw [hbias] at hr
      exact False.elim (by linarith)
    have hh := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
    have hh' := measureReal_union_le (μ := μ) (Good n)ᶜ {ω | δ ≤ T n ω}
    change prob μ _ ≤ prob μ _+prob μ Sᶜ at hh
    rw [hSzero, add_zero] at hh
    exact hh.trans hh'
  exact squeeze_zero' (Eventually.of_forall (fun n => ENNReal.toReal_nonneg)) hbound
    (by simpa using hbad.add (hTtail δ hδ))

/-! Stopped inverse weights and conditional trace bound. -/

private def p001t6trace_good {n K : ℕ} (c : ℝ) (P : Matrix (Fin n) (Fin K) ℝ) : Prop :=
  ∀ b : Fin K → ℝ, c*(∑ k, (b k)^2) ≤ (∑ i, (P.mulVec b i)^2)/(n : ℝ)

private lemma p001t6trace_good_measurable {n K : ℕ} (c : ℝ) :
    MeasurableSet {P : Matrix (Fin n) (Fin K) ℝ | p001t6trace_good c P} := by
  apply IsClosed.measurableSet
  simp only [p001t6trace_good, Set.setOf_forall]
  apply isClosed_iInter
  intro b
  exact isClosed_le continuous_const (by unfold Matrix.mulVec dotProduct; fun_prop)

private lemma p001t6trace_inverse_measurable {K : ℕ} :
    Measurable (fun Q : Matrix (Fin K) (Fin K) ℝ => Q⁻¹) := by
  have hi : (fun Q : Matrix (Fin K) (Fin K) ℝ => Q⁻¹) =
      fun Q => Q.det⁻¹ • Q.adjugate := by
    funext Q
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [hi]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

private def p001t6trace_weights {n K : ℕ} (c : ℝ) (P : Matrix (Fin n) (Fin K) ℝ) :
    Matrix (Fin K) (Fin n) ℝ :=
  if p001t6trace_good c P then (P.transpose * P)⁻¹ * P.transpose else 0

private lemma p001t6trace_weights_measurable {n K : ℕ} (c : ℝ) :
    Measurable (p001t6trace_weights (n := n) (K := K) c) := by
  apply Measurable.ite (p001t6trace_good_measurable c) _ measurable_const
  have hQ : Continuous (fun P : Matrix (Fin n) (Fin K) ℝ => P.transpose * P) := by
    exact continuous_id.matrix_transpose.matrix_mul continuous_id
  have hI := p001t6trace_inverse_measurable.comp hQ.measurable
  apply Measurable.of_eval
  intro k
  apply Measurable.of_eval
  intro i
  change Measurable (fun P : Matrix (Fin n) (Fin K) ℝ => ∑ j, ((P.transpose * P)⁻¹) k j * P i j)
  exact Finset.measurable_sum _ (fun j _ =>
    ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hI)).mul
      ((measurable_pi_apply j).comp (measurable_pi_apply i)))

private lemma p001t6trace_row_norm {n K : ℕ} (hn : 0 < n)
    (c : ℝ) (hc : 0 < c) (P : Matrix (Fin n) (Fin K) ℝ)
    (hg : p001t6trace_good c P) (k : Fin K) :
    (∑ i, (p001t6trace_weights c P k i)^2) = (P.transpose * P)⁻¹ k k ∧
    0 ≤ (P.transpose * P)⁻¹ k k ∧
    (P.transpose * P)⁻¹ k k ≤ 1/(c*(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hu := gram_unit_of_lower_bound hn P c hc hg
  let Q := P.transpose * P
  have hQ : Q.transpose = Q := by simp [Q, Matrix.transpose_mul]
  have hI : Q⁻¹.transpose = Q⁻¹ := by rw [Matrix.transpose_nonsing_inv, hQ]
  let A := Q⁻¹ * P.transpose
  have hAA : A * A.transpose = Q⁻¹ := by
    dsimp [A]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hI]
    calc
      (Q⁻¹ * P.transpose) * (P * Q⁻¹) = (Q⁻¹ * Q) * Q⁻¹ := by
        dsimp [Q]
        simp only [Matrix.mul_assoc]
      _ = Q⁻¹ := by rw [Matrix.nonsing_inv_mul Q hu, Matrix.one_mul]
  have hrowA : (∑ i, (A k i)^2) = Q⁻¹ k k := by
    have he := congrArg (fun M : Matrix (Fin K) (Fin K) ℝ => M k k) hAA
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using he
  have hrow : (∑ i, (p001t6trace_weights c P k i)^2) = Q⁻¹ k k := by
    simpa only [p001t6trace_weights, if_pos hg, A, Q] using hrowA
  let e : Fin K → ℝ := Pi.single k 1
  let w : Fin K → ℝ := Q⁻¹.mulVec e
  have hwk : w k = Q⁻¹ k k := by simp [w, e, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hQw : Q.mulVec w = e := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q hu, Matrix.one_mulVec]
  have henergy : (∑ i, (P.mulVec w i)^2) = Q⁻¹ k k := by
    rw [← gram_quadratic_form]
    change dotProduct w (Q.mulVec w) = _
    rw [hQw]
    simpa [e, dotProduct, Pi.single_apply] using hwk
  have hlower : c*(n : ℝ)*(∑ j, (w j)^2) ≤ Q⁻¹ k k := by
    have h := (le_div_iff₀ hnR).mp (hg w)
    rw [henergy] at h
    nlinarith
  have hsingle : (Q⁻¹ k k)^2 ≤ ∑ j, (w j)^2 := by
    rw [← hwk]
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have hnonneg : 0 ≤ Q⁻¹ k k := by rw [← hrow]; positivity
  refine ⟨hrow, hnonneg, ?_⟩
  apply (le_div_iff₀ (mul_pos hc hnR)).mpr
  have hsq : c*(n : ℝ)*(Q⁻¹ k k)^2 ≤ Q⁻¹ k k :=
    (mul_le_mul_of_nonneg_left hsingle (mul_pos hc hnR).le).trans hlower
  by_cases hd : Q⁻¹ k k = 0
  · rw [hd]; norm_num
  · have hp : 0 < Q⁻¹ k k := lt_of_le_of_ne hnonneg (Ne.symm hd)
    nlinarith

private lemma p001t6trace_weight_bound {n K : ℕ} (hn : 0 < n)
    (c : ℝ) (hc : 0 < c) (P : Matrix (Fin n) (Fin K) ℝ) (k : Fin K) (i : Fin n) :
    |p001t6trace_weights c P k i| ≤ Real.sqrt (1/(c*(n : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hg : p001t6trace_good c P
  · have h := p001t6trace_row_norm hn c hc P hg k
    have hs : (p001t6trace_weights c P k i)^2 ≤ 1/(c*(n : ℝ)) := by
      exact (Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)).trans
        (h.1.trans_le h.2.2)
    exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp (by
      simpa only [sq_abs, Real.sq_sqrt (by positivity : 0 ≤ 1/(c*(n : ℝ)))] using hs)
  · simp only [p001t6trace_weights, if_neg hg, Matrix.zero_apply, abs_zero]
    exact Real.sqrt_nonneg _


private lemma p001t6trace_cef_mul {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Ω → E) (hP : Measurable P)
    (Y : Ω → ℝ) (m g : E → ℝ) (h : IsCEF μ P Y m) (hg : Measurable g)
    (hY : Integrable (fun ω => g (P ω)*Y ω) μ)
    (hm : Integrable (fun ω => g (P ω)*m (P ω)) μ) :
    IsCEF μ P (fun ω => g (P ω)*Y ω) (fun p => g p*m p) := by
  have hPm : Measurable[MeasurableSpace.comap P inferInstance] P :=
    measurable_iff_comap_le.mpr le_rfl
  have hCE := condExp_mul_of_stronglyMeasurable_left (hg.comp hPm).stronglyMeasurable hY h.2.1
  simp only [Pi.mul_def, Function.comp_def] at hCE
  have hCE' := isCEF_condExp μ P hP Y m h
  refine ⟨hg.mul h.1, hY, hm, ?_⟩
  intro B hB
  rw [← setIntegral_condExp hP.comap_le hY ⟨B, hB, rfl⟩]
  apply setIntegral_congr_ae (hB.preimage hP)
  filter_upwards [hCE, hCE'] with ω hω hω' _
  change μ[(fun ω => g (P ω)*Y ω) | MeasurableSpace.comap P inferInstance] ω = _
  simpa only [Function.comp_apply, ← hω'] using hω

private lemma p001t6trace_cef_sum {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Fintype ι] (μ : Measure Ω) (P : Ω → E) (Y : ι → Ω → ℝ) (m : ι → E → ℝ)
    (h : ∀ i, IsCEF μ P (Y i) (m i)) :
    IsCEF μ P (fun ω => ∑ i, Y i ω) (fun p => ∑ i, m i p) := by
  refine ⟨Finset.measurable_sum _ (fun i _ => (h i).1),
    integrable_finsetSum _ (fun i _ => (h i).2.1),
    integrable_finsetSum _ (fun i _ => (h i).2.2.1), ?_⟩
  intro B hB
  change (∫ ω in P ⁻¹' B, ∑ i, Y i ω ∂μ) = ∫ ω in P ⁻¹' B, ∑ i, m i (P ω) ∂μ
  rw [integral_finsetSum _ (fun i _ => (h i).2.1.integrableOn),
    integral_finsetSum _ (fun i _ => show Integrable (fun ω => m i (P ω)) (μ.restrict (P ⁻¹' B)) from (h i).2.2.1.integrableOn)]
  exact Finset.sum_congr rfl (fun i _ => (h i).2.2.2 B hB)

private lemma p001t6trace_gram_inverse {n K : ℕ} (hn : 0 < n)
    (c : ℝ) (hc : 0 < c) (P : Matrix (Fin n) (Fin K) ℝ)
    (hg : p001t6trace_good c P) :
    (fixedDesignGram P)⁻¹ = (n : ℝ) • (P.transpose * P)⁻¹ := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  letI instInvertibleScaleGLP0013B5 : Invertible ((n : ℝ)⁻¹) := invertibleOfNonzero (inv_ne_zero hnR)
  rw [fixedDesignGram, Matrix.inv_smul _ _ (gram_unit_of_lower_bound hn P c hc hg)]
  simp only [invOf_eq_inv, inv_inv]

theorem sieve_finite_sampling_noise_trace_bound_proof {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {n K : ℕ} (hn : 0 < n)
  (P : Ω → Matrix (Fin n) (Fin K) ℝ) (hP : Measurable P)
  (u : Ω → Fin n → ℝ) (hu2 : ∀ i, MemLp (fun ω => u ω i) 2 μ)
  (hu0 : ∀ i, IsCEF μ P (fun ω => u ω i) (fun _ => 0))
  (huncorr : ∀ i j, i ≠ j →
    IsCEF μ P (fun ω => u ω i*u ω j) (fun _ => 0))
  (v : Matrix (Fin n) (Fin K) ℝ → Fin n → ℝ)
  (hv : ∀ i, IsCEF μ P (fun ω => (u ω i)^2) (fun p => v p i))
  (V c : ℝ) (hV : 0 ≤ V) (hc : 0 < c)
  (hvar : ∀ᵐ ω ∂μ, ∀ i, v (P ω) i ≤ V)
  : ∃ q : Matrix (Fin n) (Fin K) ℝ → ℝ,
  IsCEF μ P (fun ω => if (∀ b : Fin K → ℝ, c*(∑ k, (b k)^2) ≤
    (∑ i, ((P ω).mulVec b i)^2)/(n : ℝ))
    then ∑ k, (olsCoef (P ω) (u ω) k)^2 else 0) q ∧
  (∀ᵐ ω ∂μ, (∀ b : Fin K → ℝ, c*(∑ k, (b k)^2) ≤
    (∑ i, ((P ω).mulVec b i)^2)/(n : ℝ)) →
    q (P ω) ≤ V*(∑ k, (fixedDesignGram (P ω))⁻¹ k k)/(n : ℝ) ∧
    V*(∑ k, (fixedDesignGram (P ω))⁻¹ k k)/(n : ℝ) ≤
      V*(K : ℝ)/(c*(n : ℝ))) ∧
  mean μ (fun ω => if (∀ b : Fin K → ℝ, c*(∑ k, (b k)^2) ≤
    (∑ i, ((P ω).mulVec b i)^2)/(n : ℝ))
    then ∑ k, (olsCoef (P ω) (u ω) k)^2 else 0) ≤ V*(K : ℝ)/(c*(n : ℝ)) := by
  let A := p001t6trace_weights (n := n) (K := K) c
  let M : Fin n → Fin n → Matrix (Fin n) (Fin K) ℝ → ℝ :=
    fun i j p => if i = j then v p i else 0
  let q : Matrix (Fin n) (Fin K) ℝ → ℝ :=
    fun p => ∑ k, ∑ i, ∑ j, (A p k i*A p k j)*M i j p
  have hA (k : Fin K) (i : Fin n) : Measurable (fun p => A p k i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply k).comp (p001t6trace_weights_measurable c))
  have hprodcef (i j : Fin n) : IsCEF μ P (fun ω => u ω i*u ω j) (M i j) := by
    by_cases h : i = j
    · subst j
      simpa [M, pow_two] using hv i
    · simpa only [M, if_neg h] using huncorr i j h
  have hwbound (k : Fin K) (i j : Fin n) :
      ∀ᵐ ω ∂μ, ‖A (P ω) k i*A (P ω) k j‖ ≤ 1/(c*(n : ℝ)) := by
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_mul]
    have hi := p001t6trace_weight_bound hn c hc (P ω) k i
    have hj := p001t6trace_weight_bound hn c hc (P ω) k j
    calc
      |A (P ω) k i| * |A (P ω) k j| ≤
          Real.sqrt (1/(c*(n : ℝ))) * Real.sqrt (1/(c*(n : ℝ))) :=
        mul_le_mul hi hj (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = 1/(c*(n : ℝ)) := by rw [← pow_two, Real.sq_sqrt (by positivity)]
  have hterm (k : Fin K) (i j : Fin n) :
      IsCEF μ P (fun ω => (A (P ω) k i*A (P ω) k j)*(u ω i*u ω j))
        (fun p => (A p k i*A p k j)*M i j p) := by
    have hwm := ((hA k i).mul (hA k j)).comp hP
    exact p001t6trace_cef_mul μ P hP _ _ _ (hprodcef i j) ((hA k i).mul (hA k j))
      ((hprodcef i j).2.1.bdd_mul hwm.aestronglyMeasurable (hwbound k i j))
      ((hprodcef i j).2.2.1.bdd_mul hwm.aestronglyMeasurable (hwbound k i j))
  have hsum := p001t6trace_cef_sum μ P _ _ (fun k =>
    p001t6trace_cef_sum μ P _ _ (fun i =>
      p001t6trace_cef_sum μ P _ _ (fun j => hterm k i j)))
  have he (ω : Ω) :
      (if p001t6trace_good c (P ω) then ∑ k, (olsCoef (P ω) (u ω) k)^2 else 0) =
      ∑ k, ∑ i, ∑ j, (A (P ω) k i*A (P ω) k j)*(u ω i*u ω j) := by
    by_cases hg : p001t6trace_good c (P ω)
    · simp only [if_pos hg]
      apply Finset.sum_congr rfl
      intro k _
      have hcoef : olsCoef (P ω) (u ω) k = ∑ i, A (P ω) k i*u ω i := by
        simp only [A, p001t6trace_weights, if_pos hg, olsCoef, Matrix.mulVec_mulVec]
        rfl
      rw [hcoef, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · simp [A, p001t6trace_weights, hg]
  have hcef : IsCEF μ P (fun ω => if p001t6trace_good c (P ω)
      then ∑ k, (olsCoef (P ω) (u ω) k)^2 else 0) q := by
    simpa only [he, q] using hsum
  have hq (p : Matrix (Fin n) (Fin K) ℝ) :
      q p = ∑ k, ∑ i, (A p k i)^2 * v p i := by
    simp only [q, M, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, pow_two]
  have htrace (p : Matrix (Fin n) (Fin K) ℝ) (hg : p001t6trace_good c p) :
      V*(∑ k, (fixedDesignGram p)⁻¹ k k)/(n : ℝ) =
        V*∑ k, (p.transpose * p)⁻¹ k k := by
    rw [p001t6trace_gram_inverse hn c hc p hg]
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hupper (p : Matrix (Fin n) (Fin K) ℝ) (hg : p001t6trace_good c p) :
      V*(∑ k, (fixedDesignGram p)⁻¹ k k)/(n : ℝ) ≤ V*(K : ℝ)/(c*(n : ℝ)) := by
    rw [htrace p hg]
    calc
      V*(∑ k, (p.transpose * p)⁻¹ k k) ≤ V*∑ _ : Fin K, 1/(c*(n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hV
        exact Finset.sum_le_sum (fun k _ => (p001t6trace_row_norm hn c hc p hg k).2.2)
      _ = V*(K : ℝ)/(c*(n : ℝ)) := by simp; ring
  have hqbound : ∀ᵐ ω ∂μ, q (P ω) ≤ V*(K : ℝ)/(c*(n : ℝ)) ∧
      (p001t6trace_good c (P ω) → q (P ω) ≤
        V*(∑ k, (fixedDesignGram (P ω))⁻¹ k k)/(n : ℝ)) := by
    filter_upwards [hvar] with ω hω
    by_cases hg : p001t6trace_good c (P ω)
    · have hb : q (P ω) ≤ V*(∑ k, (fixedDesignGram (P ω))⁻¹ k k)/(n : ℝ) := by
        rw [hq, htrace _ hg]
        calc
          (∑ k, ∑ i, (A (P ω) k i)^2*v (P ω) i) ≤
              ∑ k, ∑ i, (A (P ω) k i)^2*V := by
            exact Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun i _ =>
              mul_le_mul_of_nonneg_left (hω i) (sq_nonneg _)))
          _ = V*∑ k, ((P ω).transpose * P ω)⁻¹ k k := by
            have hr (k : Fin K) : (∑ i, (A (P ω) k i)^2) = ((P ω).transpose * P ω)⁻¹ k k :=
              (p001t6trace_row_norm hn c hc (P ω) hg k).1
            simp_rw [← Finset.sum_mul, hr]
            ring
      exact ⟨hb.trans (hupper _ hg), fun _ => hb⟩
    · have hz : q (P ω) = 0 := by simp [q, A, p001t6trace_weights, hg]
      exact ⟨by rw [hz]; positivity, fun h => (hg h).elim⟩
  refine ⟨q, hcef, ?_, ?_⟩
  · filter_upwards [hqbound] with ω hω hg
    exact ⟨hω.2 hg, hupper _ hg⟩
  · have hemean := hcef.2.2.2 Set.univ MeasurableSet.univ
    simp only [Set.preimage_univ, Measure.restrict_univ] at hemean
    change (∫ ω, _ ∂μ) ≤ _
    simp only [p001t6trace_good] at hemean
    have hb : (∫ ω, q (P ω) ∂μ) ≤ V*(K : ℝ)/(c*(n : ℝ)) := by
      simpa [Function.comp_def] using
        integral_mono_ae hcef.2.2.1 (integrable_const (V*(K : ℝ)/(c*(n : ℝ))))
          (hqbound.mono (fun _ h => h.1))
    have hh := hemean.le.trans hb
    convert hh using 1 <;> congr!

end
end AronowAudit.P001.Wave1
