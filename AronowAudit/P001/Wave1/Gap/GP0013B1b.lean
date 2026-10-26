import AronowAudit.P001.P001_Foundations
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Polynomial-sieve consistency from empirical noise scores. -/

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance GP0013B1b_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-- Successive nonzero degrees span every bounded-degree polynomial space. -/
private lemma GP0013B1b_polynomial_expansion
    (p : ℕ → Polynomial ℝ) (hp : ∀ k, (p k).natDegree = k)
    (hne : ∀ k, p k ≠ 0) (d : ℕ) (q : Polynomial ℝ) (hq : q.natDegree ≤ d) :
    ∃ v : Fin (d+1) → ℝ, q = ∑ k, v k • p k := by
  let S : Polynomial.Sequence ℝ := ⟨p, fun k => by
    rw [Polynomial.degree_eq_natDegree (hne k), hp k]⟩
  have hs := S.span_degreeLT (m := d+1) (fun k _ =>
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (hne k)))
  have hr : Set.range (fun k : Fin (d+1) => p k) = S '' Set.Iio (d+1) := by
    ext t
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k.val, k.isLt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hm : q ∈ Submodule.span ℝ (Set.range (fun k : Fin (d+1) => p k)) := by
    rw [hr, hs, Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast (by omega : q.natDegree < d+1))
  obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hm
  exact ⟨v, hv.symm⟩

/-- The eventwise variance bound dominates the residual-square pushforward measure. -/
private lemma GP0013B1b_weighted_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X u : Ω → ℝ)
    (hX : Measurable X) (hu : Measurable u) (hu2 : MemLp u 2 μ)
    (V : ℝ) (hV : 0 ≤ V)
    (hvar : ∀ A : Set ℝ, MeasurableSet A →
      (∫ ω in X ⁻¹' A, (u ω)^2 ∂μ) ≤ V * prob μ (X ⁻¹' A))
    (g : ℝ → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hgi : Integrable g (μ.map X)) :
    (∫ ω, g (X ω) * (u ω)^2 ∂μ) ≤ V * ∫ x, g x ∂(μ.map X) := by
  let ρ : Measure ℝ := (μ.withDensity (fun ω => ENNReal.ofReal ((u ω)^2))).map X
  have hle : ρ ≤ ENNReal.ofReal V • μ.map X := by
    apply Measure.le_iff.mpr
    intro A hA
    dsimp only [ρ]
    rw [Measure.map_apply hX hA, withDensity_apply _ (hX hA),
      Measure.smul_apply, Measure.map_apply hX hA]
    have he : (∫⁻ ω in X ⁻¹' A, ENNReal.ofReal ((u ω)^2) ∂μ) =
        ENNReal.ofReal (∫ ω in X ⁻¹' A, (u ω)^2 ∂μ) := by
      exact (ofReal_integral_eq_lintegral_ofReal hu2.integrable_sq.integrableOn
        (ae_of_all _ (fun ω => sq_nonneg _))).symm
    rw [he]
    change _ ≤ ENNReal.ofReal V * μ (X ⁻¹' A)
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (X ⁻¹' A)),
      ← ENNReal.ofReal_mul hV]
    exact ENNReal.ofReal_le_ofReal (hvar A hA)
  have hgi' : Integrable g (ENNReal.ofReal V • μ.map X) := hgi.smul_measure ENNReal.ofReal_ne_top
  have hi := integral_mono_measure hle (ae_of_all _ hg0) hgi'
  have he : (∫ x, g x ∂ρ) = ∫ ω, g (X ω) * (u ω)^2 ∂μ := by
    dsimp only [ρ]
    rw [integral_map hX.aemeasurable hg.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul (hu.pow_const 2).ennreal_ofReal
        (ae_of_all _ (fun ω => ENNReal.ofReal_lt_top)) _]
    simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_comm]
  rw [he, integral_smul_measure, ENNReal.toReal_ofReal hV, smul_eq_mul] at hi
  exact hi

/-- The least-squares basic inequality and the Gram lower bound control population
error by empirical residual scores and a uniform polynomial approximation error. -/
private lemma GP0013B1b_deterministic_error
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a b : ℝ) (hsupp : ∀ᵐ x ∂ν, x ∈ Set.Icc a b)
    (m : ℝ → ℝ) (hm : ContinuousOn m (Set.Icc a b))
    (p : ℕ → Polynomial ℝ) (hdeg : ∀ k, (p k).natDegree = k)
    (hne : ∀ k, p k ≠ 0) (d n : ℕ) (hn : 0 < n)
    (horth : ∀ j k : Fin (d+1), mean ν (fun x =>
      (p j).eval x * (p k).eval x) = if j=k then 1 else 0)
    (x y : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc a b)
    (q f : Polynomial ℝ) (hq : q.natDegree ≤ d) (hf : f.natDegree ≤ d)
    (hmin : (∑ i, (y i - f.eval (x i))^2) ≤ ∑ i, (y i - q.eval (x i))^2)
    (δ c : ℝ) (hδ : 0 ≤ δ) (hc : 0 < c)
    (happrox : ∀ t ∈ Set.Icc a b, |m t-q.eval t| ≤ δ)
    (hgram : ∀ v : Fin (d+1) → ℝ, c*(∑ k, (v k)^2) ≤
      (∑ i, (∑ k, v k*(p k).eval (x i))^2)/(n : ℝ)) :
    (∫ t, (f.eval t-m t)^2 ∂ν) ≤
      (32/c^2) * (∑ k : Fin (d+1),
        ((∑ i, (y i-m (x i))*(p k).eval (x i))/(n : ℝ))^2) +
        (16/c+2)*δ^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨v, hv⟩ := GP0013B1b_polynomial_expansion p hdeg hne d (f-q)
    ((Polynomial.natDegree_sub_le _ _).trans (max_le hf hq))
  let z : Fin n → ℝ := fun i => ∑ k : Fin (d+1), v k*(p k).eval (x i)
  let u : Fin n → ℝ := fun i => y i-m (x i)
  let r : Fin n → ℝ := fun i => m (x i)-q.eval (x i)
  let A : Fin (d+1) → ℝ := fun k => (∑ i, u i*(p k).eval (x i))/(n : ℝ)
  let S : ℝ := ∑ k, (v k)^2
  let T : ℝ := ∑ k, (A k)^2
  let E : ℝ := (∑ i, (z i)^2)/(n : ℝ)
  have hze (t : ℝ) : f.eval t-q.eval t = ∑ k : Fin (d+1), v k*(p k).eval t := by
    have hh := congrArg (fun P : Polynomial ℝ => P.eval t) hv
    simpa only [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_smul,
      smul_eq_mul] using hh
  have hbasic : (∑ i, (z i)^2) ≤ 2*(∑ i, u i*z i) + 2*(∑ i, r i*z i) := by
    have he (i : Fin n) :
        (y i-f.eval (x i))^2 = (y i-q.eval (x i))^2 + (z i)^2 -
          2*(u i*z i) - 2*(r i*z i) := by
      have hz := hze (x i)
      change f.eval (x i)-q.eval (x i)=z i at hz
      dsimp [u,r]
      rw [sub_eq_iff_eq_add.mp hz]
      ring
    simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum] at hmin
    linarith
  have hr (i : Fin n) : (r i)^2 ≤ δ^2 := by
    have hh := happrox (x i) (hx i)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (r i)) hδ).mpr hh
  have hrz : 2*(∑ i, r i*z i) ≤ (1/2 : ℝ)*(∑ i, (z i)^2) +
      2*(n : ℝ)*δ^2 := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      show 2*(r i*z i) ≤ (1/2 : ℝ)*(z i)^2 + 2*δ^2 by
        nlinarith [sq_nonneg (z i-2*r i), hr i])
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using hh
  have hscore : (∑ i, u i*z i)/(n : ℝ) = ∑ k, v k*A k := by
    dsimp [z,A]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hE : E ≤ 4*(∑ k, v k*A k) + 4*δ^2 := by
    have hh : (∑ i, (z i)^2) ≤ 4*(∑ i, u i*z i)+4*(n : ℝ)*δ^2 := by
      linarith
    have hh' := (div_le_div_iff_of_pos_right hnR).mpr hh
    change E ≤ _ at hh'
    rw [add_div, mul_div_assoc, hscore] at hh'
    have hcancel : 4*(n : ℝ)*δ^2/(n : ℝ) = 4*δ^2 := by field_simp
    rwa [hcancel] at hh'
  have hyoung : 4*(∑ k, v k*A k) ≤ (c/2)*S+(8/c)*T := by
    have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (d+1)))) =>
      show 4*(v k*A k) ≤ (c/2)*(v k)^2+(8/c)*(A k)^2 by
        apply (mul_le_mul_iff_right₀ hc).mp
        field_simp
        nlinarith [sq_nonneg (c*v k-4*A k)])
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, S, T] using hh
  have hS : S ≤ (16/c^2)*T+(8/c)*δ^2 := by
    have hg : c*S ≤ E := hgram v
    have hh : (c/2)*S ≤ (8/c)*T+4*δ^2 := by linarith
    apply (mul_le_mul_iff_right₀ (show 0 < c^2 by positivity)).mp
    field_simp at hh ⊢
    nlinarith
  let R : ℝ → ℝ := fun t => q.eval t-m t
  have hRmeas : AEStronglyMeasurable R ν := by
    have hh : AEStronglyMeasurable R (ν.restrict (Set.Icc a b)) :=
      (q.continuous.continuousOn.sub hm).aestronglyMeasurable measurableSet_Icc
    rwa [Measure.restrict_eq_self_of_ae_mem hsupp] at hh
  have hRb : ∀ᵐ t ∂ν, ‖R t‖ ≤ δ := by
    filter_upwards [hsupp] with t ht
    simpa only [R, Real.norm_eq_abs, abs_sub_comm] using happrox t ht
  have hR2 : MemLp R 2 ν := MemLp.of_bound hRmeas δ hRb
  have hRi : (∫ t, (R t)^2 ∂ν) ≤ δ^2 := by
    apply (integral_mono_ae hR2.integrable_sq (integrable_const (δ^2)) ?_).trans_eq (by simp)
    filter_upwards [hRb] with t ht
    simpa only [Real.norm_eq_abs, sq_abs] using (sq_le_sq₀ (norm_nonneg (R t)) hδ).mpr ht
  let P : ℝ → ℝ := fun t => ∑ k : Fin (d+1), v k*(p k).eval t
  have hPi : Integrable (fun t => (P t)^2) ν :=
    (memLp_finsetSum Finset.univ (fun k _ =>
      (orthonormal_polynomial_lp ν (fun k : Fin (d+1) => p k) horth k).const_mul (v k))).integrable_sq
  have hfi : Integrable (fun t => (f.eval t-m t)^2) ν := by
    have hh : MemLp P 2 ν := memLp_finsetSum Finset.univ (fun k _ =>
      (orthonormal_polynomial_lp ν (fun k : Fin (d+1) => p k) horth k).const_mul (v k))
    have he : (fun t => f.eval t-m t) = fun t => P t+R t := by
      funext t
      have hz := hze t
      dsimp [P,R]
      linarith
    have hh2 : MemLp (fun t => f.eval t-m t) 2 ν := he ▸ hh.add hR2
    exact hh2.integrable_sq
  calc
    (∫ t, (f.eval t-m t)^2 ∂ν) ≤ ∫ t, 2*(P t)^2+2*(R t)^2 ∂ν := by
      apply integral_mono hfi ((hPi.const_mul 2).add (hR2.integrable_sq.const_mul 2))
      intro t
      have hz := hze t
      change f.eval t-q.eval t=P t at hz
      dsimp [R]
      rw [sub_eq_iff_eq_add.mp hz]
      nlinarith only [sq_nonneg (P t-(q.eval t-m t))]
    _ = 2*S+2*(∫ t, (R t)^2 ∂ν) := by
      rw [integral_add (hPi.const_mul 2) (hR2.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]
      dsimp [P]
      rw [orthonormal_polynomial_integral_sq ν (fun k : Fin (d+1) => p k) horth]
    _ ≤ 2*((16/c^2)*T+(8/c)*δ^2)+2*δ^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hS (by norm_num))
        (mul_le_mul_of_nonneg_left hRi (by norm_num))
    _ = (32/c^2)*T+(16/c+2)*δ^2 := by ring

/-- Each polynomial-weighted CEF residual is iid, centered, and has variance at most V. -/
private lemma GP0013B1b_noise_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
    (a b V : ℝ) (hV : 0 ≤ V) (hY2 : MemLp (Y 0) 2 μ)
    (hsupp : ∀ᵐ ω ∂μ, X 0 ω ∈ Set.Icc a b)
    (m : ℝ → ℝ) (hm : ContinuousOn m (Set.Icc a b))
    (hcef : IsCEF μ (X 0) (Y 0) m)
    (hvar : ∀ A : Set ℝ, MeasurableSet A →
      (∫ ω in (X 0) ⁻¹' A, (Y 0 ω-m (X 0 ω))^2 ∂μ) ≤
        V * prob μ ((X 0) ⁻¹' A))
    (p : Polynomial ℝ)
    (horth : mean μ (fun ω => (p.eval (X 0 ω))^2) = 1) :
    let W : ℕ → Ω → ℝ := fun i ω =>
      (Y i ω-m (X i ω))*p.eval (X i ω)
    IID μ W ∧ MemLp (W 0) 2 μ ∧ mean μ (W 0) = 0 ∧ var μ (W 0) ≤ V := by
  dsimp only
  let u : Ω → ℝ := fun ω => Y 0 ω-m (X 0 ω)
  have hXm : Measurable (X 0) := (hiid.1 0).fst
  have hYm : Measurable (Y 0) := (hiid.1 0).snd
  have hum : Measurable u := hYm.sub (hcef.1.comp hXm)
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).exists_bound_of_continuousOn hm
  have hm2 : MemLp (m ∘ X 0) 2 μ := MemLp.of_bound
    (hcef.1.comp hXm).aestronglyMeasurable C (by
      filter_upwards [hsupp] with ω hω using hC (X 0 ω) hω)
  have hu2 : MemLp u 2 μ := hY2.sub hm2
  obtain ⟨D,hD⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).exists_bound_of_continuousOn
    p.continuous.continuousOn
  have hpinf : MemLp (fun ω => p.eval (X 0 ω)) ∞ μ := MemLp.of_bound
    (p.continuous.measurable.comp hXm).aestronglyMeasurable D (by
      filter_upwards [hsupp] with ω hω using hD (X 0 ω) hω)
  have hp2 : MemLp (fun ω => p.eval (X 0 ω)) 2 μ := hpinf.mono_exponent (by simp)
  have hw2 : MemLp (fun ω => u ω*p.eval (X 0 ω)) 2 μ := hu2.fun_mul hpinf
  have hres := cef_residual_orthogonality_correction μ (X 0) hXm (Y 0) hY2 m hcef hm2
  have hw0 : mean μ (fun ω => u ω*p.eval (X 0 ω)) = 0 := by
    have hh := hres.2.2 (fun x => p.eval x) p.continuous.measurable hp2
    change covariance (fun ω => p.eval (X 0 ω)) u μ = 0 at hh
    rw [covariance_eq_sub hp2 hu2] at hh
    change (∫ ω, p.eval (X 0 ω)*u ω ∂μ) -
      mean μ (fun ω => p.eval (X 0 ω))*mean μ u = 0 at hh
    have hz : mean μ u = 0 := hres.2.1
    rw [hz, mul_zero, sub_zero] at hh
    simpa only [mean, mul_comm] using hh
  let f : ℝ × ℝ → ℝ := fun xy => (xy.2-m xy.1)*p.eval xy.1
  have hfm : Measurable f := (measurable_snd.sub (hcef.1.comp measurable_fst)).mul
    (p.continuous.measurable.comp measurable_fst)
  have hi : IID μ (fun i ω => (Y i ω-m (X i ω))*p.eval (X i ω)) := by
    exact ⟨fun i => hfm.comp (hiid.1 i),
      hiid.2.1.comp (fun _ => f) (fun _ => hfm), fun i => (hiid.2.2 i).comp hfm⟩
  refine ⟨hi, hw2, hw0, ?_⟩
  have hgi : Integrable (fun x => (p.eval x)^2) (μ.map (X 0)) :=
    (integrable_map_measure (p.continuous.pow 2).aestronglyMeasurable hXm.aemeasurable).mpr
      hp2.integrable_sq
  have hh := GP0013B1b_weighted_variance μ (X 0) u hXm hum hu2 V hV hvar
    (fun x => (p.eval x)^2) (p.continuous.pow 2).measurable (fun _ => sq_nonneg _) hgi
  have he : (∫ x, (p.eval x)^2 ∂μ.map (X 0)) = 1 := by
    rw [integral_map (μ := μ) (f := fun x => (p.eval x)^2) hXm.aemeasurable
      (p.continuous.pow 2).aestronglyMeasurable]
    exact horth
  rw [he, mul_one] at hh
  have hwvar : var μ (fun ω => u ω*p.eval (X 0 ω)) =
      ∫ ω, (p.eval (X 0 ω))^2*(u ω)^2 ∂μ := by
    rw [var, variance_eq_sub hw2]
    change _ - (mean μ (fun ω => u ω*p.eval (X 0 ω)))^2 = _
    rw [hw0]
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, Pi.pow_apply, mul_pow, mul_comm]
  exact hwvar.trans_le hh

private lemma GP0013B1b_score_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (W : Fin K → ℕ → Ω → ℝ)
    (hiid : ∀ k, IID μ (W k)) (h2 : ∀ k, MemLp (W k 0) 2 μ)
    (hz : ∀ k, mean μ (W k 0) = 0) (V : ℝ)
    (hv : ∀ k, var μ (W k 0) ≤ V) (n : ℕ) (hn : 0 < n) :
    Integrable (fun ω => ∑ k, (sampleMean (W k) n ω)^2) μ ∧
    (∫ ω, ∑ k, (sampleMean (W k) n ω)^2 ∂μ) ≤ (K : ℝ)*V/(n : ℝ) := by
  have hni (k : Fin K) := sample_mean_memLp μ (W k) (hiid k) (h2 k) n
  refine ⟨integrable_finsetSum _ (fun k _ => (hni k).integrable_sq), ?_⟩
  rw [integral_finsetSum _ (fun k _ => (hni k).integrable_sq)]
  have hh (k : Fin K) : (∫ ω, (sampleMean (W k) n ω)^2 ∂μ) ≤ V/(n : ℝ) := by
    have hmom := iid_sample_mean_finite_moments μ (W k) (hiid k) (h2 k) n hn
    have hzero : mean μ (sampleMean (W k) n) = 0 := hmom.1.trans (hz k)
    have he : var μ (sampleMean (W k) n) = ∫ ω, (sampleMean (W k) n ω)^2 ∂μ := by
      rw [var, variance_eq_sub (hni k)]
      change _ - (mean μ (sampleMean (W k) n))^2 = _
      rw [hzero]
      simp only [Pi.pow_apply, zero_pow (by decide : 2 ≠ 0), sub_zero]
    rw [← he, hmom.2]
    exact div_le_div_of_nonneg_right (hv k) (Nat.cast_nonneg n)
  exact (Finset.sum_le_sum (fun k _ => hh k)).trans_eq (by simp; ring)

private lemma GP0013B1b_score_null {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : ℕ → ℕ → Ω → ℝ)
    (hiid : ∀ k, IID μ (W k)) (h2 : ∀ k, MemLp (W k 0) 2 μ)
    (hz : ∀ k, mean μ (W k 0) = 0) (V : ℝ)
    (hv : ∀ k, var μ (W k 0) ≤ V) (J : ℕ → ℕ)
    (hrate : Tendsto (fun n : ℕ => ((J n+1 : ℕ) : ℝ)/(n : ℝ)) atTop (nhds 0))
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n => prob μ {ω | t ≤
      ∑ k : Fin (J n+1), (sampleMean (W k) n ω)^2}) atTop (nhds 0) := by
  have hu : Tendsto (fun n : ℕ => (V/t)*(((J n+1 : ℕ) : ℝ)/(n : ℝ)))
      atTop (nhds 0) := by simpa only [mul_zero] using hrate.const_mul (V/t)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hmom := GP0013B1b_score_expectation μ (fun k : Fin (J n+1) => W k)
      (fun k => hiid k) (fun k => h2 k) (fun k => hz k) V (fun k => hv k) n hn
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (ae_of_all μ (fun ω => Finset.sum_nonneg (fun k _ => sq_nonneg _))) hmom.1 t
    change t * prob μ {ω | t ≤ ∑ k : Fin (J n+1), (sampleMean (W k) n ω)^2} ≤ _ at hmarkov
    calc
      prob μ {ω | t ≤ ∑ k : Fin (J n+1), (sampleMean (W k) n ω)^2} ≤
          (((J n+1 : ℕ) : ℝ)*V/(n : ℝ))/t := (le_div_iff₀ ht).mpr (by linarith [hmom.2])
      _ = (V/t)*(((J n+1 : ℕ) : ℝ)/(n : ℝ)) := by ring

/-- Full-support sieve consistency under compact containment. -/
theorem sieve_consistency_full_interval_support_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
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
  have hXm (i : ℕ) : Measurable (X i) := (hiid.1 i).fst
  let GP0013B1b_instLaw : IsProbabilityMeasure (μ.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).mpr inferInstance
  have hne : ∀ k, p k ≠ 0 := by
    intro k hk
    have hh := horth k k
    simp [hk, mean] at hh
  have horthν (j k : ℕ) : mean (μ.map (X 0)) (fun x =>
      (p j).eval x*(p k).eval x) = if j=k then 1 else 0 := by
    rw [mean, integral_map (μ := μ) (f := fun x => (p j).eval x*(p k).eval x)
      (hXm 0).aemeasurable ((p j).continuous.mul (p k).continuous).aestronglyMeasurable]
    exact horth j k
  have hsuppν : ∀ᵐ x ∂μ.map (X 0), x ∈ Set.Icc a b :=
    (ae_map_iff (hXm 0).aemeasurable measurableSet_Icc).mpr hsupp
  have hsuppAll : ∀ᵐ ω ∂μ, ∀ i : ℕ, X i ω ∈ Set.Icc a b := by
    rw [ae_all_iff]
    intro i
    exact (((hiid.2.2 i).comp measurable_fst).symm).ae_mem_snd measurableSet_Icc hsupp
  let W : ℕ → ℕ → Ω → ℝ := fun k i ω => (Y i ω-m (X i ω))*(p k).eval (X i ω)
  have hW (k : ℕ) : IID μ (W k) ∧ MemLp (W k 0) 2 μ ∧
      mean μ (W k 0)=0 ∧ var μ (W k 0) ≤ V := by
    apply GP0013B1b_noise_moments μ X Y hiid a b V hV hY2 hsupp m hm hcef hvar (p k)
    simpa [pow_two] using horth k k
  let S : ℕ → Ω → ℝ := fun n ω => ∑ k : Fin (J n+1), (sampleMean (W k) n ω)^2
  let G : ℕ → Set Ω := fun n => {ω | ∀ v : Fin (J n+1) → ℝ,
    c*(∑ k, (v k)^2) ≤ (∑ i ∈ Finset.range n,
      (∑ k : Fin (J n+1), v k*(p k).eval (X i ω))^2)/(n : ℝ)}
  have hGm (n : ℕ) : MeasurableSet (G n) := by
    have hclosed : IsClosed {z : ℕ → ℝ | ∀ v : Fin (J n+1) → ℝ,
        c*(∑ k, (v k)^2) ≤ (∑ i ∈ Finset.range n,
          (∑ k : Fin (J n+1), v k*(p k).eval (z i))^2)/(n : ℝ)} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter (fun v => isClosed_le continuous_const (by fun_prop))
    exact hclosed.measurableSet.preimage (measurable_pi_iff.mpr hXm)
  have hbad : Tendsto (fun n => prob μ (G n)ᶜ) atTop (nhds 0) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hgram
    have he (n : ℕ) : prob μ (G n)ᶜ = 1-prob μ (G n) :=
      probReal_compl_eq_one_sub (hGm n)
    simp_rw [he]
    simpa only [sub_self] using hh
  intro ε hε
  let B : ℝ := 16/c+2
  let A : ℝ := 32/c^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let δ : ℝ := Real.sqrt (ε/(4*B))
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδsq : δ^2 = ε/(4*B) := Real.sq_sqrt (by positivity)
  obtain ⟨q,hq⟩ := weierstrass_approximation a b hab.le m hm δ hδ
  let t : ℝ := ε/(4*A)
  have ht : 0 < t := by dsimp [t]; positivity
  have hscore : Tendsto (fun n => prob μ {ω | t ≤ S n ω}) atTop (nhds 0) :=
    GP0013B1b_score_null μ W (fun k => (hW k).1) (fun k => (hW k).2.1)
      (fun k => (hW k).2.2.1) V (fun k => (hW k).2.2.2) J hrate t ht
  have hu : Tendsto (fun n => prob μ (G n)ᶜ + prob μ {ω | t ≤ S n ω})
      atTop (nhds 0) := by simpa using hbad.add hscore
  have hevent : ∀ᶠ n in atTop,
      prob μ {ω | ε ≤ dist (∫ x, ((fit n ω).eval x-m x)^2 ∂μ.map (X 0)) 0} ≤
        prob μ (G n)ᶜ + prob μ {ω | t ≤ S n ω} := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hJ.eventually (eventually_ge_atTop q.natDegree)] with n hn hqn
    have hsub : {ω | ε ≤ dist (∫ x, ((fit n ω).eval x-m x)^2 ∂μ.map (X 0)) 0} ≤ᵐ[μ]
        (G n)ᶜ ∪ {ω | t ≤ S n ω} := by
      filter_upwards [hsuppAll] with ω hω
      intro hωbad
      by_cases hg : ω ∈ G n
      · right
        by_contra hsmall
        have hst : S n ω < t := lt_of_not_ge hsmall
        have hf := hfit n ω
        have hb := GP0013B1b_deterministic_error (μ.map (X 0)) a b hsuppν m hm p hdeg hne
          (J n) n hn (fun j k : Fin (J n+1) => by
            simpa only [Fin.ext_iff] using horthν j k)
          (fun i : Fin n => X i ω) (fun i : Fin n => Y i ω) (fun i => hω i)
          q (fit n ω) hqn hf.1
          (by simpa only [Finset.sum_range] using hf.2 q hqn)
          δ c hδ.le hc (fun x hx => (hq x hx).le)
          (fun v => by simpa only [Finset.sum_range] using hg v)
        have hb' : (∫ x, ((fit n ω).eval x-m x)^2 ∂μ.map (X 0)) ≤ A*S n ω+B*δ^2 := by
          simpa only [A,B,S,W,sampleMean,Finset.sum_range] using hb
        have hdist : dist (∫ x, ((fit n ω).eval x-m x)^2 ∂μ.map (X 0)) 0 =
            ∫ x, ((fit n ω).eval x-m x)^2 ∂μ.map (X 0) := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
        rw [hdist] at hωbad
        have hAt : A*t = ε/4 := by dsimp [t]; field_simp [hA.ne']
        have hBd : B*δ^2 = ε/4 := by rw [hδsq]; field_simp [hB.ne']
        have hstrict := mul_lt_mul_of_pos_left hst hA
        linarith only [hb',hωbad,hstrict,hAt,hBd,hε]
      · exact Or.inl hg
    have hm := measure_mono_ae hsub
    exact (ENNReal.toReal_mono (measure_ne_top μ _) hm).trans (measureReal_union_le _ _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) hevent

end
end AronowAudit.P001.Wave1
