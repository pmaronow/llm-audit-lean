import AronowAudit.P023.Wave1.Lib.UniformProjectionTailC

namespace AronowAudit.P023.Wave1
noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter
local instance tc04_density_decidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Borel-set domination gives domination as measures. -/
theorem tc04_density_measure_domination (μ : Measure ℝ) (c δ : ℝ)
    (hdom : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (-δ) δ →
      ENNReal.ofReal c * volume A ≤ μ A) :
    ENNReal.ofReal c • (volume : Measure ℝ).restrict (Icc (-δ) δ) ≤ μ := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, Measure.restrict_apply hA]
  exact (hdom (A ∩ Icc (-δ) δ) (hA.inter measurableSet_Icc) inter_subset_right).trans
    (measure_mono inter_subset_left)

/-- Integral domination with integrability checked against the larger measure. -/
theorem tc04_density_integral_domination (μ : Measure ℝ) (c δ : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (-δ) δ →
      ENNReal.ofReal c * volume A ≤ μ A)
    (f : ℝ → ℝ) (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x) :
    c * (∫ x in Icc (-δ) δ, f x) ≤ ∫ x, f x ∂μ := by
  have hi := integral_mono_measure (tc04_density_measure_domination μ c δ hdom)
    (Filter.Eventually.of_forall hn) hf
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul] using hi

/-- Local density domination bounds the squared error of every polynomial
approximation to the party indicator. -/
theorem tc04_density_polynomial_domination (ν : Measure (ℝ × ℝ)) (α β : ℝ)
    (h : ℝ → ℝ) (c δ L σ2 : ℝ) (hr : RepairedRegularity ν α β h c δ L σ2)
    (p : Polynomial ℝ) :
    c * (∫ x in Icc (-δ) δ, (party x - p.eval x) ^ 2) ≤
      expectation (marginLaw ν) (fun x => (party x - p.eval x) ^ 2) := by
  rcases hr with ⟨hprob, hsupp, hzero, hsq, hc, hδ, hδ1, hL, hσ, hdom,
    h0, hlip, hmean, hvar⟩
  have hmprob : marginLaw ν univ = 1 := by
    simpa only [ProbabilityLaw, marginLaw, Measure.map_apply measurable_fst MeasurableSet.univ,
      preimage_univ] using hprob
  letI tc04_density_margin_probability : IsProbabilityMeasure (marginLaw ν) := ⟨hmprob⟩
  exact tc04_density_integral_domination _ c δ hc.le hdom _
    (tc04_supported_square_integrable _ hsupp p) (fun x => sq_nonneg _)

theorem tc04_density_square_zero (μ : Measure ℝ) [IsFiniteMeasure μ] (hs : MarginSupport μ)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hdom : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (-δ) δ →
      ENNReal.ofReal c * volume A ≤ μ A)
    (p : Polynomial ℝ) (hz : expectation μ (fun x => p.eval x ^ 2) = 0) : p = 0 := by
  have hint : Integrable (fun x => p.eval x ^ 2) μ := by
    apply (tc04_supported_poly_integrable μ hs (p^2)).congr
    exact Filter.Eventually.of_forall (fun x => by simp)
  have hd := tc04_density_integral_domination μ c δ hc.le hdom _ hint (fun x => sq_nonneg (p.eval x))
  have hn : 0 ≤ ∫ x in Icc (-δ) δ, p.eval x ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  have hi : (∫ x in Icc (-δ) δ, p.eval x ^ 2) = 0 := by
    change c * (∫ x in Icc (-δ) δ, p.eval x ^ 2) ≤ expectation μ _ at hd
    rw [hz] at hd
    nlinarith
  have hlocal : Integrable (fun x => p.eval x ^ 2) ((volume : Measure ℝ).restrict (Icc (-δ) δ)) :=
    (p.continuous.pow 2).integrableOn_Icc
  have hae : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (-δ) δ), p.eval x = 0 := by
    have hsquare := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (p.eval x)) hlocal).mp hi
    filter_upwards [hsquare] with x hx
    exact sq_eq_zero_iff.mp hx
  have heq := Measure.eqOn_Icc_of_ae_eq volume (show -δ ≠ δ by linarith) hae
    p.continuous.continuousOn continuous_const.continuousOn
  apply p.eq_zero_of_infinite_isRoot
  exact (Set.Ioo_infinite (show -δ < δ by linarith)).mono
    (fun x hx => heq ⟨hx.1.le, hx.2.le⟩)

/-- Existence of the actual epsilon-chosen projection under local domination. -/
theorem tc04_density_chosen_projection (ν : Measure (ℝ × ℝ)) (α β : ℝ)
    (h : ℝ → ℝ) (c δ L σ2 : ℝ) (hr : RepairedRegularity ν α β h c δ L σ2)
    (J : ℕ) : IsProjection (marginLaw ν) J (projection (marginLaw ν) J) := by
  rcases hr with ⟨hprob, hsupp, hzero, hsq, hc, hδ, hδ1, hL, hσ, hdom,
    h0, hlip, hmean, hvar⟩
  have hmprob : marginLaw ν univ = 1 := by
    simpa only [ProbabilityLaw, marginLaw, Measure.map_apply measurable_fst MeasurableSet.univ,
      preimage_univ] using hprob
  letI tc04_density_margin_probability : IsProbabilityMeasure (marginLaw ν) := ⟨hmprob⟩
  exact tc04_projection_spec (marginLaw ν) hsupp
    (tc04_density_square_zero (marginLaw ν) hsupp c δ hc hδ hdom) J


theorem tc04_density_uniform_minimum (J : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ J) :
    residualVariance uniformMargins J ≤
      expectation uniformMargins (fun x => (party x - p.eval x) ^ 2) := by
  letI tc04_density_uniform_probability : IsProbabilityMeasure uniformMargins := ⟨uniform_law_normalized.1⟩
  exact tc04_projection_minimum uniformMargins uniform_law_normalized.2 J
    (projection uniformMargins J) p (tc04_chosen_spec J) hp

/-- Affine rescaling of a competitor, including the factor `2 * δ`. -/
theorem tc04_density_scaled_projection_minimum (J : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ J) :
    2 * δ * residualVariance uniformMargins J ≤
      ∫ x in Icc (-δ) δ, (party x - p.eval x) ^ 2 := by
  let s := p.comp (Polynomial.C δ * Polynomial.X)
  have hs : s.natDegree ≤ J := by
    apply Polynomial.natDegree_comp_le.trans
    have hd : (Polynomial.C δ * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by compute_degree
    exact (Nat.mul_le_mul_left p.natDegree hd).trans (by simpa using hp)
  have hparty (t : ℝ) : party (δ * t) = party t := by
    simp only [party, mul_nonneg_iff_of_pos_left hδ]
  have he : (∫ x in Icc (-δ) δ, (party x - p.eval x) ^ 2) =
      2 * δ * expectation uniformMargins (fun t => (party t - s.eval t) ^ 2) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -δ ≤ δ by linarith), tc04_eq_interval]
    have hchange := intervalIntegral.smul_integral_comp_mul_left
      (fun x : ℝ => (party x - p.eval x) ^ 2) (a := (-1 : ℝ)) (b := 1) δ
    simp only [smul_eq_mul, mul_neg, mul_one, mul_one, neg_mul, one_mul] at hchange
    rw [← hchange]
    have heval (t : ℝ) : s.eval t = p.eval (δ * t) := by
      simp [s, Polynomial.eval_comp]
    simp_rw [hparty, ← heval]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (tc04_density_uniform_minimum J s hs) (by positivity)

/-- Pure scalar portion of the variance chain. No Legendre input is needed. -/
theorem tc04_density_denominator_chain (J : ℕ) (hJ : 1 ≤ J) (c δ : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) :
    let n := (J + 1) / 2
    c * δ * centralBinomial n ^ 2 / 2 ≥ c * δ / (8 * (n : ℝ)) ∧
      c * δ / (8 * (n : ℝ)) ≥ c * δ / (4 * ((J : ℝ) + 1)) := by
  dsimp only
  let n := (J + 1) / 2
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have htwice : 2 * n ≤ J + 1 := by dsimp [n]; omega
  have hreal : 2 * (n : ℝ) ≤ (J : ℝ) + 1 := by exact_mod_cast htwice
  constructor
  · have hb := mul_le_mul_of_nonneg_left (central_binomial_lower_bound n hn)
      (show 0 ≤ c * δ / 2 by positivity)
    calc
      c * δ / (8 * (n : ℝ)) = (c * δ / 2) * (1 / (4 * (n : ℝ))) := by
        field_simp
        <;> ring
      _ ≤ (c * δ / 2) * centralBinomial n ^ 2 := hb
      _ = c * δ * centralBinomial n ^ 2 / 2 := by ring
  · apply (div_le_div_iff₀ (show 0 < 4 * ((J : ℝ) + 1) by positivity)
      (show 0 < 8 * (n : ℝ) by positivity)).mpr
    exact mul_le_mul_of_nonneg_left (show 8 * (n : ℝ) ≤ 4 * ((J : ℝ) + 1) by linarith)
      (show 0 ≤ c * δ by positivity)


theorem density_residual_comparison_proof (ν : Measure (ℝ × ℝ)) (α β : ℝ)
    (h : ℝ → ℝ) (c δ L σ2 : ℝ) (hr : RepairedRegularity ν α β h c δ L σ2)
    (J : ℕ) (hJ : 1 ≤ J) :
    let μ := marginLaw ν
    let n := (J+1)/2
    (∀ p : Polynomial ℝ, p.natDegree ≤ J →
      expectation μ (fun x => (party x-p.eval x)^2) ≥
        c*(∫ x in Set.Icc (-δ) δ, (party x-p.eval x)^2)) ∧
    residualVariance μ J ≥ 2*c*δ*residualVariance uniformMargins J ∧
    2*c*δ*residualVariance uniformMargins J = c*δ*centralBinomial n^2/2 ∧
    c*δ*centralBinomial n^2/2 ≥ c*δ/(8*(n:ℝ)) ∧
    c*δ/(8*(n:ℝ)) ≥ c*δ/(4*((J:ℝ)+1)) := by
  have hc : 0 < c := hr.2.2.2.2.1
  have hδ : 0 < δ := hr.2.2.2.2.2.1
  have hdom := tc04_density_polynomial_domination ν α β h c δ L σ2 hr
  have hprojection := tc04_density_chosen_projection ν α β h c δ L σ2 hr J
  have hscaled := tc04_density_scaled_projection_minimum J δ hδ
    (projection (marginLaw ν) J) hprojection.1
  have hden := tc04_density_denominator_chain J hJ c δ hc hδ
  refine ⟨fun p _ => hdom p, ?_, ?_, hden.1, hden.2⟩
  · have hm := mul_le_mul_of_nonneg_left hscaled hc.le
    change 2*c*δ*residualVariance uniformMargins J ≤
      expectation (marginLaw ν) (fun x => (party x-(projection (marginLaw ν) J).eval x)^2)
    calc
      _ = c*(2*δ*residualVariance uniformMargins J) := by ring
      _ ≤ c*(∫ x in Icc (-δ) δ, (party x-(projection (marginLaw ν) J).eval x)^2) := hm
      _ ≤ _ := hdom _
  · rw [(uniform_projection_variance J hJ).2.2.1]
    ring

end
end AronowAudit.P023.Wave1
