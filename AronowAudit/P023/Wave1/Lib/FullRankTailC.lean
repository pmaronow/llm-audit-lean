import AronowAudit.P023.Wave1.Lib.PopulationNormalTailC

namespace AronowAudit.P023.Wave1
noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter Polynomial
local instance tc04_rank_decidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The constant coefficient of either fitted polynomial. -/
theorem tc04_fit_coeff_zero (J : ℕ) (a : Fin (J+2) → ℝ) (d : ℝ) :
    (tc04_fit_polynomial J a d).coeff 0 = a ⟨0,by omega⟩ + a ⟨1,by omega⟩*d := by
  simp [tc04_fit_polynomial, Polynomial.finsetSum_coeff, Fin.sum_univ_succ,
    tc04_column_polynomial, Polynomial.coeff_C_mul_X_pow]

theorem tc04_fit_coeff_pos (J : ℕ) (a : Fin (J+2) → ℝ) (d : ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hkJ : k ≤ J) :
    (tc04_fit_polynomial J a d).coeff k = a ⟨k+1,by omega⟩ := by
  have hk0 : k ≠ 0 := by omega
  unfold tc04_fit_polynomial
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (⟨k+1,by omega⟩ : Fin (J+2))]
  · simp [tc04_column_polynomial, hk0, Polynomial.coeff_C_mul_X_pow]
  · intro j _ hj
    have hv : j.val ≠ k+1 := fun h => hj (Fin.ext h)
    by_cases h0 : j.val=0
    · simp [tc04_column_polynomial, h0, Polynomial.coeff_C, hk0]
    · by_cases h1 : j.val=1
      · simp [tc04_column_polynomial,h0,h1, Polynomial.coeff_C, hk0]
      · simp [tc04_column_polynomial,h0,h1, Polynomial.coeff_C_mul_X_pow,
          show k ≠ j.val-1 by omega]
  · simp

/-- Local Lebesgue domination gives full rank of (1,D,x,...,x^J). -/
theorem tc04_full_rank_of_domination (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hs : MarginSupport μ) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hdom : ENNReal.ofReal c • (volume : Measure ℝ).restrict (Icc (-δ) δ) ≤ μ)
    (J : ℕ) : MomentPositiveDefinite μ J := by
  intro a ha
  let X := polynomialDesign J (fun x : ℝ => x) party
  have hn : 0 ≤ expectation μ (fun x => predict X a x^2) := integral_nonneg (fun x => sq_nonneg _)
  apply lt_of_le_of_ne hn
  intro hz
  have hz' : expectation μ (fun x => predict X a x^2)=0 := hz.symm
  have hae : ∀ᵐ x ∂μ, predict X a x=0 := by
    have hsq := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (predict X a x))
      (tc04_fit_square_integrable μ hs J a)).mp hz'
    filter_upwards [hsq] with x hx
    exact sq_eq_zero_iff.mp hx
  have halocal : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (-δ) δ), predict X a x=0 :=
    (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hc)).mp
      (ae_mono hdom hae)
  have hneg : tc04_fit_polynomial J a 0=0 := by
    have hsub : Icc (-δ) (-δ/2) ⊆ Icc (-δ) δ := by
      intro x hx
      exact ⟨hx.1,by linarith [hx.2]⟩
    have hn' := ae_restrict_of_ae_restrict_of_subset hsub halocal
    have hpoly : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (-δ) (-δ/2)),
        (tc04_fit_polynomial J a 0).eval x=0 := by
      filter_upwards [hn',ae_restrict_mem measurableSet_Icc] with x hx hmem
      rw [tc04_fit_piecewise] at hx
      simpa only [if_neg (show ¬0 ≤ x by linarith [hmem.2])] using hx
    have heq := Measure.eqOn_Icc_of_ae_eq volume (show -δ ≠ -δ/2 by linarith)
      hpoly (tc04_fit_polynomial J a 0).continuous.continuousOn continuous_const.continuousOn
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact (Set.Ioo_infinite (show -δ < -δ/2 by linarith)).mono
      (fun x hx => heq ⟨hx.1.le,hx.2.le⟩)
  have hpos : tc04_fit_polynomial J a 1=0 := by
    have hsub : Icc (δ/2) δ ⊆ Icc (-δ) δ := by
      intro x hx
      exact ⟨by linarith [hx.1],hx.2⟩
    have hn' := ae_restrict_of_ae_restrict_of_subset hsub halocal
    have hpoly : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (δ/2) δ),
        (tc04_fit_polynomial J a 1).eval x=0 := by
      filter_upwards [hn',ae_restrict_mem measurableSet_Icc] with x hx hmem
      rw [tc04_fit_piecewise] at hx
      simpa only [if_pos (show 0 ≤ x by linarith [hmem.1])] using hx
    have heq := Measure.eqOn_Icc_of_ae_eq volume (show δ/2 ≠ δ by linarith)
      hpoly (tc04_fit_polynomial J a 1).continuous.continuousOn continuous_const.continuousOn
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact (Set.Ioo_infinite (show δ/2 < δ by linarith)).mono
      (fun x hx => heq ⟨hx.1.le,hx.2.le⟩)
  apply ha
  have h0 : a ⟨0,by omega⟩=0 := by
    have h := congrArg (fun p : Polynomial ℝ => p.coeff 0) hneg
    simpa [tc04_fit_coeff_zero] using h
  have h1 : a ⟨1,by omega⟩=0 := by
    have h := congrArg (fun p : Polynomial ℝ => p.coeff 0) hpos
    rw [tc04_fit_coeff_zero,Polynomial.coeff_zero] at h
    norm_num only [mul_one] at h
    linarith [h0]
  funext j
  change a j=0
  by_cases hj0 : j.val=0
  · have hj : j=(⟨0,by omega⟩ : Fin (J+2)) := Fin.ext hj0
    simpa only [hj] using h0
  · by_cases hj1 : j.val=1
    · have hj : j=(⟨1,by omega⟩ : Fin (J+2)) := Fin.ext hj1
      simpa only [hj] using h1
    · have h := congrArg (fun p : Polynomial ℝ => p.coeff (j.val-1)) hneg
      rw [tc04_fit_coeff_pos J a 0 (j.val-1) (by omega) (by omega), Polynomial.coeff_zero] at h
      have hj : (⟨j.val-1+1,by omega⟩ : Fin (J+2))=j := Fin.ext (by simp only; omega)
      rw [hj] at h
      exact h

/-- Full uniform rank holds at every finite degree, including zero. -/
theorem uniform_full_rank (J : ℕ) : MomentPositiveDefinite uniformMargins J := by
  letI tc04_rank_uniform_probability : IsProbabilityMeasure uniformMargins := ⟨uniform_law_normalized.1⟩
  apply tc04_full_rank_of_domination uniformMargins uniform_law_normalized.2 (1/2) 1
    (by norm_num) (by norm_num) _ J
  unfold uniformMargins
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
  norm_num

end
end AronowAudit.P023.Wave1
