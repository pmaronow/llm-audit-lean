import SAP.P001a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

namespace SAP.P001a.WH.W1.P.T6_L2

lemma compact_abs_bound {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    {f : ℝ → ℝ} (hf : ContinuousOn f K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hf.abs
  have hC0 : 0 ≤ C := by
    obtain ⟨x, hx⟩ := hne
    exact (abs_nonneg (f x)).trans (hC (Set.mem_image_of_mem _ hx))
  exact ⟨C, hC0, fun x hx => hC (Set.mem_image_of_mem _ hx)⟩

end SAP.P001a.WH.W1.P.T6_L2

theorem SAP.P001a.WH.W1.T6_L2_proof : SAP.P001a.WH.W1.T6_L2 := by
  intro Ω hΩ μ hμ X Y a b V m h
  let K : Set ℝ := Set.Icc a b
  let g : ℝ → ℝ := K.indicator m
  have hKm : MeasurableSet K := by
    simpa [K] using (measurableSet_Icc : MeasurableSet (Set.Icc a b))
  have hKcompact : IsCompact K := by simpa [K] using isCompact_Icc
  have hKne : K.Nonempty := by
    refine ⟨a, ?_⟩
    simp [K, h.interval.le]
  obtain ⟨C, hC0, hCm⟩ := SAP.P001a.WH.W1.P.T6_L2.compact_abs_bound
    hKcompact hKne (by simpa [K] using h.continuous)
  have hcontK : ContinuousOn m K := by simpa [K] using h.continuous
  have hgmeas : Measurable g := by
    have hpiece : Measurable (K.piecewise m (fun _ => (0 : ℝ))) :=
      hcontK.measurable_piecewise continuousOn_const hKm
    have hgeq : g = K.piecewise m (fun _ => (0 : ℝ)) := by
      funext x
      simp [g, Set.indicator, Set.piecewise]
    rw [hgeq]
    exact hpiece
  have hgBound : ∀ x, |g x| ≤ C := by
    intro x
    by_cases hx : x ∈ K
    · simpa [g, hx] using hCm x hx
    · simpa [g, hx] using hC0
  have hX : Measurable (X 0) := measurable_fst.comp (h.iid.1 0)
  have hgXmeas : Measurable (fun ω => g (X 0 ω)) := hgmeas.comp hX
  have hYint : Integrable (Y 0) μ := h.cef.1
  have hcond : μ[Y 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ]
      (fun ω => m (X 0 ω)) := h.cef.2
  have hmXaesm : AEStronglyMeasurable (fun ω => m (X 0 ω)) μ :=
    (show Integrable (μ[Y 0 | MeasurableSpace.comap (X 0) inferInstance]) μ from
      integrable_condExp).aestronglyMeasurable.congr hcond
  have hgXbound : ∀ᵐ ω ∂μ, |g (X 0 ω)| ≤ C :=
    h.support.mono fun ω hω => hgBound (X 0 ω)
  have hgXint : Integrable (fun ω => g (X 0 ω)) μ :=
    Integrable.of_bound hgXmeas.aestronglyMeasurable C (by
      filter_upwards [hgXbound] with ω hω
      simpa only [Real.norm_eq_abs] using hω)
  have hmXbound : ∀ᵐ ω ∂μ, |m (X 0 ω)| ≤ C :=
    h.support.mono fun ω hω => hCm (X 0 ω) hω
  have hmXmul : Integrable (fun ω => m (X 0 ω) * m (X 0 ω)) μ :=
    Integrable.of_bound (hmXaesm.mul hmXaesm) (C ^ 2) (by
    filter_upwards [hmXbound] with ω hω
    simpa [Real.norm_eq_abs, abs_mul, pow_two] using
      (mul_le_mul hω hω (abs_nonneg _) hC0))
  have hmXsq : Integrable (fun ω => (m (X 0 ω)) ^ 2) μ := by
    simpa only [pow_two] using hmXmul
  let r : Ω → ℝ := fun ω => Y 0 ω - m (X 0 ω)
  have hraesm : AEStronglyMeasurable r μ := by
    dsimp [r]
    exact hYint.aestronglyMeasurable.sub hmXaesm
  have hrLp : MemLp r 2 μ :=
    (memLp_two_iff_integrable_sq hraesm).2 (by simpa [r] using h.noise_integrable)
  have hmXLp : MemLp (fun ω => m (X 0 ω)) 2 μ :=
    (memLp_two_iff_integrable_sq hmXaesm).2 (by simpa using hmXsq)
  have hYLp : MemLp (Y 0) 2 μ := by
    have hsum := hrLp.add hmXLp
    convert hsum using 1
    ext ω
    simp [r]
  have hnoise_nonneg : 0 ≤ ∫ ω, r ω ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg (r ω))
  have hvar := h.variance_bound Set.univ MeasurableSet.univ
  have hV : ∫ ω, r ω ^ 2 ∂μ ≤ V := by
    simpa [r, SAP.P001a.prob] using hvar
  have hVnonneg : 0 ≤ V := le_trans hnoise_nonneg hV
  have hgXae : (fun ω => g (X 0 ω)) =ᵐ[μ] (fun ω => m (X 0 ω)) := by
    filter_upwards [h.support] with ω hω
    simp [g, K, hω]
  have hcef : SAP.P001a.IsCEF μ (X 0) (Y 0) g := by
    refine ⟨hgmeas, hYint, hgXint, ?_⟩
    intro A hA
    have hpre : MeasurableSet ((X 0) ⁻¹' A) := hX hA
    have hpreC : MeasurableSet[MeasurableSpace.comap (X 0) inferInstance]
        ((X 0) ⁻¹' A) := ⟨A, hA, rfl⟩
    calc
      (∫ ω in (X 0) ⁻¹' A, Y 0 ω ∂μ) =
          ∫ ω in (X 0) ⁻¹' A, μ[Y 0 | MeasurableSpace.comap (X 0) inferInstance] ω ∂μ := by
            symm
            exact setIntegral_condExp hX.comap_le hYint hpreC
      _ = ∫ ω in (X 0) ⁻¹' A, m (X 0 ω) ∂μ := by
            apply setIntegral_congr_ae hpre
            exact hcond.mono fun ω hω _ => hω
      _ = ∫ ω in (X 0) ⁻¹' A, g (X 0 ω) ∂μ := by
            apply setIntegral_congr_ae hpre
            exact hgXae.symm.mono fun ω hω _ => hω
  have hpoly : ∀ q : Polynomial ℝ,
      Integrable (fun x => (q.eval x - m x) ^ 2) (μ.map (X 0)) := by
    intro q
    obtain ⟨B, hB0, hBq⟩ := SAP.P001a.WH.W1.P.T6_L2.compact_abs_bound
      hKcompact hKne (f := fun x : ℝ => Polynomial.eval x q) q.continuous.continuousOn
    let f : ℝ → ℝ := fun x => (q.eval x - g x) ^ 2
    have hfmeas : Measurable f := by
      dsimp [f]
      fun_prop
    have hfXmeas : Measurable (fun ω => f (X 0 ω)) := hfmeas.comp hX
    have hfXbound : ∀ᵐ ω ∂μ, ‖f (X 0 ω)‖ ≤ (B + C) ^ 2 := by
      filter_upwards [h.support] with ω hω
      have hq := hBq (X 0 ω) hω
      have hdiff : |q.eval (X 0 ω) - g (X 0 ω)| ≤ B + C := by
        calc
          |q.eval (X 0 ω) - g (X 0 ω)| ≤ |q.eval (X 0 ω)| + |g (X 0 ω)| := abs_sub _ _
          _ ≤ B + C := add_le_add hq (hgBound (X 0 ω))
      dsimp [f]
      simpa [Real.norm_eq_abs, abs_pow] using
        (sq_le_sq₀ (abs_nonneg _) (add_nonneg hB0 hC0)).mpr hdiff
    have hfXint : Integrable (fun ω => f (X 0 ω)) μ :=
      Integrable.of_bound hfXmeas.aestronglyMeasurable ((B + C) ^ 2) hfXbound
    have hfint : Integrable f (μ.map (X 0)) :=
      (integrable_map_measure hfmeas.aestronglyMeasurable hX.aemeasurable).2 hfXint
    have hmapK : ∀ᵐ x ∂(μ.map (X 0)), x ∈ K := by
      apply (ae_map_iff hX.aemeasurable (p := fun x => x ∈ K) (by simpa using hKm)).2
      simpa [K] using h.support
    have hfeq : f =ᵐ[μ.map (X 0)] (fun x => (q.eval x - m x) ^ 2) := by
      filter_upwards [hmapK] with x hx
      simp [f, g, hx]
    exact hfint.congr hfeq
  exact ⟨hVnonneg, hYLp, hcef, hgXae, hpoly⟩
