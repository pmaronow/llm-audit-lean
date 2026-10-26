import AronowAudit.P018.Wave1.WeightedConsistency.G6

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

/-- Domination by a fixed multiple of a null error. -/
theorem inProbability_of_norm_bound {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ∀ N, Ω N → E} {g : ∀ N, Ω N → F} (hg : inProbability μ g)
    (c : ℝ) (hc : 0 < c) (hbound : ∀ᶠ N in atTop, ∀ ω, ‖f N ω‖ ≤ c * ‖g N ω‖) :
    inProbability μ f := by
  apply inProbability_event_mono μ hg
  intro ε hε
  refine ⟨ε / c, div_pos hε hc, ?_⟩
  filter_upwards [hbound] with N hN ω hω
  change ε / c ≤ ‖g N ω‖
  exact (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hω.trans (hN ω))

theorem g8_proof : G8.{u} := by
  intro Ω _ k μ _ Bn Mn B0 T B hBn hB0 hT hMn
  obtain ⟨c, hc⟩ := hT
  have hB0p : inProbability μ (fun N (_ : Ω N) => B0 N - B) :=
    inProbability_deterministic μ _ (by convert hB0.sub_const B using 1 <;> simp only [sub_self] <;> rfl)
  have hB0neg : inProbability μ (fun N (_ : Ω N) => B - B0 N) :=
    inProbability_deterministic μ _ (by convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => B) atTop (𝓝 B)).sub hB0 using 1 <;>
        simp only [sub_self] <;> rfl)
  have hD : inProbability μ (fun N ω => Bn N ω - B0 N) := by
    have hh := inProbability_add μ hBn hB0neg
    simpa only [sub_add_sub_cancel] using hh
  have hmul {f : ∀ N, Ω N → Mat k} (hf : inProbability μ f) :
      inProbability μ (fun N ω => Bn N ω * f N ω) :=
    inProbability_product_null μ (fun A C : Mat k => A * C) (k : ℝ)
      (Nat.cast_nonneg _) norm_matrix_mul_le Bn B f hBn hf
  have hmulR {f : ∀ N, Ω N → Mat k} (hf : inProbability μ f) :
      inProbability μ (fun N ω => f N ω * Bn N ω) :=
    inProbability_product_null μ (fun A C : Mat k => C * A) (k : ℝ)
      (Nat.cast_nonneg _) (fun A C => by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using norm_matrix_mul_le C A)
      Bn B f hBn hf
  have hmulB0 {f : ∀ N, Ω N → Mat k} (hf : inProbability μ f) :
      inProbability μ (fun N ω => B0 N * f N ω) :=
    inProbability_product_null μ (fun A C : Mat k => A * C) (k : ℝ)
      (Nat.cast_nonneg _) norm_matrix_mul_le (fun N _ => B0 N) B f hB0p hf
  have hTmul {f : ∀ N, Ω N → Mat k} (hf : inProbability μ f) :
      inProbability μ (fun N ω => T N * f N ω) := by
    apply inProbability_of_norm_bound μ hf ((k : ℝ) * |c| + 1) (by positivity)
    apply Eventually.of_forall
    intro N ω
    calc
      _ ≤ (k : ℝ) * ‖T N‖ * ‖f N ω‖ := norm_matrix_mul_le _ _
      _ ≤ ((k : ℝ) * |c| + 1) * ‖f N ω‖ := by
        have ht := (hc N).trans (le_abs_self c)
        calc
          _ ≤ (k : ℝ) * |c| * ‖f N ω‖ := by gcongr
          _ ≤ _ := by nlinarith [norm_nonneg (f N ω)]

  have hmulT {f : ∀ N, Ω N → Mat k} (hf : inProbability μ f) :
      inProbability μ (fun N ω => f N ω * T N) := by
    apply inProbability_of_norm_bound μ hf ((k : ℝ) * |c| + 1) (by positivity)
    apply Eventually.of_forall
    intro N ω
    calc
      _ ≤ (k : ℝ) * ‖f N ω‖ * ‖T N‖ := norm_matrix_mul_le _ _
      _ ≤ ((k : ℝ) * |c| + 1) * ‖f N ω‖ := by
        have ht := (hc N).trans (le_abs_self c)
        calc
          _ ≤ (k : ℝ) * ‖f N ω‖ * |c| := by gcongr
          _ ≤ _ := by nlinarith [norm_nonneg (f N ω)]
  have h₁ := hmulR (hmul hMn)
  have h₂ := hmulR (hmulT hD)
  have h₃ := hmulB0 (hTmul hD)
  have hs := inProbability_add μ (inProbability_add μ h₁ h₂) h₃
  convert hs using 1
  funext N ω
  simpa only [sandwich, Matrix.mul_assoc] using
    sandwich_difference (Bn N ω) (B0 N) (Mn N ω) (T N)

end
end AronowAudit.P018.Wave1.WeightedConsistency
