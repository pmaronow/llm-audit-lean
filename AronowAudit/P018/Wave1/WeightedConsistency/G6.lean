import AronowAudit.P018.Wave1.WeightedConsistencyBlueprint

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

section ProbabilityAlgebra
variable {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)]
  (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
  {E F J : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup J]

/-- Outer-probability bound for an arbitrary union. -/
theorem probability_union_bound (N : ℕ) (s t : Set (Ω N)) :
    (μ N (s ∪ t)).toReal ≤ (μ N s).toReal + (μ N t).toReal := by
  calc
    _ ≤ (μ N s + μ N t).toReal :=
      ENNReal.toReal_mono (by finiteness) (measure_union_le s t)
    _ = _ := ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)

/-- Transfer through eventual inclusions of deviation events. -/
theorem inProbability_event_mono {f : ∀ N, Ω N → E} {g : ∀ N, Ω N → F}
    (hg : inProbability μ g)
    (h : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ᶠ N in atTop,
      {ω | ε ≤ ‖f N ω‖} ⊆ {ω | δ ≤ ‖g N ω‖}) : inProbability μ f := by
  intro ε hε
  obtain ⟨δ, hδ, hsub⟩ := h ε hε
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) _ (hg δ hδ)
  filter_upwards [hsub] with N hN
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hN)

theorem inProbability_add {f g : ∀ N, Ω N → E}
    (hf : inProbability μ f) (hg : inProbability μ g) :
    inProbability μ (fun N ω => f N ω + g N ω) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _
    (by simpa using (hf (ε / 2) hhalf).add (hg (ε / 2) hhalf))
  intro N
  calc
    _ ≤ (μ N ({ω | ε / 2 ≤ ‖f N ω‖} ∪ {ω | ε / 2 ≤ ‖g N ω‖})).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro ω hω
      change ε ≤ ‖f N ω + g N ω‖ at hω
      by_contra hn
      have h₁ : ‖f N ω‖ < ε / 2 := lt_of_not_ge (fun h => hn (Or.inl h))
      have h₂ : ‖g N ω‖ < ε / 2 := lt_of_not_ge (fun h => hn (Or.inr h))
      have := norm_add_le (f N ω) (g N ω)
      linarith
    _ ≤ _ := probability_union_bound μ N _ _

theorem inProbability_deterministic (A : ℕ → E) (hA : Tendsto A atTop (𝓝 0)) :
    inProbability μ (fun N (_ : Ω N) => A N) := by
  intro ε hε
  have ht : ∀ᶠ N in atTop, ‖A N‖ < ε := by
    have h := (tendsto_norm_zero.comp hA).eventually (gt_mem_nhds hε)
    simpa only [Function.comp_apply] using h
  apply tendsto_const_nhds.congr'
  filter_upwards [ht] with N hN
  have he : {ω : Ω N | ε ≤ ‖A N‖} = ∅ := by ext; simp [not_le.mpr hN]
  simp only [he, measure_empty, ENNReal.toReal_zero]

theorem inProbability_eventually_eq {f g : ∀ N, Ω N → E}
    (hfg : ∀ᶠ N in atTop, ∀ ω, f N ω = g N ω) (hf : inProbability μ f) :
    inProbability μ g := by
  intro ε hε
  apply (hf ε hε).congr'
  filter_upwards [hfg] with N hN
  have heq : f N = g N := funext hN
  rw [heq]

/-- Continuous mapping at a fixed limit, for changing probability spaces. -/
theorem inProbability_continuousAt {f : ∀ N, Ω N → E} {x : E} {φ : E → F}
    (hφ : ContinuousAt φ x) (hf : inProbability μ (fun N ω => f N ω - x)) :
    inProbability μ (fun N ω => φ (f N ω) - φ x) := by
  apply inProbability_event_mono μ hf
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hφ ε hε
  refine ⟨δ, hδ, Eventually.of_forall ?_⟩
  intro N ω hω
  change δ ≤ ‖f N ω - x‖
  by_contra hn
  have := hcont (show dist (f N ω) x < δ by simpa [dist_eq_norm] using lt_of_not_ge hn)
  have ht : ‖φ (f N ω) - φ x‖ < ε := by simpa only [dist_eq_norm] using this
  exact (not_le.mpr ht) hω

/-- A uniformly bounded bilinear estimate is enough for a null random product. -/
theorem inProbability_product_null (φ : E → F → J) (c : ℝ) (hc : 0 ≤ c)
    (hφ : ∀ x y, ‖φ x y‖ ≤ c * ‖x‖ * ‖y‖)
    (f : ∀ N, Ω N → E) (x : E) (g : ∀ N, Ω N → F)
    (hf : inProbability μ (fun N ω => f N ω - x)) (hg : inProbability μ g) :
    inProbability μ (fun N ω => φ (f N ω) (g N ω)) := by
  intro ε hε
  let L : ℝ := c * (‖x‖ + 1) + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hδ : 0 < ε / L := div_pos hε hL
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _
    (by simpa using (hf 1 zero_lt_one).add (hg (ε / L) hδ))
  intro N
  calc
    _ ≤ (μ N ({ω | 1 ≤ ‖f N ω - x‖} ∪ {ω | ε / L ≤ ‖g N ω‖})).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro ω hω
      by_contra hn
      have h₁ : ‖f N ω - x‖ < 1 := lt_of_not_ge (fun h => hn (Or.inl h))
      have h₂ : ‖g N ω‖ < ε / L := lt_of_not_ge (fun h => hn (Or.inr h))
      have hfbound : ‖f N ω‖ ≤ ‖x‖ + 1 := by
        have := norm_add_le (f N ω - x) x
        rw [sub_add_cancel] at this
        linarith
      have hcoef : c * ‖f N ω‖ ≤ L := by
        have := mul_le_mul_of_nonneg_left hfbound hc
        dsimp [L]
        linarith
      have hlt : ‖φ (f N ω) (g N ω)‖ < ε := calc
        _ ≤ c * ‖f N ω‖ * ‖g N ω‖ := hφ _ _
        _ ≤ L * ‖g N ω‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
        _ < L * (ε / L) := mul_lt_mul_of_pos_left h₂ hL
        _ = ε := mul_div_cancel₀ ε hL.ne'
      exact (not_le.mpr hlt) hω
    _ ≤ _ := probability_union_bound μ N _ _

end ProbabilityAlgebra

/-- Elementwise matrix norm bound for matrix-vector multiplication. -/
theorem norm_mulVec_le {k : ℕ} (A : Mat k) (s : Vec k) :
    ‖A.mulVec s‖ ≤ (k : ℝ) * ‖A‖ * ‖s‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j, A i j * s j‖ ≤ _
  calc
    _ ≤ ∑ j : Fin k, ‖A i j * s j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin k, ‖A‖ * ‖s‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i))
        (norm_le_pi_norm s j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

/-- Elementwise matrix norm bound for matrix multiplication. -/
theorem norm_matrix_mul_le {k : ℕ} (A B : Mat k) :
    ‖A * B‖ ≤ (k : ℝ) * ‖A‖ * ‖B‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  change ‖∑ l, A i l * B l j‖ ≤ _
  calc
    _ ≤ ∑ l : Fin k, ‖A i l * B l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin k, ‖A‖ * ‖B‖ := by
      apply Finset.sum_le_sum
      intro l hl
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (A i) l).trans (norm_le_pi_norm A i))
        ((norm_le_pi_norm (B l) j).trans (norm_le_pi_norm B l))
          (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

theorem g6_proof : G6.{u} := by
  intro Ω _ k μ _
  refine ⟨fun f g hf hg => inProbability_add μ hf hg,
    fun f g hf hg => inProbability_add μ hf hg,
    fun A hA => inProbability_deterministic μ A hA, ?_, ?_, ?_⟩
  · intro f g hfg hf
    obtain ⟨N₀, hN₀⟩ := hfg
    exact inProbability_eventually_eq μ
      (eventually_atTop.mpr ⟨N₀, hN₀⟩) hf
  · intro f g hfg hf
    obtain ⟨N₀, hN₀⟩ := hfg
    exact inProbability_eventually_eq μ
      (eventually_atTop.mpr ⟨N₀, hN₀⟩) hf
  · intro A A₀ s hA hs
    exact inProbability_product_null μ (fun (A : Mat k) (s : Vec k) => A.mulVec s) (k : ℝ)
      (Nat.cast_nonneg k) (norm_mulVec_le (k := k)) A A₀ s hA hs

end
end AronowAudit.P018.Wave1.WeightedConsistency
