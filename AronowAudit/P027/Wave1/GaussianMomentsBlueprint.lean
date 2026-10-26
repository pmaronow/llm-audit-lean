import AronowAudit.P027.P027_Audit

/-! # Gaussian noise and second moments

`GaussianNoise μ ε σ2` specifies measurable coordinates with law `N(0, σ2)`
and joint independence, as in supplement pp. A2–A3. For `0 ≤ σ2`, it implies
`NoiseMoments μ ε σ2`: mean zero, finite second moments, diagonal moment `σ2`,
and zero cross moments for distinct coordinates.
-/

namespace AronowAudit.P027.Wave1.GaussianMoments

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable

/-- Independent `N(0, σ2)` coordinates satisfy `NoiseMoments` with
the same real `σ2`, provided `0 ≤ σ2` (needed to recover `σ2` from `σ2.toNNReal`). -/
def Target : Prop :=
  ∀ {Ξ K : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (ε : K → Ξ → ℝ) (σ2 : ℝ), 0 ≤ σ2 → GaussianNoise μ ε σ2 → NoiseMoments μ ε σ2

/-- Gaussian finite first and second moments transfer through an
`AEMeasurable` law map. A real random variable with law `N(0, v)` is integrable
with mean zero, and its square is integrable with integral `v`. -/
def N1 : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : Ξ → ℝ) (v : ℝ≥0), AEMeasurable X μ → μ.map X = gaussianReal 0 v →
    (Integrable X μ ∧ ∫ ξ, X ξ ∂μ = 0) ∧
    (Integrable (fun ξ => X ξ * X ξ) μ ∧ ∫ ξ, X ξ * X ξ ∂μ = (v : ℝ))

/-- Independent integrable mean-zero coordinates have an integrable
product whose integral is the product of their zero means. -/
def N2 : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X Y : Ξ → ℝ), IndepFun X Y μ → Integrable X μ → Integrable Y μ →
    ∫ ξ, X ξ ∂μ = 0 → ∫ ξ, Y ξ ∂μ = 0 →
    Integrable (fun ξ => X ξ * Y ξ) μ ∧ ∫ ξ, X ξ * Y ξ ∂μ = 0

/-- Diagonal moments follow from `N1`; off-diagonal moments follow from `N2`
and pairwise independence extracted from `iIndepFun`. -/
theorem assemble (h1 : N1) (h2 : N2) : Target := by
  intro Ξ K _ μ _ ε σ2 hσ hε
  obtain ⟨hlaw, hind⟩ := hε
  have hcoord (k : K) := h1 μ (ε k) σ2.toNNReal (hlaw k).1 (hlaw k).2
  refine ⟨fun k => (hcoord k).1, fun k l => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    refine ⟨(hcoord k).2.1, ?_⟩
    rw [show (if k = k then σ2 else 0) = σ2 from by simp]
    unfold outcomeE
    rw [(hcoord k).2.2, Real.coe_toNNReal _ hσ]
  · obtain ⟨hint, hzero⟩ := h2 μ (ε k) (ε l) (hind.indepFun hkl)
      (hcoord k).1.1 (hcoord l).1.1 (hcoord k).1.2 (hcoord l).1.2
    refine ⟨hint, ?_⟩
    simp only [hkl, ↓reduceIte]
    exact hzero



end
end AronowAudit.P027.Wave1.GaussianMoments
