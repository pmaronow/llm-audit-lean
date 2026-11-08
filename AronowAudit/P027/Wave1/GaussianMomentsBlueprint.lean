import AronowAudit.P027.P027_Audit

/-! # Blueprint (shared): Gaussian noise implies the stated second moments

Shared library-to-project glue for the two P027-T7 refutations (records 10 and 11 of
dossier group P027): `GaussianNoise μ ε σ2` (measurable coordinates with law
`N(0, σ2)` and joint independence, supplement pp. A2–A3) implies the project's
`NoiseMoments μ ε σ2` (mean zero, finite second moments, diagonal moment σ2,
zero distinct-coordinate cross moments). Map-P027 report, "Shared lemmas and
obligations", item 3; both referees accepted it with the hypothesis `0 ≤ σ2`.

Final declaration (writer): `AronowAudit.P027.Wave1.gaussian_noise_moments`
in `AronowAudit/P027/Wave1/GaussianMoments.lean`.
-/

namespace AronowAudit.P027.Wave1.GaussianMoments

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable

/-- Frozen target: independent `N(0, σ2)` coordinates satisfy `NoiseMoments` with
the same real `σ2`, provided `0 ≤ σ2` (needed to recover `σ2` from `σ2.toNNReal`). -/
def Target : Prop :=
  ∀ {Ξ K : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (ε : K → Ξ → ℝ) (σ2 : ℝ), 0 ≤ σ2 → GaussianNoise μ ε σ2 → NoiseMoments μ ε σ2

/-- N1 (paper-proof step "each coordinate has the pushforward law gaussianReal 0 σ2;
Gaussian finite first and second moments transfer through the AEMeasurable law
map"): a single real random variable with law `N(0, v)` is integrable with mean
zero, and its square is integrable with integral `v`. -/
def N1 : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : Ξ → ℝ) (v : ℝ≥0), AEMeasurable X μ → μ.map X = gaussianReal 0 v →
    (Integrable X μ ∧ ∫ ξ, X ξ ∂μ = 0) ∧
    (Integrable (fun ξ => X ξ * X ξ) μ ∧ ∫ ξ, X ξ * X ξ ∂μ = (v : ℝ))

/-- N2 (paper-proof step "for k ≠ l, independent integrable coordinates have an
integrable product whose integral is the product of the two zero means"). -/
def N2 : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X Y : Ξ → ℝ), IndepFun X Y μ → Integrable X μ → Integrable Y μ →
    ∫ ξ, X ξ ∂μ = 0 → ∫ ξ, Y ξ ∂μ = 0 →
    Integrable (fun ξ => X ξ * Y ξ) μ ∧ ∫ ξ, X ξ * Y ξ ∂μ = 0

/-- The nodes suffice: diagonal moments from N1, off-diagonal moments from N2 and
pairwise independence extracted from `iIndepFun`. -/
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

/- Satisfiability of the hypotheses: the finite and countable Gaussian product
witnesses of the record-11 (`CancellationModelBlueprint`, node N2) and record-10
(`CancellationLimitBlueprint`, node N9) blueprints satisfy `GaussianNoise` with
`σ2 = 1791/100 > 0`. -/

end
end AronowAudit.P027.Wave1.GaussianMoments
