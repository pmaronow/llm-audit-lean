import AronowAudit.P001.Wave1.GapLawBlueprint

/-!
# Counterexample to PDA local-support invariance (P001-T102)

Differentiability of two CEF versions at every point of positive covariate density
does not ensure that they have a common coordinate derivative at the covariate mean,
even when the covariate coordinates and the outcome are integrable.
`Target` negates this universal assertion for `Ω : Type` (universe 0).

The witness has `Ω = ℝ × ℝ`, `μ = gapJointLaw`, `K = 1`, `X = gapX`,
`Y = Prod.snd`, `f x = gapPDF (x 0)`, `m = 0`, `m' = bumpVec`, and `k = 0`.
Both CEF versions are globally `C¹`, including at the support endpoints.
At the covariate mean `0`, their derivatives are `0` and `1`.
A support-neighbourhood hypothesis is a different condition and is not refuted by
this counterexample.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.PdaLocalSupport

open AronowAudit.P001 AronowAudit.P001.Wave1.GapLaw MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

/-- Negation of the universal assertion (universe 0). -/
def Target : Prop :=
  ¬ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
    (X : Ω → Fin K → ℝ) (Y : Ω → ℝ), Measurable X →
    (∀ j, Integrable (fun ω => X ω j) μ) → Integrable Y μ →
    ∀ (f : (Fin K → ℝ) → ℝ), HasVectorPDF (μ.map X) f →
    ∀ (m m' : (Fin K → ℝ) → ℝ), IsCEF μ X Y m → IsCEF μ X Y m' →
    ∀ (k : Fin K),
    (∀ x, 0 < f x → DifferentiableAt ℝ (fun t => m (Function.update x k (x k + t))) 0) →
    (∀ x, 0 < f x → DifferentiableAt ℝ (fun t => m' (Function.update x k (x k + t))) 0) →
    ∃ a : ℝ,
      HasDerivAt (fun t => m (Function.update (fun j => mean μ (fun ω => X ω j)) k
        (mean μ (fun ω => X ω k) + t))) a 0 ∧
      HasDerivAt (fun t => m' (Function.update (fun j => mean μ (fun ω => X ω j)) k
        (mean μ (fun ω => X ω k) + t))) a 0

/-- Along the updated `0`-th coordinate path, `bumpVec` is the scalar bump shifted by `c`. -/
theorem bumpVec_path (x : Fin 1 → ℝ) (c t : ℝ) :
    bumpVec (Function.update x 0 (c + t)) = pdaBump (c + t) := by
  simp [bumpVec]

/-- For the gap witness, the asserted common derivative would equal both `0`
for the constant CEF version and `1` for the bump version. -/
theorem assemble (h1 : GapLaw.N1) (h2 : GapLaw.N2) (h3 : GapLaw.N3) (h4 : GapLaw.N4)
    (h5 : GapLaw.N5) : Target := by
  intro H
  have hprob : IsProbabilityMeasure gapJointLaw := h1.1
  have hY : Integrable Prod.snd gapJointLaw := h1.2.2.1
  obtain ⟨hXm, -, -, hint, -, hmean, -⟩ := h4 h1 h2
  obtain ⟨hpdf, hcef0, hcef1⟩ := h5 h1 h2 h3
  have hdiff : Differentiable ℝ pdaBump := h2.1.differentiable (by norm_num)
  obtain ⟨a, ha0, ha1⟩ := @H (ℝ × ℝ) _ gapJointLaw hprob 1 gapX Prod.snd hXm hint hY
    (fun x => gapPDF (x 0)) hpdf (fun _ => 0) bumpVec hcef0 hcef1 0
    (fun _ _ => differentiableAt_const _)
    (fun x _ => by
      simp only [bumpVec_path]
      exact (hdiff _).comp _ ((differentiableAt_const _).add differentiableAt_id))
  have e0 : a = 0 := ha0.unique (hasDerivAt_const _ _)
  have hpath : (fun t : ℝ => bumpVec (Function.update
      (fun j => mean gapJointLaw (fun ω => gapX ω j)) 0
      (mean gapJointLaw (fun ω => gapX ω 0) + t))) = pdaBump := by
    funext t
    rw [bumpVec_path, hmean, zero_add]
  rw [hpath] at ha1
  have e1 : a = 1 := ha1.unique h2.2.2
  rw [e0] at e1
  exact zero_ne_one e1

end

end AronowAudit.P001.Wave1.PdaLocalSupport
