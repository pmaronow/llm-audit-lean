import AronowAudit.P001.Wave1.GapLawBlueprint

/-!
# Blueprint: refutation of `AronowAudit.P001.printed_pda_local_support_invariance` (P001-T102)

Record 2 of group P001a: P001-T102 / `AronowAudit.P001.printed_pda_local_support_invariance`;
resolution `refute`. Frozen contract (P001_Foundations.lean:10000): on every probability
space, for a covariate vector `X` with integrable coordinates and a vector PDF `f`, an
integrable `Y`, two CEF versions `m, m'` whose `k`-th coordinate paths are differentiable at
every point of positive density, there is one common derivative `a` of both paths at the
covariate mean.

`Target` is the negation of exactly that contract with `Ω : Type` (universe 0); the
universe-polymorphic frozen theorem would in particular give its universe-0 instance, so
this negation refutes it. The `example` checks by `Iff.rfl` that `Target` is the negation of
the frozen type at universe 0.

Witness (paper proof, record 2): `Ω = ℝ × ℝ`, `μ = gapJointLaw`, `K = 1`, `X = gapX`,
`Y = Prod.snd`, `f x = gapPDF (x 0)`, `m = 0`, `m' = bumpVec`, `k = 0`. Both versions are
globally `C¹`, so all local differentiability premises hold (including at the support
endpoints); the mean is `0`, where the derivatives are `0` and `1`.

Nodes: `GapLaw.N1`-`GapLaw.N5` (shared with record 1). No record-specific node; the
assembly is fully proved. The separately corrected support-neighbourhood theorem is a
different statement and is not refuted here.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.PdaLocalSupport

open AronowAudit.P001 AronowAudit.P001.Wave1.GapLaw MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded contract
`printed_pda_local_support_invariance` (universe 0). -/
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

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration, universe 0).
Only the frozen theorem's *type* is read; its `sorry` proof is never used. -/
example : Target ↔
    ¬ (type_of% @AronowAudit.P001.printed_pda_local_support_invariance.{0}) := Iff.rfl

/-- Along the `0`-th coordinate path, `bumpVec` is the scalar bump shifted by `x 0`. -/
theorem bumpVec_path (x : Fin 1 → ℝ) (c t : ℝ) :
    bumpVec (Function.update x 0 (c + t)) = pdaBump (c + t) := by
  simp [bumpVec]

/-- The nodes suffice: specialize the frozen contract to the gap witness; the common
derivative would be both `0` (constant version) and `1` (bump version). -/
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

/-- Nonvacuity record: given the shared nodes, the witness satisfies every hypothesis of the
frozen contract, including both local differentiability premises on `{f > 0}`. -/
example (h1 : GapLaw.N1) (h2 : GapLaw.N2) (h3 : GapLaw.N3) (h4 : GapLaw.N4)
    (h5 : GapLaw.N5) :
    IsProbabilityMeasure gapJointLaw ∧ Measurable gapX ∧
    (∀ j, Integrable (fun ω => gapX ω j) gapJointLaw) ∧ Integrable Prod.snd gapJointLaw ∧
    HasVectorPDF (gapJointLaw.map gapX) (fun x => gapPDF (x 0)) ∧
    IsCEF gapJointLaw gapX Prod.snd (fun _ => 0) ∧ IsCEF gapJointLaw gapX Prod.snd bumpVec ∧
    (∀ x : Fin 1 → ℝ, 0 < gapPDF (x 0) →
      DifferentiableAt ℝ (fun t => bumpVec (Function.update x 0 (x 0 + t))) 0) := by
  have hprob : IsProbabilityMeasure gapJointLaw := h1.1
  have hY : Integrable Prod.snd gapJointLaw := h1.2.2.1
  obtain ⟨hXm, -, -, hint, -, -, -⟩ := h4 h1 h2
  obtain ⟨hpdf, hcef0, hcef1⟩ := h5 h1 h2 h3
  refine ⟨hprob, hXm, hint, hY, hpdf, hcef0, hcef1, fun x _ => ?_⟩
  simp only [bumpVec_path]
  exact ((h2.1.differentiable (by norm_num)) _).comp _
    ((differentiableAt_const _).add differentiableAt_id)

end

end AronowAudit.P001.Wave1.PdaLocalSupport
