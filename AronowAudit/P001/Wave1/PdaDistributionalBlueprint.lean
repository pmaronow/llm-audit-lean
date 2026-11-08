import AronowAudit.P001.Wave1.GapLawBlueprint

/-!
# Blueprint: refutation of `AronowAudit.P001.printed_pda_is_distributional` (P001-T102)

Record 1 of group P001a: P001-T102 / `AronowAudit.P001.printed_pda_is_distributional`;
resolution `refute`. Frozen contract (P001_Foundations.lean:5139): for every `K`, every
probability law `ν` on `Fin K → ℝ` with integrable coordinates, and all globally `C¹`
functions `m, m'` with `m = m'` `ν`-a.e., the coordinate derivatives `partialAt` at the
mean vector agree.

`Target` is the negation of exactly that contract; the `example` checks by `Iff.rfl` that
it is the negation of the frozen declaration's type.

Witness (paper proof, record 1): `K = 1`, `ν = gapJointLaw.map gapX` (covariate density
`(1/2)·1_{[-2,-1]∪[1,2]}`, mean `0`), `m = 0`, `m' = bumpVec`, `k = 0`. Both are `C¹`
and agree `ν`-a.e., while `partialAt m 0 0 = 0` and `partialAt m' 0 0 = 1`.

Nodes: `GapLaw.N1`-`GapLaw.N5` (shared with record 2, see `GapLawBlueprint`). There is no
record-specific node; the assembly below is fully proved.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.PdaDistributional

open AronowAudit.P001 AronowAudit.P001.Wave1.GapLaw MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded contract
`printed_pda_is_distributional`. -/
def Target : Prop :=
  ¬ ∀ {K : ℕ} (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν],
    (∀ k, Integrable (fun x => x k) ν) →
    ∀ (m m' : (Fin K → ℝ) → ℝ), ContDiff ℝ 1 m → ContDiff ℝ 1 m' → m =ᵐ[ν] m' →
    ∀ (k : Fin K),
      partialAt m (fun j => ∫ x, x j ∂ν) k = partialAt m' (fun j => ∫ x, x j ∂ν) k

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration). Only the
frozen theorem's *type* is read; its `sorry` proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P001.printed_pda_is_distributional) := Iff.rfl

/-- The coordinate derivative of the constant version at the zero mean is `0`. -/
theorem partialAt_zero_const : partialAt (fun _ : Fin 1 → ℝ => (0 : ℝ)) 0 0 = 0 := by
  simp [partialAt]

/-- The coordinate derivative of the bump version at the zero mean is `1` (from `N2`). -/
theorem partialAt_bumpVec (h2 : GapLaw.N2) : partialAt bumpVec 0 0 = 1 := by
  have h : (fun t : ℝ => bumpVec (Function.update (0 : Fin 1 → ℝ) 0 ((0 : Fin 1 → ℝ) 0 + t)))
      = pdaBump := by
    funext t
    simp [bumpVec]
  rw [partialAt, h]
  exact h2.2.2.deriv

/-- The nodes suffice: specialize the frozen contract to the gap witness at `K = 1`,
`k = 0`; it would force `0 = 1`. -/
theorem assemble (h1 : GapLaw.N1) (h2 : GapLaw.N2) (h4 : GapLaw.N4) : Target := by
  intro H
  obtain ⟨-, hprob, hint, -, hmean, -, hae⟩ := h4 h1 h2
  have hbump : ContDiff ℝ 1 bumpVec := h2.1.comp (contDiff_apply ℝ ℝ (0 : Fin 1))
  have key := @H 1 (gapJointLaw.map gapX) hprob hint (fun _ => 0) bumpVec contDiff_const
    hbump hae 0
  rw [hmean, partialAt_zero_const, partialAt_bumpVec h2] at key
  exact zero_ne_one key

/-- Nonvacuity record: given the shared nodes, the witness satisfies every hypothesis of the
frozen contract (probability law, integrable coordinates, two `C¹` functions equal a.e.). -/
example (h1 : GapLaw.N1) (h2 : GapLaw.N2) (h4 : GapLaw.N4) :
    IsProbabilityMeasure (gapJointLaw.map gapX) ∧
    (∀ k, Integrable (fun x : Fin 1 → ℝ => x k) (gapJointLaw.map gapX)) ∧
    ContDiff ℝ 1 (fun _ : Fin 1 → ℝ => (0 : ℝ)) ∧ ContDiff ℝ 1 bumpVec ∧
    (fun _ : Fin 1 → ℝ => (0 : ℝ)) =ᵐ[gapJointLaw.map gapX] bumpVec := by
  obtain ⟨-, hprob, hint, -, -, -, hae⟩ := h4 h1 h2
  exact ⟨hprob, hint, contDiff_const, h2.1.comp (contDiff_apply ℝ ℝ (0 : Fin 1)), hae⟩

end

end AronowAudit.P001.Wave1.PdaDistributional
