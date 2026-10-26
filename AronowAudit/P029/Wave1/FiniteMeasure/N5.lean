import AronowAudit.P029.Wave1.FiniteMeasureBlueprint

namespace AronowAudit.P029.Wave1.FiniteMeasure

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

noncomputable section

/-- Conditional finite independence holds under the literal normalized restriction. -/
theorem n5_proof : N5 := by
  classical
  intro hN2 hN4 L A B Y _ _ _ _ _ _ _ p hp V W X hCond x hx
  obtain ⟨hvalid, hmeasure⟩ := hN4 p hp X x hx
  -- This identity keeps the conditioning conjunction explicit, including at zero event mass.
  have hcondP (E : L → Prop) :
      fP (condLaw p X x) E =
        fP p (fun i => E i ∧ X i = x) / fP p (fun i => X i = x) := by
    simp only [fP, Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases hE : E i <;> by_cases hX : X i = x <;> simp [condLaw, fP, hE, hX]
  have hfinite : FIndep (condLaw p X x) V W := by
    intro a b
    rw [hcondP, hcondP, hcondP]
    simpa only [and_assoc] using hCond x a b hx
  rw [hmeasure]
  exact hN2 (condLaw p X x) hvalid V W hfinite

end

end AronowAudit.P029.Wave1.FiniteMeasure
