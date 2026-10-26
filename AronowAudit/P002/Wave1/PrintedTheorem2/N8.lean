import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Every full-rank observed assignment accepts the LATE. -/
theorem n8_proof : N8 := by
  intro hprob hresidual haccept hfailure n P α hn hXi
  rcases hprob n P.pop with ⟨hbounded, hmono, hunion, hcompl, hmarkov⟩
  let failure : Finset (Fin n) → Prop :=
    fun S => (gram P.x S).det = 0 ∨ (gram P.x Sᶜ).det = 0
  have hcontains :
      probability P.pop (fun S => ¬ failure S) ≤ adjustedCoverage P (late P.pop) α := by
    unfold adjustedCoverage
    apply hmono
    intro S hS hgood
    have hT : (gram P.x S).det ≠ 0 := fun h => hgood (Or.inl h)
    have hC : (gram P.x Sᶜ).det ≠ 0 := fun h => hgood (Or.inr h)
    exact haccept n P α S hXi (hresidual n P hXi) hS hT hC
  have hcomp : probability P.pop (fun S => ¬ failure S) =
      1 - probability P.pop failure := hcompl hXi.1 failure
  have hbound : probability P.pop failure ≤ 1548 / ((n : ℝ) - 1) :=
    hfailure n P hn hXi
  apply max_le
  · exact (hbounded (adjustedAccepted P (late P.pop) α)).1
  · rw [hcomp] at hcontains
    linarith

end
end AronowAudit.P002.Wave1.PrintedTheorem2
