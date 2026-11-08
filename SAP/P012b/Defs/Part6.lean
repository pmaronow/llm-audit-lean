import SAP.P012b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P012b

/-- Objective in Web Appendix 1, display (1); its second coordinate is inactive. -/
noncomputable def annealingObjective (ε h p : ℝ) : ℝ := 1 / (1 + ε + h)

/-- Scalar objective values on the displayed square, independently of compatibility. -/
def squareObjectiveValues (ε : ℝ) : Set ℝ :=
  {r | ∃ h ∈ Set.Icc (-1 : ℝ) 1, ∃ p ∈ Set.Icc (-1 : ℝ) 1,
    r = annealingObjective ε h p}

def T24Statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (∀ h ∈ Set.Icc (-1 : ℝ) 1, ∀ p ∈ Set.Icc (-1 : ℝ) 1,
      0 < annealingObjective ε h p ∧ annealingObjective ε h p ≤ 1 / ε) ∧
    IsGreatest (squareObjectiveValues ε) (1 / ε) ∧
    annealingObjective ε (-1) 0 = 1 / ε ∧
    (∀ H : State, Simple H → 0 < traitDegree H false → 0 < traitDegree H true →
      HomophilyDefined H ∧ homophily H = some (hValue H) ∧
      -1 ≤ hValue H ∧ hValue H ≤ 1 ∧
      0 < annealingObjective ε (hValue H) 0 ∧
      annealingObjective ε (hValue H) 0 ≤ 1 / ε)

end SAP.P012b
