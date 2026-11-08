import SAP.P030.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P030
open scoped BigOperators
noncomputable section

/-- Ordinary partial division, so a zero denominator has no real value. -/
def partialRealQuotient (a b : ℝ) : Option ℝ := by
  classical
  exact if b = 0 then none else some (a / b)
def inverseSquare (d : ℝ) : ℝ := 1 / (((3/2 : ℝ)*d)^2)
def inverseSquareIndirect {N : ℕ} (d : Fin N → Fin N → ℝ) (z : Assignment N)
    (i : Fin N) : ℝ := ∑ j ∈ Finset.univ.erase i, treatment z j * inverseSquare (d i j)
def inverseSquareSpatial {N : ℕ} (d : Fin N → Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, inverseSquare (d i j)

def completeAssignments (N M : ℕ) : Finset (Assignment N) := by
  classical
  exact Finset.univ.filter (fun z => (Finset.univ.filter (fun i => z i = true)).card = M)
def proximalExposure {N : ℕ} (neighbors : Finset (Fin N)) (z : Assignment N) : ℝ :=
  ∑ j ∈ neighbors, treatment z j
def uniformMean {A : Type*} (Ω : Finset A) (X : A → ℝ) : ℝ :=
  (∑ z ∈ Ω, X z) / (Ω.card : ℝ)
def fixedSizeObjective (C M f : ℤ) : ℤ := f*(C-f)*M

end
end SAP.P030
