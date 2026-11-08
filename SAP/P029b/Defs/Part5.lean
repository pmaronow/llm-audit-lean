import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b

open scoped BigOperators

/-- Root mean squared error for a supplied estimate array and benchmark array. -/
noncomputable def empiricalRMSE {R : ℕ} (t b : Fin R → ℝ) : ℝ :=
  Real.sqrt ((∑ r, (t r - b r) ^ 2) / (R : ℝ))

/-- The scoring convention alone, with a supplied benchmark and 2500 replicates. -/
def T22Statement : Prop :=
  ∀ t : Fin 2500 → ℝ,
    empiricalRMSE t (fun _ => 5) =
      Real.sqrt ((∑ r, (t r - 5) ^ 2) / (2500 : ℝ))

end SAP.P029b
