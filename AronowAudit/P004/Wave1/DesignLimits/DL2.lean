import AronowAudit.P004.Wave1.DesignLimits.DL1

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Vanishing moments imply convergence to zero in probability. -/
theorem dl2_proof : DL2 := by
  classical
  intro p hp U
  constructor
  · intro hmoment ε hε
    have hupper : Tendsto (fun N => expect (p N) (fun z => |U N z|) / ε)
        atTop (nhds 0) := by
      simpa only [zero_div] using hmoment.div_const ε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun N => prob_nonneg_finite (p N) (hp N) _)
      (fun N => (dl1_proof (p N) (hp N) (U N) ε hε).1)
  · intro hmoment ε hε
    have hupper : Tendsto (fun N => expect (p N) (fun z => (U N z) ^ 2) / ε ^ 2)
        atTop (nhds 0) := by
      simpa only [zero_div] using hmoment.div_const (ε ^ 2)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun N => prob_nonneg_finite (p N) (hp N) _)
      (fun N => (dl1_proof (p N) (hp N) (U N) ε hε).2)

end
end AronowAudit.P004.Wave1.DesignLimits
