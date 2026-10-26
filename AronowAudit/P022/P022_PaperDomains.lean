import Mathlib

namespace AronowAudit.P022.PaperDomains

/-- T2's corrected finite bracketing step includes equality of the endpoint
CDF increment with the partition tolerance. No strict-gap premise is needed. -/
theorem cdf_partition_bracket (Pa Px Pb Aa Ax Ab δ : ℝ)
    (hPa : Pa ≤ Px) (hPb : Px ≤ Pb) (hAa : Aa ≤ Ax) (hAb : Ax ≤ Ab)
    (hgap : Pb ≤ Pa + δ) :
    Pb - Ab - δ ≤ Px - Ax ∧ Px - Ax ≤ Pa - Aa + δ := by
  constructor <;> linarith

end AronowAudit.P022.PaperDomains
