import Mathlib

/-! Smoke test for the pinned project: Mathlib imports and a trivial lemma checks. -/

namespace AronowAudit

theorem smoke (a b : ℝ) : a * b = b * a := mul_comm a b

end AronowAudit
