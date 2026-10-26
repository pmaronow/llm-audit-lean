import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # SieveRate N10: the Chebyshev bound on [-1,1] -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n10_proof : N10 := by
  intro d z hz
  have hcos : Real.cos (Real.arccos z) = z := Real.cos_arccos hz.1 hz.2
  calc
    |(Chebyshev.T ℝ (d : ℤ)).eval z| =
        |(Chebyshev.T ℝ (d : ℤ)).eval (Real.cos (Real.arccos z))| := by rw [hcos]
    _ = |Real.cos (((d : ℤ) : ℝ) * Real.arccos z)| := by
      rw [Polynomial.Chebyshev.T_real_cos]
    _ ≤ 1 := Real.abs_cos_le_one _

end

end AronowAudit.P001.Wave1.SieveRate
