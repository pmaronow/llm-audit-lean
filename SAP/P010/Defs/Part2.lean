import SAP.P010.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P010

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology BigOperators

/-! Bayes propensities, odds, and normalization using Mathlib sums and integrals. -/

noncomputable def propensity (π fR fO : ℝ) : ℝ := π*fR / (π*fR+(1-π)*fO)

noncomputable def odds (p : ℝ) : ℝ := p/(1-p)

noncomputable def reverseOdds (p : ℝ) : ℝ := (1-p)/p

noncomputable def normalizeMass {n : ℕ} (f w : Fin n → ℝ) (x : Fin n) : ℝ :=
  f x*w x / ∑ u : Fin n, f u*w u

noncomputable def originalDistribution : Fin 2 → ℝ := ![3/4,1/4]

noncomputable def replicationDistribution : Fin 2 → ℝ := ![1/4,3/4]

noncomputable def cellPropensity (x : Fin 2) : ℝ :=
  propensity (1/2) (replicationDistribution x) (originalDistribution x)

noncomputable def sigmoid (η : ℝ) : ℝ := Real.exp η/(1+Real.exp η)

noncomputable def normalizeDensity {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f w : Ω → ℝ) (x : Ω) : ℝ :=
  f x*w x / ∫ u, f u*w u ∂ν

end SAP.P010
