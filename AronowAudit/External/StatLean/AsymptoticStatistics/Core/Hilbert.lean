/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The mean-zero subspace of `L²(P)`

This file defines the constant function `oneL2`, the integral functional
`integralL2`, and its kernel `L2ZeroMean P`, the submodule of mean-zero
functions in `Lp ℝ 2 P`.

Reference: van der Vaart, *Asymptotic Statistics*, §25.2.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.Hilbert

/-! ## The mean-zero `L²(P)` subspace -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The constant function `1` lifted to `Lp ℝ 2 P`. Available whenever `P` is a
finite (in particular probability) measure. -/
noncomputable def oneL2 (P : Measure Ω) [IsFiniteMeasure P] : Lp ℝ 2 P :=
  (memLp_const (1 : ℝ)).toLp _

/-- The integral functional `f ↦ ∫ f ∂P` as a continuous linear functional on
`Lp ℝ 2 P`, realised as the inner product against the constant `1`. The
identification `integralL2 P f = ∫ f ∂P` is left for downstream lemmas. -/
noncomputable def integralL2 (P : Measure Ω) [IsFiniteMeasure P] :
    Lp ℝ 2 P →L[ℝ] ℝ :=
  innerSL ℝ (oneL2 P)

/-- The closed submodule of mean-zero `L²(P)` functions: the kernel of the
integral functional `integralL2 P`. -/
noncomputable def L2ZeroMean (P : Measure Ω) [IsFiniteMeasure P] :
    Submodule ℝ (Lp ℝ 2 P) :=
  LinearMap.ker (integralL2 P).toLinearMap




section Hilbert

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]


variable [CompleteSpace E]


end Hilbert

end AsymptoticStatistics.Core.Hilbert
