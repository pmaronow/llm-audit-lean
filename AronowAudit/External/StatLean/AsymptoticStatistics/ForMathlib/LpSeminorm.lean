/-
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The `L²` seminorm on a.e. strongly measurable functions

For an a.e. strongly measurable function, `eLpNorm f 2 μ` equals the integral
seminorm `eLpNorm' f 2 μ`.
-/

namespace MeasureTheory
open scoped ENNReal


variable {α ε : Type*} [MeasurableSpace α] [ENorm ε] [TopologicalSpace ε]
  {μ : Measure α} {f : α → ε}

/-- On a.e. strongly measurable functions, `eLpNorm f 2` is the integral seminorm. -/
theorem eLpNorm_two_eq_eLpNorm' (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = eLpNorm' f 2 μ := by
  simpa only [ENNReal.toReal_ofNat] using
    eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num) hf


end MeasureTheory
