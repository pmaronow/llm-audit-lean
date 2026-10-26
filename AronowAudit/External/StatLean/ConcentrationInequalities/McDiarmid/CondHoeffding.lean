/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.Probability.Moments.SubGaussian

/-!
# Imports for conditional sub-Gaussian bounds

This retained import bridge provides Mathlib's sub-Gaussian moment-generating
function infrastructure. It introduces no declarations.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {μ : Measure Ω}


end StatLean.ConcentrationInequalities
