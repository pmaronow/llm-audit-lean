/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
Convergence in probability from mean + variance control.

The probability estimate in Step 4 of Theorem 7.2 is: if `E[Y_n] → c` and
`Var[Y_n] → 0`, then `Y_n → c` in probability.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics


end AsymptoticStatistics
