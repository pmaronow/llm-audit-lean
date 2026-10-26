/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set



/-!
Import bridge for Bochner integrals and set integrals.

This retained module imports the Mathlib integral infrastructure used by its
dependents. No Markov estimate or union-bound declaration remains in this file.
-/

open MeasureTheory Filter Topology

namespace AsymptoticStatistics
namespace ForMathlib

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


end ForMathlib
end AsymptoticStatistics
