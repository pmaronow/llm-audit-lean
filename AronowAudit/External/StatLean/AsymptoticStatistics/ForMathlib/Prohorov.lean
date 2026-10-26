/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.Contiguity

/-!
# Prohorov-type tightness and subsequence extraction on probability measures

Van der Vaart's representation theorem (Theorem 7.10, §7.3,
"Convergence to a Normal Experiment") uses two Prohorov-type facts:
tight marginals give tight joint laws, and a tight sequence of probability
measures on a Polish space admits a weakly convergent subsequence.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics
namespace Prohorov


end Prohorov
end AsymptoticStatistics
