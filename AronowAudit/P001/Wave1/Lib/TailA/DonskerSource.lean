import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalDistribution

/-!
# Half-line Donsker source

The StatLean half-line Donsker theorem gives the full empirical-process limit
for an arbitrary real probability measure, including measures with atoms.
-/

namespace AronowAudit.P001.Wave1.TailA

open MeasureTheory

/-- Direct access to the carrier-agnostic half-line Donsker theorem. -/
theorem half_line_donsker_source (P : Measure ℝ) [IsProbabilityMeasure P] :
    AsymptoticStatistics.EmpiricalProcess.IsPDonskerWithBridge
      AsymptoticStatistics.EmpiricalProcess.halfLineIndicatorClass P :=
  AsymptoticStatistics.EmpiricalProcess.halfLine_isPDonskerWithBridge P

end AronowAudit.P001.Wave1.TailA
