import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- Evaluate the real statistics at an enumerated assignment, then commute the
rational-to-real embedding with each statistic. -/
theorem n11_proof : N11 := by
  change StatisticIdentification
  intro t r
  have hExposure : exposure cliqueAdj (cliqueAssignments r) = cliqueF r :=
    (congrFun cliqueF_is_exposure r).symm
  constructor
  · calc
      htContrast (fun z => exposure cliqueAdj z) yR (castW t) .d01 .d00
          (cliqueAssignments r) =
          htContrast cliqueF yR (castW t) .d01 .d00 r := by
        simp only [htContrast, htMean, htTerm, hExposure]
      _ = ((cliqueT t r : ℚ) : ℝ) := by
        exact ratCast_htContrast cliqueF cliqueY (cliqueWeights t) .d01 .d00 r
  · calc
      varianceEstimate (fun z => exposure cliqueAdj z) yR (castW t) (castJ t)
          .d01 .d00 (cliqueAssignments r) =
          varianceEstimate cliqueF yR (castW t) (castJ t) .d01 .d00 r := by
        simp only [varianceEstimate, totalVarianceEstimate, totalCovarianceEstimate,
          hExposure]
      _ = ((cliqueV t r : ℚ) : ℝ) := by
        exact ratCast_varianceEstimate cliqueF cliqueY (cliqueWeights t)
          (cliqueJoints t) .d01 .d00 r

end

end AronowAudit.P044.Wave1.SimulatedVariance
