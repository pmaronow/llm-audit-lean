import AronowAudit.P001.Wave1.MeanHadamardBlueprint
import AronowAudit.P001.Wave1.MeanHadamard.N1
import AronowAudit.P001.Wave1.MeanHadamard.N2
import AronowAudit.P001.Wave1.MeanHadamard.N3

set_option autoImplicit false

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

theorem printed_finite_variance_mean_hadamard_refuted :
  ¬ ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], MemLp id 2 ν →
    ∃ L : KolmogorovSpace →L[ℝ] ℝ,
      HadamardAt {F | finiteSecondCDF F} Set.univ cdfMeanFunctional
        (kolmogorovEmbed (cdf ν id)) L :=
  MeanHadamard.assemble MeanHadamard.n1_proof MeanHadamard.n2_proof MeanHadamard.n3_proof

end

end AronowAudit.P001.Wave1
