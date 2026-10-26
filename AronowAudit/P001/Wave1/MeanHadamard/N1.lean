import AronowAudit.P001.Wave1.MeanHadamardBlueprint

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.MeanHadamard

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

theorem n1_proof : N1 := by
  classical
  intro ν _ hν
  let F : KolmogorovSpace := kolmogorovEmbed (AronowAudit.P001.cdf ν id)
  have hF : finiteSecondCDF F := by
    refine ⟨ν, inferInstance, hν, ?_⟩
    intro x
    exact (kolmogorov_embedding_preserves_cdf_supporting ν x).symm
  refine ⟨hF, ?_⟩
  change cdfMeanFunctional F = mean ν id
  rw [cdfMeanFunctional, dif_pos hF]
  let ρ : Measure ℝ := hF.choose
  have hρ : IsProbabilityMeasure ρ := hF.choose_spec.1
  letI : IsProbabilityMeasure ρ := hρ
  have hρcdf (x : ℝ) : AronowAudit.P001.cdf ρ id x =
      AronowAudit.P001.cdf ν id x := by
    calc
      AronowAudit.P001.cdf ρ id x = F x := hF.choose_spec.2.2 x
      _ = AronowAudit.P001.cdf ν id x :=
        kolmogorov_embedding_preserves_cdf_supporting ν x
  have hCDF : ProbabilityTheory.cdf ρ = ProbabilityTheory.cdf ν := by
    apply StieltjesFunction.ext
    intro x
    rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
    simpa only [AronowAudit.P001.cdf, prob, Measure.real, id_eq,
      Set.Iic] using hρcdf x
  have hEq : ρ = ν := Measure.eq_of_cdf ρ ν hCDF
  change mean ρ id = mean ν id
  rw [hEq]

end

end AronowAudit.P001.Wave1.MeanHadamard
