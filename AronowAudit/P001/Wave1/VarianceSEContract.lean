import AronowAudit.P001.Wave1.VarianceSEContractBlueprint
import AronowAudit.P001.Wave1.VarianceSEContract.N1

namespace AronowAudit.P001.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableP001cFinalVarianceSEContract (p : Prop) : Decidable p := Classical.propDecidable p

theorem variance_estimator_consistency_contract
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (θhat Vhat : ℕ → Ω → ℝ) (θ : ℝ)
    (hθmeas : ∀ n, Measurable (θhat n)) (hVmeas : ∀ n, Measurable (Vhat n))
    (hVnonneg : ∀ n ω, 0 ≤ Vhat n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν2 : MemLp id 2 ν)
    (hlimit : CD μ (fun n ω => Real.sqrt n * (θhat n ω - θ)) ν) :
    (VarianceConsistent μ Vhat (var ν id) ↔
      CP μ (fun n ω => (n : ℝ) * Vhat n ω - var ν id) 0) ∧
    (SEConsistent μ Vhat (var ν id) ↔
      CP μ (fun n ω => Real.sqrt n * Real.sqrt (Vhat n ω) -
        Real.sqrt (var ν id)) 0) ∧
    (VarianceConsistent μ Vhat (var ν id) ↔ SEConsistent μ Vhat (var ν id)) :=
  VarianceSEContract.n1_proof μ θhat Vhat θ hθmeas hVmeas hVnonneg ν hν2 hlimit

end
end AronowAudit.P001.Wave1
