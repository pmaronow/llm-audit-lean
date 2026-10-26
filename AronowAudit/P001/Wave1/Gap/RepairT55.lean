import AronowAudit.P001.Wave1.VarianceSEContract.N1

/-! # P001-T55: the general variance-estimator contract

Definition 3.2.32 and footnote 23, pp. 113–114: arbitrary measurable estimators
with a root-`n` limiting law, and arbitrary nonnegative measurable estimates of
their sampling variance. The limiting law need not be Gaussian and its variance
may be zero.
-/

namespace AronowAudit.P001.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableRepairT55 (p : Prop) : Decidable p := Classical.propDecidable p

/-- The corrected variance and standard-error consistency definitions, their two
centered forms, and their equivalence, for an arbitrary estimator and limit law.
The estimator and its root-`n` limit identify `var ν id` as the target variance;
centering and the square-root/square continuous-mapping argument establish the
equivalences without normality or strict positivity. -/
theorem variance_estimate_scale_general_contract
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
