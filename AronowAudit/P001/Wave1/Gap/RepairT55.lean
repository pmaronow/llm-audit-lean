import AronowAudit.P001.Wave1.VarianceSEContract.N1

/-! # P001-T55: the general variance-estimator contract

Definition 3.2.32 and footnote 23, pp. 113–114: arbitrary measurable estimators
with a root-`n` limiting law, and arbitrary nonnegative measurable estimates of
their sampling variance. The limiting law need not be Gaussian and its variance
may be zero. This exposes the accepted general bridge as the replacement for
the sample-mean-only association rejected by verifier ver-07.
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

-- Exact check against the already accepted arbitrary-estimator bridge.
example : VarianceSEContract.Target := variance_estimate_scale_general_contract

/-- Sample-mean specialization: once the corrected estimate's nonnegativity and
variance consistency have been established by the sample-mean calculation, all
three remaining consistency conclusions follow from the general contract.
Finite-sample residual identities and unbiasedness are separate facts. -/
example
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (h2 : MemLp (X 0) 2 μ)
    (hv : 0 < var μ (X 0))
    (hVnonneg : ∀ n ω, 0 ≤ sampleVariance X n ω / ((n : ℝ) - 1))
    (hVC : VarianceConsistent μ
      (fun n ω => sampleVariance X n ω / ((n : ℝ) - 1)) (var μ (X 0))) :
    let vhat : ℕ → Ω → ℝ := fun n ω => sampleVariance X n ω / ((n : ℝ) - 1)
    SEConsistent μ vhat (var μ (X 0)) ∧
    CP μ (fun n ω => (n : ℝ) * vhat n ω - var μ (X 0)) 0 ∧
    CP μ (fun n ω => Real.sqrt n * Real.sqrt (vhat n ω) -
      Real.sqrt (var μ (X 0))) 0 := by
  intro vhat
  have hmean : ∀ n, Measurable (sampleMean X n) := by
    intro n
    exact (Finset.measurable_sum _ fun i _ => hiid.1 i).div_const _
  have hV : ∀ n, Measurable (vhat n) := by
    intro n
    exact (((Finset.measurable_sum _ fun i _ => (hiid.1 i).pow_const 2).div_const _).sub
      ((hmean n).pow_const 2)).div_const _
  haveI instRepairT55GaussianProbability : IsProbabilityMeasure (gaussianReal 0 ⟨var μ (X 0), hv.le⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have h := variance_estimate_scale_general_contract μ (sampleMean X) vhat
    (mean μ (X 0)) hmean hV hVnonneg
    (gaussianReal 0 ⟨var μ (X 0), hv.le⟩)
    (memLp_id_gaussianReal' 2 (by norm_num))
    (central_limit_finite_variance μ X hiid h2 hv)
  have hvar : var (gaussianReal 0 ⟨var μ (X 0), hv.le⟩) id = var μ (X 0) :=
    variance_id_gaussianReal
  rw [hvar] at h
  have hSE := h.2.2.mp hVC
  exact ⟨hSE, h.1.mp hVC, h.2.1.mp hSE⟩

end
end AronowAudit.P001.Wave1
