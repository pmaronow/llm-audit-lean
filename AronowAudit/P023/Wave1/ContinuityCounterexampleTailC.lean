import AronowAudit.P023.Wave1.Lib.AmplificationSharpTailC
import AronowAudit.P023.Wave1.Lib.PopulationContinuityTailC

/-! The complete fixed uniform-law continuity counterexample, with its sharp amplification constant. -/
namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem continuity_only_counterexample_proof :
    Tendsto (amplification uniformMargins) atTop atTop ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∃ J₀, ∀ J ≥ J₀, 1 ≤ J →
      |amplification uniformMargins J - (4/Real.pi)*Real.log J| ≤ C) ∧
    (∀ J, 1 ≤ J → sSup {t | ∃ h : ℝ → ℝ, ContinuousOn h (Set.Icc (-1) 1) ∧ h 0 = 0 ∧
      (∀ x ∈ Set.Icc (-1) 1, |h x| ≤ 1) ∧ t = biasFunctional uniformMargins J h} = amplification uniformMargins J) ∧
    (∃ h : ℝ → ℝ, ∃ degrees : ℕ → ℕ,
      ContinuousOn h (Set.Icc (-1) 1) ∧ h 0 = 0 ∧
      (∀ x ∈ Set.Icc (-1) 1, |h x| ≤ 1/12) ∧ StrictMono degrees ∧
      (∀ m, 1 ≤ m → biasFunctional uniformMargins (degrees m) h ≥ (m : ℝ)/4) ∧
      (∀ J, 1 ≤ J → populationCoefficient uniformMargins J (fun x => 1/2+h x) = biasFunctional uniformMargins J h) ∧
      Tendsto (fun m => populationCoefficient uniformMargins (degrees m) (fun x => 1/2+h x)) atTop atTop ∧
      ¬ Tendsto (fun J => populationCoefficient uniformMargins J (fun x => 1/2+h x)) atTop (nhds 0) ∧
      Tendsto (populationRD uniformMargins (fun x => 1/2+h x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      (∀ x ∈ Set.Icc (-1) 1, 5/12 ≤ 1/2+h x ∧ 1/2+h x ≤ 7/12) ∧
      ¬ (∃ L : ℝ, ∀ x ∈ Set.Icc (-1) 1, ∀ x' ∈ Set.Icc (-1) 1, |h x-h x'| ≤ L*|x-x'|)) := by
  exact ⟨uniform_amplification_diverges, uniform_amplification_sharp_log,
    continuous_bias_norm, tc11_fixed_bad_mean_properties⟩

end
end AronowAudit.P023.Wave1
