import AronowAudit.P001.Wave1.FinitePopulationPluginBlueprint
import AronowAudit.P001.Wave1.FinitePopulationPlugin.N1

namespace AronowAudit.P001.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance instDecidableP001cFinalFinitePopulationPlugin (p : Prop) : Decidable p := Classical.propDecidable p

theorem finite_population_and_plugin_display_corrections
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ2 : MemLp Z 2 μ) :
    (∀ (N : ℕ) (hN : 0 < N) (x : Fin N → ℝ),
      (∀ t : ℝ, fprob (uniformFiniteLaw N hN) (fun i => x i = t) =
        ((Finset.univ.filter (fun i => x i = t)).card : ℝ) / (N : ℝ)) ∧
      fmean (uniformFiniteLaw N hN) x = (∑ i, x i) / (N : ℝ) ∧
      fvar (uniformFiniteLaw N hN) x =
        (∑ i, (x i - (∑ j, x j) / (N : ℝ))^2) / (N : ℝ)) ∧
    (fprob (uniformFiniteLaw 4 (by norm_num))
        (fun i => (![3,4,3,10] : Fin 4 → ℝ) i = 3) = 1 / 2 ∧
      fprob (uniformFiniteLaw 4 (by norm_num))
        (fun i => (![3,4,3,10] : Fin 4 → ℝ) i = 4) = 1 / 4 ∧
      fprob (uniformFiniteLaw 4 (by norm_num))
        (fun i => (![3,4,3,10] : Fin 4 → ℝ) i = 10) = 1 / 4 ∧
      fmean (uniformFiniteLaw 4 (by norm_num)) ![3,4,3,10] = 5 ∧
      fvar (uniformFiniteLaw 4 (by norm_num)) ![3,4,3,10] = 17 / 2) ∧
    (var μ Z = mean μ (fun ω => (Z ω)^2) - (mean μ Z)^2) ∧
    (mean μ (fun ω => (Z ω)^2) + (mean μ Z)^2 - var μ Z = 2 * (mean μ Z)^2) ∧
    (∀ (x : ℕ → ℝ) (n : ℕ), 0 < n →
      let ν := empirical (fun i (_ : Unit) => x i) n ()
      IsProbabilityMeasure ν ∧
      mean ν id = (∑ i ∈ Finset.range n, x i) / (n : ℝ) ∧
      var ν id = (∑ i ∈ Finset.range n, (x i)^2) / (n : ℝ) -
        ((∑ i ∈ Finset.range n, x i) / (n : ℝ))^2) :=
  FinitePopulationPlugin.n1_proof μ Z hZ2

end
end AronowAudit.P001.Wave1
