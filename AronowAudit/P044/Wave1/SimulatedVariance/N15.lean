import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- The omission-formula weight depends on a unit only through its omitted label. -/
def momentTypeWeight (d a : Exposure) : ℚ :=
  ((cliqueFullCount a - if d = a then 1 else 0 : ℕ) + 1 : ℕ) / (66 : ℚ)

theorem momentTypeWeight_eq (t : Fin 66) (i : Fin 12) (a : Exposure) :
    cliqueWeights t i a = momentTypeWeight (cliqueF t i) a := rfl

/-- Expand the four-element exposure type without enumerating assignments. -/
theorem moment_sum_exposure (f : Exposure → ℚ) :
    (∑ d : Exposure, f d) = f .d11 + (f .d10 + (f .d01 + f .d00)) := by
  change (∑ d ∈ ({Exposure.d11, .d10, .d01, .d00} : Finset Exposure), f d) = _
  simp

theorem moment_average (f : Fin 66 → ℚ) :
    expect (fun _ : Fin 66 => (1 / 66 : ℚ)) f = (∑ t : Fin 66, f t) / 66 := by
  unfold expect
  rw [← Finset.mul_sum]
  ring

/-- True independent-observation marginals are the full counts divided by 66. -/
theorem momentObservationMarginal_eq (t : Fin 66) (i : Fin 12) (a : Exposure) :
    cliqueObservationMarginal t false i a = (cliqueFullCount a : ℚ) / 66 := rfl

theorem n15_proof : N15 := by
  intro htypes
  change expect (fun _ : Fin 66 => (1 / 66 : ℚ))
    (fun t => cliqueConditionalMean t false) = -67 / 53592
  let Φ : Exposure → ℚ := fun d =>
    ((cliqueFullCount .d01 : ℚ) / 66) / momentTypeWeight d .d01 -
      ((cliqueFullCount .d00 : ℚ) / 66) / momentTypeWeight d .d00
  have hmean (t : Fin 66) :
      cliqueConditionalMean t false = (∑ i : Fin 12, Φ (cliqueF t i)) / 12 := by
    dsimp [cliqueConditionalMean, cliqueObservationMarginal, cliqueWeights,
      momentTypeWeight, Φ]
    rw [Finset.sum_sub_distrib]
  have hcount :
      (∑ t : Fin 66, ∑ i : Fin 12, Φ (cliqueF t i)) =
        12 * ∑ d : Exposure, (cliqueFullCount d : ℚ) * Φ d := htypes Φ
  rw [moment_average]
  simp_rw [hmean]
  rw [← Finset.sum_div, hcount] <;>
    norm_num [moment_sum_exposure, Φ, momentTypeWeight, cliqueFullCount]

end

end AronowAudit.P044.Wave1.SimulatedVariance
