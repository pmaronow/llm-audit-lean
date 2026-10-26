import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- Count the labels separately at each unit, then sum over the twelve units. -/
theorem n13_proof : N13 := by
  intro hN2
  change TypeCount1
  intro Φ
  have hunit (i : Fin 12) :
      (∑ t : Fin 66, Φ (cliqueF t i)) =
        ∑ d : Exposure, (cliqueFullCount d : ℚ) * Φ d := by
    calc
      (∑ t : Fin 66, Φ (cliqueF t i)) =
          ∑ d : Exposure, ∑ t ∈ Finset.univ.filter (fun t => cliqueF t i = d),
            Φ (cliqueF t i) :=
        (Finset.sum_fiberwise (Finset.univ : Finset (Fin 66))
          (fun t => cliqueF t i) (fun t => Φ (cliqueF t i))).symm
      _ = ∑ d : Exposure, (cliqueFullCount d : ℚ) * Φ d := by
        apply Finset.sum_congr rfl
        intro d _
        calc
          (∑ t ∈ Finset.univ.filter (fun t => cliqueF t i = d), Φ (cliqueF t i)) =
              ∑ _t ∈ Finset.univ.filter (fun t => cliqueF t i = d), Φ d := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [(Finset.mem_filter.mp ht).2]
          _ = (cliqueFullCount d : ℚ) * Φ d := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            rw [show (Finset.univ.filter (fun t => cliqueF t i = d)).card =
                cliqueFullCount d from hN2 i d]
  calc
    (∑ t : Fin 66, ∑ i : Fin 12, Φ (cliqueF t i)) =
        ∑ i : Fin 12, ∑ t : Fin 66, Φ (cliqueF t i) := Finset.sum_comm
    _ = ∑ _i : Fin 12, ∑ d : Exposure, (cliqueFullCount d : ℚ) * Φ d := by
      apply Finset.sum_congr rfl
      intro i _
      exact hunit i
    _ = 12 * ∑ d : Exposure, (cliqueFullCount d : ℚ) * Φ d := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]

end

end AronowAudit.P044.Wave1.SimulatedVariance
