import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDensity

/-! Finite-window counts and their measurability. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellWindowCounts (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000

def markedWindowCount {n : ℕ} (E : Set MatchUnit) (z : Fin n → MatchUnit) : ℕ :=
  (Finset.univ.filter (fun i => z i ∈ E)).card

theorem marked_window_count_measurable (n : ℕ) (E : Set MatchUnit)
    (hE : MeasurableSet E) : Measurable (fun z : Fin n → MatchUnit => markedWindowCount E z) := by
  have heq : (fun z : Fin n → MatchUnit => markedWindowCount E z) =
      fun z => ∑ i, if z i ∈ E then (1 : ℕ) else 0 := by
    funext z
    simp only [Finset.sum_boole, markedWindowCount, Nat.cast_id]
  rw [heq]
  exact Finset.measurable_sum _ (fun i _ =>
    Measurable.ite (hE.preimage (measurable_pi_apply i)) measurable_const measurable_const)


end AronowAudit.P001.TailA
