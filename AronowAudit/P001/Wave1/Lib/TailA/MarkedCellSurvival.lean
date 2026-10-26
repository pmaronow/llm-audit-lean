import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDiscreteLimits
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellLocalization
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellWindowCounts

/-! Finite-window counts are bounded by the sample size and additive on disjoint sets. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellSurvival (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000


theorem marked_window_count_le (n : ℕ) (E : Set MatchUnit) (z : Fin n → MatchUnit) :
    markedWindowCount E z ≤ n := by
  simpa only [markedWindowCount, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun i => z i ∈ E)

theorem marked_window_count_union (n : ℕ) (E F : Set MatchUnit) (hEF : Disjoint E F)
    (z : Fin n → MatchUnit) :
    markedWindowCount (E ∪ F) z = markedWindowCount E z+markedWindowCount F z := by
  have hd : Disjoint (Finset.univ.filter (fun i => z i ∈ E))
      (Finset.univ.filter (fun i => z i ∈ F)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Set.disjoint_left.mp hEF (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  calc
    _ = (Finset.univ.filter (fun i => z i ∈ E) ∪
        Finset.univ.filter (fun i => z i ∈ F)).card := by
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Set.mem_union]
    _ = _ := Finset.card_union_of_disjoint hd


end AronowAudit.P001.TailA
