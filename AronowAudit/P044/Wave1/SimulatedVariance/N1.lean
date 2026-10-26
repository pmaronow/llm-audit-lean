import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint
import Mathlib.Tactic.FinCases

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Recover the increasing treated pair from its Boolean assignment. -/
theorem n1_proof : N1 := by
  have hlt : ∀ r : Fin 66, (cliquePairs r).1 < (cliquePairs r).2 := by
    intro r
    fin_cases r <;> decide +kernel
  -- Split the first index so each remaining check has only 66 cases.
  have hpairs : Function.Injective cliquePairs := by
    change ∀ r s : Fin 66, cliquePairs r = cliquePairs s → r = s
    intro r
    fin_cases r <;> decide +kernel
  change Function.Injective cliqueAssignments
  intro r s hrs
  have hmem (i : Fin 12) :
      (i = (cliquePairs r).1 ∨ i = (cliquePairs r).2) ↔
        (i = (cliquePairs s).1 ∨ i = (cliquePairs s).2) := by
    have he := congrFun hrs i
    change decide (i = (cliquePairs r).1 ∨ i = (cliquePairs r).2) =
      decide (i = (cliquePairs s).1 ∨ i = (cliquePairs s).2) at he
    exact decide_eq_decide.mp he
  have hu : (cliquePairs r).1 = (cliquePairs s).1 ∨
      (cliquePairs r).1 = (cliquePairs s).2 :=
    (hmem (cliquePairs r).1).mp (Or.inl rfl)
  have hv : (cliquePairs r).2 = (cliquePairs s).1 ∨
      (cliquePairs r).2 = (cliquePairs s).2 :=
    (hmem (cliquePairs r).2).mp (Or.inr rfl)
  apply hpairs
  rcases hu with hu | hu
  · have hv' : (cliquePairs r).2 = (cliquePairs s).2 := by
      rcases hv with hv | hv
      · exact (clique_pair_distinct r (hu.trans hv.symm)).elim
      · exact hv
    exact Prod.ext hu hv'
  · rcases hv with hv | hv
    · have hrev : (cliquePairs s).2 < (cliquePairs s).1 := by
        simpa only [hu, hv] using hlt r
      exact (lt_asymm (hlt s) hrev).elim
    · exact (clique_pair_distinct r (hu.trans hv.symm)).elim

end

end AronowAudit.P044.Wave1.SimulatedVariance
