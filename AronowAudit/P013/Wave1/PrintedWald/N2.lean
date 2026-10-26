import AronowAudit.P013.Wave1.PrintedWaldBlueprint
import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Disjoint collections of coordinates give full vector independence; a coordinate
contains at most two units, including at the odd population sizes. -/
theorem n2_proof : N2 := by
  classical
  intro n
  have hbase : GenuineDependency (wBase n) (wBasePop n).exposure (wGraph n) := by
    have h := coordinate_population_genuine_dependency (wAtom n) (wCoords n)
      (wIndex n) (fun i a => pairExposure a (decide (i.val % 2 = 1)))
    change GenuineDependency (wBase n) (wBasePop n).exposure
      (fun i j => decide (i.val / 2 = j.val / 2))
    simpa only [wBase, wBasePop, Fin.ext_iff, wIndex] using h
  constructor
  · intro A B hdis hno a b
    have h := hbase A B hdis hno a b
    simpa only [wDesign, wPop, relabelPopulation, probability_relabel,
      Equiv.symm_apply_apply] using h
  · intro i
    change (∑ j : Fin (n + 1),
      if decide (i.val / 2 = j.val / 2) = true then 1 else 0 : ℕ) ≤ 2
    simp only [decide_eq_true_eq]
    rw [sum_boole]
    -- The remainder modulo two is injective on a fixed quotient fibre.
    let bit : Fin (n + 1) → Fin 2 := fun j => ⟨j.val % 2, by omega⟩
    have hinj : Set.InjOn bit
        (↑(univ.filter (fun j : Fin (n + 1) => i.val / 2 = j.val / 2)) :
          Set (Fin (n + 1))) := by
      intro j hj k hk hbit
      have hjq : i.val / 2 = j.val / 2 := (mem_filter.mp hj).2
      have hkq : i.val / 2 = k.val / 2 := (mem_filter.mp hk).2
      have hrem : j.val % 2 = k.val % 2 := congrArg Fin.val hbit
      apply Fin.ext
      omega
    have hcard : (univ.filter (fun j : Fin (n + 1) => i.val / 2 = j.val / 2)).card ≤
        (univ : Finset (Fin 2)).card := by
      apply card_le_card_of_injOn bit
      · intro j _
        exact mem_univ _
      · exact hinj
    simpa only [card_univ, Fintype.card_fin, Nat.cast_id] using hcard

end

end AronowAudit.P013.Wave1.PrintedWald
