import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- The abbreviated full-joint function agrees with the full count function,
using N3 for its explicitly tabulated entries as well as its fallback.
This is valid at every ordered pair of labels. -/
private theorem n9_full_joint (hN3 : N3) (i j : Fin 12) (a b : Exposure) :
    jointCount cliqueF i j a b = cliqueFullJoint i j a b := by
  unfold N3 at hN3
  rw [hN3 i j a b]
  cases a <;> cases b <;>
    by_cases hij : i = j <;>
    by_cases hs : i.val / 4 = j.val / 4 <;>
    simp [cliqueFullJoint, cliqueJointTable, hij, hs, hN3]

/-- Reindex an arbitrary retained ordering by its image, subtract the omitted
event in natural numbers, and only then cast the smoothed counts. -/
theorem n9_proof : N9 := by
  intro hN2 hN3
  change RetainedInputs
  intro σ t hσ
  have hdelete (test : Fin 66 → Prop) [DecidablePred test] :
      (Finset.univ.filter (fun r : Fin 65 => test (σ r))).card =
        (Finset.univ.filter test).card - if test t then 1 else 0 := by
    calc
      (Finset.univ.filter (fun r : Fin 65 => test (σ r))).card =
          ((Finset.univ.map σ).filter test).card := by
        simp only [Finset.filter_map, Finset.card_map] <;> rfl
      _ = ((Finset.univ.filter test).erase t).card := by
        rw [hσ, Finset.filter_erase]
      _ = (Finset.univ.filter test).card - if test t then 1 else 0 := by
        by_cases ht : test t
        · simpa only [ht, ite_true] using
            (Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩))
        · rw [Finset.erase_eq_of_notMem (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ht)]
          simp only [ht, if_false, Nat.sub_zero]
  have hc (i : Fin 12) (a : Exposure) :
      exposureCount (fun r : Fin 65 => cliqueF (σ r)) i a =
        cliqueFullCount a - if cliqueF t i = a then 1 else 0 := by
    change (Finset.univ.filter (fun r : Fin 65 => cliqueF (σ r) i = a)).card = _
    rw [hdelete (fun r => cliqueF r i = a)]
    rw [show (Finset.univ.filter (fun r => cliqueF r i = a)).card =
        cliqueFullCount a from hN2 i a]
  have hj (i j : Fin 12) (a b : Exposure) :
      jointCount (fun r : Fin 65 => cliqueF (σ r)) i j a b =
        cliqueFullJoint i j a b - if cliqueF t i = a ∧ cliqueF t j = b then 1 else 0 := by
    change (Finset.univ.filter (fun r : Fin 65 =>
        cliqueF (σ r) i = a ∧ cliqueF (σ r) j = b)).card = _
    rw [hdelete (fun r => cliqueF r i = a ∧ cliqueF r j = b)]
    rw [show (Finset.univ.filter (fun r => cliqueF r i = a ∧ cliqueF r j = b)).card =
        cliqueFullJoint i j a b from n9_full_joint hN3 i j a b]
  have hbankF :
      (fun r : Fin 65 => exposure cliqueAdj (cliqueAssignments (σ r))) =
        (fun r : Fin 65 => cliqueF (σ r)) := by
    funext r
    exact (congrFun cliqueF_is_exposure (σ r)).symm
  constructor
  · funext i a
    change (smoothedWeight (fun r : Fin 65 =>
      exposure cliqueAdj (cliqueAssignments (σ r))) i a : ℝ) =
        ((cliqueWeights t i a : ℚ) : ℝ)
    rw [hbankF]
    unfold smoothedWeight cliqueWeights
    rw [hc i a]
    -- Subtraction stays inside ℕ on both sides: no cast-subtraction premise is needed.
    simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_add,
      Nat.cast_one] <;> norm_num
  · funext i j a b
    change (smoothedJoint (fun r : Fin 65 =>
      exposure cliqueAdj (cliqueAssignments (σ r))) i j a b : ℝ) =
        ((cliqueJoints t i j a b : ℚ) : ℝ)
    rw [hbankF]
    unfold smoothedJoint cliqueJoints
    rw [hj i j a b]
    by_cases hab : a = b <;> by_cases hij : i = j <;>
      simp [hab, hij, Rat.cast_div, Rat.cast_natCast, Nat.cast_add] <;> norm_num

end

end AronowAudit.P044.Wave1.SimulatedVariance
