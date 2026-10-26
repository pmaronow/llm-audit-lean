import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- A finite sum of a function of a type is its fiber counts times its values. -/
private theorem n14_sum_by_type {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) (g : β → ℚ) :
    (∑ x : α, g (f x)) =
      ∑ y : β, ((Finset.univ.filter (fun x => f x = y)).card : ℚ) * g y := by
  calc
    (∑ x : α, g (f x)) =
        ∑ y : β, ∑ x ∈ Finset.univ.filter (fun x => f x = y), g (f x) :=
      (Finset.sum_fiberwise (Finset.univ : Finset α) f (fun x => g (f x))).symm
    _ = ∑ y : β, ((Finset.univ.filter (fun x => f x = y)).card : ℚ) * g y := by
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ x ∈ Finset.univ.filter (fun x => f x = y), g (f x)) =
            ∑ _x ∈ Finset.univ.filter (fun x => f x = y), g y := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ = ((Finset.univ.filter (fun x => f x = y)).card : ℚ) * g y := by
          simp only [Finset.sum_const, nsmul_eq_mul]

/-- First group assignment indices by ordered exposure pair; then group
ordered unit pairs by equality and clique membership. -/
theorem n14_proof : N14 := by
  intro hN3
  unfold N3 at hN3
  change TypeCount2
  intro Ψ
  let A : Bool → Bool → ℚ := fun e s =>
    ∑ d : Exposure, ∑ d' : Exposure,
      (cliqueJointTable e s d d' : ℚ) * Ψ e s d d'
  have hpair (i j : Fin 12) :
      (∑ t : Fin 66,
        Ψ (decide (i = j)) (decide (i.val / 4 = j.val / 4))
          (cliqueF t i) (cliqueF t j)) =
        A (decide (i = j)) (decide (i.val / 4 = j.val / 4)) := by
    calc
      (∑ t : Fin 66,
          Ψ (decide (i = j)) (decide (i.val / 4 = j.val / 4))
            (cliqueF t i) (cliqueF t j)) =
          ∑ d : Exposure, ∑ d' : Exposure,
            (jointCount cliqueF i j d d' : ℚ) *
              Ψ (decide (i = j)) (decide (i.val / 4 = j.val / 4)) d d' := by
        simpa only [Fintype.sum_prod_type, Prod.mk.injEq, jointCount] using
          (n14_sum_by_type
            (fun t : Fin 66 => (cliqueF t i, cliqueF t j))
            (fun p : Exposure × Exposure =>
              Ψ (decide (i = j)) (decide (i.val / 4 = j.val / 4)) p.1 p.2))
      _ = A (decide (i = j)) (decide (i.val / 4 = j.val / 4)) := by
        simp only [A, hN3]
  let pairClass : Fin 12 × Fin 12 → Bool × Bool := fun p =>
    (decide (p.1 = p.2), decide (p.1.val / 4 = p.2.val / 4))
  have hclass (e s : Bool) :
      (Finset.univ.filter (fun p : Fin 12 × Fin 12 => pairClass p = (e, s))).card =
        cliquePairClassCount e s := by
    -- Four checks of 144 unit pairs; no exposure table is enumerated here.
    cases e <;> cases s <;> decide
  have hclasses :
      (∑ p : Fin 12 × Fin 12, A (pairClass p).1 (pairClass p).2) =
        ∑ e : Bool, ∑ s : Bool, (cliquePairClassCount e s : ℚ) * A e s := by
    calc
      (∑ p : Fin 12 × Fin 12, A (pairClass p).1 (pairClass p).2) =
          ∑ c : Bool × Bool,
            ((Finset.univ.filter (fun p => pairClass p = c)).card : ℚ) * A c.1 c.2 :=
        n14_sum_by_type pairClass (fun c : Bool × Bool => A c.1 c.2)
      _ = ∑ e : Bool, ∑ s : Bool, (cliquePairClassCount e s : ℚ) * A e s := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro e _
        apply Finset.sum_congr rfl
        intro s _
        rw [hclass e s]
  calc
    (∑ t : Fin 66, ∑ i : Fin 12, ∑ j : Fin 12,
        Ψ (decide (i = j)) (decide (i.val / 4 = j.val / 4))
          (cliqueF t i) (cliqueF t j)) =
        ∑ i : Fin 12, ∑ j : Fin 12, ∑ t : Fin 66,
          Ψ (decide (i = j)) (decide (i.val / 4 = j.val / 4))
            (cliqueF t i) (cliqueF t j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 12, ∑ j : Fin 12,
        A (decide (i = j)) (decide (i.val / 4 = j.val / 4)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hpair i j
    _ = ∑ p : Fin 12 × Fin 12, A (pairClass p).1 (pairClass p).2 := by
      simpa only [pairClass] using
        (Fintype.sum_prod_type (fun p : Fin 12 × Fin 12 =>
          A (pairClass p).1 (pairClass p).2)).symm
    _ = ∑ e : Bool, ∑ s : Bool, (cliquePairClassCount e s : ℚ) * A e s := hclasses
    _ = ∑ e : Bool, ∑ s : Bool, (cliquePairClassCount e s : ℚ) *
        ∑ d : Exposure, ∑ d' : Exposure,
          (cliqueJointTable e s d d' : ℚ) * Ψ e s d d' := rfl

end

end AronowAudit.P044.Wave1.SimulatedVariance
