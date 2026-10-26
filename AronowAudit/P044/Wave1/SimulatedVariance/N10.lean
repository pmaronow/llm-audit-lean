import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.Basic

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- Transport every statistic of the bank inputs and actual assignment.
The two factors of 66 come from the omitted profile and independent assignment. -/
theorem n10_proof : N10 := by
  intro hDesign hBank hFiber hInputs
  change IndependentTransport
  intro P hP φ
  let G : (Fin 65 → Assignment 12) → ℝ := fun b =>
    (∑ r : Fin 66, φ (bankW b) (bankQ b) (cliqueAssignments r)) / 66
  let g : Fin 66 → ℝ := fun t =>
    (∑ r : Fin 66, φ (castW t) (castJ t) (cliqueAssignments r)) / 66
  have hActual (b : Fin 65 → Assignment 12) :
      expect P.mass (fun z => φ (bankW b) (bankQ b) z) = G b := by
    change (∑ z, P.mass z * φ (bankW b) (bankQ b) z) = _
    rw [hP]
    exact hDesign.2.2 (fun z => φ (bankW b) (bankQ b) z)
  have hRetained (σ : Fin 65 ↪ Fin 66) (t : Fin 66)
      (hσ : Finset.univ.map σ = Finset.univ.erase t) :
      G (fun r => cliqueAssignments (σ r)) = g t := by
    obtain ⟨hw, hq⟩ := hInputs σ t hσ
    dsimp only [G, g]
    rw [hw, hq]
  have hFiberSum :
      (∑ σ : Fin 65 ↪ Fin 66, G (fun r => cliqueAssignments (σ r))) =
        (Nat.factorial 65 : ℝ) * ∑ t : Fin 66, g t :=
    hFiber (fun σ => G (fun r => cliqueAssignments (σ r))) g hRetained
  have hFac : (Nat.factorial 66 : ℝ) = 66 * (Nat.factorial 65 : ℝ) := by
    exact_mod_cast (Nat.factorial_succ 65)
  have hFac0 : (Nat.factorial 65 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero 65)
  have hCancel (v : ℝ) :
      ((Nat.factorial 65 : ℝ) * (v / 66)) / (Nat.factorial 66 : ℝ) =
        (1 / 4356 : ℝ) * v := by
    rw [hFac]
    field_simp [hFac0] <;> ring
  calc
    expect (indepMass P) (fun x => φ (bankW x.1) (bankQ x.1) x.2) =
        ∑ b : Fin 65 → Assignment 12,
          distinctBankMass P b * expect P.mass (fun z => φ (bankW b) (bankQ b) z) := by
      simp only [expect, indepMass, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
    _ = ∑ b : Fin 65 → Assignment 12, distinctBankMass P b * G b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [hActual b]
    _ = (∑ σ : Fin 65 ↪ Fin 66, G (fun r => cliqueAssignments (σ r))) /
        (Nat.factorial 66 : ℝ) := hBank P hP G
    _ = ((Nat.factorial 65 : ℝ) * ∑ t : Fin 66, g t) /
        (Nat.factorial 66 : ℝ) := by rw [hFiberSum]
    _ = (1 / 4356 : ℝ) *
        (∑ t : Fin 66, ∑ r : Fin 66,
          φ (castW t) (castJ t) (cliqueAssignments r)) := by
      dsimp only [g]
      rw [← Finset.sum_div]
      exact hCancel _
    _ = expect (fun x : Fin 66 × Fin 66 => ((cliqueJointMass false x : ℚ) : ℝ))
        (fun x => φ (castW x.1) (castJ x.1) (cliqueAssignments x.2)) := by
      simp [expect, cliqueJointMass, Fintype.sum_prod_type, Finset.mul_sum]

end

end AronowAudit.P044.Wave1.SimulatedVariance
