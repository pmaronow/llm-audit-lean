import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Order.Interval.Finset.Fin

namespace AronowAudit.P044.Wave1.SimulatedVariance

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

/-- The successive sampling factors telescope to the reciprocal of `66!`. -/
theorem n6_proof : N6 := by
  classical
  intro h1 _h4
  change Function.Injective cliqueAssignments at h1
  intro P hP b
  have hmass (t : Fin 66) : P.mass (cliqueAssignments t) = (1 / 66 : ℝ) := by
    rw [hP]
    unfold cliqueMass
    simp only [h1.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hzero (z : Assignment 12) (hz : z ∉ Set.range cliqueAssignments) :
      P.mass z = 0 := by
    rw [hP]
    unfold cliqueMass
    apply Finset.sum_eq_zero
    intro t _
    have hne : cliqueAssignments t ≠ z := by
      intro ht
      exact hz ⟨t, ht⟩
    exact if_neg hne
  have hmass_range (z : Assignment 12) (hz : z ∈ Set.range cliqueAssignments) :
      P.mass z = (1 / 66 : ℝ) := by
    obtain ⟨t, rfl⟩ := hz
    exact hmass t
  constructor
  · rintro ⟨hb, hs⟩
    have hprefix (r : Fin 65) :
        (∑ j ∈ Finset.univ.filter (fun j : Fin 65 => j < r), P.mass (b j)) =
          (r.val : ℝ) / 66 := by
      have hcard :
          (Finset.univ.filter (fun j : Fin 65 => j < r)).card = r.val := by
        have heq : Finset.univ.filter (fun j : Fin 65 => j < r) = Finset.Iio r := by
          ext j
          simp
        rw [heq, Fin.card_Iio]
      calc
        (∑ j ∈ Finset.univ.filter (fun j : Fin 65 => j < r), P.mass (b j)) =
            ∑ j ∈ Finset.univ.filter (fun j : Fin 65 => j < r), (1 / 66 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hmass_range (b j) (hs j)
        _ = (r.val : ℝ) / 66 := by
          rw [Finset.sum_const, hcard]
          simp only [nsmul_eq_mul]
          ring
    have hfactor (r : Fin 65) :
        P.mass (b r) /
            (1 - ∑ j ∈ Finset.univ.filter (fun j : Fin 65 => j < r), P.mass (b j)) =
          1 / ((66 - r.val : ℕ) : ℝ) := by
      rw [hmass_range (b r) (hs r), hprefix r]
      have hr : r.val < 65 := r.isLt
      have hrle : r.val ≤ 66 := by omega
      have hrpos : 0 < 66 - r.val := by omega
      have hcast : ((66 - r.val : ℕ) : ℝ) = (66 : ℝ) - (r.val : ℝ) := by
        simpa only [Nat.cast_ofNat] using (Nat.cast_sub (R := ℝ) hrle)
      have hne : (66 : ℝ) - (r.val : ℝ) ≠ 0 := by
        rw [← hcast]
        exact_mod_cast (Nat.ne_of_gt hrpos)
      have hden : (1 : ℝ) - (r.val : ℝ) / 66 ≠ 0 := by
        have hrR : (r.val : ℝ) < 65 := by exact_mod_cast hr
        have hdenpos : (0 : ℝ) < 1 - (r.val : ℝ) / 66 := by linarith
        exact ne_of_gt hdenpos
      rw [hcast]
      field_simp [hne, hden] <;> ring
    -- Prove the factorial identity in Naturals before casting the product.
    -- The omitted final factor in the 66-term descending product is 1.
    have hprodNat : (∏ k ∈ Finset.range 65, (66 - k)) = Nat.factorial 66 := by
      have hfac := Nat.factorial_mul_descFactorial (n := 66) (k := 65)
        (by decide : 65 ≤ 66)
      calc
        (∏ k ∈ Finset.range 65, (66 - k)) = Nat.descFactorial 66 65 :=
          (Nat.descFactorial_eq_prod_range 66 65).symm
        _ = Nat.factorial 66 := by
          simpa only [show (66 - 65 : ℕ) = 1 from rfl, Nat.factorial_one, one_mul] using hfac
    have hprod : (∏ r : Fin 65, ((66 - r.val : ℕ) : ℝ)) =
        (Nat.factorial 66 : ℝ) := by
      calc
        (∏ r : Fin 65, ((66 - r.val : ℕ) : ℝ)) =
            ∏ k ∈ Finset.range 65, ((66 - k : ℕ) : ℝ) :=
          Fin.prod_univ_eq_prod_range (fun k : ℕ => ((66 - k : ℕ) : ℝ)) 65
        _ = (Nat.factorial 66 : ℝ) := by exact_mod_cast hprodNat
    calc
      distinctBankMass P b =
          ∏ r : Fin 65, P.mass (b r) /
            (1 - ∑ j ∈ Finset.univ.filter (fun j : Fin 65 => j < r), P.mass (b j)) := by
        rw [distinctBankMass, if_pos hb]
      _ = ∏ r : Fin 65, 1 / ((66 - r.val : ℕ) : ℝ) := by
        apply Finset.prod_congr rfl
        intro r _
        exact hfactor r
      _ = 1 / (Nat.factorial 66 : ℝ) := by
        simp only [one_div, Finset.prod_inv_distrib, hprod]
  · intro hbad
    by_cases hb : Function.Injective b
    · have hnotall : ¬ ∀ r, b r ∈ Set.range cliqueAssignments := by
        intro hs
        exact hbad ⟨hb, hs⟩
      obtain ⟨r, hr⟩ := not_forall.mp hnotall
      rw [distinctBankMass, if_pos hb]
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      rw [hzero (b r) hr, zero_div]
    · simp only [distinctBankMass, if_neg hb]

end

end AronowAudit.P044.Wave1.SimulatedVariance
