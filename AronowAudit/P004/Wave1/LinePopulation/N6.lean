import AronowAudit.P004.Wave1.LinePopulation.N1
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring

namespace AronowAudit.P004.Wave1.LinePopulation

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem n6_proof : N6 := by
  intro N R i r hr
  classical
  let q : ℤ := ⌊r / 10⌋
  let f : Fin N → ℤ := fun j => (j.val : ℤ) - (i.val : ℤ)
  have hq : 0 ≤ q := Int.floor_nonneg.mpr (by positivity)
  have hmaps : Set.MapsTo f
      (↑(ball (nodeSeparation (linePopulation R)) i r) : Set (Fin N))
      (↑(Finset.Icc (-q) q) : Set ℤ) := by
    intro j hj
    have hj' : 10 * |(i : ℝ) - (j : ℝ)| ≤ r := by
      have hmem := (Finset.mem_filter.mp hj).2
      simpa only [n1_proof R] using hmem
    have hcast : (f j : ℝ) = (j : ℝ) - (i : ℝ) := by
      simp [f]
    have hupper : f j ≤ q := by
      apply Int.le_floor.mpr
      rw [hcast]
      have hneg := neg_le_abs ((i : ℝ) - (j : ℝ))
      linarith
    have hlower : -f j ≤ q := by
      apply Int.le_floor.mpr
      rw [Int.cast_neg, hcast]
      have hpos := le_abs_self ((i : ℝ) - (j : ℝ))
      linarith
    exact Finset.mem_Icc.mpr ⟨by omega, hupper⟩
  have hinj : (↑(ball (nodeSeparation (linePopulation R)) i r) : Set (Fin N)).InjOn f := by
    intro j _hj k _hk hjk
    have hval : (j.val : ℤ) = (k.val : ℤ) := by
      dsimp only [f] at hjk
      omega
    apply Fin.val_injective
    exact_mod_cast hval
  have hcard : (ball (nodeSeparation (linePopulation R)) i r).card ≤
      (Finset.Icc (-q) q).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have hcard_int : ((Finset.Icc (-q) q).card : ℤ) = 2 * q + 1 := by
    rw [Int.card_Icc_of_le (-q) q (by omega : -q ≤ q + 1)]
    ring
  have hcard_real : ((Finset.Icc (-q) q).card : ℝ) = 2 * (q : ℝ) + 1 := by
    exact_mod_cast hcard_int
  have hfloor : (q : ℝ) ≤ r / 10 := Int.floor_le (r / 10)
  calc
    ((ball (nodeSeparation (linePopulation R)) i r).card : ℝ) ≤
        ((Finset.Icc (-q) q).card : ℝ) := by exact_mod_cast hcard
    _ = 2 * (q : ℝ) + 1 := hcard_real
    _ ≤ r / 5 + 1 := by linarith

end
end AronowAudit.P004.Wave1.LinePopulation
