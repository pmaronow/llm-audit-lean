import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint
import Mathlib.Algebra.BigOperators.Fin

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Combine the two arm bounds, using only the probability bound for small designs. -/
theorem n7_proof : N7 := by
  intro hprob harm n P hn hXi
  rcases hprob n P.pop with ⟨hbounded, hmono, hunion, hcompl, hmarkov⟩
  rcases hXi with
    ⟨hdesign, hreceipt, hcompliers, hallocLo, hallocHi, hcov, hres,
      hcenter, hfourth, hrayleigh⟩
  have hN : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNm1 : 0 < (n : ℝ) - 1 := by linarith
  by_cases hlarge : 8 ≤ n
  · have hsizeT : n ≤ 4 * P.pop.n1 := by
      have h : (n : ℝ) ≤ 4 * (P.pop.n1 : ℝ) := by linarith
      exact_mod_cast h
    have hsizeC : n ≤ 4 * (n - P.pop.n1) := by
      have h : (n : ℝ) ≤ 4 * ((n - P.pop.n1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (Nat.le_of_lt hdesign.2.2)]
        linarith
      exact_mod_cast h
    have hmT : 2 ≤ P.pop.n1 := by omega
    have hmC : 2 ≤ n - P.pop.n1 := by omega
    have hmTpos : 0 < (P.pop.n1 : ℝ) := by
      exact_mod_cast (show 0 < P.pop.n1 by omega)
    have hmCpos : 0 < (n : ℝ) - (P.pop.n1 : ℝ) := by
      exact sub_pos.mpr (by exact_mod_cast hdesign.2.2)
    have hQ : (1 / 4 : ℝ) ≤ mean (fun i => P.x i 0 ^ 2) := by
      have h := hrayleigh (fun _ => (1 : ℝ))
      simpa [normSq, dotProduct, Fin.sum_univ_one] using h
    obtain ⟨hT, hC⟩ :=
      harm n P (hcenter 0) hQ (hfourth 0) hmT hmC
    have hfT :
        ((n : ℝ) - P.pop.n1) / ((P.pop.n1 : ℝ) * ((n : ℝ) - 1)) ≤
          3 / ((n : ℝ) - 1) := by
      apply (div_le_div_iff₀ (mul_pos hmTpos hNm1) hNm1).2
      have halloc : 0 ≤ 4 * (P.pop.n1 : ℝ) - (n : ℝ) := by linarith
      nlinarith only [mul_nonneg halloc hNm1.le]
    have hfC :
        (P.pop.n1 : ℝ) / (((n : ℝ) - P.pop.n1) * ((n : ℝ) - 1)) ≤
          3 / ((n : ℝ) - 1) := by
      apply (div_le_div_iff₀ (mul_pos hmCpos hNm1) hNm1).2
      have halloc : 0 ≤ 3 * (n : ℝ) - 4 * (P.pop.n1 : ℝ) := by linarith
      nlinarith only [mul_nonneg halloc hNm1.le]
    calc
      probability P.pop (fun S =>
          (gram P.x S).det = 0 ∨ (gram P.x Sᶜ).det = 0) ≤
          probability P.pop (fun S => (gram P.x S).det = 0) +
            probability P.pop (fun S => (gram P.x Sᶜ).det = 0) := hunion _ _
      _ ≤ 258 * (3 / ((n : ℝ) - 1)) + 258 * (3 / ((n : ℝ) - 1)) :=
        add_le_add
          (hT.trans (mul_le_mul_of_nonneg_left hfT (by norm_num)))
          (hC.trans (mul_le_mul_of_nonneg_left hfC (by norm_num)))
      _ = 1548 / ((n : ℝ) - 1) := by ring
  · have hnSmall : (n : ℝ) ≤ 7 := by
      exact_mod_cast (show n ≤ 7 by omega)
    have htrivial : (1 : ℝ) ≤ 1548 / ((n : ℝ) - 1) := by
      apply (le_div_iff₀ hNm1).2
      linarith
    exact (hbounded _).2.trans htrivial

end
end AronowAudit.P002.Wave1.PrintedTheorem2
