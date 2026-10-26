import AronowAudit.P002.Wave1.E61EigenvalueBlueprint
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

universe u

/-- The binomial mass at `m` is a mode; conditioning on that count costs at most `N+1`. -/
theorem n1_proof : N1 := by
  intro N m hm hmN E
  have hNnat : 0 < N := lt_trans hm hmN
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmNR : (m : ℝ) < N := by exact_mod_cast hmN
  let p : ℝ := (m : ℝ) / N
  let q : ℝ := 1 - p
  have hp : 0 < p := div_pos hmR hN
  have hp1 : p < 1 := (div_lt_one hN).2 hmNR
  have hq : 0 < q := sub_pos.mpr hp1
  have hpN : p * (N : ℝ) = (m : ℝ) := by
    dsimp [p]
    exact div_mul_cancel₀ _ hN.ne'
  let b : ℕ → ℝ := fun j => (N.choose j : ℝ) * p ^ j * q ^ (N - j)
  have hb (j : ℕ) : 0 ≤ b j := by
    dsimp [b]
    positivity
  have hrec (j : ℕ) (hj : j < N) :
      b (j + 1) * (((j : ℝ) + 1) * q) =
        b j * (((N - j : ℕ) : ℝ) * p) := by
    have hchoose : (N.choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
        (N.choose j : ℝ) * ((N - j : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq N j
    have hpow : q ^ (N - j) = q ^ (N - (j + 1)) * q := by
      rw [show N - j = (N - (j + 1)) + 1 by omega, pow_succ]
    dsimp [b]
    rw [pow_succ, hpow]
    calc
      _ = ((N.choose (j + 1) : ℝ) * ((j : ℝ) + 1)) *
          p ^ j * q ^ (N - (j + 1)) * q * p := by ring
      _ = ((N.choose j : ℝ) * ((N - j : ℕ) : ℝ)) *
          p ^ j * q ^ (N - (j + 1)) * q * p := by rw [hchoose]
      _ = _ := by ring
  have hup (j : ℕ) (hj : j < m) : b j ≤ b (j + 1) := by
    have hjN : j < N := lt_trans hj hmN
    have hjR : (j : ℝ) + 1 ≤ m := by
      exact_mod_cast (show j + 1 ≤ m by omega)
    have hNj : ((N - j : ℕ) : ℝ) = (N : ℝ) - j :=
      Nat.cast_sub (Nat.le_of_lt hjN)
    have hcoef : ((j : ℝ) + 1) * q ≤ ((N - j : ℕ) : ℝ) * p := by
      rw [hNj]
      dsimp [q]
      nlinarith [hpN]
    have hfactor : 0 < ((j : ℝ) + 1) * q := by positivity
    apply (mul_le_mul_iff_left₀ hfactor).mp
    rw [hrec j hjN]
    exact mul_le_mul_of_nonneg_left hcoef (hb j)
  have hdown (j : ℕ) (hmj : m ≤ j) (hj : j < N) : b (j + 1) ≤ b j := by
    have hmjR : (m : ℝ) ≤ j := by exact_mod_cast hmj
    have hNj : ((N - j : ℕ) : ℝ) = (N : ℝ) - j :=
      Nat.cast_sub (Nat.le_of_lt hj)
    have hcoef : ((N - j : ℕ) : ℝ) * p ≤ ((j : ℝ) + 1) * q := by
      rw [hNj]
      dsimp [q]
      nlinarith [hpN]
    have hfactor : 0 < ((j : ℝ) + 1) * q := by positivity
    apply (mul_le_mul_iff_left₀ hfactor).mp
    rw [hrec j hj]
    exact mul_le_mul_of_nonneg_left hcoef (hb j)
  have hleft (j d : ℕ) : j + d ≤ m → b j ≤ b (j + d) := by
    induction d with
    | zero => intro _; simp
    | succ d ih =>
        intro hd
        have h1 := ih (by omega)
        have h2 := hup (j + d) (by omega)
        exact h1.trans (by simpa only [Nat.add_assoc] using h2)
  have hright (d : ℕ) : m + d ≤ N → b (m + d) ≤ b m := by
    induction d with
    | zero => intro _; simp
    | succ d ih =>
        intro hd
        have h1 := hdown (m + d) (by omega) (by omega)
        have h2 := ih (by omega)
        have hstep : b (m + (d + 1)) ≤ b (m + d) := by
          simpa only [Nat.add_assoc] using h1
        exact hstep.trans h2
  have hmode (j : ℕ) (hj : j ≤ N) : b j ≤ b m := by
    by_cases hjm : j ≤ m
    · simpa only [Nat.add_sub_of_le hjm] using hleft j (m - j) (by omega)
    · have hmj : m ≤ j := by omega
      simpa only [Nat.add_sub_of_le hmj] using hright (j - m) (by omega)
  have htotal : (∑ j ∈ Finset.range (N + 1), b j) = 1 := by
    calc
      _ = (p + q) ^ N := by
        dsimp [b]
        simpa only [mul_assoc, mul_comm, mul_left_comm] using (add_pow p q N).symm
      _ = 1 := by rw [show p + q = 1 by dsimp [q]; ring, one_pow]
  have hmass : 1 ≤ ((N : ℝ) + 1) * b m := by
    calc
      1 = ∑ j ∈ Finset.range (N + 1), b j := htotal.symm
      _ ≤ ∑ _j ∈ Finset.range (N + 1), b m := by
        apply Finset.sum_le_sum
        intro j hj
        exact hmode j (by have := Finset.mem_range.mp hj; omega)
      _ = ((N : ℝ) + 1) * b m := by simp [nsmul_eq_mul, Nat.cast_add]
  let w : Finset (Fin N) → ℝ := fun T => p ^ T.card * q ^ (N - T.card)
  let F : Finset (Finset (Fin N)) := (Finset.univ.powersetCard m).filter E
  have hw (T : Finset (Fin N)) : 0 ≤ w T := by dsimp [w]; positivity
  have hFcard (T : Finset (Fin N)) (hT : T ∈ F) : T.card = m := by
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
  have hFsum : (∑ T ∈ F, w T) = (F.card : ℝ) * (p ^ m * q ^ (N - m)) := by
    calc
      _ = ∑ _T ∈ F, (p ^ m * q ^ (N - m)) := by
        apply Finset.sum_congr rfl
        intro T hT
        dsimp [w]
        rw [hFcard T hT]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hFle : (F.card : ℝ) * (p ^ m * q ^ (N - m)) ≤
      ∑ T : Finset (Fin N), if E T then w T else 0 := by
    rw [← hFsum]
    calc
      _ = ∑ T ∈ F, if E T then w T else 0 := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [if_pos (Finset.mem_filter.mp hT).2]
      _ ≤ ∑ T : Finset (Fin N), if E T then w T else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
        intro T _ _
        split_ifs <;> first | exact hw T | exact le_rfl
  have hc : (0 : ℝ) < (N.choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt hmN)
  change (F.card : ℝ) / (N.choose m : ℝ) ≤
    ((N : ℝ) + 1) * ∑ T : Finset (Fin N), if E T then w T else 0
  apply (div_le_iff₀ hc).2
  have hscaled := mul_le_mul_of_nonneg_left hFle
    (show (0 : ℝ) ≤ (N : ℝ) + 1 by positivity)
  calc
    (F.card : ℝ) ≤ (F.card : ℝ) * (((N : ℝ) + 1) * b m) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass
        (show (0 : ℝ) ≤ (F.card : ℝ) by positivity)
    _ = (((N : ℝ) + 1) * ((F.card : ℝ) * (p ^ m * q ^ (N - m)))) *
        (N.choose m : ℝ) := by dsimp [b]; ring
    _ ≤ (((N : ℝ) + 1) *
        ∑ T : Finset (Fin N), if E T then w T else 0) * (N.choose m : ℝ) :=
      mul_le_mul_of_nonneg_right hscaled hc.le

end
end AronowAudit.P002.Wave1.E61Eigenvalue
