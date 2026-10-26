import AronowAudit.P027.Wave1.UniformStartBlueprint
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Fin

/-! The cumulative-size prefix is the sum of full preceding blocks and
the prefix of the phase inside the current block. -/

namespace AronowAudit.P027.Wave1.UniformStart

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory
attribute [local instance] Classical.propDecidable

private theorem sum_fin_lt_const {n : ℕ} (k : Fin n) (c : ℝ) :
    (∑ j : Fin n, if j.val < k.val then c else 0) = (k : ℝ) * c := by
  have hfilter : (Finset.univ.filter (fun j : Fin n => j.val < k.val)) =
      Finset.Iio k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, Fin.card_Iio, nsmul_eq_mul]

/-- Comparison of two bounded remainders in two blocks. The proof only
uses multiplication to compare the starts of adjacent whole blocks. -/
private theorem blockIndex_lt_iff (q t' t j' j : ℕ) (ht' : t' < q) (ht : t < q) :
    t' + q * j' < t + q * j ↔ j' < j ∨ (j' = j ∧ t' < t) := by
  constructor
  · intro h
    by_cases hj : j' < j
    · exact Or.inl hj
    · right
      have heq : j' = j := by
        by_contra hne
        have hsucc : j + 1 ≤ j' := by omega
        have hmul := Nat.mul_le_mul_left q hsucc
        simp only [Nat.mul_succ] at hmul
        omega
      refine ⟨heq, ?_⟩
      subst j'
      omega
  · rintro (hj | ⟨rfl, hrem⟩)
    · have hmul := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hj)
      simp only [Nat.mul_succ] at hmul
      omega
    · omega

theorem n1_proof : N1 := by
  intro r m k
  rcases k with ⟨⟨i, b⟩, j⟩
  have hbval : b.val < 2 := b.isLt
  have ht : 2 * i.val + b.val < 2 * r := by
    have hi := i.isLt
    omega
  have horder (g : Fin r × Fin 2) (j' : Fin m) :
      phaseIndex (⟨g, j'⟩ : Σ _ : Fin r × Fin 2, Fin m) <
          phaseIndex (⟨(i, b), j⟩ : Σ _ : Fin r × Fin 2, Fin m) ↔
        j'.val < j.val ∨ (j' = j ∧ 2 * g.1.val + g.2.val < 2 * i.val + b.val) := by
    have htg : 2 * g.1.val + g.2.val < 2 * r := by
      have hi := g.1.isLt
      have hb := g.2.isLt
      omega
    simpa only [phaseIndex, Fin.val_inj] using
      (blockIndex_lt_iff (2 * r) (2 * g.1.val + g.2.val)
        (2 * i.val + b.val) j'.val j.val htg ht)
  have hinner (g : Fin r × Fin 2) :
      (∑ j' : Fin m,
        if phaseIndex (⟨g, j'⟩ : Σ _ : Fin r × Fin 2, Fin m) <
            phaseIndex (⟨(i, b), j⟩ : Σ _ : Fin r × Fin 2, Fin m)
          then phaseSize (⟨g, j'⟩ : Σ _ : Fin r × Fin 2, Fin m) else 0) =
        (j : ℝ) * (if g.2 = 0 then 2 else 10) +
          (if 2 * g.1.val + g.2.val < 2 * i.val + b.val
            then (if g.2 = 0 then 2 else 10) else 0) := by
    calc
      _ = ∑ j' : Fin m,
          ((if j'.val < j.val then (if g.2 = 0 then (2 : ℝ) else 10) else 0) +
            (if j' = j then
              (if 2 * g.1.val + g.2.val < 2 * i.val + b.val
                then (if g.2 = 0 then 2 else 10) else 0) else 0)) := by
        apply Finset.sum_congr rfl
        intro j' _
        simp only [horder g j']
        unfold phaseSize
        by_cases hjlt : j'.val < j.val
        · have hjne : j' ≠ j := by
            intro heq
            subst j'
            omega
          simp [hjlt, hjne]
        · by_cases heq : j' = j <;> simp [hjlt, heq]
      _ = _ := by
        rw [Finset.sum_add_distrib, sum_fin_lt_const]
        simp
  have htotal : (∑ g : Fin r × Fin 2, if g.2 = 0 then (2 : ℝ) else 10) =
      12 * (r : ℝ) := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_const, nsmul_eq_mul]
    <;> ring
  have hpair (i' : Fin r) :
      (∑ b' : Fin 2, if 2 * i'.val + b'.val < 2 * i.val + b.val
        then (if b' = 0 then (2 : ℝ) else 10) else 0) =
      (if i'.val < i.val then 12 else 0) +
        (if i' = i then (if b = 0 then 0 else 2) else 0) := by
    rw [Fin.sum_univ_two]
    by_cases hlt : i'.val < i.val
    · have hne : i' ≠ i := by
        intro heq
        subst i'
        omega
      have h0 : 2 * i'.val < 2 * i.val + b.val := by omega
      have h1 : 2 * i'.val + 1 < 2 * i.val + b.val := by omega
      norm_num [hlt, hne, h0, h1]
    · by_cases heq : i' = i
      · subst i'
        by_cases hb : b = 0
        · have hb0 : b.val = 0 := by simp [hb]
          have h1 : ¬ (2 * i.val + 1 < 2 * i.val) := by omega
          norm_num [hb, hb0, h1]
        · have hb1 : b.val = 1 := by
            have hbne : b.val ≠ 0 := by
              intro hv
              apply hb
              exact Fin.ext hv
            omega
          have h0 : 2 * i.val < 2 * i.val + 1 := by omega
          norm_num [hb, hb1, h0]
      · have hvne : i'.val ≠ i.val := by
          intro hv
          exact heq (Fin.ext hv)
        have h0 : ¬ (2 * i'.val < 2 * i.val + b.val) := by omega
        have h1 : ¬ (2 * i'.val + 1 < 2 * i.val + b.val) := by omega
        norm_num [hlt, heq, h0, h1]
  have hprefix :
      (∑ g : Fin r × Fin 2,
        if 2 * g.1.val + g.2.val < 2 * i.val + b.val
          then (if g.2 = 0 then (2 : ℝ) else 10) else 0) = phaseStartLeft (i, b) := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ i' : Fin r, ((if i'.val < i.val then (12 : ℝ) else 0) +
            (if i' = i then (if b = 0 then 0 else 2) else 0)) := by
        apply Finset.sum_congr rfl
        intro i' _
        exact hpair i'
      _ = phaseStartLeft (i, b) := by
        rw [Finset.sum_add_distrib, sum_fin_lt_const]
        simp [phaseStartLeft, mul_comm]
  calc
    unitLeft r m (⟨(i, b), j⟩ : Σ _ : Fin r × Fin 2, Fin m) =
        ∑ g : Fin r × Fin 2,
          ((j : ℝ) * (if g.2 = 0 then 2 else 10) +
            (if 2 * g.1.val + g.2.val < 2 * i.val + b.val
              then (if g.2 = 0 then 2 else 10) else 0)) := by
      unfold unitLeft
      rw [Fintype.sum_sigma]
      exact Finset.sum_congr rfl (fun g _ => hinner g)
    _ = (j : ℝ) * (∑ g : Fin r × Fin 2, if g.2 = 0 then (2 : ℝ) else 10) +
        (∑ g : Fin r × Fin 2,
          if 2 * g.1.val + g.2.val < 2 * i.val + b.val
            then (if g.2 = 0 then (2 : ℝ) else 10) else 0) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = phaseStartLeft (i, b) + 12 * (r : ℝ) * (j : ℝ) := by
      rw [htotal, hprefix]
      ring

end
end AronowAudit.P027.Wave1.UniformStart
