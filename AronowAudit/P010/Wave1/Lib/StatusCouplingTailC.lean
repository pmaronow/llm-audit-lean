import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace AronowAudit.P010.Wave1

open scoped BigOperators

/-- Split the mass of one distinguished atom and its complement. The formula
uses no division by the distinguished mass, and totalized division handles a
complement of mass zero. -/
theorem tcStatus_split {ι : Type*} [Fintype ι] (u : ι) (w : ι → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hs : ∑ s, w s = 1)
    (q p α : ℝ) (hu : w u = q) (hq : q ≤ 1)
    (ha0 : 0 ≤ α) (haq : α ≤ q) (hap : α ≤ p)
    (hlo : q + p - 1 ≤ α) :
    ∃ t : ι → ℝ, (∀ s, 0 ≤ t s ∧ t s ≤ w s) ∧
      (∑ s, t s) = p ∧ t u = α := by
  classical
  let c := (p - α) / (1 - q)
  have hc0 : 0 ≤ c := div_nonneg (sub_nonneg.mpr hap) (sub_nonneg.mpr hq)
  have hc1 : c ≤ 1 := by
    by_cases he : q = 1
    · simp [c, he]
    · apply (div_le_one (sub_pos.mpr (lt_of_le_of_ne hq he))).mpr
      linarith
  have hc : c * (1 - q) = p - α := by
    by_cases he : q = 1
    · have hpa : p = α := by linarith
      simp [he, hpa]
    · exact div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm he))
  have ho : (∑ s, if s = u then 0 else w s) = 1 - q := by
    have he : (∑ s, w s) = w u + ∑ s, if s = u then 0 else w s := by
      calc
        _ = ∑ s, ((if s = u then w s else 0) +
            (if s = u then 0 else w s)) := by
          apply Finset.sum_congr rfl
          intro s _
          split_ifs <;> simp
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    rw [hs, hu] at he
    linarith
  refine ⟨fun s => if s = u then α else c * w s, ?_, ?_, by simp⟩
  · intro s
    by_cases he : s = u
    · simpa [he, hu] using And.intro ha0 haq
    · simp only [he, ite_false]
      exact ⟨mul_nonneg hc0 (hw s), by nlinarith [hw s]⟩
  · have he (s : ι) : (if s = u then α else c * w s) =
        (if s = u then α else 0) + c * (if s = u then 0 else w s) := by
      split_ifs <;> simp
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ho]
    simpa using (show α + c * (1 - q) = p by linarith)

/-- Summation of Boolean vectors by their first coordinate. -/
theorem tcStatus_sum_cons {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ s, f s) = ∑ t : Fin n → Bool, (f (Fin.cons true t) + f (Fin.cons false t)) := by
  classical
  let e : (Bool × (Fin n → Bool)) ≃ (Fin (n + 1) → Bool) :=
    { toFun := fun x => Fin.cons x.1 x.2
      invFun := fun s => (s 0, Fin.tail s)
      left_inv := by intro x; simp
      right_inv := Fin.cons_self_tail }
  calc
    _ = ∑ x : Bool × (Fin n → Bool), f (e x) := (e.sum_comp f).symm
    _ = _ := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
      rfl

/-- Every feasible all-pass mass is attained by a finite real weight vector.
All status vectors, including those of weight zero, remain in the index type. -/
theorem bernoulli_status_coupling (K : ℕ) (p : Fin K → ℝ) (α : ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hαp : ∀ i, α ≤ p i) (hL : 1 - ∑ i, (1 - p i) ≤ α) :
    ∃ w : (Fin K → Bool) → ℝ,
      (∀ s, 0 ≤ w s) ∧ (∑ s, w s) = 1 ∧
      (∀ i, (∑ s, if s i = true then w s else 0) = p i) ∧
      w (fun _ => true) = α := by
  classical
  induction K generalizing α with
  | zero =>
      have ha : α = 1 := le_antisymm hα1 (by simpa using hL)
      refine ⟨fun _ => 1, by simp, by simp, ?_, by simp [ha]⟩
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      let q := max α (1 - ∑ i : Fin n, (1 - p i.succ))
      have hq0 : 0 ≤ q := le_trans hα0 (le_max_left _ _)
      have hq1 : q ≤ 1 := by
        apply max_le hα1
        have he : 0 ≤ ∑ i : Fin n, (1 - p i.succ) :=
          Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hp i.succ).2
        linarith
      have hqp (i : Fin n) : q ≤ p i.succ := by
        apply max_le (hαp i.succ)
        have he : 1 - p i.succ ≤ ∑ j : Fin n, (1 - p j.succ) :=
          Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hp j.succ).2) (Finset.mem_univ i)
        linarith
      obtain ⟨w, hw, hs, hm, hu⟩ := ih (fun i => p i.succ) q
        (fun i => hp i.succ) hq0 hq1 hqp (le_max_right _ _)
      have hlo : q + p 0 - 1 ≤ α := by
        have he : q ≤ α - p 0 + 1 := by
          apply max_le
          · linarith [(hp 0).2]
          · rw [Fin.sum_univ_succ] at hL
            linarith
        linarith
      obtain ⟨t, ht, hts, htu⟩ := tcStatus_split (fun _ : Fin n => true) w hw hs
        q (p 0) α hu hq1 hα0 (le_max_left _ _) (hαp 0) hlo
      let v : (Fin (n + 1) → Bool) → ℝ := fun s =>
        if s 0 = true then t (Fin.tail s) else w (Fin.tail s) - t (Fin.tail s)
      have hvt (s : Fin n → Bool) : v (Fin.cons true s) = t s := by simp [v]
      have hvf (s : Fin n → Bool) : v (Fin.cons false s) = w s - t s := by simp [v]
      refine ⟨v, ?_, ?_, ?_, ?_⟩
      · intro s
        dsimp [v]
        split_ifs
        · exact (ht _).1
        · exact sub_nonneg.mpr (ht _).2
      · rw [tcStatus_sum_cons]
        simp_rw [hvt, hvf, add_sub_cancel]
        exact hs
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [tcStatus_sum_cons]
          simpa [hvt] using hts
        · rw [tcStatus_sum_cons]
          have he (s : Fin n → Bool) :
              (if (Fin.cons true s : Fin (n + 1) → Bool) j.succ = true then v (Fin.cons true s) else 0) +
              (if (Fin.cons false s : Fin (n + 1) → Bool) j.succ = true then v (Fin.cons false s) else 0) =
              if s j = true then w s else 0 := by
            by_cases hh : s j = true <;> simp [hh, hvt, hvf]
          simp_rw [he]
          exact hm j
      · change t (fun _ => true) = α
        exact htu

end AronowAudit.P010.Wave1
