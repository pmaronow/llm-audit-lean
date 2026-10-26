import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
Count ties by the number of one-digits. Each one-count fiber is in bijection with
the corresponding fixed-cardinality powerset. The pair fibers are products, so
Vandermonde gives the central binomial coefficient.
-/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

private def tieOnes {k : ℕ} (v : Fin k → Fin 2) : Finset (Fin k) :=
  Finset.univ.filter (fun j => v j = 1)

private theorem tie_digit_eq (a b : Fin 2) (h : a = 1 ↔ b = 1) : a = b := by
  fin_cases a <;> fin_cases b <;> simp_all

private theorem tie_sign_sum {k : ℕ} (v : Fin k → Fin 2) :
    (∑ j, sgn2 (v j)) = 2 * ((tieOnes v).card : ℝ) - (k : ℝ) := by
  have hd (a : Fin 2) : sgn2 a = 2 * (if a = 1 then (1 : ℝ) else 0) - 1 := by
    fin_cases a <;> norm_num [sgn2]
  have hcount : (∑ j : Fin k, if v j = 1 then (1 : ℝ) else 0) =
      ((tieOnes v).card : ℝ) := by
    simp [tieOnes, Finset.sum_ite]
  calc
    (∑ j, sgn2 (v j)) = ∑ j : Fin k, (2 * (if v j = 1 then (1 : ℝ) else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hd (v j)
    _ = 2 * (∑ j : Fin k, if v j = 1 then (1 : ℝ) else 0) - (k : ℝ) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcount]
      simp
    _ = _ := by rw [hcount]

private theorem tie_sign_sum_eq_iff {k : ℕ} (v w : Fin k → Fin 2) :
    (∑ j, sgn2 (v j)) = (∑ j, sgn2 (w j)) ↔ (tieOnes v).card = (tieOnes w).card := by
  rw [tie_sign_sum v, tie_sign_sum w]
  constructor
  · intro h
    have h' : ((tieOnes v).card : ℝ) = ((tieOnes w).card : ℝ) := by linarith
    exact_mod_cast h'
  · intro h
    rw [h]

private theorem tie_ones_fiber_card (k t : ℕ) :
    (Finset.univ.filter (fun v : Fin k → Fin 2 => (tieOnes v).card = t)).card =
      k.choose t := by
  calc
    _ = ((Finset.univ : Finset (Fin k)).powersetCard t).card := by
      apply Finset.card_bij (fun v _ => tieOnes v)
      · intro v hv
        exact Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, (Finset.mem_filter.mp hv).2⟩
      · intro v hv w hw h
        funext j
        apply tie_digit_eq
        calc
          v j = 1 ↔ j ∈ tieOnes v := by simp [tieOnes]
          _ ↔ j ∈ tieOnes w := by rw [h]
          _ ↔ w j = 1 := by simp [tieOnes]
      · intro s hs
        let v : Fin k → Fin 2 := fun j => if j ∈ s then 1 else 0
        have hv : tieOnes v = s := by
          ext j
          simp [tieOnes, v]
        refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hv⟩
        rw [hv]
        exact (Finset.mem_powersetCard.mp hs).2
    _ = _ := by simp

private theorem tie_digit_pairs_card (k : ℕ) :
    (Finset.univ.filter (fun vw : (Fin k → Fin 2) × (Fin k → Fin 2) =>
      (tieOnes vw.1).card = (tieOnes vw.2).card)).card = (2 * k).choose k := by
  let S := Finset.univ.filter (fun vw : (Fin k → Fin 2) × (Fin k → Fin 2) =>
    (tieOnes vw.1).card = (tieOnes vw.2).card)
  have hmaps : (S : Set ((Fin k → Fin 2) × (Fin k → Fin 2))).MapsTo
      (fun vw => (tieOnes vw.1).card) (Finset.range (k + 1)) := by
    intro vw _
    have hle : (tieOnes vw.1).card ≤ k := by
      simpa [tieOnes] using
        (Finset.card_filter_le (Finset.univ : Finset (Fin k)) (fun j => vw.1 j = 1))
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hfiber (t : ℕ) :
      S.filter (fun vw => (tieOnes vw.1).card = t) =
        (Finset.univ.filter (fun v : Fin k → Fin 2 => (tieOnes v).card = t)) ×ˢ
        (Finset.univ.filter (fun w : Fin k → Fin 2 => (tieOnes w).card = t)) := by
    ext vw
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨hvw, hv⟩
      exact ⟨hv, hvw ▸ hv⟩
    · rintro ⟨hv, hw⟩
      exact ⟨hv.trans hw.symm, hv⟩
  calc
    _ = S.card := rfl
    _ = ∑ t ∈ Finset.range (k + 1), (S.filter (fun vw => (tieOnes vw.1).card = t)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ t ∈ Finset.range (k + 1), (k.choose t) ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [hfiber t, Finset.card_product, tie_ones_fiber_card, pow_two]
    _ = (2 * k).choose k := Nat.sum_range_choose_sq k

theorem n14_proof : N14 := by
  intro n
  let e := finFunctionFinEquiv (m := 2) (n := hcK n)
  have hq (i j : Fin (hcN n)) : hcQ n i = hcQ n j ↔
      (tieOnes (hcDigits n i)).card = (tieOnes (hcDigits n j)).card := by
    unfold hcQ
    rw [div_left_inj' (by positivity : (2 * ((n : ℝ) + 1)) ≠ 0)]
    exact tie_sign_sum_eq_iff _ _
  have he (v : Fin (hcK n) → Fin 2) : hcDigits n (e v) = v :=
    e.symm_apply_apply v
  calc
    _ = (Finset.univ.filter
        (fun vw : (Fin (hcK n) → Fin 2) × (Fin (hcK n) → Fin 2) =>
          (tieOnes vw.1).card = (tieOnes vw.2).card)).card := by
      apply Finset.card_bij (fun ij _ => (hcDigits n ij.1, hcDigits n ij.2))
      · intro ij hij
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (hq ij.1 ij.2).mp (Finset.mem_filter.mp hij).2⟩
      · intro ij hij uv huv h
        apply Prod.ext
        · exact e.symm.injective (congrArg Prod.fst h)
        · exact e.symm.injective (congrArg Prod.snd h)
      · intro vw hvw
        refine ⟨(e vw.1, e vw.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · apply (hq _ _).mpr
          simpa only [he] using (Finset.mem_filter.mp hvw).2
        · exact Prod.ext (he vw.1) (he vw.2)
    _ = (2 * hcK n).choose (hcK n) := tie_digit_pairs_card (hcK n)

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
