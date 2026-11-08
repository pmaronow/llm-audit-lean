import SAP.P025a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a.WH.W1.P.T3_L1

open scoped BigOperators

theorem segment_in_box {n : ℕ} (α β : ℝ) (wL wH : Fin n → ℝ)
    (hL : weightBox α β wL) (hH : weightBox α β wH)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    weightBox α β (wholeSegment wL wH t) := by
  intro i
  have hcoeffL : 0 ≤ 1 - t := by linarith [ht.2]
  constructor
  · dsimp [wholeSegment]
    have h1 := mul_nonneg hcoeffL (sub_nonneg.mpr (hL i).1)
    have h2 := mul_nonneg ht.1 (sub_nonneg.mpr (hH i).1)
    nlinarith
  · dsimp [wholeSegment]
    have h1 := mul_nonneg hcoeffL (sub_nonneg.mpr (hL i).2)
    have h2 := mul_nonneg ht.1 (sub_nonneg.mpr (hH i).2)
    nlinarith

end SAP.P025a.WH.W1.P.T3_L1

theorem SAP.P025a.WH.W1.T3_L1_proof : SAP.P025a.WH.W1.T3_L1 := by
  intro n hn y α β hα hαβ wL wH hL hH
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hβ : 0 < β := hα.trans_le hαβ
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      weightBox α β (wholeSegment wL wH t) := by
    intro t ht
    exact SAP.P025a.WH.W1.P.T3_L1.segment_in_box α β wL wH hL hH ht
  have hsum : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < ∑ i, wholeSegment wL wH t i := by
    intro t ht
    apply Finset.sum_pos
    · intro i hi
      have hcoord := (hseg t ht i).1
      exact lt_of_lt_of_le (one_div_pos.mpr hβ) hcoord
    · exact Finset.univ_nonempty
  constructor
  · intro t ht
    exact ⟨hseg t ht, hsum t ht⟩
  · apply ContinuousOn.div
    · change ContinuousOn
        (fun t => ∑ i : Fin n, 1 * ((1 - t) * wL i + t * wH i) * y i)
        (Set.Icc 0 1)
      fun_prop
    · change ContinuousOn
        (fun t => ∑ i : Fin n, 1 * ((1 - t) * wL i + t * wH i))
        (Set.Icc 0 1)
      fun_prop
    · intro t ht
      have hd := hsum t ht
      simpa [wholeSegment] using hd.ne'

