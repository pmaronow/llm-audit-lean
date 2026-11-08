import SAP.P001e.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Classical

namespace SAP.P001e.WH.W2.P.T85_L2

theorem recordedOutcome_mul_binary (y r : ℝ) (hr : r = 0 ∨ r = 1) :
    SAP.P001e.recordedOutcome y r * r = y * r := by
  rcases hr with hr | hr <;> simp [SAP.P001e.recordedOutcome, hr]

end SAP.P001e.WH.W2.P.T85_L2

theorem SAP.P001e.WH.W2.T85_L2_proof : SAP.P001e.WH.W2.T85_L2 := by
  intro n E inst X R hb hr S
  classical
  let xi : ∀ i : Fin n, wholeCells X := fun i =>
    ⟨X i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let Y : Fin n → ℝ := fun i => S (xi i) / wholeCellR X R (xi i)
  refine ⟨Y, ?_⟩
  intro x
  have hs : wholeCellS X R Y x =
      ∑ i : Fin n, if X i = x.1 then
        (S x / wholeCellR X R x) * R i else 0 := by
    unfold wholeCellS
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hix : X i = x.1
    · simp only [if_pos hix]
      have hxi : xi i = x := Subtype.ext hix
      rw [SAP.P001e.WH.W2.P.T85_L2.recordedOutcome_mul_binary (Y i) (R i) (hb i)]
      dsimp [Y]
      rw [hxi]
    · simp [hix]
  have hsum :
      (∑ i : Fin n, if X i = x.1 then
        (S x / wholeCellR X R x) * R i else 0) =
      (S x / wholeCellR X R x) * wholeCellR X R x := by
    calc
      (∑ i : Fin n, if X i = x.1 then
          (S x / wholeCellR X R x) * R i else 0) =
          ∑ i : Fin n, (S x / wholeCellR X R x) *
            (if X i = x.1 then R i else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hix : X i = x.1 <;> simp [hix]
      _ = (S x / wholeCellR X R x) *
          (∑ i : Fin n, if X i = x.1 then R i else 0) := by
          rw [Finset.mul_sum]
      _ = (S x / wholeCellR X R x) * wholeCellR X R x := rfl
  calc
    wholeCellS X R Y x =
        ∑ i : Fin n, if X i = x.1 then
          (S x / wholeCellR X R x) * R i else 0 := hs
    _ = (S x / wholeCellR X R x) * wholeCellR X R x := hsum
    _ = S x := div_mul_cancel₀ _ (ne_of_gt (hr x.1 x.2))
