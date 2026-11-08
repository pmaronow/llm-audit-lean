import SAP.P001e.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators Classical

namespace SAP.P001e.WH.W2.P.T85_L1

lemma grouped_sum {n : ℕ} {E : Type*} [DecidableEq E]
    (X : Fin n → E) (f : Fin n → ℝ) :
    (∑ i, f i) =
      ∑ x : {x // x ∈ SAP.P001e.wholeCells X},
        ∑ i, if X i = x.1 then f i else 0 := by
  let C := SAP.P001e.wholeCells X
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin n)), X i ∈ C := by
    intro i hi
    exact Finset.mem_image_of_mem X (Finset.mem_univ i)
  calc
    (∑ i, f i) =
        ∑ x ∈ C, ∑ i ∈ (Finset.univ : Finset (Fin n)) with X i = x, f i :=
      (Finset.sum_fiberwise_of_maps_to hmaps f).symm
    _ = ∑ x : {x // x ∈ C}, ∑ i, if X i = x.1 then f i else 0 := by
      rw [← Finset.sum_coe_sort C]
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.sum_filter]

end SAP.P001e.WH.W2.P.T85_L1

open SAP.P001e.WH.W2.P.T85_L1

theorem SAP.P001e.WH.W2.T85_L1_proof : SAP.P001e.WH.W2.T85_L1 := by
  intro n E _ hn X R q hb
  let C := SAP.P001e.wholeCells X
  let N : C → ℝ := fun x => SAP.P001e.wholeCellN X x
  let r : C → ℝ := fun x => SAP.P001e.wholeCellR X R x
  have hN : ∀ x : C, 0 < N x := by
    intro x
    rcases Finset.mem_image.mp x.property with ⟨i, hi, hxi⟩
    unfold N SAP.P001e.wholeCellN
    apply Finset.sum_pos' (s := Finset.univ)
    · intro j hj
      split_ifs <;> norm_num
    · exact ⟨i, Finset.mem_univ i, by simp [hxi]⟩
  have htotal : (∑ x : C, N x) = (n : ℝ) := by
    change (∑ x : {x // x ∈ SAP.P001e.wholeCells X},
      SAP.P001e.wholeCellN X x) = (n : ℝ)
    simp only [SAP.P001e.wholeCellN]
    rw [← SAP.P001e.WH.W2.P.T85_L1.grouped_sum X (fun _ => (1 : ℝ))]
    simp
  refine ⟨hN, htotal, ?_, ?_⟩
  · change (∑ i, R i / q (X i)) / (n : ℝ) =
      (∑ x : C, r x / q x) / (n : ℝ)
    congr 1
    calc
      (∑ i, R i / q (X i)) =
          ∑ x : C, ∑ i, if X i = x.1 then R i / q (X i) else 0 :=
        SAP.P001e.WH.W2.P.T85_L1.grouped_sum X (fun i => R i / q (X i))
      _ = ∑ x : C, r x / q x := by
        apply Finset.sum_congr rfl
        intro x hx
        calc
          (∑ i, if X i = x.1 then R i / q (X i) else 0) =
              ∑ i, (if X i = x.1 then R i else 0) / q x.1 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h : X i = x.1 <;> simp [h]
          _ = (∑ i, if X i = x.1 then R i else 0) / q x.1 := by
            rw [← Finset.sum_div]
          _ = r x / q x := by
            simp [r, SAP.P001e.wholeCellR]
  · intro Y
    refine ⟨?_, ?_, ?_⟩
    · change (∑ i, SAP.P001e.recordedOutcome (Y i) (R i) * R i / q (X i)) /
          (n : ℝ) =
        (∑ x : C, SAP.P001e.wholeCellS X R Y x / q x) / (n : ℝ)
      congr 1
      calc
        (∑ i, SAP.P001e.recordedOutcome (Y i) (R i) * R i / q (X i)) =
            ∑ x : C, ∑ i, if X i = x.1 then
              SAP.P001e.recordedOutcome (Y i) (R i) * R i / q (X i) else 0 :=
          SAP.P001e.WH.W2.P.T85_L1.grouped_sum X
            (fun i => SAP.P001e.recordedOutcome (Y i) (R i) * R i / q (X i))
        _ = ∑ x : C, SAP.P001e.wholeCellS X R Y x / q x := by
          apply Finset.sum_congr rfl
          intro x hx
          calc
            (∑ i, if X i = x.1 then
                SAP.P001e.recordedOutcome (Y i) (R i) * R i / q (X i) else 0) =
                ∑ i, (if X i = x.1 then
                  SAP.P001e.recordedOutcome (Y i) (R i) * R i else 0) / q x.1 := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases h : X i = x.1 <;> simp [h]
            _ = (∑ i, if X i = x.1 then
                  SAP.P001e.recordedOutcome (Y i) (R i) * R i else 0) / q x.1 := by
              rw [← Finset.sum_div]
            _ = SAP.P001e.wholeCellS X R Y x / q x := by
              simp [SAP.P001e.wholeCellS]
    · change (∑ x ∈ SAP.P001e.wholeCells X,
          (SAP.P001e.wholeCellS X R Y x / SAP.P001e.wholeCellR X R x) *
            (SAP.P001e.wholeCellN X x / (n : ℝ))) =
        (∑ x : C, N x * SAP.P001e.wholeCellS X R Y x / r x) / (n : ℝ)
      rw [← Finset.sum_coe_sort C
        (fun x => (SAP.P001e.wholeCellS X R Y x / SAP.P001e.wholeCellR X R x) *
          (SAP.P001e.wholeCellN X x / (n : ℝ)))]
      calc
        (∑ x : C, (SAP.P001e.wholeCellS X R Y x / SAP.P001e.wholeCellR X R x) *
            (SAP.P001e.wholeCellN X x / (n : ℝ))) =
            ∑ x : C, (N x * SAP.P001e.wholeCellS X R Y x / r x) / (n : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [N, r]
          ring
        _ = (∑ x : C, N x * SAP.P001e.wholeCellS X R Y x / r x) / (n : ℝ) := by
          rw [← Finset.sum_div]
    · unfold SAP.P001e.wholeSampleIPW
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rcases hb i with h | h <;> simp [SAP.P001e.recordedOutcome, h]
