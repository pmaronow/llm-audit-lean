import SAP.P001f.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

open scoped BigOperators

namespace SAP.P001f.WH.W1.P.T97_L1

private theorem sum_cells {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (X : Fin n → E) (f : Fin n → ℝ) :
    (∑ x : E, ∑ i : Fin n, if X i = x then f i else 0) = ∑ i, f i := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [eq_comm]

private theorem sum_cells_div {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (X : Fin n → E) (f : Fin n → ℝ) (g : E → ℝ) :
    (∑ x : E, (∑ i : Fin n, if X i = x then f i else 0) / g x) =
      ∑ i, f i / g (X i) := by
  classical
  calc
    (∑ x : E, (∑ i : Fin n, if X i = x then f i else 0) / g x) =
        ∑ x, ∑ i, if X i = x then f i / g x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_div]
      simp only [ite_div, zero_div]
    _ = ∑ i, ∑ x, if X i = x then f i / g x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i, f i / g (X i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.sum_ite_eq]

private theorem cell_size_eq {n : ℕ} {E : Type*}
    (X : Fin n → E) (D : Fin n → ℝ) (x : E) :
    wholeTreatedCount X D x + wholeControlCount X D x = wholeCellSize X x := by
  simp only [wholeControlCount]
  ring

end SAP.P001f.WH.W1.P.T97_L1

theorem SAP.P001f.WH.W1.T97_L1_proof : SAP.P001f.WH.W1.T97_L1 := by
  classical
  intro n E _ _ X D Y q
  have hcontrol : ∀ x, wholeControlCount X D x =
      ∑ i, if X i = x then 1 - D i else 0 := by
    intro x
    simp only [wholeControlCount, wholeCellSize, wholeTreatedCount]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : X i = x <;> simp [h]
  refine ⟨hcontrol, ?_, ?_⟩
  · unfold wholeUnitIPW cellIPW
    have ht : (∑ x, wholeTreatedSum X D Y x / q x) =
        ∑ i, Y i * D i / q (X i) := by
      calc
        (∑ x, wholeTreatedSum X D Y x / q x) =
            ∑ x, (∑ i, if X i = x then Y i * D i else 0) / q x := by
          apply Finset.sum_congr rfl
          intro x hx
          apply congrArg (fun z : ℝ => z / q x)
          unfold wholeTreatedSum
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : X i = x <;> simp [h]
        _ = _ := SAP.P001f.WH.W1.P.T97_L1.sum_cells_div X
          (fun i => Y i * D i) q
    have hc : (∑ x, wholeControlSum X D Y x / (1 - q x)) =
        ∑ i, Y i * (1 - D i) / (1 - q (X i)) := by
      calc
        (∑ x, wholeControlSum X D Y x / (1 - q x)) =
            ∑ x, (∑ i, if X i = x then Y i * (1 - D i) else 0) / (1 - q x) := by
          apply Finset.sum_congr rfl
          intro x hx
          apply congrArg (fun z : ℝ => z / (1 - q x))
          unfold wholeControlSum
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : X i = x <;> simp [h]
        _ = _ := SAP.P001f.WH.W1.P.T97_L1.sum_cells_div X
          (fun i => Y i * (1 - D i)) (fun x => 1 - q x)
    apply congrArg (fun z : ℝ => z / (n : ℝ))
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← ht, ← hc]
  · unfold wholeCausalPlugin poststratifiedAverage cellPoststratification
    simp only [wholeTreatedSum, wholeControlSum]
    have hsize : ∀ x, wholeTreatedCount X D x + wholeControlCount X D x =
        wholeCellSize X x := fun x => SAP.P001f.WH.W1.P.T97_L1.cell_size_eq X D x
    have hcell : ∀ x, (∑ i : Fin n, if X i = x then (1 : ℝ) else 0) =
        wholeTreatedCount X D x + wholeControlCount X D x := by
      intro x
      calc
        (∑ i : Fin n, if X i = x then (1 : ℝ) else 0) = wholeCellSize X x := by
          unfold wholeCellSize
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : X i = x <;> simp [h]
        _ = wholeTreatedCount X D x + wholeControlCount X D x := (hsize x).symm
    simp_rw [hcell, hcontrol, wholeTreatedCount]
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    ring_nf
