import SAP.P001f.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001f.WH.W1.P.T97_L2

open scoped BigOperators
universe v

theorem wholeTreatedCount_sum {n : ℕ} {E : Type v}
    [Fintype E] [DecidableEq E] (X : Fin n → E) (D : Fin n → ℝ) (x : E) :
    SAP.P001f.wholeTreatedCount X D x =
      ∑ i, if X i = x then D i else 0 := by
  unfold SAP.P001f.wholeTreatedCount
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hix : X i = x <;> simp [hix]

theorem wholeControlCount_sum {n : ℕ} {E : Type v}
    [Fintype E] [DecidableEq E] (X : Fin n → E) (D : Fin n → ℝ) (x : E) :
    SAP.P001f.wholeControlCount X D x =
      ∑ i, if X i = x then 1 - D i else 0 := by
  unfold SAP.P001f.wholeControlCount SAP.P001f.wholeCellSize
    SAP.P001f.wholeTreatedCount
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hix : X i = x <;> simp [hix]

theorem treated_term {n : ℕ} {E : Type v} [Fintype E]
    [DecidableEq E] (X : Fin n → E) (D : Fin n → ℝ)
    (st sc : E → ℝ) (i : Fin n)
    (hD : D i = 0 ∨ D i = 1) :
    ((st (X i) / SAP.P001f.wholeTreatedCount X D (X i) * D i +
        sc (X i) / SAP.P001f.wholeControlCount X D (X i) * (1 - D i)) * D i) =
      st (X i) / SAP.P001f.wholeTreatedCount X D (X i) * D i := by
  rcases hD with hD | hD
  · rw [hD]
    ring
  · rw [hD]
    ring

theorem control_term {n : ℕ} {E : Type v} [Fintype E]
    [DecidableEq E] (X : Fin n → E) (D : Fin n → ℝ)
    (st sc : E → ℝ) (i : Fin n)
    (hD : D i = 0 ∨ D i = 1) :
    ((st (X i) / SAP.P001f.wholeTreatedCount X D (X i) * D i +
        sc (X i) / SAP.P001f.wholeControlCount X D (X i) * (1 - D i)) * (1 - D i)) =
      sc (X i) / SAP.P001f.wholeControlCount X D (X i) * (1 - D i) := by
  rcases hD with hD | hD
  · rw [hD]
    ring
  · rw [hD]
    ring

theorem treated_factor {n : ℕ} {E : Type v} [Fintype E]
    [DecidableEq E] (X : Fin n → E) (D : Fin n → ℝ)
    (st sc : E → ℝ) (x : E) (i : Fin n)
    (hD : D i = 0 ∨ D i = 1) :
    (if X i = x then
        (st (X i) / SAP.P001f.wholeTreatedCount X D (X i) * D i +
          sc (X i) / SAP.P001f.wholeControlCount X D (X i) * (1 - D i)) * D i
      else 0) =
      (if X i = x then D i else 0) *
        (st x / SAP.P001f.wholeTreatedCount X D x) := by
  by_cases hix : X i = x
  · simp only [if_pos hix]
    rw [treated_term X D st sc i hD]
    rw [hix]
    ring
  · rw [if_neg hix, if_neg hix]
    simp

theorem control_factor {n : ℕ} {E : Type v} [Fintype E]
    [DecidableEq E] (X : Fin n → E) (D : Fin n → ℝ)
    (st sc : E → ℝ) (x : E) (i : Fin n)
    (hD : D i = 0 ∨ D i = 1) :
    (if X i = x then
        (st (X i) / SAP.P001f.wholeTreatedCount X D (X i) * D i +
          sc (X i) / SAP.P001f.wholeControlCount X D (X i) * (1 - D i)) * (1 - D i)
      else 0) =
      (if X i = x then 1 - D i else 0) *
        (sc x / SAP.P001f.wholeControlCount X D x) := by
  by_cases hix : X i = x
  · simp only [if_pos hix]
    rw [control_term X D st sc i hD]
    rw [hix]
    ring
  · rw [if_neg hix, if_neg hix]
    simp

end SAP.P001f.WH.W1.P.T97_L2

theorem SAP.P001f.WH.W1.T97_L2_proof : SAP.P001f.WH.W1.T97_L2 := by
  classical
  intro n E _ _ X D hD ht hc st sc
  let Y : Fin n → ℝ := fun i =>
    st (X i) / SAP.P001f.wholeTreatedCount X D (X i) * D i +
      sc (X i) / SAP.P001f.wholeControlCount X D (X i) * (1 - D i)
  refine ⟨Y, ?_, ?_⟩
  · funext x
    unfold SAP.P001f.wholeTreatedSum
    simp only [Y]
    calc
      (∑ i, if X i = x then
          (st (X i) / SAP.P001f.wholeTreatedCount X D (X i) * D i +
            sc (X i) / SAP.P001f.wholeControlCount X D (X i) * (1 - D i)) * D i
        else 0) =
          ∑ i, (if X i = x then D i else 0) *
            (st x / SAP.P001f.wholeTreatedCount X D x) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact SAP.P001f.WH.W1.P.T97_L2.treated_factor X D st sc x i (hD i)
      _ = (∑ i, if X i = x then D i else 0) *
            (st x / SAP.P001f.wholeTreatedCount X D x) := by
              rw [← Finset.sum_mul]
      _ = SAP.P001f.wholeTreatedCount X D x *
            (st x / SAP.P001f.wholeTreatedCount X D x) := by
              rw [SAP.P001f.WH.W1.P.T97_L2.wholeTreatedCount_sum]
      _ = st x := by
        have hne : SAP.P001f.wholeTreatedCount X D x ≠ 0 := ne_of_gt (ht x)
        field_simp
  · funext x
    unfold SAP.P001f.wholeControlSum
    simp only [Y]
    calc
      (∑ i, if X i = x then
          (st (X i) / SAP.P001f.wholeTreatedCount X D (X i) * D i +
            sc (X i) / SAP.P001f.wholeControlCount X D (X i) * (1 - D i)) * (1 - D i)
        else 0) =
          ∑ i, (if X i = x then 1 - D i else 0) *
            (sc x / SAP.P001f.wholeControlCount X D x) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact SAP.P001f.WH.W1.P.T97_L2.control_factor X D st sc x i (hD i)
      _ = (∑ i, if X i = x then 1 - D i else 0) *
            (sc x / SAP.P001f.wholeControlCount X D x) := by
              rw [← Finset.sum_mul]
      _ = SAP.P001f.wholeControlCount X D x *
            (sc x / SAP.P001f.wholeControlCount X D x) := by
              rw [SAP.P001f.WH.W1.P.T97_L2.wholeControlCount_sum]
      _ = sc x := by
        have hne : SAP.P001f.wholeControlCount X D x ≠ 0 := ne_of_gt (hc x)
        field_simp

