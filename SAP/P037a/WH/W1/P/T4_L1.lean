import SAP.P037a.WH.W1.Leaves
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W1.P.T4_L1

open SAP.P037a
open scoped BigOperators

lemma append_castSucc (n : ℕ) (p : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    appendSimplex (n+1) p i.castSucc = p i := by
  unfold appendSimplex
  have hi : (i.castSucc : Fin (n+2)).val < n+1 := by simpa using i.isLt
  rw [dif_pos hi]
  rfl

lemma append_last (n : ℕ) (p : Fin (n+1) → ℝ) :
    appendSimplex (n+1) p (Fin.last (n+1)) = 1 - ∑ i, p i := by
  unfold appendSimplex
  have hi : ¬ (Fin.last (n+1) : Fin (n+2)).val < n+1 := by simp
  rw [dif_neg hi]

lemma map_castSucc (n : ℕ) (x : Fin (n+2) → ℝ) (i : Fin (n+1)) :
    simplexConeMap n x i.castSucc = x (Fin.last (n+1)) * x i.castSucc := by
  simp [simplexConeMap, append_castSucc]

lemma map_last (n : ℕ) (x : Fin (n+2) → ℝ) :
    simplexConeMap n x (Fin.last (n+1)) =
      x (Fin.last (n+1)) * (1 - ∑ i : Fin (n+1), x i.castSucc) := by
  simp [simplexConeMap, append_last]

lemma map_sum (n : ℕ) (x : Fin (n+2) → ℝ) :
    (∑ i : Fin (n+2), simplexConeMap n x i) = x (Fin.last (n+1)) := by
  rw [Fin.sum_univ_castSucc]
  simp_rw [map_castSucc]
  rw [map_last]
  rw [← Finset.mul_sum]
  ring

lemma inverse_mem (n : ℕ) (e : Fin (n+2) → ℝ) (he : e ∈ positiveOrthant n) :
    simplexConeInverse n e ∈ simplexCone n := by
  have hsum : 0 < ∑ i : Fin (n+2), e i := Finset.sum_pos (fun i _ => he i) Finset.univ_nonempty
  have hsplit : (∑ i : Fin (n+2), e i) = (∑ i : Fin (n+1), e i.castSucc) + e (Fin.last (n+1)) :=
    by simpa using (Fin.sum_univ_castSucc (fun i : Fin (n+2) => e i))
  change (fun i : Fin (n+1) => simplexConeInverse n e i.castSucc) ∈ openSimplex (n+1) ∧
    0 < simplexConeInverse n e (Fin.last (n+1))
  constructor
  · change (∀ i : Fin (n+1), 0 < simplexConeInverse n e i.castSucc) ∧
      (∑ i : Fin (n+1), simplexConeInverse n e i.castSucc) < 1
    refine ⟨?_, ?_⟩
    · intro (i : Fin (n+1))
      simp only [simplexConeInverse, Fin.snoc_castSucc]
      exact div_pos (he i.castSucc) hsum
    · simp only [simplexConeInverse, Fin.snoc_castSucc]
      calc
        (∑ i : Fin (n+1), e i.castSucc / (∑ j : Fin (n+2), e j)) =
            (∑ i : Fin (n+1), e i.castSucc) / (∑ j : Fin (n+2), e j) := by
              rw [Finset.sum_div]
        _ < 1 := (div_lt_one hsum).2 (by rw [hsplit]; linarith [he (Fin.last (n+1))])
  · simp only [simplexConeInverse, Fin.snoc_last]
    exact hsum

lemma inverse_map (n : ℕ) (e : Fin (n+2) → ℝ) (he : e ∈ positiveOrthant n) :
    simplexConeMap n (simplexConeInverse n e) = e := by
  have hs : 0 < ∑ i : Fin (n+2), e i := by
    exact Finset.sum_pos (fun i _ => he i) Finset.univ_nonempty
  have hsum : (∑ i : Fin (n+2), e i) = (∑ i : Fin (n+1), e i.castSucc) + e (Fin.last (n+1)) :=
    by simpa using (Fin.sum_univ_castSucc (fun i : Fin (n+2) => e i))
  ext i
  cases i using Fin.lastCases with
  | last =>
    rw [map_last]
    simp only [simplexConeInverse, Fin.snoc_last, Fin.snoc_castSucc]
    rw [← Finset.sum_div]
    field_simp [ne_of_gt hs]
    linarith
  | cast j =>
    rw [map_castSucc]
    simp only [simplexConeInverse, Fin.snoc_castSucc, Fin.snoc_last]
    field_simp [ne_of_gt hs]

lemma inverse_map_map (n : ℕ) (x : Fin (n+2) → ℝ) (hx : x ∈ simplexCone n) :
    simplexConeInverse n (simplexConeMap n x) = x := by
  rcases hx with ⟨hp, ht⟩
  have hs : (∑ i : Fin (n+2), simplexConeMap n x i) = x (Fin.last (n+1)) := map_sum n x
  ext i
  cases i using Fin.lastCases with
  | last => simp [simplexConeInverse, hs]
  | cast j =>
    rw [simplexConeInverse, Fin.snoc_castSucc]
    rw [hs, map_castSucc]
    field_simp [ne_of_gt ht]

lemma jacobian_castSucc (n : ℕ) (x v : Fin (n+2) → ℝ) (i : Fin (n+1)) :
    (Matrix.toLin' (simplexConeJacobian n x)).toContinuousLinearMap v i.castSucc =
      x (Fin.last (n+1)) * v i.castSucc + x i.castSucc * v (Fin.last (n+1)) := by
  change (Matrix.toLin' (simplexConeJacobian n x) v) i.castSucc = _
  rw [Matrix.toLin'_apply]
  change (∑ j : Fin (n+2), simplexConeJacobian n x i.castSucc j * v j) = _
  rw [Fin.sum_univ_castSucc]
  have hentry : ∀ j : Fin (n+1),
      simplexConeJacobian n x i.castSucc j.castSucc * v j.castSucc =
        (if i = j then x (Fin.last (n+1)) * v j.castSucc else 0) := by
    intro j
    have hi : (i.castSucc : Fin (n+2)).val < n+1 := by simpa using i.isLt
    have hj : (j.castSucc : Fin (n+2)).val < n+1 := by simpa using j.isLt
    have hi' : (i : ℕ) ≤ n := by omega
    have hj' : (j : ℕ) ≤ n := by omega
    simp [simplexConeJacobian, hi', hj']
  have hlast : simplexConeJacobian n x i.castSucc (Fin.last (n+1)) *
      v (Fin.last (n+1)) = x i.castSucc * v (Fin.last (n+1)) := by
    have hi : (i.castSucc : Fin (n+2)).val < n+1 := by simpa using i.isLt
    have hl : ¬ (Fin.last (n+1) : Fin (n+2)).val < n+1 := by simp
    have hi' : (i : ℕ) ≤ n := by omega
    simp [simplexConeJacobian, hi', hl]
  rw [Finset.sum_congr rfl (by intro j hj; exact hentry j), hlast]
  simp

lemma jacobian_last (n : ℕ) (x v : Fin (n+2) → ℝ) :
    (Matrix.toLin' (simplexConeJacobian n x)).toContinuousLinearMap v (Fin.last (n+1)) =
      -x (Fin.last (n+1)) * (∑ i : Fin (n+1), v i.castSucc) +
        (1 - ∑ i : Fin (n+1), x i.castSucc) * v (Fin.last (n+1)) := by
  change (Matrix.toLin' (simplexConeJacobian n x) v) (Fin.last (n+1)) = _
  rw [Matrix.toLin'_apply]
  change (∑ j : Fin (n+2), simplexConeJacobian n x (Fin.last (n+1)) j * v j) = _
  rw [Fin.sum_univ_castSucc]
  have hentry : ∀ j : Fin (n+1),
      simplexConeJacobian n x (Fin.last (n+1)) j.castSucc * v j.castSucc =
        -x (Fin.last (n+1)) * v j.castSucc := by
    intro j
    have hj : (j.castSucc : Fin (n+2)).val < n+1 := by simpa using j.isLt
    have hl : ¬ (Fin.last (n+1) : Fin (n+2)).val < n+1 := by simp
    have hj' : (j : ℕ) ≤ n := by omega
    simp [simplexConeJacobian, hj', hl]
  have hlast : simplexConeJacobian n x (Fin.last (n+1)) (Fin.last (n+1)) *
      v (Fin.last (n+1)) = (1 - ∑ i : Fin (n+1), x i.castSucc) * v (Fin.last (n+1)) := by
    have hl : ¬ (Fin.last (n+1) : Fin (n+2)).val < n+1 := by simp
    simp [simplexConeJacobian, hl]
  rw [Finset.sum_congr rfl (by intro j hj; exact hentry j), hlast]
  rw [← Finset.mul_sum]

lemma map_hasFDerivAt (n : ℕ) (x : Fin (n+2) → ℝ) :
    HasFDerivAt (simplexConeMap n)
      (Matrix.toLin' (simplexConeJacobian n x)).toContinuousLinearMap x := by
  apply hasFDerivAt_pi'.2
  intro i
  cases i using Fin.lastCases with
  | last =>
    have ht : HasFDerivAt (fun y : Fin (n+2) → ℝ => y (Fin.last (n+1)))
        (ContinuousLinearMap.proj (Fin.last (n+1)) : (Fin (n+2) → ℝ) →L[ℝ] ℝ) x :=
      (ContinuousLinearMap.proj (Fin.last (n+1)) : (Fin (n+2) → ℝ) →L[ℝ] ℝ).hasFDerivAt
    have hs : HasFDerivAt (fun y : Fin (n+2) → ℝ =>
        ∑ j : Fin (n+1), y j.castSucc)
        (∑ j : Fin (n+1),
          (ContinuousLinearMap.proj j.castSucc : (Fin (n+2) → ℝ) →L[ℝ] ℝ)) x := by
      apply HasFDerivAt.fun_sum
      intro j hj
      exact (ContinuousLinearMap.proj j.castSucc : (Fin (n+2) → ℝ) →L[ℝ] ℝ).hasFDerivAt
    have hq := hs.const_sub (1 : ℝ)
    have hm := ht.mul hq
    have hcoord : HasFDerivAt (fun y : Fin (n+2) → ℝ =>
        simplexConeMap n y (Fin.last (n+1)))
        (x (Fin.last (n+1)) •
          (-∑ j : Fin (n+1),
            (ContinuousLinearMap.proj j.castSucc : (Fin (n+2) → ℝ) →L[ℝ] ℝ)) +
          (1 - ∑ j : Fin (n+1), x j.castSucc) •
            (ContinuousLinearMap.proj (Fin.last (n+1)) : (Fin (n+2) → ℝ) →L[ℝ] ℝ)) x := by
      exact hm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => map_last n y)
    convert hcoord using 1
    ext v
    change (Matrix.toLin' (simplexConeJacobian n x)).toContinuousLinearMap v
      (Fin.last (n+1)) = _
    rw [jacobian_last]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  | cast j =>
    have ht : HasFDerivAt (fun y : Fin (n+2) → ℝ => y (Fin.last (n+1)))
        (ContinuousLinearMap.proj (Fin.last (n+1)) : (Fin (n+2) → ℝ) →L[ℝ] ℝ) x :=
      (ContinuousLinearMap.proj (Fin.last (n+1)) : (Fin (n+2) → ℝ) →L[ℝ] ℝ).hasFDerivAt
    have hp : HasFDerivAt (fun y : Fin (n+2) → ℝ => y j.castSucc)
        (ContinuousLinearMap.proj j.castSucc : (Fin (n+2) → ℝ) →L[ℝ] ℝ) x :=
      (ContinuousLinearMap.proj j.castSucc : (Fin (n+2) → ℝ) →L[ℝ] ℝ).hasFDerivAt
    have hm := ht.mul hp
    have hcoord : HasFDerivAt (fun y : Fin (n+2) → ℝ => simplexConeMap n y j.castSucc)
        (x (Fin.last (n+1)) •
          (ContinuousLinearMap.proj j.castSucc : (Fin (n+2) → ℝ) →L[ℝ] ℝ) +
          x j.castSucc •
            (ContinuousLinearMap.proj (Fin.last (n+1)) : (Fin (n+2) → ℝ) →L[ℝ] ℝ)) x := by
      exact hm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => map_castSucc n y j)
    convert hcoord using 1
    ext v
    change (Matrix.toLin' (simplexConeJacobian n x)).toContinuousLinearMap v j.castSucc = _
    rw [jacobian_castSucc]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

lemma sum_erase_last_eq_castSucc (n : ℕ) (f : Fin (n+2) → ℝ) :
    (∑ k ∈ Finset.univ.erase (Fin.last (n+1)), f k) = ∑ i : Fin (n+1), f i.castSucc := by
  have hsplit : (∑ k ∈ Finset.univ, f k) =
      (∑ i : Fin (n+1), f i.castSucc) + f (Fin.last (n+1)) :=
    by simpa using (Fin.sum_univ_castSucc f)
  have herase : (∑ k ∈ Finset.univ.erase (Fin.last (n+1)), f k) + f (Fin.last (n+1)) =
      ∑ k ∈ Finset.univ, f k :=
    Finset.sum_erase_add Finset.univ f (a := Fin.last (n+1)) (Finset.mem_univ _)
  rw [hsplit] at herase
  exact add_right_cancel herase

lemma jacobian_top_column_sum (n : ℕ) (x : Fin (n+2) → ℝ) (j : Fin (n+1)) :
    (∑ i : Fin (n+1), simplexConeJacobian n x i.castSucc j.castSucc) =
      x (Fin.last (n+1)) := by
  have hentry : ∀ i : Fin (n+1),
      simplexConeJacobian n x i.castSucc j.castSucc =
        (if i = j then x (Fin.last (n+1)) else 0) := by
    intro i
    have hi : (i : ℕ) ≤ n := by omega
    have hj : (j : ℕ) ≤ n := by omega
    simp [simplexConeJacobian, hi, hj]
  rw [Finset.sum_congr rfl (by intro i hi; exact hentry i)]
  simp

lemma jacobian_top_last_sum (n : ℕ) (x : Fin (n+2) → ℝ) :
    (∑ i : Fin (n+1), simplexConeJacobian n x i.castSucc (Fin.last (n+1))) =
      ∑ i : Fin (n+1), x i.castSucc := by
  apply Finset.sum_congr rfl
  intro i hi
  have hrow : (i.castSucc : Fin (n+2)).val < n+1 := by simpa using i.isLt
  have hrow' : (i : ℕ) ≤ n := by omega
  have hlast : ¬ (Fin.last (n+1) : Fin (n+2)).val < n+1 := by simp
  simp [simplexConeJacobian, hrow', hlast]

lemma jacobian_det (n : ℕ) (x : Fin (n+2) → ℝ) :
    (simplexConeJacobian n x).det = x (Fin.last (n+1))^(n+1) := by
  let J := simplexConeJacobian n x
  let l := Fin.last (n+1)
  let K := J.updateRow l (J l + ∑ i : Fin (n+1), J i.castSucc)
  have hrow : (1 : ℝ) • J l +
      ∑ k ∈ Finset.univ.erase l, (1 : ℝ) • J k = J l + ∑ i : Fin (n+1), J i.castSucc := by
    ext j
    simp only [one_smul, Pi.add_apply]
    rw [Finset.sum_apply j (Finset.univ.erase l) (fun k => J k)]
    rw [sum_erase_last_eq_castSucc n (fun k => J k j)]
    rw [Finset.sum_apply j (Finset.univ : Finset (Fin (n+1)))
      (fun i : Fin (n+1) => J i.castSucc)]
  have hdet : K.det = J.det := by
    have h := Matrix.det_updateRow_sum_aux J (Finset.univ.erase l)
      (Finset.univ.notMem_erase l) (fun _ => (1 : ℝ)) (1 : ℝ)
    rw [hrow] at h
    simpa [K] using h
  have hzero (j : Fin (n+1)) : K l j.castSucc = 0 := by
    simp only [K, Matrix.updateRow_self, Pi.add_apply, Finset.sum_apply, J]
    rw [jacobian_top_column_sum]
    have hj' : (j : ℕ) ≤ n := by omega
    simp [simplexConeJacobian, l, hj']
  have hlast : K l l = 1 := by
    simp only [K, Matrix.updateRow_self, Pi.add_apply, Finset.sum_apply, J]
    rw [jacobian_top_last_sum]
    simp [simplexConeJacobian, l]
  have htri : K.IsUpperTriangular := by
    intro i j hij
    by_cases hi : i = l
    · subst i
      cases j using Fin.lastCases with
      | last => exact (lt_irrefl _ hij).elim
      | cast j => exact hzero j
    · have hi' : (i : ℕ) < n+1 := by
        by_contra hn
        have hv : i.val = n+1 := by omega
        exact hi (Fin.ext hv)
      have hj' : (j : ℕ) < n+1 := by
        have hij' : j < i := by simpa using hij
        have hval := (Fin.lt_def.mp hij')
        omega
      have hij' : j < i := by simpa using hij
      have hne : i ≠ j := ne_of_gt hij'
      simp [K, Matrix.updateRow, Function.update, J, simplexConeJacobian, hi, hi', hj', hne]
  have hdiag : ∀ i : Fin (n+2), K i i = if i = l then 1 else x l := by
    intro i
    by_cases hi : i = l
    · subst i
      simp [hlast]
    · have hi' : (i : ℕ) < n+1 := by
        by_contra hn
        have hv : i.val = n+1 := by omega
        exact hi (Fin.ext hv)
      simp [K, Matrix.updateRow, Function.update, J, simplexConeJacobian, l, hi, hi']
  calc
    J.det = K.det := hdet.symm
    _ = ∏ i : Fin (n+2), K i i := Matrix.det_of_isUpperTriangular htri
    _ = x l^(n+1) := by
      rw [Fin.prod_univ_castSucc]
      simp [l, hdiag]

end SAP.P037a.WH.W1.P.T4_L1

theorem SAP.P037a.WH.W1.T4_L1_proof : SAP.P037a.WH.W1.T4_L1 := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro x hx i
      rcases hx with ⟨hp, ht⟩
      rcases hp with ⟨hpos, hsum⟩
      cases i using Fin.lastCases with
      | last =>
        rw [SAP.P037a.WH.W1.P.T4_L1.map_last]
        exact mul_pos ht (by linarith)
      | cast j =>
        rw [SAP.P037a.WH.W1.P.T4_L1.map_castSucc]
        exact mul_pos ht (hpos j)
    · constructor
      · intro x hx y hy hxy
        have hx' := SAP.P037a.WH.W1.P.T4_L1.inverse_map_map n x hx
        have hy' := SAP.P037a.WH.W1.P.T4_L1.inverse_map_map n y hy
        calc
          x = simplexConeInverse n (simplexConeMap n x) := hx'.symm
          _ = simplexConeInverse n (simplexConeMap n y) := by rw [hxy]
          _ = y := hy'
      · intro e he
        exact ⟨simplexConeInverse n e,
          SAP.P037a.WH.W1.P.T4_L1.inverse_mem n e he,
          SAP.P037a.WH.W1.P.T4_L1.inverse_map n e he⟩
  · intro e he
    exact ⟨SAP.P037a.WH.W1.P.T4_L1.inverse_mem n e he,
      SAP.P037a.WH.W1.P.T4_L1.inverse_map n e he⟩
  · intro x hx
    refine ⟨SAP.P037a.WH.W1.P.T4_L1.inverse_map_map n x hx,
      SAP.P037a.WH.W1.P.T4_L1.map_hasFDerivAt n x, ?_⟩
    rw [SAP.P037a.WH.W1.P.T4_L1.jacobian_det]
    exact abs_of_pos (pow_pos hx.2 (n+1))
