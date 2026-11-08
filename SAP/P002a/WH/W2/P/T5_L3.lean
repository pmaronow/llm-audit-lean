import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2.P.T5_L3

open scoped BigOperators

private def sign (m : ℕ) {n : ℕ} (i : Fin n) : ℝ :=
  if i.val < m then -1 else 1

private theorem sign_sum (m : ℕ) : (∑ i : Fin (2*m), sign m i) = 0 := by
  rw [show 2*m = m+m by omega, Fin.sum_univ_add]
  have hleft : (∑ i : Fin m, sign m (Fin.castAdd m i)) = -(m : ℝ) := by
    simp [sign, Fin.val_castAdd]
  have hright : (∑ i : Fin m, sign m (Fin.natAdd m i)) = (m : ℝ) := by
    calc
      _ = ∑ i : Fin m, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [sign, Fin.val_natAdd]
        have h : ¬ m + i.val < m := by omega
        simp [h]
      _ = (m : ℝ) := by simp
  rw [hleft, hright]
  ring

private theorem sign_sq (m : ℕ) (i : Fin (2*m)) : sign m i ^ 2 = 1 := by
  unfold sign
  split_ifs <;> norm_num

private theorem sign_four (m : ℕ) (i : Fin (2*m)) : sign m i ^ 4 = 1 := by
  unfold sign
  split_ifs <;> norm_num

private theorem sign_mean (m : ℕ) : mean (sign m (n := 2*m)) = 0 := by
  unfold mean
  rw [sign_sum]
  simp

private theorem sign_popVar (m : ℕ) :
    popVar (sign m (n := 2*m)) = ((2*m : ℕ) : ℝ) / (((2*m : ℕ) : ℝ) - 1) := by
  have hs : (∑ i : Fin (2*m), (sign m i)^2) = ((2*m : ℕ) : ℝ) := by
    calc
      _ = ∑ _i : Fin (2*m), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact sign_sq m i
      _ = ((2*m : ℕ) : ℝ) := by simp
  unfold popVar
  rw [sign_mean]
  simp only [sub_zero]
  rw [hs]

private theorem sign_fourthNorm (m : ℕ) (hm : 0 < m) :
    fourthNorm (sign m (n := 2*m)) = 1 := by
  have hs : mean (fun i : Fin (2*m) => sign m i ^ 4) = 1 := by
    unfold mean
    have hsum : (∑ i : Fin (2*m), sign m i ^ 4) = ((2*m : ℕ) : ℝ) := by
      calc
        _ = ∑ _i : Fin (2*m), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact sign_four m i
        _ = ((2*m : ℕ) : ℝ) := by simp
    rw [hsum]
    have hn : (2*m : ℕ) ≠ 0 := by omega
    field_simp [hn]
  unfold fourthNorm
  rw [hs]
  norm_num

end SAP.P002a.WH.W2.P.T5_L3

namespace SAP.P002a.WH.W2

open scoped BigOperators

theorem T5_L3_proof : SAP.P002a.WH.W2.T5_L3 := by
  classical
  intro δ r A hδ hr hA j
  let P := W2RawSharpModel j
  let m := j + 1
  have hmpos : 0 < m := by simp [m]
  have hn2 : 2 ≤ 2*m := by omega
  have hnR : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast hn2
  have hden : 0 < ((2*m : ℕ) : ℝ) - 1 := by linarith
  have hC : compliers P = ({0} : Finset (Fin (2*m))) := by
    ext i
    simp only [compliers, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro h
      have hi : i.val = 0 := by
        simpa [P, W2RawSharpModel] using h.2
      exact Fin.ext hi
    · intro h
      subst i
      simp [P, W2RawSharpModel]
  have hlate : late P = 0 := by
    simp [late, P, groupMean, W2RawSharpModel]
  have hw (a : Bool) : w P a (late P) =
      SAP.P002a.WH.W2.P.T5_L3.sign m (n := 2*m) := by
    funext i
    rw [hlate]
    simp [w, P, m, W2RawSharpModel, binary,
      SAP.P002a.WH.W2.P.T5_L3.sign]
  have hv (a : Bool) : v P a (late P) =
      SAP.P002a.WH.W2.P.T5_L3.sign m (n := 2*m) := by
    funext i
    rw [v, hw, SAP.P002a.WH.W2.P.T5_L3.sign_mean m]
    simp
  have hvar (a : Bool) :
      popVar (w P a (late P)) = ((2*m : ℕ) : ℝ) / (((2*m : ℕ) : ℝ) - 1) := by
    rw [hw]
    exact SAP.P002a.WH.W2.P.T5_L3.sign_popVar m
  have hroot : 1 ≤ Real.sqrt ((((2*m : ℕ) : ℝ) / (((2*m : ℕ) : ℝ) - 1))) := by
    apply Real.one_le_sqrt.mpr
    apply (le_div_iff₀ hden).2
    linarith
  have hTheta : Theta P δ r A := by
    unfold Theta
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold ValidDesign P W2RawSharpModel
      change (2 ≤ 2*m ∧ 0 < m ∧ m < 2*m)
      omega
    · intro i hi
      simp [P, W2RawSharpModel] at hi ⊢
    · rw [hC]
      exact Finset.singleton_nonempty _
    · have hmR : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      change r * ((2*m : ℕ) : ℝ) ≤ (m : ℝ)
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hr.2 hmR]
    · have hmR : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      change (m : ℝ) ≤ (1-r) * ((2*m : ℕ) : ℝ)
      push_cast
      have hr' : (1/2 : ℝ) ≤ 1-r := by linarith [hr.2]
      nlinarith [mul_le_mul_of_nonneg_left hr' hmR]
    · rw [hC]
      simp [groupCov, groupVar]
    · intro a
      rw [hv a, hvar a, SAP.P002a.WH.W2.P.T5_L3.sign_fourthNorm m hmpos]
      have hA0 : 0 ≤ A := by linarith
      have hmul := mul_le_mul_of_nonneg_left hroot hA0
      exact le_trans hA (by simpa using hmul)
  have hconst : ∀ i, P.y i true = P.y i false := by
    intro i
    rfl
  have hpop : 0 < popVar (fun i => P.y i false) := by
    change 0 < popVar (SAP.P002a.WH.W2.P.T5_L3.sign m (n := 2*m))
    rw [SAP.P002a.WH.W2.P.T5_L3.sign_popVar]
    have hnpos : 0 < 2*m := by omega
    exact div_pos (by exact_mod_cast hnpos) hden
  exact ⟨hTheta, hconst, hpop⟩

end SAP.P002a.WH.W2
