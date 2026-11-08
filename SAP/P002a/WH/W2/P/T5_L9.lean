import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2.P.T5_L9

open SAP.P002a
open SAP.P002a.WH.W2
open scoped BigOperators

noncomputable section

def flipPattern {k : ℕ} (a : Fin (k + 1)) :
    (Fin (k + 1) → Bool) ≃ (Fin (k + 1) → Bool) where
  toFun p t := if t = a then !p t else p t
  invFun p t := if t = a then !p t else p t
  left_inv p := by
    funext t
    by_cases h : t = a <;> simp [h]
  right_inv p := by
    funext t
    by_cases h : t = a <;> simp [h]

def cubeFlipEquiv (k j : ℕ) (a : Fin (k + 1)) :
    Fin (W2CubeSize k j) ≃ Fin (W2CubeSize k j) :=
  (W2CubeEquiv k j).trans
    ((Equiv.prodCongr (flipPattern a) (Equiv.refl (Fin (j + 1)))).trans
      (W2CubeEquiv k j).symm)

lemma cubeFlip_equiv_apply (k j : ℕ) (a : Fin (k + 1))
    (i : Fin (W2CubeSize k j)) :
    W2CubeEquiv k j (cubeFlipEquiv k j a i) =
      (flipPattern a (W2CubeEquiv k j i).1, (W2CubeEquiv k j i).2) := by
  simp [cubeFlipEquiv, Equiv.prodCongr, Prod.map]

lemma cubeSign_flip_self (k j : ℕ) (a : Fin (k + 1))
    (i : Fin (W2CubeSize k j)) :
    W2CubeSign k j a (cubeFlipEquiv k j a i) = -W2CubeSign k j a i := by
  rw [W2CubeSign, cubeFlip_equiv_apply]
  cases h : (W2CubeEquiv k j i).1 a <;> simp [W2CubeSign, flipPattern, h]

lemma cubeSign_flip_other (k j : ℕ) (a b : Fin (k + 1)) (hab : a ≠ b)
    (i : Fin (W2CubeSize k j)) :
    W2CubeSign k j b (cubeFlipEquiv k j a i) = W2CubeSign k j b i := by
  rw [W2CubeSign, cubeFlip_equiv_apply]
  simp [W2CubeSign, flipPattern, Ne.symm hab]

lemma cube_sum_flip_zero (k j : ℕ) (a : Fin (k + 1))
    (f : Fin (W2CubeSize k j) → ℝ)
    (hflip : ∀ i, f (cubeFlipEquiv k j a i) = -f i) :
    (∑ i, f i) = 0 := by
  have hcomp : (∑ i, f (cubeFlipEquiv k j a i)) = ∑ i, f i :=
    Equiv.sum_comp (cubeFlipEquiv k j a) f
  have hneg : (∑ i, f (cubeFlipEquiv k j a i)) = -∑ i, f i := by
    simp_rw [hflip]
    rw [Finset.sum_neg_distrib]
  linarith

lemma cubeSign_sum_zero (k j : ℕ) (a : Fin (k + 1)) :
    (∑ i, W2CubeSign k j a i) = 0 := by
  apply cube_sum_flip_zero k j a
  intro i
  exact cubeSign_flip_self k j a i

lemma cubeSign_mul_sum_zero (k j : ℕ) (a b : Fin (k + 1)) (hab : a ≠ b) :
    (∑ i, W2CubeSign k j a i * W2CubeSign k j b i) = 0 := by
  apply cube_sum_flip_zero k j a
  intro i
  rw [cubeSign_flip_self, cubeSign_flip_other k j a b hab]
  ring

lemma cubeSign_sq (k j : ℕ) (a : Fin (k + 1)) (i : Fin (W2CubeSize k j)) :
    W2CubeSign k j a i ^ 2 = 1 := by
  simp [W2CubeSign]

lemma cubeSign_fourth (k j : ℕ) (a : Fin (k + 1)) (i : Fin (W2CubeSize k j)) :
    W2CubeSign k j a i ^ 4 = 1 := by
  norm_num [W2CubeSign]

lemma cube_size_pos (k j : ℕ) : 0 < (W2CubeSize k j : ℝ) := by
  unfold W2CubeSize
  positivity

lemma cube_mean_of_sum (n : ℕ) (q : Fin n → ℝ) (c : ℝ)
    (hsum : (∑ i, q i) = (n : ℝ) * c) (hn : 0 < n) : mean q = c := by
  rw [mean, hsum]
  have hcast : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

lemma cube_mean_zero_of_sum (n : ℕ) (q : Fin n → ℝ)
    (hsum : (∑ i, q i) = 0) : mean q = 0 := by
  simp [mean, hsum]

lemma cube_sum_const (n : ℕ) (c : ℝ) :
    (∑ _i : Fin n, c) = (n : ℝ) * c := by
  simp

lemma cube_castSucc_ne_last (k : ℕ) (s : Fin k) : s.castSucc ≠ Fin.last k := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv
  omega

lemma cube_x_sum_zero (k j : ℕ) (eR : ℝ) (s : Fin k) :
    (∑ i : Fin (W2CubeSize k j),
      Real.sqrt eR * W2CubeSign k j s.castSucc i) = 0 := by
  rw [← Finset.mul_sum]
  rw [cubeSign_sum_zero]
  simp

lemma cube_cov_mean (k j : ℕ) (e : ℝ) (he : 0 < e) (s t : Fin k) :
    mean (fun i : Fin (W2CubeSize k j) =>
      (Real.sqrt e * W2CubeSign k j s.castSucc i) *
        (Real.sqrt e * W2CubeSign k j t.castSucc i)) =
      if s = t then e else 0 := by
  have hn : 0 < W2CubeSize k j := by
    unfold W2CubeSize
    positivity
  by_cases hst : s = t
  · subst t
    have hsum :
        (∑ i : Fin (W2CubeSize k j),
          (Real.sqrt e * W2CubeSign k j s.castSucc i) *
            (Real.sqrt e * W2CubeSign k j s.castSucc i)) =
          (W2CubeSize k j : ℝ) * e := by
      calc
        _ = ∑ _i : Fin (W2CubeSize k j), e := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            (Real.sqrt e * W2CubeSign k j s.castSucc i) *
                (Real.sqrt e * W2CubeSign k j s.castSucc i) =
              ((Real.sqrt e) ^ 2) * (W2CubeSign k j s.castSucc i ^ 2) := by ring
            _ = e := by rw [Real.sq_sqrt (le_of_lt he), cubeSign_sq]; ring
        _ = (W2CubeSize k j : ℝ) * e := cube_sum_const _ _
    rw [mean, hsum]
    have hcast : (W2CubeSize k j : ℝ) ≠ 0 := (cube_size_pos k j).ne'
    field_simp [hcast]
    simp
  · have hcoord : s.castSucc ≠ t.castSucc := by
      intro h
      exact hst (Fin.castSucc_inj.mp h)
    have hsum :
        (∑ i : Fin (W2CubeSize k j),
          (Real.sqrt e * W2CubeSign k j s.castSucc i) *
            (Real.sqrt e * W2CubeSign k j t.castSucc i)) = 0 := by
      calc
        _ = ∑ i : Fin (W2CubeSize k j),
            (Real.sqrt e) ^ 2 *
              (W2CubeSign k j s.castSucc i * W2CubeSign k j t.castSucc i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (Real.sqrt e) ^ 2 *
            ∑ i : Fin (W2CubeSize k j),
              W2CubeSign k j s.castSucc i * W2CubeSign k j t.castSucc i := by
          rw [Finset.mul_sum]
        _ = 0 := by rw [cubeSign_mul_sum_zero k j s.castSucc t.castSucc hcoord]; simp
    rw [mean, hsum]
    simp [hst]

lemma cube_x_fourth_mean (k j : ℕ) (e : ℝ) (he : 0 < e) (s : Fin k) :
    mean (fun i : Fin (W2CubeSize k j) =>
      (Real.sqrt e * W2CubeSign k j s.castSucc i) ^ 4) = e ^ 2 := by
  have hn : 0 < W2CubeSize k j := by
    unfold W2CubeSize
    positivity
  have hsum :
      (∑ i : Fin (W2CubeSize k j),
        (Real.sqrt e * W2CubeSign k j s.castSucc i) ^ 4) =
        (W2CubeSize k j : ℝ) * e ^ 2 := by
    calc
      _ = ∑ _i : Fin (W2CubeSize k j), e ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          (Real.sqrt e * W2CubeSign k j s.castSucc i) ^ 4 =
              ((Real.sqrt e) ^ 2) ^ 2 * W2CubeSign k j s.castSucc i ^ 4 := by ring
          _ = e ^ 2 := by rw [Real.sq_sqrt (le_of_lt he), cubeSign_fourth]; ring
      _ = (W2CubeSize k j : ℝ) * e ^ 2 := cube_sum_const _ _
  rw [mean, hsum]
  have hcast : (W2CubeSize k j : ℝ) ≠ 0 := (cube_size_pos k j).ne'
  field_simp

lemma cube_cross_mean_zero (k j : ℕ) (e : ℝ) (s : Fin k) :
    mean (fun i : Fin (W2CubeSize k j) =>
      (Real.sqrt e * W2CubeSign k j s.castSucc i) *
        W2CubeSign k j (Fin.last k) i) = 0 := by
  have hn : 0 < W2CubeSize k j := by
    unfold W2CubeSize
    positivity
  have hcoord : s.castSucc ≠ Fin.last k := cube_castSucc_ne_last k s
  have hsum :
      (∑ i : Fin (W2CubeSize k j),
        (Real.sqrt e * W2CubeSign k j s.castSucc i) *
          W2CubeSign k j (Fin.last k) i) = 0 := by
    calc
      _ = Real.sqrt e *
          ∑ i : Fin (W2CubeSize k j),
            W2CubeSign k j s.castSucc i * W2CubeSign k j (Fin.last k) i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [cubeSign_mul_sum_zero k j s.castSucc (Fin.last k) hcoord]; simp
  exact cube_mean_zero_of_sum _ _ hsum

end

end SAP.P002a.WH.W2.P.T5_L9

open SAP.P002a.WH.W2.P.T5_L9

theorem SAP.P002a.WH.W2.T5_L9_proof : SAP.P002a.WH.W2.T5_L9 := by
  intro k e j hk he
  dsimp only [SAP.P002a.WH.W2.T5_L9, W2CubeModel]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cubeSign_sum_zero k j (Fin.last k)
  · have hs : ∀ i : Fin (W2CubeSize k j),
        W2CubeSign k j (Fin.last k) i ^ 2 = 1 := by
      intro i
      exact cubeSign_sq k j (Fin.last k) i
    have hn : 0 < W2CubeSize k j := by
      unfold W2CubeSize
      positivity
    apply cube_mean_of_sum _ _ 1 ?_ hn
    calc
      (∑ i : Fin (W2CubeSize k j), W2CubeSign k j (Fin.last k) i ^ 2) =
          ∑ _i : Fin (W2CubeSize k j), (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hs i
      _ = (W2CubeSize k j : ℝ) * 1 := cube_sum_const _ _
  · have hs : ∀ i : Fin (W2CubeSize k j),
        W2CubeSign k j (Fin.last k) i ^ 4 = 1 := by
      intro i
      exact cubeSign_fourth k j (Fin.last k) i
    have hn : 0 < W2CubeSize k j := by
      unfold W2CubeSize
      positivity
    apply cube_mean_of_sum _ _ 1 ?_ hn
    calc
      (∑ i : Fin (W2CubeSize k j), W2CubeSign k j (Fin.last k) i ^ 4) =
          ∑ _i : Fin (W2CubeSize k j), (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hs i
      _ = (W2CubeSize k j : ℝ) * 1 := cube_sum_const _ _
  · intro s
    exact cube_x_sum_zero k j e s
  · intro s t
    exact cube_cov_mean k j e he s t
  · intro s
    exact cube_x_fourth_mean k j e he s
  · intro s
    exact cube_cross_mean_zero k j e s
