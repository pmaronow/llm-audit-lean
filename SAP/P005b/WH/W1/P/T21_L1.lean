import SAP.P005b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005b.WH.W1.P.T21_L1

noncomputable section
open scoped BigOperators Matrix
open Finset
open SAP.P005b

private lemma avg_add {n : ℕ} (S : Finset (Fin n)) (f g : Fin n → ℝ) :
    mean S (fun i => f i + g i) = mean S f + mean S g := by
  simp [mean, Finset.sum_add_distrib, add_div]

private lemma avg_sub {n : ℕ} (S : Finset (Fin n)) (f g : Fin n → ℝ) :
    mean S (fun i => f i - g i) = mean S f - mean S g := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

private lemma avg_mul {n : ℕ} (S : Finset (Fin n)) (f : Fin n → ℝ) (c : ℝ) :
    mean S (fun i => c * f i) = c * mean S f := by
  unfold mean
  rw [← Finset.mul_sum]
  ring

private lemma avg_const {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (c : ℝ) :
    mean S (fun _ => c) = c := by
  have h : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  simp [mean, nsmul_eq_mul, h]

private lemma avg_dot {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (v : Fin d → ℝ) :
    mean S (fun i => dot (P.x i) v) = dot (xMean P S) v := by
  simp only [mean, dot, xMean, div_mul_eq_mul_div, Finset.sum_div, Finset.sum_mul]
  exact Finset.sum_comm

private lemma indicator_sum_local {n : ℕ} (S : Finset (Fin n)) (a : Fin n → ℝ) :
    (∑ i, indicator S i * a i) = ∑ i ∈ S, a i := by
  calc
    (∑ i, indicator S i * a i) = ∑ i ∈ S, indicator S i * a i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i hi hnot
      simp [indicator, hnot]
    _ = ∑ i ∈ S, a i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [indicator, hi]

private lemma mean_congr_on {n : ℕ} (S : Finset (Fin n)) (f g : Fin n → ℝ)
    (h : ∀ i ∈ S, f i = g i) : mean S f = mean S g := by
  unfold mean
  congr 1
  exact Finset.sum_congr rfl h

private lemma control_card {n m : ℕ} {S : Finset (Fin n)}
    (hS : S ∈ design n m) : (control S).card = n-m := by
  rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp only [Finset.card_univ, Fintype.card_fin, (Finset.mem_powersetCard.mp hS).2]

private lemma mean_split {n m : ℕ} {S : Finset (Fin n)}
    (hS : S ∈ design n m) (hm : 0 < m) (hmn : m < n)
    (f g : Fin n → ℝ) :
    mean univ (fun i => if i ∈ S then f i else g i) =
      pT n m * mean S f + pC n m * mean (control S) g := by
  have hsum : (∑ i, (if i ∈ S then f i else g i)) =
      (∑ i ∈ S, f i) + ∑ i ∈ control S, g i := by
    calc
      _ = (∑ i ∈ control S, (if i ∈ S then f i else g i)) +
          ∑ i ∈ S, (if i ∈ S then f i else g i) := by
        simpa only [control] using
          (Finset.sum_sdiff (Finset.subset_univ S)
            (f := fun i => if i ∈ S then f i else g i)).symm
      _ = (∑ i ∈ control S, g i) + ∑ i ∈ S, f i := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          change i ∈ univ \ S at hi
          simp [(Finset.mem_sdiff.mp hi).2]
        · apply Finset.sum_congr rfl
          intro i hi
          simp [hi]
      _ = _ := by ring
  have hscard : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hccard : (control S).card = n-m := control_card hS
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hcR : ((n-m : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hmn))
  have hnR : (n : ℝ) ≠ 0 := by
    have hnNat : n ≠ 0 := by omega
    exact_mod_cast hnNat
  have hT : pT n m * mean S f = (∑ i ∈ S, f i) / (n : ℝ) := by
    unfold pT mean
    rw [hscard]
    field_simp [hmR, hnR]
  have hC : pC n m * mean (control S) g =
      (∑ i ∈ control S, g i) / (n : ℝ) := by
    unfold pC mean
    rw [hccard]
    have hcast : ((n-m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
      exact_mod_cast Nat.cast_sub (le_of_lt hmn)
    rw [hcast]
    change (((n : ℝ) - (m : ℝ)) / (n : ℝ)) *
      ((∑ i ∈ control S, g i) / ((n : ℝ) - (m : ℝ))) = _
    have hdiff : (n : ℝ) - (m : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply sub_pos.mpr
      exact_mod_cast hmn
    calc
      _ = (((n : ℝ) - (m : ℝ)) * (∑ i ∈ control S, g i)) /
          (((n : ℝ) - (m : ℝ)) * (n : ℝ)) := by field_simp [hdiff, hnR]
      _ = (∑ i ∈ control S, g i) / (n : ℝ) := by field_simp [hdiff, hnR]
  have huniv : mean univ (fun i => if i ∈ S then f i else g i) =
      (∑ i, (if i ∈ S then f i else g i)) / (n : ℝ) := by
    simp [mean, Finset.card_univ, Fintype.card_fin]
  rw [huniv, hsum, add_div, ← hT, ← hC]

private lemma armL_weighted_eq_Lhat {n d m : ℕ} (P : Population n d)
    (hm : 0 < m) (hmn : m < n) (hG : gram P = 1) (S : Finset (Fin n))
    (hS : S ∈ design n m) :
    (fun k l => pT n m * armL P S k l +
      pC n m * armL P (control S) k l) = Lhat P m S := by
  funext k
  funext l
  have hsplit := mean_split hS hm hmn
    (fun i => P.x i k * P.x i l) (fun i => P.x i k * P.x i l)
  have hg : mean univ (fun i => P.x i k * P.x i l) = if k = l then 1 else 0 := by
    change gram P k l = _
    rw [hG]
    simp [Matrix.one_apply]
  have hsplit' : mean univ (fun i => P.x i k * P.x i l) =
      pT n m * mean S (fun i => P.x i k * P.x i l) +
        pC n m * mean (control S) (fun i => P.x i k * P.x i l) := by
    simpa only [ite_self] using hsplit
  change pT n m * (mean S (fun i => P.x i k * P.x i l) -
        xMean P S k * xMean P S l) +
      pC n m * (mean (control S) (fun i => P.x i k * P.x i l) -
        xMean P (control S) k * xMean P (control S) l) =
      (if k = l then 1 else 0) -
        pT n m * (xMean P S k * xMean P S l) -
        pC n m * (xMean P (control S) k * xMean P (control S) l)
  have hsumG : pT n m * mean S (fun i => P.x i k * P.x i l) +
      pC n m * mean (control S) (fun i => P.x i k * P.x i l) =
      if k = l then 1 else 0 := hsplit'.symm.trans hg
  calc
    _ = (pT n m * mean S (fun i => P.x i k * P.x i l) +
        pC n m * mean (control S) (fun i => P.x i k * P.x i l)) -
        pT n m * (xMean P S k * xMean P S l) -
        pC n m * (xMean P (control S) k * xMean P (control S) l) := by ring
    _ = _ := by rw [hsumG]

private lemma arm_x_residual_moment {n d : ℕ} (P : Population n d)
    (A : Finset (Fin n)) (hA : A.Nonempty) (y : Fin n → ℝ)
    (b : Fin d → ℝ) (k : Fin d) :
    mean A (fun i => P.x i k *
      (y i - mean A y - (dot (P.x i) b - dot (xMean P A) b))) =
      armN P A y k - ∑ l, armL P A k l * b l := by
  have hq : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hA
  have hxdot : mean A (fun i => P.x i k * dot (P.x i) b) =
      ∑ l, mean A (fun i => P.x i k * P.x i l) * b l := by
    simp only [dot, mean, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    calc
      (∑ i ∈ A, P.x i k * (P.x i l * b l) / (A.card : ℝ)) =
          (∑ i ∈ A, (P.x i k * P.x i l) / (A.card : ℝ)) * b l := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by ring
  have hxconst : mean A (fun i => P.x i k * dot (xMean P A) b) =
      xMean P A k * dot (xMean P A) b := by
    have hf : (fun i => P.x i k * dot (xMean P A) b) =
        (fun i => dot (xMean P A) b * P.x i k) := by
      funext i
      ring
    calc
      _ = mean A (fun i => dot (xMean P A) b * P.x i k) := by rw [hf]
      _ = dot (xMean P A) b * mean A (fun i => P.x i k) :=
        avg_mul A (fun i => P.x i k) (dot (xMean P A) b)
      _ = _ := by change dot (xMean P A) b * xMean P A k = _; ring
  have hfun : (fun i => P.x i k *
      (y i - mean A y - (dot (P.x i) b - dot (xMean P A) b))) =
      (fun i => (P.x i k * y i - P.x i k * mean A y) -
        (P.x i k * dot (P.x i) b - P.x i k * dot (xMean P A) b)) := by
    funext i
    ring
  have hmy : mean A (fun i => P.x i k * mean A y) = mean A y * xMean P A k := by
    calc
      _ = mean A (fun i => mean A y * P.x i k) := by
        apply mean_congr_on
        intro i hi
        ring
      _ = mean A y * mean A (fun i => P.x i k) :=
        avg_mul A (fun i => P.x i k) (mean A y)
      _ = _ := rfl
  have hfirst : mean A (fun i => P.x i k * y i) -
      mean A y * xMean P A k = armN P A y k := by
    unfold armN
    have hswap : mean A (fun i => P.x i k * y i) =
        mean A (fun i => y i * P.x i k) := by
      apply mean_congr_on
      intro i hi
      ring
    rw [hswap]
  have hsecond : mean A (fun i => P.x i k * dot (P.x i) b) -
      mean A (fun i => P.x i k * dot (xMean P A) b) =
      ∑ l, armL P A k l * b l := by
    rw [hxdot, hxconst]
    simp only [armL, dot, xMean]
    simp only [sub_mul]
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
    have hs : (∑ l, (mean A fun i => P.x i k) *
        ((mean A fun i => P.x i l) * b l)) =
        ∑ l, ((mean A fun i => P.x i k) * mean A (fun i => P.x i l)) * b l := by
      apply Finset.sum_congr rfl
      intro l hl
      ring
    rw [hs]
  have hmeanfun : mean A (fun i =>
      (P.x i k * y i - P.x i k * mean A y) -
        (P.x i k * dot (P.x i) b - P.x i k * dot (xMean P A) b)) =
      mean A (fun i => P.x i k * y i - P.x i k * mean A y) -
        mean A (fun i => P.x i k * dot (P.x i) b -
          P.x i k * dot (xMean P A) b) := by
    exact avg_sub A
      (fun i => P.x i k * y i - P.x i k * mean A y)
      (fun i => P.x i k * dot (P.x i) b - P.x i k * dot (xMean P A) b)
  calc
    _ = mean A (fun i =>
          (P.x i k * y i - P.x i k * mean A y) -
            (P.x i k * dot (P.x i) b - P.x i k * dot (xMean P A) b)) := by
      apply mean_congr_on
      intro i hi
      exact congrFun hfun i
    _ = mean A (fun i => P.x i k * y i - P.x i k * mean A y) -
          mean A (fun i => P.x i k * dot (P.x i) b -
            P.x i k * dot (xMean P A) b) := hmeanfun
    _ = (mean A (fun i => P.x i k * y i) -
          mean A (fun i => P.x i k * mean A y)) -
        (mean A (fun i => P.x i k * dot (P.x i) b) -
          mean A (fun i => P.x i k * dot (xMean P A) b)) := by
      rw [avg_sub A
        (fun i => P.x i k * y i) (fun i => P.x i k * mean A y)]
      rw [avg_sub A
        (fun i => P.x i k * dot (P.x i) b)
        (fun i => P.x i k * dot (xMean P A) b)]
    _ = armN P A y k - ∑ l, armL P A k l * b l := by
      rw [hmy, hfirst, hsecond]

theorem target_proof : SAP.P005b.WH.W1.T21_L1 := by
  intro n d m P hn hm hmn hP S hS hdet
  let a := wholeW1Intercept P m S
  let t := adjustedATE P m S
  let b := betaHat P m S
  let e := fun i => wholeW1Observed P S i - wholeW1Fit P S a t b i
  have hcardS : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hcardC : (control S).card = n-m := control_card hS
  have hST : S.Nonempty := Finset.card_pos.mp (by omega)
  have hSC : (control S).Nonempty := Finset.card_pos.mp (by rw [hcardC]; omega)
  have ha : a = mean (control S) P.yC - dot (xMean P (control S)) b := rfl
  have ht : t = mean S P.yT - mean (control S) P.yC -
      dot (xMean P S - xMean P (control S)) b := rfl
  have hdot_sub : dot (xMean P S - xMean P (control S)) b =
      dot (xMean P S) b - dot (xMean P (control S)) b := by
    simp [dot, Finset.sum_sub_distrib, sub_mul]
  have hat : a + t = mean S P.yT - dot (xMean P S) b := by
    rw [ha, ht, hdot_sub]
    ring
  have hfitC : mean (control S) (fun i => wholeW1Fit P S a t b i) =
      mean (control S) P.yC := by
    have hp : ∀ i ∈ control S, wholeW1Fit P S a t b i = a + dot (P.x i) b := by
      intro i hi
      change i ∈ univ \ S at hi
      have hnot : i ∉ S := (Finset.mem_sdiff.mp hi).2
      simp [wholeW1Fit, indicator, hnot]
    rw [mean_congr_on _ _ _ hp]
    calc
      mean (control S) (fun i => a + dot (P.x i) b) =
          mean (control S) (fun i => (fun _ : Fin n => a) i + dot (P.x i) b) := rfl
      _ = mean (control S) (fun _ : Fin n => a) +
          mean (control S) (fun i => dot (P.x i) b) :=
        avg_add _ _ _
      _ = mean (control S) P.yC := by
        have hc := avg_const (control S) hSC a
        have hd := avg_dot P (control S) b
        rw [hc, hd, ha]
        ring
  have hfitT : mean S (fun i => wholeW1Fit P S a t b i) = mean S P.yT := by
    have hp : ∀ i ∈ S, wholeW1Fit P S a t b i = a + t + dot (P.x i) b := by
      intro i hi
      simp [wholeW1Fit, indicator, hi]
    rw [mean_congr_on _ _ _ hp]
    calc
      mean S (fun i => a+t + dot (P.x i) b) =
          mean S (fun i => (fun _ : Fin n => a+t) i + dot (P.x i) b) := rfl
      _ = mean S (fun _ : Fin n => a+t) +
          mean S (fun i => dot (P.x i) b) := avg_add _ _ _
      _ = mean S P.yT := by
        have hc := avg_const S hST (a+t)
        have hd := avg_dot P S b
        rw [hc, hd, hat]
        ring
  have hmeanC : mean (control S) (fun i => P.yC i - wholeW1Fit P S a t b i) = 0 := by
    calc
      mean (control S) (fun i => P.yC i - wholeW1Fit P S a t b i) =
          mean (control S) P.yC -
            mean (control S) (fun i => wholeW1Fit P S a t b i) :=
        avg_sub _ _ _
      _ = 0 := by rw [hfitC]; ring
  have hmeanT : mean S (fun i => P.yT i - wholeW1Fit P S a t b i) = 0 := by
    calc
      mean S (fun i => P.yT i - wholeW1Fit P S a t b i) =
          mean S P.yT - mean S (fun i => wholeW1Fit P S a t b i) :=
        avg_sub _ _ _
      _ = 0 := by rw [hfitT]; ring
  have hsumC : (∑ i ∈ control S, (P.yC i - wholeW1Fit P S a t b i)) = 0 := by
    have h := hmeanC
    unfold mean at h
    rw [hcardC] at h
    have hcardne : (((n-m : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hmn))
    exact (div_eq_zero_iff.mp h).resolve_right hcardne
  have hsumT : (∑ i ∈ S, (P.yT i - wholeW1Fit P S a t b i)) = 0 := by
    have h := hmeanT
    unfold mean at h
    rw [hcardS] at h
    have hcardne : ((m : ℝ)) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    exact (div_eq_zero_iff.mp h).resolve_right hcardne
  have heC : ∀ i ∈ control S, e i = P.yC i - wholeW1Fit P S a t b i := by
    intro i hi
    change i ∈ univ \ S at hi
    have hnot : i ∉ S := (Finset.mem_sdiff.mp hi).2
    simp [e, wholeW1Observed, hnot]
  have heT : ∀ i ∈ S, e i = P.yT i - wholeW1Fit P S a t b i := by
    intro i hi
    simp [e, wholeW1Observed, hi]
  have htotal : (∑ i, e i) = 0 := by
    rw [← Finset.sum_sdiff (Finset.subset_univ S) (f := e)]
    change (∑ i ∈ control S, e i) + (∑ i ∈ S, e i) = 0
    rw [Finset.sum_congr rfl heC, Finset.sum_congr rfl heT]
    rw [hsumC, hsumT]
    ring
  have htreated : (∑ i, indicator S i * e i) = 0 := by
    calc
      (∑ i, indicator S i * e i) = ∑ i ∈ S, e i :=
        indicator_sum_local S e
      _ = 0 := by rw [Finset.sum_congr rfl heT, hsumT]
  have hbeta : Lhat P m S *ᵥ b = Nhat P m S := by
    dsimp [b, betaHat]
    have hunit : IsUnit (Lhat P m S).det := (isUnit_iff_ne_zero).2 hdet
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (Lhat P m S) hunit,
      Matrix.one_mulVec]
  have hL := armL_weighted_eq_Lhat P hm hmn hP.2 S hS
  have hcov : ∀ k, (∑ i, P.x i k * e i) = 0 := by
    intro k
    have hsplit := mean_split hS hm hmn
      (fun i => P.x i k * (P.yT i - mean S P.yT -
        (dot (P.x i) b - dot (xMean P S) b)))
      (fun i => P.x i k * (P.yC i - mean (control S) P.yC -
        (dot (P.x i) b - dot (xMean P (control S)) b)))
    have heTform : ∀ i ∈ S, e i = P.yT i - mean S P.yT -
        (dot (P.x i) b - dot (xMean P S) b) := by
      intro i hi
      calc
        e i = P.yT i - wholeW1Fit P S a t b i := heT i hi
        _ = P.yT i - (a+t + dot (P.x i) b) := by
          simp [wholeW1Fit, indicator, hi]
        _ = P.yT i - mean S P.yT -
            (dot (P.x i) b - dot (xMean P S) b) := by
          rw [hat]
          ring
    have heCform : ∀ i ∈ control S, e i = P.yC i - mean (control S) P.yC -
        (dot (P.x i) b - dot (xMean P (control S)) b) := by
      intro i hi
      change i ∈ univ \ S at hi
      have hnot : i ∉ S := (Finset.mem_sdiff.mp hi).2
      calc
        e i = P.yC i - wholeW1Fit P S a t b i := heC i hi
        _ = P.yC i - (a + dot (P.x i) b) := by
          simp [wholeW1Fit, indicator, hnot]
        _ = P.yC i - mean (control S) P.yC -
            (dot (P.x i) b - dot (xMean P (control S)) b) := by
          rw [ha]
          ring
    have hmeanid : mean univ (fun i => P.x i k * e i) =
        pT n m * (armN P S P.yT k - ∑ l, armL P S k l * b l) +
        pC n m * (armN P (control S) P.yC k -
          ∑ l, armL P (control S) k l * b l) := by
      have hp : ∀ i ∈ univ,
          P.x i k * e i = if i ∈ S then
            P.x i k * (P.yT i - mean S P.yT -
              (dot (P.x i) b - dot (xMean P S) b)) else
            P.x i k * (P.yC i - mean (control S) P.yC -
              (dot (P.x i) b - dot (xMean P (control S)) b)) := by
        intro i hi
        by_cases his : i ∈ S
        · rw [if_pos his, heTform i his]
        · have hic : i ∈ control S := by simp [control, his]
          rw [if_neg his, heCform i hic]
      rw [mean_congr_on univ _ _ hp]
      rw [mean_split hS hm hmn]
      rw [arm_x_residual_moment P S hST P.yT b k,
        arm_x_residual_moment P (control S) hSC P.yC b k]
    have hnorm : mean univ (fun i => P.x i k * e i) = 0 := by
      rw [hmeanid]
      have hnEq : pT n m * armN P S P.yT k +
          pC n m * armN P (control S) P.yC k = Nhat P m S k := by
        rfl
      have hmatrix : (∑ l, Lhat P m S k l * b l) = Nhat P m S k := by
        have hh := congrArg (fun v : Fin d → ℝ => v k) hbeta
        change dot (fun l => Lhat P m S k l) b = Nhat P m S k at hh
        simpa [dot] using hh
      have hLcoord : (∑ l, Lhat P m S k l * b l) =
          pT n m * ∑ l, armL P S k l * b l +
          pC n m * ∑ l, armL P (control S) k l * b l := by
        rw [← hL]
        calc
          _ = ∑ l, (pT n m * (armL P S k l * b l) +
              pC n m * (armL P (control S) k l * b l)) := by
            apply Finset.sum_congr rfl
            intro l hl
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      calc
        _ = (pT n m * armN P S P.yT k +
            pC n m * armN P (control S) P.yC k) -
            (pT n m * (∑ l, armL P S k l * b l) +
              pC n m * (∑ l, armL P (control S) k l * b l)) := by ring
        _ = Nhat P m S k - (∑ l, Lhat P m S k l * b l) := by
          rw [hnEq, ← hLcoord]
        _ = 0 := by rw [hmatrix]; simp
    have hnR : (n : ℝ) ≠ 0 := by
      have hnNat : n ≠ 0 := by omega
      exact_mod_cast hnNat
    have htotalmean : (∑ i, P.x i k * e i) / (n : ℝ) = 0 := by
      simpa only [mean, Finset.card_univ, Fintype.card_fin] using hnorm
    exact (div_eq_zero_iff.mp htotalmean).resolve_right hnR
  exact ⟨htotal, htreated, hcov⟩

end

end SAP.P005b.WH.W1.P.T21_L1

theorem SAP.P005b.WH.W1.T21_L1_proof : SAP.P005b.WH.W1.T21_L1 := by
  exact SAP.P005b.WH.W1.P.T21_L1.target_proof
