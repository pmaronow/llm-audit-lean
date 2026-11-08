import SAP.P005b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P005b.WH.W1.P.T21_L2

noncomputable section
open scoped BigOperators Matrix
open Finset

private lemma mean_add {n : ℕ} (S : Finset (Fin n)) (f g : Fin n → ℝ) :
    SAP.P005b.mean S (fun i => f i + g i) =
      SAP.P005b.mean S f + SAP.P005b.mean S g := by
  simp [SAP.P005b.mean, Finset.sum_add_distrib, add_div]

private lemma mean_congr {n : ℕ} (S : Finset (Fin n)) (f g : Fin n → ℝ)
    (h : ∀ i ∈ S, f i = g i) : SAP.P005b.mean S f = SAP.P005b.mean S g := by
  unfold SAP.P005b.mean
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact h i hi

private lemma mean_const {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (c : ℝ) :
    SAP.P005b.mean S (fun _ => c) = c := by
  have hc : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hS)
  simp [SAP.P005b.mean, nsmul_eq_mul, hc]

private lemma mean_mul {n : ℕ} (S : Finset (Fin n)) (f : Fin n → ℝ) (c : ℝ) :
    SAP.P005b.mean S (fun i => c * f i) = c * SAP.P005b.mean S f := by
  unfold SAP.P005b.mean
  rw [← Finset.mul_sum]
  ring

private lemma mean_dot {n d : ℕ} (P : SAP.P005b.Population n d)
    (S : Finset (Fin n)) (v : Fin d → ℝ) :
    SAP.P005b.mean S (fun i => SAP.P005b.dot (P.x i) v) =
      SAP.P005b.dot (SAP.P005b.xMean P S) v := by
  simp only [SAP.P005b.mean, SAP.P005b.dot, SAP.P005b.xMean,
    div_mul_eq_mul_div, Finset.sum_div, Finset.sum_mul]
  exact Finset.sum_comm

private lemma mean_sum {n d : ℕ} (S : Finset (Fin n))
    (f : Fin d → Fin n → ℝ) :
    SAP.P005b.mean S (fun i => ∑ j, f j i) = ∑ j, SAP.P005b.mean S (f j) := by
  simp only [SAP.P005b.mean, Finset.sum_div]
  exact Finset.sum_comm

private lemma mean_fit_arm {n d : ℕ} (P : SAP.P005b.Population n d)
    (A : Finset (Fin n)) (hA : A.Nonempty) (c : ℝ) (b : Fin d → ℝ) :
    SAP.P005b.mean A (fun i => c + SAP.P005b.dot (P.x i) b) =
      c + SAP.P005b.dot (SAP.P005b.xMean P A) b := by
  rw [mean_add, mean_const A hA, mean_dot]

private lemma armN_projection {n d : ℕ} (P : SAP.P005b.Population n d)
    (S : Finset (Fin n)) (v : Fin d → ℝ) :
    SAP.P005b.armN P S (fun i => SAP.P005b.dot (P.x i) v) =
      SAP.P005b.armL P S *ᵥ v := by
  funext k
  simp only [SAP.P005b.armN, SAP.P005b.armL, Matrix.mulVec, dotProduct,
    sub_mul, Finset.sum_sub_distrib]
  rw [mean_dot]
  have hh : SAP.P005b.mean S
      (fun i => SAP.P005b.dot (P.x i) v * P.x i k) =
      ∑ j, SAP.P005b.mean S (fun i => P.x i k * P.x i j) * v j := by
    calc
      _ = SAP.P005b.mean S (fun i => ∑ j, (P.x i j * v j) * P.x i k) := by
        congr 1
        funext i
        simp only [SAP.P005b.dot, Finset.sum_mul]
      _ = ∑ j, SAP.P005b.mean S (fun i => (P.x i j * v j) * P.x i k) :=
        mean_sum S (fun j i => (P.x i j * v j) * P.x i k)
      _ = ∑ j, SAP.P005b.mean S (fun i => P.x i k * P.x i j) * v j := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          SAP.P005b.mean S (fun i => (P.x i j * v j) * P.x i k) =
              SAP.P005b.mean S (fun i => v j * (P.x i k * P.x i j)) := by
                apply mean_congr
                intro i hi
                ring
          _ = SAP.P005b.mean S (fun i => P.x i k * P.x i j) * v j := by
                rw [mean_mul]
                ring
  rw [hh]
  simp only [SAP.P005b.dot, SAP.P005b.xMean, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma weighted_partition_mean {n m : ℕ} (hm : 0 < m) (hmn : m < n)
    (S : Finset (Fin n)) (hS : S ∈ SAP.P005b.design n m) (f : Fin n → ℝ) :
    SAP.P005b.pT n m * SAP.P005b.mean S f +
      SAP.P005b.pC n m * SAP.P005b.mean (SAP.P005b.control S) f =
        SAP.P005b.popMean f := by
  have hScard : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hCcard : (SAP.P005b.control S).card = n-m := by
    rw [SAP.P005b.control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [hScard]
  have hsumC : (∑ i ∈ SAP.P005b.control S, f i) =
      (∑ i, f i) - (∑ i ∈ S, f i) := by
    rw [SAP.P005b.control, Finset.sum_sdiff_eq_sub (Finset.subset_univ S)]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  have hcm0 : ((n-m : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hmn))
  have hTmean : SAP.P005b.pT n m * SAP.P005b.mean S f =
      (∑ i ∈ S, f i)/(n : ℝ) := by
    rw [SAP.P005b.pT, SAP.P005b.mean, hScard]
    field_simp [hm0, hn0]
  have hCmean : SAP.P005b.pC n m * SAP.P005b.mean (SAP.P005b.control S) f =
      (∑ i ∈ SAP.P005b.control S, f i)/(n : ℝ) := by
    rw [SAP.P005b.pC, SAP.P005b.mean, hCcard,
      Nat.cast_sub (le_of_lt hmn)]
    field_simp [hn0]
    have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    have hcmR : (n : ℝ) - (m : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hmnR)
    calc
      _ = (∑ i ∈ SAP.P005b.control S, f i) *
          (((n : ℝ)-(m : ℝ)) * ((n : ℝ)-(m : ℝ))⁻¹) := by ring
      _ = (∑ i ∈ SAP.P005b.control S, f i) := by
        rw [mul_inv_cancel₀ hcmR, mul_one]
  calc
    _ = (∑ i ∈ S, f i)/(n : ℝ) +
        (∑ i ∈ SAP.P005b.control S, f i)/(n : ℝ) := by rw [hTmean, hCmean]
    _ = SAP.P005b.popMean f := by
      rw [SAP.P005b.popMean, SAP.P005b.mean, hsumC]
      simp only [Finset.card_univ, Fintype.card_fin]
      ring

private lemma Lhat_eq_weighted_armL {n d m : ℕ} (P : SAP.P005b.Population n d)
    (hm : 0 < m) (hmn : m < n) (S : Finset (Fin n))
    (hS : S ∈ SAP.P005b.design n m) (hG : SAP.P005b.gram P = 1) :
    SAP.P005b.Lhat P m S =
      SAP.P005b.pT n m • SAP.P005b.armL P S +
        SAP.P005b.pC n m • SAP.P005b.armL P (SAP.P005b.control S) := by
  ext k l
  have hpart := weighted_partition_mean hm hmn S hS
    (fun i => P.x i k * P.x i l)
  have hgram := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M k l) hG
  have hgram' : SAP.P005b.popMean (fun i => P.x i k * P.x i l) =
      if k = l then 1 else 0 := by simpa [SAP.P005b.gram, Matrix.one_apply] using hgram
  change (SAP.P005b.Lhat P m S) k l =
    (SAP.P005b.pT n m • SAP.P005b.armL P S +
      SAP.P005b.pC n m • SAP.P005b.armL P (SAP.P005b.control S)) k l
  simp only [SAP.P005b.Lhat, SAP.P005b.armL, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Matrix.add_apply, smul_eq_mul]
  have hpart' : pT n m * mean S (fun i => P.x i k * P.x i l) +
      pC n m * mean (control S) (fun i => P.x i k * P.x i l) =
        if k = l then 1 else 0 := hpart.trans hgram'
  nlinarith [hpart']

private lemma armN_zero_of_const_projection {n d : ℕ}
    (P : SAP.P005b.Population n d) (A : Finset (Fin n)) (hA : A.Nonempty)
    (b : Fin d → ℝ) (c : ℝ)
    (hconst : ∀ i ∈ A, SAP.P005b.dot (P.x i) b = c) :
    SAP.P005b.armN P A (fun i => SAP.P005b.dot (P.x i) b) = 0 := by
  have hm : SAP.P005b.mean A (fun i => SAP.P005b.dot (P.x i) b) = c := by
    calc
      _ = SAP.P005b.mean A (fun _ => c) := mean_congr A _ _ hconst
      _ = c := mean_const A hA c
  funext k
  have hprod : SAP.P005b.mean A
      (fun i => SAP.P005b.dot (P.x i) b * P.x i k) = c * SAP.P005b.xMean P A k := by
    calc
      _ = SAP.P005b.mean A (fun i => c * P.x i k) :=
        mean_congr A _ _ (by
          intro i hi
          rw [hconst i hi])
      _ = c * SAP.P005b.mean A (fun i => P.x i k) :=
        mean_mul A (fun i => P.x i k) c
      _ = c * SAP.P005b.xMean P A k := rfl
  simp only [SAP.P005b.armN, hprod, hm, Pi.zero_apply]
  ring

private lemma mean_zero_of_zero_on {n : ℕ} (A : Finset (Fin n))
    (f : Fin n → ℝ) (hf : ∀ i ∈ A, f i = 0) :
    SAP.P005b.mean A f = 0 := by
  calc
    _ = SAP.P005b.mean A (fun _ => 0) := mean_congr A _ _ hf
    _ = 0 := by simp [SAP.P005b.mean]

end
end SAP.P005b.WH.W1.P.T21_L2

open SAP.P005b SAP.P005b.Bridge
open SAP.P005b.WH.W1.P.T21_L2
open scoped BigOperators Matrix

theorem SAP.P005b.WH.W1.T21_L2_proof : SAP.P005b.WH.W1.T21_L2 := by
  intro n d m P hn hm hmn hP S hS hinv a t b hfit
  have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hc : (control S).card = n-m := by
    rw [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp [hs]
  have htNonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcNonempty : (control S).Nonempty := Finset.card_pos.mp (by omega)
  have hprojT : ∀ i ∈ S, dot (P.x i) b = -(a+t) := by
    intro i hi
    have h := hfit i
    simp [wholeW1Fit, indicator, hi] at h
    linarith
  have hprojC : ∀ i ∈ control S, dot (P.x i) b = -a := by
    intro i hi
    have hnot : i ∉ S := by simpa [control] using hi
    have h := hfit i
    simp [wholeW1Fit, indicator, hnot] at h
    linarith
  have hNT := armN_zero_of_const_projection P S htNonempty b (-(a+t)) hprojT
  have hNC := armN_zero_of_const_projection P (control S) hcNonempty b (-a) hprojC
  have hLT : armL P S *ᵥ b = 0 := by
    rw [← armN_projection P S b]
    exact hNT
  have hLC : armL P (control S) *ᵥ b = 0 := by
    rw [← armN_projection P (control S) b]
    exact hNC
  have hL := Lhat_eq_weighted_armL P hm hmn S hS hP.2
  have hLb : Lhat P m S *ᵥ b = 0 := by
    rw [hL, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hLT, hLC]
    simp
  have hunitDet : IsUnit (Lhat P m S).det := isUnit_iff_ne_zero.mpr hinv
  have hunit : IsUnit (Lhat P m S) := (Lhat P m S).isUnit_iff_isUnit_det.mpr hunitDet
  have hinj : Function.Injective (fun v : Fin d → ℝ => Lhat P m S *ᵥ v) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hb : b = 0 := by
    apply hinj
    simpa using hLb
  have hmeanT : a+t+dot (xMean P S) b = 0 := by
    have hz := mean_zero_of_zero_on S (wholeW1Fit P S a t b) (fun i hi => hfit i)
    have hcongr : mean S (wholeW1Fit P S a t b) =
        mean S (fun i => (a+t)+dot (P.x i) b) := by
      apply mean_congr
      intro i hi
      simp [wholeW1Fit, indicator, hi]
    rw [hcongr, mean_fit_arm P S htNonempty (a+t) b] at hz
    linarith
  have hmeanC : a+dot (xMean P (control S)) b = 0 := by
    have hz := mean_zero_of_zero_on (control S) (wholeW1Fit P S a t b)
      (fun i hi => hfit i)
    have hcongr : mean (control S) (wholeW1Fit P S a t b) =
        mean (control S) (fun i => a+dot (P.x i) b) := by
      apply mean_congr
      intro i hi
      have hnot : i ∉ S := by simpa [control] using hi
      simp [wholeW1Fit, indicator, hnot]
    rw [hcongr, mean_fit_arm P (control S) hcNonempty a b] at hz
    linarith
  rw [hb] at hmeanT hmeanC
  simp [dot] at hmeanT hmeanC
  refine ⟨?_, ?_, hb⟩ <;> linarith
