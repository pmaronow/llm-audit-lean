import AronowAudit.P002.Wave1.Theorem2.Studentization

/-! The residual-mixture finite-population CLT. -/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def T2C_D_total {n} (P : Population n) : ℝ :=
  popVar (w P true (late P)) + popVar (w P false (late P))


def T2C_D_mix {n} (P : Population n) (i : Fin n) : ℝ :=
  (1-fraction P)*w P true (late P) i + fraction P*w P false (late P) i

lemma T2C_D_sizes {n} (P : Population n) (hP : ValidDesign P) :
    0 < (n : ℝ) ∧ 0 < (P.n1 : ℝ) ∧ 0 < controlSize P ∧
      0 < fraction P ∧ fraction P < 1 := by
  have hm : (0 : ℝ) < P.n1 := by exact_mod_cast hP.2.1
  have hmn : (P.n1 : ℝ) < n := by exact_mod_cast hP.2.2
  have hn := hm.trans hmn
  exact ⟨hn,hm,sub_pos.mpr hmn,div_pos hm hn,(div_lt_one hn).mpr hmn⟩

lemma T2C_D_fourth {n} (P : Population n) (δ r A : ℝ) (hP : Theta P δ r A)
    (a : Bool) :
    ∑ i, v P a (late P) i^4 ≤ A^4*n*(popVar (w P a (late P)))^2 := by
  have hn : (0 : ℝ) < n := (T2C_D_sizes P hP.1).1
  have hv := T2C_U_popVar_nonneg hP.1.1 (w P a (late P))
  have hf := hP.2.2.2.2.2.2 a
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hf 4
  have hmean4 : 0 ≤ mean (fun i => v P a (late P) i^4) := by
    exact div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) hn.le
  have hroot : (fourthNorm (v P a (late P)))^4 = mean (fun i => v P a (late P) i^4) := by
    unfold fourthNorm
    calc
      _ = ((Real.sqrt (Real.sqrt (mean (fun i => v P a (late P) i^4))))^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hmean4]
  change (fourthNorm (v P a (late P)))^4 ≤ (A*Real.sqrt (popVar (w P a (late P))))^4 at hp
  rw [hroot, mul_pow, show (Real.sqrt (popVar (w P a (late P))))^4 =
      ((Real.sqrt (popVar (w P a (late P))))^2)^2 by ring, Real.sq_sqrt hv] at hp
  nlinarith only [(div_le_iff₀ hn).mp hp]


lemma T2C_D_mix_center {n} (P : Population n) :
    ∀ i, T2C_D_mix P i - mean (T2C_D_mix P) =
      (1-fraction P)*v P true (late P) i + fraction P*v P false (late P) i := by
  intro i
  simp only [T2C_D_mix, mean, Finset.sum_add_distrib, ← Finset.mul_sum, v]
  ring

lemma T2C_D_mix_tau {n} (P : Population n) (hP : ValidDesign P)
    (hm : MonotoneReceipt P) (hc : (compliers P).Nonempty)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    rawTau P (T2C_D_mix P) S = tau P (late P) S := by
  have hn := (T2C_D_sizes P hP).1.ne'
  have hmt := (T2C_D_sizes P hP).2.1.ne'
  have hct := (T2C_D_sizes P hP).2.2.1.ne'
  have hcard := (Finset.mem_powersetCard.mp hS).2
  have hccard : (Sᶜ.card : ℝ) = controlSize P := by
    rw [Finset.card_compl, Fintype.card_fin, hcard, Nat.cast_sub hP.2.2.le]
    rfl
  have he := mean_w_equal_at_late P hm hc
  have hes : ∑ i, w P true (late P) i = ∑ i, w P false (late P) i := by
    exact (div_left_inj' hn).mp he
  have hsplit := Finset.sum_add_sum_compl S (w P false (late P))
  have hcomp : (∑ i ∈ Sᶜ, w P false (late P) i) =
      (∑ i, w P false (late P) i) - ∑ i ∈ S, w P false (late P) i := by linarith
  rw [NDS_tau_as_contrast P hP (late P) S hS, rawTau_sum]
  simp only [T2C_D_mix, Finset.sum_add_distrib, ← Finset.mul_sum, groupMean,
    hcard, hccard, hes, hcomp]
  dsimp [fraction, controlSize] at *
  field_simp [hn,hmt,hct]
  <;> ring

lemma T2C_D_mix_variance {n} (P : Population n) (hP : ValidDesign P)
    (hm : MonotoneReceipt P) (hc : (compliers P).Nonempty) :
    designVariance P (tau P (late P)) =
      fraction P*(1-fraction P)/(n : ℝ)*popVar (T2C_D_mix P) := by
  calc
    _ = designVariance P (rawTau P (T2C_D_mix P)) :=
      NDS_variance_congr P (fun S hS => (T2C_D_mix_tau P hP hm hc S hS).symm)
    _ = _ := by
      rw [T2C_U_rawTau_variance P hP]
      have hm := (T2C_D_sizes P hP).2.1.ne'
      have hn := (T2C_D_sizes P hP).1.ne'
      dsimp [fraction]
      field_simp
      <;> ring

lemma T2C_D_mix_lower {n} (P : Population n) (δ r A : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A) (hP : Theta P δ r A) :
    ((1-max δ 0)*r^2)*T2C_D_total P ≤ popVar (T2C_D_mix P) := by
  have hs := T2C_D_sizes P hP.1
  have hp : r ≤ fraction P := (le_div_iff₀ hs.1).mpr hP.2.2.2.1
  have hpc : r ≤ 1-fraction P := by
    have h := (div_le_iff₀ hs.1).mpr hP.2.2.2.2.1
    change fraction P ≤ 1-r at h
    linarith
  have hfac : 0 < fraction P*(1-fraction P)/(n : ℝ) := by
    exact div_pos (mul_pos hs.2.2.2.1 (sub_pos.mpr hs.2.2.2.2)) hs.1
  have hb := corrected_lemma5_proof P δ r A hδ hr hA hP
  rw [T2C_D_mix_variance P hP.1 hP.2.1 hP.2.2.1] at hb
  have he : (1-max δ 0) * (controlSize P/((n : ℝ)*(P.n1 : ℝ))*S2 P (late P) true +
      (P.n1 : ℝ)/((n : ℝ)*controlSize P)*S2 P (late P) false) =
      (fraction P*(1-fraction P)/(n : ℝ))*((1-max δ 0)*
        ((1-fraction P)^2*popVar (w P true (late P)) +
          (fraction P)^2*popVar (w P false (late P)))) := by
    dsimp [S2,fraction,controlSize]
    have hn := hs.1.ne'
    have hm := hs.2.1.ne'
    have hc := hs.2.2.1.ne'
    dsimp [controlSize] at hc
    field_simp
    <;> ring
  rw [he] at hb
  have hb := (mul_le_mul_iff_right₀ hfac).mp hb
  have hd : 0 ≤ 1-max δ 0 := by exact sub_nonneg.mpr (max_le hδ.le (by norm_num))
  have hv1 := T2C_U_popVar_nonneg hP.1.1 (w P true (late P))
  have hv0 := T2C_U_popVar_nonneg hP.1.1 (w P false (late P))
  have h1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1.le hpc 2) hv1
  have h0 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1.le hp 2) hv0
  apply le_trans _ hb
  have h := mul_le_mul_of_nonneg_left (add_le_add h1 h0) hd
  simpa only [T2C_D_total, mul_add, mul_assoc] using h

lemma T2C_D_mix_fourth {n} (P : Population n) (δ r A : ℝ)
    (hP : Theta P δ r A) :
    ∑ i, (T2C_D_mix P i-mean (T2C_D_mix P))^4 ≤ 8*A^4*n*(T2C_D_total P)^2 := by
  have hs := T2C_D_sizes P hP.1
  have hp4 : (fraction P)^4 ≤ 1 := by
    simpa using pow_le_pow_left₀ hs.2.2.2.1.le hs.2.2.2.2.le 4
  have hc4 : (1-fraction P)^4 ≤ 1 := by
    have hc : 0 ≤ 1-fraction P := by linarith [hs.2.2.2.2]
    simpa using pow_le_pow_left₀ hc (show 1-fraction P ≤ 1 by linarith [hs.2.2.2.1]) 4
  have hpoint (i) : (T2C_D_mix P i-mean (T2C_D_mix P))^4 ≤
      8*(v P true (late P) i^4+v P false (late P) i^4) := by
    rw [T2C_D_mix_center]
    have hf (a b : ℝ) : (a+b)^4 ≤ 8*a^4+8*b^4 := by
      nlinarith [sq_nonneg (a^2-b^2),sq_nonneg ((a-b)^2)]
    have h := hf ((1-fraction P)*v P true (late P) i) (fraction P*v P false (late P) i)
    simp only [mul_pow] at h
    have h1 := mul_le_mul_of_nonneg_right hc4 (show 0 ≤ v P true (late P) i^4 by positivity)
    have h0 := mul_le_mul_of_nonneg_right hp4 (show 0 ≤ v P false (late P) i^4 by positivity)
    nlinarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  have hv1 := T2C_U_popVar_nonneg hP.1.1 (w P true (late P))
  have hv0 := T2C_U_popVar_nonneg hP.1.1 (w P false (late P))
  have hf1 := T2C_D_fourth P δ r A hP true
  have hf0 := T2C_D_fourth P δ r A hP false
  have hvar : (popVar (w P true (late P)))^2 + (popVar (w P false (late P)))^2 ≤
      (T2C_D_total P)^2 := by dsimp [T2C_D_total]; nlinarith
  have hmul := mul_le_mul_of_nonneg_left hvar (show 0 ≤ 8*A^4*n by positivity)
  nlinarith


lemma T2C_D_mix_CLT (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (δ r A : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A)
    (hP : ∀ j, Theta (P j) δ r A) (hT : ∀ j, 0 < T2C_D_total (P j)) :
    (∀ j, 0 < popVar (T2C_D_mix (P j))) ∧
    ∀ t : ℝ, 0 ≤ t → Tendsto (fun j => probability (P j) (fun S =>
      |rawTau (P j) (T2C_D_mix (P j)) S /
        Real.sqrt (designVariance (P j) (rawTau (P j) (T2C_D_mix (P j))))| ≤ t))
      atTop (nhds (SH_absNormalCDF t)) := by
  let C := (1-max δ 0)*r^2
  have hC : 0 < C := mul_pos (sub_pos.mpr (max_lt hδ (by norm_num))) (sq_pos_of_pos hr.1)
  have hlo (j) : C*T2C_D_total (P j) ≤ popVar (T2C_D_mix (P j)) :=
    T2C_D_mix_lower (P j) δ r A hδ hr hA (hP j)
  have hv (j) : 0 < popVar (T2C_D_mix (P j)) := (mul_pos hC (hT j)).trans_le (hlo j)
  have hfour (j) : ∑ i, (T2C_D_mix (P j) i-mean (T2C_D_mix (P j)))^4 ≤
      (8*A^4/C^2)*sizes j*(popVar (T2C_D_mix (P j)))^2 := by
    have hh := pow_le_pow_left₀ (mul_pos hC (hT j)).le (hlo j) 2
    have hdiv : (T2C_D_total (P j))^2 ≤ (popVar (T2C_D_mix (P j)))^2/C^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hC)).mpr
      nlinarith only [hh]
    apply (T2C_D_mix_fourth (P j) δ r A (hP j)).trans
    have hm := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ 8*A^4*sizes j by positivity)
    convert hm using 1 <;> ring
  refine ⟨hv,fun t ht => ?_⟩
  apply T2C_U_abs_cdf sizes P _ _ t ht
  exact T2C_U_rawCLT sizes hsizes P (fun j => T2C_D_mix (P j)) (fun j => (hP j).1)
    hv r (8*A^4/C^2) hr.1 (by positivity) (fun j => (hP j).2.2.2.1)
    (fun j => (hP j).2.2.2.2.1) hfour

end
end AronowAudit.P002.Wave1
