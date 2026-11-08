import SAP.P002a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2.P.T2_L1

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

private lemma w_difference_compliers {n} (P : Population n) (hm : MonotoneReceipt P)
    (β : ℝ) (i : Fin n) :
    w P true β i-w P false β i =
      if i ∈ compliers P then P.y i true-P.y i false-β else 0 := by
  cases h0 : P.d i false <;> cases h1 : P.d i true
  · simp [w, binary, compliers, h0, h1]
  · simp [w, binary, compliers, h0, h1]
    ring
  · have hh := hm i h0
    simp [h1] at hh
  · simp [w, binary, compliers, h0, h1]

private lemma sum_w_difference {n} (P : Population n) (hm : MonotoneReceipt P)
    (hc : (compliers P).Nonempty) (β : ℝ) :
    (∑ i : Fin n, (w P true β i-w P false β i)) =
      ((compliers P).card : ℝ)*(late P-β) := by
  have hcard : ((compliers P).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hc)
  have hrestrict : (∑ i : Fin n, (w P true β i-w P false β i)) =
      ∑ i ∈ compliers P, (w P true β i-w P false β i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hin
    rw [w_difference_compliers P hm β i, if_neg hin]
  rw [hrestrict]
  simp_rw [w_difference_compliers P hm β]
  have hs : (∑ i ∈ compliers P,
      if i ∈ compliers P then P.y i true-P.y i false-β else 0) =
      (∑ i ∈ compliers P, (P.y i true-P.y i false))-
        ((compliers P).card : ℝ)*β := by
    simp [Finset.sum_sub_distrib]
  rw [hs]
  unfold late groupMean
  field_simp [hcard]
  <;> ring

private lemma mean_w_equal_at_late {n} (P : Population n) (hm : MonotoneReceipt P)
    (hc : (compliers P).Nonempty) :
    mean (w P true (late P)) = mean (w P false (late P)) := by
  have h := sum_w_difference P hm hc (late P)
  simp only [sub_self, mul_zero, Finset.sum_sub_distrib, sub_eq_zero] at h
  simp only [mean, h]

private lemma group_means {n} (P : Population n) (hm : MonotoneReceipt P)
    (hc : (compliers P).Nonempty) :
    groupMean (compliers P) (w P true (late P)) =
      groupMean (compliers P) (w P false (late P)) := by
  have hs : (∑ i ∈ compliers P, (w P true (late P) i-w P false (late P) i)) =
      ∑ i : Fin n, (w P true (late P) i-w P false (late P) i) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hin
    rw [w_difference_compliers P hm, if_neg hin]
  have hz := sum_w_difference P hm hc (late P)
  rw [← hs] at hz
  simp only [sub_self, mul_zero, Finset.sum_sub_distrib, sub_eq_zero] at hz
  simp only [groupMean, hz]

private lemma group_identity {n} (S : Finset (Fin n)) (u v : Fin n → ℝ)
    (htwo : 2 ≤ S.card) (hmean : groupMean S u = groupMean S v) :
    (∑ i ∈ S, (u i-v i)^2) = ((S.card : ℝ)-1)*
      (groupVar S u+groupVar S v-2*groupCov S u v) := by
  have hden : (S.card : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ S.card := by exact_mod_cast htwo
    linarith
  have hpoint (i : Fin n) : (u i-v i)^2 =
      (u i-groupMean S u)^2+(v i-groupMean S v)^2-
        2*((u i-groupMean S u)*(v i-groupMean S v)) := by
    rw [hmean]
    ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    groupVar, groupCov, if_pos htwo, ← pow_two]
  field_simp [hden]
  <;> ring

private lemma group_variance_second_moment {n} (S : Finset (Fin n)) (q : Fin n → ℝ)
    (c : ℝ) (htwo : 2 ≤ S.card) :
    groupVar S q ≤ (∑ i ∈ S, (q i-c)^2)/((S.card : ℝ)-1) := by
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hden : 0 ≤ (S.card : ℝ)-1 := by
    have h : (1 : ℝ) ≤ S.card := by exact_mod_cast (show 1 ≤ S.card by omega)
    linarith
  have hm : groupMean S (fun i => (q i-groupMean S q)^2) ≤
      groupMean S (fun i => (q i-c)^2) := by
    have hmA : AronowAudit.P002.groupMean S
        (fun i => (q i-AronowAudit.P002.groupMean S q)^2) ≤
        AronowAudit.P002.groupMean S (fun i => (q i-c)^2) := by
      rw [AronowAudit.P002.square_centering S q c hSne]
      exact sub_le_self _ (sq_nonneg _)
    simpa only [AronowAudit.P002.groupMean, groupMean] using hmA
  have hs : (∑ i ∈ S, (q i-groupMean S q)^2) ≤ ∑ i ∈ S, (q i-c)^2 :=
    (div_le_div_iff_of_pos_right hcard).mp hm
  simp only [groupVar, groupCov, if_pos htwo]
  have hp : (∑ i ∈ S, (q i-groupMean S q)*(q i-groupMean S q)) =
      ∑ i ∈ S, (q i-groupMean S q)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hp]
  exact div_le_div_of_nonneg_right hs hden

lemma groupVar_nonneg {n} (S : Finset (Fin n)) (q : Fin n → ℝ) :
    0 ≤ groupVar S q := by
  unfold groupVar groupCov
  split_ifs with hS
  · apply div_nonneg
    · exact Finset.sum_nonneg fun i hi => mul_self_nonneg _
    · have hh : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
      linarith
  · exact le_rfl

private lemma difference_algebra (c t A B δ : ℝ)
    (hc : 0 < c) (ht : 0 < t) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) :
    A+B+2*δ*Real.sqrt A*Real.sqrt B ≤
      (1+δ*c/t)*A + (1+δ*t/c)*B := by
  have h := AronowAudit.P002.corrected_variance_algebra c t (Real.sqrt A) (Real.sqrt B)
      (-δ*Real.sqrt A*Real.sqrt B) δ hc ht (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) le_rfl
  rw [max_eq_left hδ] at h
  rw [Real.sq_sqrt hA, Real.sq_sqrt hB] at h
  have hh := mul_nonneg (le_of_lt (add_pos hc ht)) (sub_nonneg.mpr h)
  have he : (c+t) *
      (A/t+B/c-(A+B-2*(-δ*Real.sqrt A*Real.sqrt B))/(c+t) -
        (1-δ)*(c/((c+t)*t)*A+t/((c+t)*c)*B)) =
      (1+δ*c/t)*A+(1+δ*t/c)*B-(A+B-2*(-δ*Real.sqrt A*Real.sqrt B)) := by
    field_simp [hc.ne', ht.ne', (add_pos hc ht).ne']
    <;> ring_nf
  rw [he] at hh
  nlinarith [hh]

end
end SAP.P002a.WH.W2.P.T2_L1

open SAP.P002a
open scoped BigOperators Classical

theorem SAP.P002a.WH.W2.T2_L1_proof : SAP.P002a.WH.W2.T2_L1 := by
  change W2T2GroupChain
  intro n P δ r A hδ hr hA hP htwo
  dsimp only
  obtain ⟨hvalid, hm, hc, hr0, hr1, hcov, hfour⟩ := hP
  let C := compliers P
  let u := w P true (late P)
  let u0 := w P false (late P)
  let V1 := groupVar C u
  let V0 := groupVar C u0
  let C10 := groupCov C u u0
  let d := (C.card : ℝ)-1
  let b1 := 1+max δ 0*controlSize P/(P.n1 : ℝ)
  let b0 := 1+max δ 0*(P.n1 : ℝ)/controlSize P
  have hd : 0 < d := by
    dsimp [d, C]
    have hh : (2 : ℝ) ≤ (compliers P).card := by exact_mod_cast htwo
    linarith
  have hcontrol : 0 < controlSize P := by
    have hn1 : P.n1 < n := hvalid.2.2
    unfold controlSize
    exact sub_pos.mpr (by exact_mod_cast hn1)
  have htreat : 0 < (P.n1 : ℝ) := by exact_mod_cast hvalid.2.1
  have hmean : groupMean C u = groupMean C u0 := by
    dsimp [C, u, u0]
    exact SAP.P002a.WH.W2.P.T2_L1.group_means P hm hc
  have hmeanPop : mean u = mean u0 := by
    dsimp [u, u0]
    exact SAP.P002a.WH.W2.P.T2_L1.mean_w_equal_at_late P hm hc
  have hvdiff (i : Fin n) : v P true (late P) i-v P false (late P) i = u i-u0 i := by
    dsimp [u, u0, v]
    rw [hmeanPop]
    ring
  have hidentity :
      (∑ i ∈ C, (v P true (late P) i-v P false (late P) i)^2)/d =
        V1+V0-2*C10 := by
    have hres : (∑ i ∈ C, (v P true (late P) i-v P false (late P) i)^2) =
        ∑ i ∈ C, (u i-u0 i)^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hvdiff]
    rw [hres, SAP.P002a.WH.W2.P.T2_L1.group_identity C u u0 htwo hmean]
    dsimp [d, V1, V0, C10]
    exact mul_div_cancel_left₀ _ hd.ne'
  have hcovU : -δ*Real.sqrt V1*Real.sqrt V0 ≤ C10 := by
    dsimp [V1, V0, C10, C, u, u0]
    exact hcov
  have hsqrt : 0 ≤ Real.sqrt V1*Real.sqrt V0 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hdelta : δ ≤ max δ 0 := le_max_left _ _
  have hcovRelax : -max δ 0*Real.sqrt V1*Real.sqrt V0 ≤ C10 := by
    have hm := mul_le_mul_of_nonneg_right hdelta hsqrt
    nlinarith [hcovU]
  have hineq2 : V1+V0-2*C10 ≤ V1+V0+2*max δ 0*Real.sqrt V1*Real.sqrt V0 := by
    linarith
  have hineq3 : V1+V0+2*max δ 0*Real.sqrt V1*Real.sqrt V0 ≤ b1*V1+b0*V0 := by
    have hb := SAP.P002a.WH.W2.P.T2_L1.difference_algebra (controlSize P) (P.n1 : ℝ)
      V1 V0 (max δ 0) hcontrol htreat
      (SAP.P002a.WH.W2.P.T2_L1.groupVar_nonneg C u)
      (SAP.P002a.WH.W2.P.T2_L1.groupVar_nonneg C u0)
      (le_max_right _ _)
    simpa only [b1, b0] using hb
  have hcoef1 : 0 ≤ b1 := by dsimp [b1]; positivity
  have hcoef0 : 0 ≤ b0 := by dsimp [b0]; positivity
  have hproj1 : V1 ≤ (∑ i ∈ C, (u i-mean u)^2)/d := by
    dsimp [V1, d]
    exact SAP.P002a.WH.W2.P.T2_L1.group_variance_second_moment C u (mean u) htwo
  have hproj0 : V0 ≤ (∑ i ∈ C, (u0 i-mean u0)^2)/d := by
    dsimp [V0, d]
    exact SAP.P002a.WH.W2.P.T2_L1.group_variance_second_moment C u0 (mean u0) htwo
  have hv1 (i : Fin n) : v P true (late P) i = u i-mean u := by rfl
  have hv0 (i : Fin n) : v P false (late P) i = u0 i-mean u0 := by rfl
  have hsum1 : (∑ i ∈ C, (u i-mean u)^2) = ∑ i ∈ C, (v P true (late P) i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hv1]
  have hsum0 : (∑ i ∈ C, (u0 i-mean u0)^2) = ∑ i ∈ C, (v P false (late P) i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hv0]
  have hproj : b1*V1+b0*V0 ≤
      (b1*(∑ i ∈ C, (v P true (late P) i)^2)+
       b0*(∑ i ∈ C, (v P false (late P) i)^2))/d := by
    calc
      _ ≤ b1*((∑ i ∈ C, (u i-mean u)^2)/d) +
          b0*((∑ i ∈ C, (u0 i-mean u0)^2)/d) :=
        add_le_add (mul_le_mul_of_nonneg_left hproj1 hcoef1)
          (mul_le_mul_of_nonneg_left hproj0 hcoef0)
      _ = _ := by rw [hsum1, hsum0]; field_simp [hd.ne'] <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hidentity
  · rw [hidentity]
    exact hineq2
  · exact hineq3
  · exact hproj
