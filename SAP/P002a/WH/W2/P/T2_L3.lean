import SAP.P002a.WH.W2.Leaves
import AronowAudit.P002.Wave1.Theorem2.Observed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W2.P.T2_L3

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
open SAP.P002a.Bridge
attribute [local instance] Classical.propDecidable

lemma weighted_sqrt_bound (x y n1 c0 d : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hn1 : 0 < n1) (hc0 : 0 < c0)
    (hd : 0 ≤ d) :
    2*d*Real.sqrt x*Real.sqrt y ≤ d*c0/n1*x + d*n1/c0*y := by
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hsy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hsq : 2*n1*c0*Real.sqrt x*Real.sqrt y ≤ c0^2*x+n1^2*y := by
    nlinarith [sq_nonneg (c0*Real.sqrt x-n1*Real.sqrt y)]
  have hsq' := mul_le_mul_of_nonneg_left hsq hd
  have hdiv :
      2*d*Real.sqrt x*Real.sqrt y ≤
        d*(c0^2*x+n1^2*y)/(n1*c0) := by
    apply (le_div_iff₀ (mul_pos hn1 hc0)).2
    nlinarith [hsq']
  calc
    2*d*Real.sqrt x*Real.sqrt y ≤ d*(c0^2*x+n1^2*y)/(n1*c0) := hdiv
    _ = d*c0/n1*x + d*n1/c0*y := by
      field_simp

end

end SAP.P002a.WH.W2.P.T2_L3

theorem SAP.P002a.WH.W2.T2_L3_proof : SAP.P002a.WH.W2.T2_L3 := by
  unfold SAP.P002a.WH.W2.T2_L3 SAP.P002a.W2T2Residual
  intro n k P δ e A B r hk hδ he hA hB hr hXi
  let q1 : Fin n → ℝ := residual P true (late P.pop)
  let q0 : Fin n → ℝ := residual P false (late P.pop)
  have hvalid : ValidDesign P.pop := hXi.1
  have hn2 : 2 ≤ n := hvalid.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 0 < (P.pop.n1 : ℝ) := by exact_mod_cast hvalid.2.1
  have hc0 : 0 < controlSize P.pop := by
    unfold controlSize
    have hlt : (P.pop.n1 : ℝ) < (n : ℝ) := by exact_mod_cast hvalid.2.2
    linarith
  have hnminus : 0 < (n : ℝ)-1 := by
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hXi' : AronowAudit.P002.Xi (SAP.P002a.Bridge.toCovPopulation P) δ e A B r := by
    rw [← SAP.P002a.Bridge.xi_eq P δ e A B r]
    exact hXi
  have hm1 : mean q1 = 0 := by
    dsimp [q1]
    rw [SAP.P002a.Bridge.residual_eq P, SAP.P002a.Bridge.late_eq P.pop]
    exact AronowAudit.P002.Wave1.T2C_residual_centered (SAP.P002a.Bridge.toCovPopulation P).x _
      (AronowAudit.P002.Wave1.T2C_Xi_residual_score (SAP.P002a.Bridge.toCovPopulation P)
        δ e A B r he hXi' true)
  have hm0 : mean q0 = 0 := by
    dsimp [q0]
    rw [SAP.P002a.Bridge.residual_eq P, SAP.P002a.Bridge.late_eq P.pop]
    exact AronowAudit.P002.Wave1.T2C_residual_centered (SAP.P002a.Bridge.toCovPopulation P).x _
      (AronowAudit.P002.Wave1.T2C_Xi_residual_score (SAP.P002a.Bridge.toCovPopulation P)
        δ e A B r he hXi' false)
  have hv1 : 0 ≤ popVar q1 := by
    unfold popVar
    apply div_nonneg
    · exact Finset.sum_nonneg fun i _ => sq_nonneg _
    · linarith
  have hv0 : 0 ≤ popVar q0 := by
    unfold popVar
    apply div_nonneg
    · exact Finset.sum_nonneg fun i _ => sq_nonneg _
    · linarith
  have hsum1 : (∑ i, q1 i^2) = ((n : ℝ)-1)*popVar q1 := by
    unfold popVar
    simp only [hm1, sub_zero]
    field_simp [ne_of_gt hnminus]
  have hsum0 : (∑ i, q0 i^2) = ((n : ℝ)-1)*popVar q0 := by
    unfold popVar
    simp only [hm0, sub_zero]
    field_simp [ne_of_gt hnminus]
  have hcovsum : (∑ i, q1 i*q0 i) = ((n : ℝ)-1)*popCov q1 q0 := by
    unfold popCov
    simp only [hm1, hm0, sub_zero]
    field_simp [ne_of_gt hnminus]
  have hcontrast :
      (∑ i, (q1 i-q0 i)^2) =
        ((n : ℝ)-1)*(popVar q1+popVar q0-2*popCov q1 q0) := by
    calc
      (∑ i, (q1 i-q0 i)^2) =
          (∑ i, q1 i^2)+(∑ i, q0 i^2)-2*(∑ i, q1 i*q0 i) := by
        simp_rw [sub_sq]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        ring
      _ = ((n : ℝ)-1)*(popVar q1+popVar q0-2*popCov q1 q0) := by
        rw [hsum1, hsum0, hcovsum]
        ring
  have hcov := hXi.2.2.2.2.2.1
  have hd : 0 ≤ max δ 0 := le_max_right _ _
  have hδd : δ ≤ max δ 0 := le_max_left _ _
  have hrootprod : 0 ≤ Real.sqrt (popVar q1)*Real.sqrt (popVar q0) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcov' :
      -max δ 0*Real.sqrt (popVar q1)*Real.sqrt (popVar q0) ≤ popCov q1 q0 := by
    have := hcov
    have ht := mul_le_mul_of_nonneg_right hδd hrootprod
    linarith
  have hupper :
      (∑ i, (q1 i-q0 i)^2) ≤
        ((n : ℝ)-1)*(popVar q1+popVar q0+
          2*max δ 0*Real.sqrt (popVar q1)*Real.sqrt (popVar q0)) := by
    rw [hcontrast]
    have := mul_le_mul_of_nonneg_left
      (show popVar q1+popVar q0-2*popCov q1 q0 ≤
        popVar q1+popVar q0+2*max δ 0*Real.sqrt (popVar q1)*Real.sqrt (popVar q0) by
          nlinarith [hcov']) hnminus.le
    exact this
  have hweighted := SAP.P002a.WH.W2.P.T2_L3.weighted_sqrt_bound (popVar q1) (popVar q0)
    (P.pop.n1 : ℝ) (controlSize P.pop) (max δ 0) hv1 hv0 hn1 hc0 hd
  have hmiddle :
      popVar q1+popVar q0+
        2*max δ 0*Real.sqrt (popVar q1)*Real.sqrt (popVar q0) ≤
      W2b1 P.pop δ*popVar q1+W2b0 P.pop δ*popVar q0 := by
    dsimp [W2b1, W2b0]
    nlinarith [hweighted]
  have hscaled := mul_le_mul_of_nonneg_left hmiddle hnminus.le
  simpa [q1, q0] using (calc
    (∑ i, (q1 i-q0 i)^2) ≤
        ((n : ℝ)-1)*(W2b1 P.pop δ*popVar q1+W2b0 P.pop δ*popVar q0) :=
      hupper.trans hscaled
    _ = W2b1 P.pop δ*(∑ i, q1 i^2)+W2b0 P.pop δ*(∑ i, q0 i^2) := by
      rw [hsum1, hsum0]
      ring)
