import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.MeasureTheory.Measure.Real

/-! Assembly of the fixed-design probability estimate.  A useful simplification
is to prove `sigma2 > 2 * N` directly; this avoids dividing by the empirical
sum of squares. -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n15_proof : N15 := by
  classical
  intro h5 h7 h8 h9 h10 h11 h12 h13 h14
  intro t ht x hx
  have ht2 : 2 ≤ t := by omega
  have ht0 : 0 < t := by omega
  have htR : (25 : ℝ) ≤ t := by exact_mod_cast ht
  have htRpos : (0 : ℝ) < t := by positivity
  have hnpos : (0 : ℝ) < (t : ℝ) ^ 4 := by positivity
  have hcols : t ^ 3 + 1 ≤ t ^ 4 := by
    have hp : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ ht0
    calc
      t ^ 3 + 1 ≤ t ^ 3 + t ^ 3 := Nat.add_le_add_left hp _
      _ = 2 * t ^ 3 := by omega
      _ ≤ t * t ^ 3 := Nat.mul_le_mul_right _ ht2
      _ = t ^ 4 := by ring
  change (∀ i, 1 / ((t ^ 4 : ℕ) : ℝ) ≤ x i ∧ x i ≤ 1) ∧ Function.Injective x at hx
  rcases hx with ⟨hbox, hinj⟩
  let r : Polynomial ℝ := chebR t
  let P : Matrix (Fin (t ^ 4)) (Fin (t ^ 3 + 1)) ℝ := vand (t ^ 3) x
  let c : Fin (t ^ 3 + 1) → ℝ := fun k => r.coeff (k : ℕ)
  let w : Fin (t ^ 3 + 1) → ℝ := regionMoments (t ^ 3) r
  let N : ℝ := regionInt r r
  let sigma2 : ℝ := w ⬝ᵥ ((P.transpose * P)⁻¹).mulVec w
  let E : ℝ := ∑ i : Fin (t ^ 4), (P.mulVec c i) ^ 2
  rcases h12 h10 h11 t ht2 with ⟨hdegree, hsup, hnorm⟩
  have hdegree_r : r.natDegree ≤ t ^ 3 := hdegree
  have hc : coeffPoly c = r := by
    change (∑ k : Fin (t ^ 3 + 1), C (r.coeff (k : ℕ)) * X ^ (k : ℕ)) = r
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => C (r.coeff k) * X ^ k) (t ^ 3 + 1)]
    exact (r.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hdegree_r)).symm
  have hP : IsUnit (P.transpose * P).det := h5 (t ^ 4) (t ^ 3) x hcols hinj
  have hNdot : c ⬝ᵥ w = N := by
    rw [← h8.1 (t ^ 3) c r, hc]
  have hE0 : 0 ≤ E := Finset.sum_nonneg (fun i _ => sq_nonneg (P.mulVec c i))
  have hEbound : E ≤ (t : ℝ) ^ 4 := by
    calc
      E ≤ ∑ i : Fin (t ^ 4), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have heval : P.mulVec c i = r.eval (x i) := by
          rw [h8.2 (t ^ 3) (t ^ 4) x c i, hc]
        rw [heval]
        have hi : x i ∈ Set.Icc (1 / ((t : ℝ) ^ 4)) 1 := by
          exact ⟨by simpa only [Nat.cast_pow] using (hbox i).1, (hbox i).2⟩
        have hsmall : |r.eval (x i)| ≤ 1 := hsup (x i) hi
        have hsq : |r.eval (x i)| ^ 2 ≤ (1 : ℝ) ^ 2 := by gcongr
        simpa only [sq_abs, one_pow] using hsq
      _ = (t : ℝ) ^ 4 := by simp
  have ht4 : (390625 : ℝ) ≤ (t : ℝ) ^ 4 := by
    calc
      (390625 : ℝ) = (25 : ℝ) ^ 4 := by norm_num
      _ ≤ (t : ℝ) ^ 4 := by gcongr
  have hnum : (3276800 : ℝ) < 9 * (t : ℝ) ^ 4 := by linarith
  have hlower : 2 * (t : ℝ) ^ 4 < 9 * (t : ℝ) ^ 8 / 1638400 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 1638400)).2
    have hm := mul_pos hnpos (sub_pos.2 hnum)
    nlinarith [show (t : ℝ) ^ 8 = ((t : ℝ) ^ 4) ^ 2 by ring]
  have hNlarge : 2 * (t : ℝ) ^ 4 < N := hlower.trans_le hnorm
  have hNpos : 0 < N := by linarith
  have hCS : N ^ 2 ≤ E * sigma2 := by
    have h := h9 (t ^ 4) (t ^ 3 + 1) P hP c w
    change (c ⬝ᵥ w) ^ 2 ≤ E * sigma2 at h
    rwa [hNdot] at h
  have hsigma : 0 < sigma2 := by
    by_contra! hnonpos
    have hm := mul_nonpos_of_nonneg_of_nonpos hE0 hnonpos
    have hNsq : 0 < N ^ 2 := pow_pos hNpos 2
    linarith
  have hCSn : N ^ 2 ≤ (t : ℝ) ^ 4 * sigma2 :=
    hCS.trans (mul_le_mul_of_nonneg_right hEbound hsigma.le)
  have hsigma_large : 2 * N < sigma2 := by
    have hm := mul_pos hNpos (sub_pos.2 hNlarge)
    by_contra! hle
    have hm' := mul_le_mul_of_nonneg_left hle hnpos.le
    nlinarith
  let L : (Fin (t ^ 4) → ℝ) → ℝ := fun y => olsCoef P y ⬝ᵥ w
  have hLmeas : Measurable L := by
    dsimp [L, olsCoef]
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hAmeas : MeasurableSet {z : ℝ | sigma2 / 2 < z ^ 2} :=
    measurableSet_lt measurable_const (measurable_id.pow_const 2)
  have hcoe : ((sigma2.toNNReal : ℝ≥0) : ℝ) = sigma2 := Real.coe_toNNReal sigma2 hsigma.le
  have htail : (1 : ℝ) / 12 ≤
      ((gaussVec (t ^ 4)) {y | sigma2 / 2 < L y ^ 2}).toReal := by
    have hv : 0 < sigma2.toNNReal := Real.toNNReal_pos.2 hsigma
    have hb := h14 sigma2.toNNReal hv
    have hb' : (1 : ℝ) / 12 ≤
        ((gaussianReal 0 sigma2.toNNReal) {z : ℝ | sigma2 / 2 < z ^ 2}).toReal := by
      simpa only [hcoe] using hb
    have hlaw := h13 (t ^ 4) (t ^ 3 + 1) P hP w
    change (gaussVec (t ^ 4)).map L = gaussianReal 0 sigma2.toNNReal at hlaw
    rw [← hlaw, Measure.map_apply hLmeas hAmeas] at hb'
    exact hb'
  have hsubset : {y : Fin (t ^ 4) → ℝ | sigma2 / 2 < L y ^ 2} ⊆
      {y | 1 < regionInt (olsPoly (t ^ 3) x y) (olsPoly (t ^ 3) x y)} := by
    intro y hy
    have hlinear : regionInt (olsPoly (t ^ 3) x y) r = L y :=
      h8.1 (t ^ 3) (olsCoef P y) r
    have hregional := h7 (olsPoly (t ^ 3) x y) r hNpos
    rw [hlinear] at hregional
    change L y ^ 2 / N ≤ regionInt (olsPoly (t ^ 3) x y) (olsPoly (t ^ 3) x y)
      at hregional
    have hy' : sigma2 / 2 < L y ^ 2 := hy
    have hfrac : 1 < L y ^ 2 / N := by
      apply (lt_div_iff₀ hNpos).2
      change 1 * N < L y ^ 2
      linarith [hsigma_large, hy']
    exact hfrac.trans_le hregional
  haveI : IsProbabilityMeasure (gaussVec (t ^ 4)) := by
    unfold gaussVec
    infer_instance
  exact htail.trans
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset))

end

end AronowAudit.P001.Wave1.SieveRate
