import SAP.P020.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P020.WH.W1.P.T14_L3

open scoped BigOperators
open SAP.P020 SAP.P020.Bridge AronowAudit.P020

noncomputable section

end
end SAP.P020.WH.W1.P.T14_L3

open SAP.P020.WH.W1 SAP.P020 SAP.P020.Bridge AronowAudit.P020

theorem SAP.P020.WH.W1.T14_L3_proof : SAP.P020.WH.W1.T14_L3 := by
  intro P hsize_ne
  have hsize_nonneg : 0 ≤ W1SizeVariance P := by
    exact clusterVariance_nonneg (W1Sizes P)
  have hsize : 0 < W1SizeVariance P :=
    lt_of_le_of_ne hsize_nonneg (Ne.symm hsize_ne)
  have hsne : W1SizeVariance P ≠ 0 := ne_of_gt hsize
  have hmc_nat : 0 < controlCount P := Nat.sub_pos_of_lt P.mt_lt
  have hM_nat : 0 < P.M := lt_trans P.mt_pos P.mt_lt
  have hmc : 0 < (controlCount P : ℝ) := by exact_mod_cast hmc_nat
  have hmt : 0 < (P.mt : ℝ) := by exact_mod_cast P.mt_pos
  have hMr : 0 < (P.M : ℝ) := by exact_mod_cast hM_nat
  have hmcne : (controlCount P : ℝ) ≠ 0 := ne_of_gt hmc
  have hmtne : (P.mt : ℝ) ≠ 0 := ne_of_gt hmt
  have hMne : (P.M : ℝ) ≠ 0 := ne_of_gt hMr
  have hcount : (controlCount P : ℝ) + (P.mt : ℝ) = (P.M : ℝ) := by
    simp [controlCount, Nat.cast_sub (le_of_lt P.mt_lt)]
  have hcplus : W1c P + 1 = (P.M : ℝ) / controlCount P := by
    unfold W1c
    field_simp [hmcne]
    <;> ring
  have htplus : W1t P + 1 = (P.M : ℝ) / P.mt := by
    unfold W1t
    field_simp [hmtne]
    <;> ring
  have hCeq : W1c P + W1t P + 2 =
      (P.M : ℝ) / controlCount P + (P.M : ℝ) / P.mt := by
    rw [← hcplus, ← htplus]
    ring
  have hC : 0 < W1c P + W1t P + 2 := by
    rw [hCeq]
    positivity
  have hfac0 : (W1c P + W1t P + 2) * ((P.mt : ℝ) / P.M) = W1c P + 1 := by
    rw [hCeq, hcplus]
    field_simp [hmcne, hmtne, hMne]
    nlinarith [hcount]
  have hfac1 : (W1c P + W1t P + 2) * ((controlCount P : ℝ) / P.M) = W1t P + 1 := by
    rw [hCeq, htplus]
    field_simp [hmcne, hmtne, hMne]
    nlinarith [hcount]
  have hcoef0 : armOptimalCoefficient P false =
      W1SizeCovariance P false / W1SizeVariance P := by
    rfl
  have hcoef1 : armOptimalCoefficient P true =
      W1SizeCovariance P true / W1SizeVariance P := by
    rfl
  have hq0 : W1SizeCovariance P false =
      W1SizeVariance P * armOptimalCoefficient P false := by
    rw [hcoef0]
    field_simp [hsne]
  have hq1 : W1SizeCovariance P true =
      W1SizeVariance P * armOptimalCoefficient P true := by
    rw [hcoef1]
    field_simp [hsne]
  have hweighted :
      (W1c P + 1) * armOptimalCoefficient P false +
        (W1t P + 1) * armOptimalCoefficient P true =
      (W1c P + W1t P + 2) *
        (((P.mt : ℝ) / P.M) * armOptimalCoefficient P false +
          ((controlCount P : ℝ) / P.M) * armOptimalCoefficient P true) := by
    calc
      _ = ((W1c P + W1t P + 2) * ((P.mt : ℝ) / P.M)) *
            armOptimalCoefficient P false +
          ((W1c P + W1t P + 2) * ((controlCount P : ℝ) / P.M)) *
            armOptimalCoefficient P true := by rw [hfac0, hfac1]
      _ = _ := by ring
  have hκ : optimalCoefficient P =
      (P.mt : ℝ) / P.M * armOptimalCoefficient P false +
        (controlCount P : ℝ) / P.M * armOptimalCoefficient P true := by
    rfl
  have hU :
      (W1c P + W1t P + 2) * W1SizeVariance P * optimalCoefficient P =
        (W1c P + 1) * W1SizeCovariance P false +
          (W1t P + 1) * W1SizeCovariance P true := by
    rw [hκ]
    calc
      _ = W1SizeVariance P *
            ((W1c P + W1t P + 2) *
              (((P.mt : ℝ) / P.M) * armOptimalCoefficient P false +
                ((controlCount P : ℝ) / P.M) * armOptimalCoefficient P true)) := by ring
      _ = W1SizeVariance P *
            ((W1c P + 1) * armOptimalCoefficient P false +
             (W1t P + 1) * armOptimalCoefficient P true) := by
        rw [← hweighted]
      _ = (W1c P + 1) * W1SizeCovariance P false +
          (W1t P + 1) * W1SizeCovariance P true := by rw [hq0, hq1]; ring
      _ = _ := by ring
  dsimp [W1EfficiencyChain]
  intro k
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩⟩
  · have himp := (retained_T14.2.2.2.2.2.1 P hsize k).2.2.1
    have hpoly :
        (W1c P + W1t P + 2) * k^2 * W1SizeVariance P <
            2 * k * ((W1c P + 1) * W1SizeCovariance P false +
              (W1t P + 1) * W1SizeCovariance P true) ↔
          k^2 < 2 * k * optimalCoefficient P := by
      rw [← hU]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_lt_mul_iff_right₀ (mul_pos hC hsize) :
          ((W1c P + W1t P + 2) * W1SizeVariance P) * k^2 <
            ((W1c P + W1t P + 2) * W1SizeVariance P) * (2 * k * optimalCoefficient P) ↔
            k^2 < 2 * k * optimalCoefficient P)
    exact himp.trans hpoly.symm
  · have hdiv :
        ((W1c P + W1t P + 2) * k^2 * W1SizeVariance P <
          2 * k * ((W1c P + 1) * W1SizeCovariance P false +
            (W1t P + 1) * W1SizeCovariance P true)) ↔
        ((W1c P + W1t P + 2) * k^2 <
          2 * k * ((W1c P + 1) * (W1SizeCovariance P false / W1SizeVariance P) +
            (W1t P + 1) * (W1SizeCovariance P true / W1SizeVariance P))) := by
      have hcancel :
          (2 * k * ((W1c P + 1) * (W1SizeCovariance P false / W1SizeVariance P) +
            (W1t P + 1) * (W1SizeCovariance P true / W1SizeVariance P))) *
              W1SizeVariance P =
          2 * k * ((W1c P + 1) * W1SizeCovariance P false +
            (W1t P + 1) * W1SizeCovariance P true) := by
        field_simp [hsne]
        <;> ring
      constructor
      · intro hh
        have hm : ((W1c P + W1t P + 2) * k^2) * W1SizeVariance P <
            (2 * k * ((W1c P + 1) * (W1SizeCovariance P false / W1SizeVariance P) +
              (W1t P + 1) * (W1SizeCovariance P true / W1SizeVariance P))) *
              W1SizeVariance P := by
          rw [hcancel]
          simpa [mul_assoc] using hh
        exact (mul_lt_mul_iff_left₀ hsize).mp hm
      · intro hh
        have hm := (mul_lt_mul_iff_left₀ hsize).mpr hh
        rw [hcancel] at hm
        simpa [mul_assoc] using hm
    exact hdiv
  · rw [hcoef0, hcoef1]
  · have hnorm :
        ((W1c P + W1t P + 2) * k^2 <
          2 * k * ((W1c P + 1) * armOptimalCoefficient P false +
            (W1t P + 1) * armOptimalCoefficient P true)) ↔
        (k^2 < 2 * k * (((P.mt : ℝ) / P.M) * armOptimalCoefficient P false +
            ((controlCount P : ℝ) / P.M) * armOptimalCoefficient P true)) := by
      rw [hweighted]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_lt_mul_iff_right₀ hC :
        (W1c P + W1t P + 2) * k^2 <
          (W1c P + W1t P + 2) * (2 * k * (((P.mt : ℝ) / P.M) *
            armOptimalCoefficient P false + ((controlCount P : ℝ) / P.M) *
            armOptimalCoefficient P true)) ↔
          k^2 < 2 * k * (((P.mt : ℝ) / P.M) * armOptimalCoefficient P false +
            ((controlCount P : ℝ) / P.M) * armOptimalCoefficient P true))
    exact hnorm
  · rw [hκ]
  · exact coefficient_improvement_intervals k (optimalCoefficient P)
