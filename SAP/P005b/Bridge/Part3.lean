import SAP.P005b.Bridge.Part2
import AronowAudit.P005.Wave1.Gap.GP005B2
import AronowAudit.P005.Wave1.Gap.GP005B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005b.Bridge

open scoped BigOperators Matrix
open Finset

noncomputable section

/-- Undo the population-average divisor in the Gram matrix. -/
theorem sum_outer_eq {n d : ℕ} (P : SAP.P005b.Population n d) (hn : 0 < n) :
    (∑ i, Matrix.vecMulVec (P.x i) (P.x i)) = (n : ℝ) • SAP.P005b.gram P := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  ext k l
  simp [SAP.P005b.gram, SAP.P005b.popMean, SAP.P005b.mean, Matrix.vecMulVec,
    Matrix.sum_apply, Matrix.of_apply]
  field_simp [hn0]

/-- Linearity and the existing arm-covariance expectation formulas give (11) and (12). -/
theorem bias_parts_expectation {n d m : ℕ} (P : SAP.P005b.Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (ht : 2 ≤ m) (hc : 2 ≤ n-m) :
    SAP.P005b.expectation m (SAP.P005b.biasPart11 P m) =
      (SAP.P005b.leverageCov P P.yC-SAP.P005b.leverageCov P P.yT)/(n-1 : ℝ) ∧
    SAP.P005b.expectation m (SAP.P005b.biasPart12 P m) =
      (SAP.P005b.pT n m/SAP.P005b.pC n m)*SAP.P005b.NTTT n m*SAP.P005b.leverageCov P P.yT -
        (SAP.P005b.pT n m/SAP.P005b.pC n m)*SAP.P005b.NTTC n m*SAP.P005b.leverageCov P P.yC := by
  have hT : SAP.P005b.expectation m (fun S => SAP.P005b.sampleCov S (SAP.P005b.leverage P) P.yT) =
      ((m : ℝ)-1)*n/((m : ℝ)*(n-1))*SAP.P005b.leverageCov P P.yT :=
    AronowAudit.P005.Wave1.control_arm_covariance_expectation hn hm (le_of_lt hmn) _ _
  have hC : SAP.P005b.expectation m (fun S => SAP.P005b.sampleCov (SAP.P005b.control S)
      (SAP.P005b.leverage P) P.yC) =
      ((n : ℝ)-m-1)*n/(((n : ℝ)-m)*(n-1))*SAP.P005b.leverageCov P P.yC := by
    change AronowAudit.P005.expectation m
      (fun S => AronowAudit.P005.sampleCov (AronowAudit.P005.control S) _ _) = _
    rw [AronowAudit.P005.Wave1.control_arm_transport (le_of_lt hmn)
      (fun U => AronowAudit.P005.sampleCov U (SAP.P005b.leverage P) P.yC)]
    have h := AronowAudit.P005.Wave1.control_arm_covariance_expectation hn
      (Nat.sub_pos_of_lt hmn) (Nat.sub_le n m) (SAP.P005b.leverage P) P.yC
    simpa only [Nat.cast_sub (le_of_lt hmn), SAP.P005b.leverageCov, popCov_eq] using h
  change AronowAudit.P005.expectation m (fun S => SAP.P005b.sampleCov S
    (SAP.P005b.leverage P) P.yT) = _ at hT
  change AronowAudit.P005.expectation m (fun S => SAP.P005b.sampleCov (SAP.P005b.control S)
    (SAP.P005b.leverage P) P.yC) = _ at hC
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast ht
  have hcR' : (m : ℝ)+2 ≤ n := by exact_mod_cast (show m+2 ≤ n by omega)
  have hcR : (2 : ℝ) ≤ (n : ℝ)-m := by linarith
  have n0 : (n : ℝ) ≠ 0 := by linarith
  have n1 : (n : ℝ)-1 ≠ 0 := by linarith
  have m0 : (m : ℝ) ≠ 0 := by linarith
  have m1 : (m : ℝ)-1 ≠ 0 := by linarith
  have c0 : (n : ℝ)-m ≠ 0 := by linarith
  have c1 : (n : ℝ)-m-1 ≠ 0 := by linarith
  constructor
  · unfold SAP.P005b.biasPart11
    simp only [expectation_eq,
      AronowAudit.P005.expectation_mul, AronowAudit.P005.Wave1.t13_E_sub]
    rw [hT, hC]
    field_simp [n0, n1, m0, m1, c0, c1]
  · unfold SAP.P005b.biasPart12
    simp only [expectation_eq,
      AronowAudit.P005.expectation_mul, AronowAudit.P005.Wave1.t13_E_sub]
    rw [hT, hC]
    simp only [SAP.P005b.pT, SAP.P005b.pC]
    field_simp [n0, n1, m0, m1, c0, c1]

end
end SAP.P005b.Bridge
