import SAP.P040.Defs
import AronowAudit.P040.P040_Binomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P040.Bridge
open scoped BigOperators

/- Each type below is the exported project type expressed with shared SAP definitions.
The proof is only transport along definitional equality. -/

theorem observed_count_mass :
    binomialMass (4 / 5) 14 = (805306368 : ℝ) / 6103515625 ∧
    (1 : ℝ) / 20 < binomialMass (4 / 5) 14 := by
  exact AronowAudit.P040.observed_count_mass

theorem method_free_counterexample (I : DetectionCount → Set ℝ)
    (hI : (4 / 5 : ℝ) ∉ I 14) :
    intervalCoverage (4 / 5) I ≤ (5298209257 : ℝ) / 6103515625 ∧
    intervalCoverage (4 / 5) I < (19 : ℝ) / 20 := by
  exact AronowAudit.P040.method_free_counterexample I hI

theorem lower_bound_counterexample (ell : DetectionCount → ℝ)
    (hell : (4 / 5 : ℝ) < ell 14) :
    countProbability (4 / 5) (fun k => ell k ≤ 4 / 5) ≤
        (5298209257 : ℝ) / 6103515625 ∧
    countProbability (4 / 5) (fun k => ell k ≤ 4 / 5) < (19 : ℝ) / 20 := by
  exact AronowAudit.P040.lower_bound_counterexample ell hell

theorem printed_endpoint_excludes_witness :
    (4 / 5 : ℝ) ∉ Set.Ioo (81 / 100 : ℝ) (106 / 100) ∧
    (∀ l : ℝ, roundsTwo l (81 / 100) → (4 / 5 : ℝ) < l) := by
  exact AronowAudit.P040.printed_endpoint_excludes_witness

theorem wald_membership_sq (z : ℝ) (hz : 0 ≤ z) (p : ℝ) (k : DetectionCount) :
    p ∈ waldInterval z k ↔
      (p - detectionProportion k) ^ 2 ≤ z ^ 2 *
        (detectionProportion k * (1 - detectionProportion k) / 15) := by
  exact AronowAudit.P040.wald_membership_sq z hz p k

theorem printed_wald_arithmetic :
    detectionProportion 14 = (14 : ℝ) / 15 ∧
    detectionProportion 14 * (1 - detectionProportion 14) / 15 = (14 : ℝ) / 3375 ∧
    waldRadius (49 / 25) 14 ^ 2 = (33614 : ℝ) / 2109375 ∧
    (8070 / 10000 : ℝ) < detectionProportion 14 - waldRadius (49 / 25) 14 ∧
    detectionProportion 14 - waldRadius (49 / 25) 14 < (8071 / 10000 : ℝ) ∧
    (10595 / 10000 : ℝ) < detectionProportion 14 + waldRadius (49 / 25) 14 ∧
    detectionProportion 14 + waldRadius (49 / 25) 14 < (10596 / 10000 : ℝ) ∧
    roundsTwo (detectionProportion 14 - waldRadius (49 / 25) 14) (81 / 100) ∧
    roundsTwo (detectionProportion 14 + waldRadius (49 / 25) 14) (106 / 100) ∧
    (1 : ℝ) < detectionProportion 14 + waldRadius (49 / 25) 14 ∧
    (4 / 5 : ℝ) ∉ waldInterval (49 / 25) 14 := by
  exact AronowAudit.P040.printed_wald_arithmetic

theorem wald_witness_membership (z : ℝ)
    (hzlo : (19599 / 10000 : ℝ) ≤ z) (hzhi : z ≤ (19601 / 10000 : ℝ))
    (k : DetectionCount) :
    (4 / 5 : ℝ) ∈ waldInterval z k ↔ 9 ≤ k.val ∧ k.val ≤ 13 := by
  exact AronowAudit.P040.wald_witness_membership z hzlo hzhi k

theorem wald_lower_membership (z : ℝ)
    (hzlo : (19599 / 10000 : ℝ) ≤ z) (hzhi : z ≤ (19601 / 10000 : ℝ))
    (k : DetectionCount) :
    detectionProportion k - waldRadius z k ≤ (4 / 5 : ℝ) ↔ k.val ≤ 13 := by
  exact AronowAudit.P040.wald_lower_membership z hzlo hzhi k

theorem wald_coverage_counterexample (z : ℝ)
    (hzlo : (19599 / 10000 : ℝ) ≤ z) (hzhi : z ≤ (19601 / 10000 : ℝ)) :
    intervalCoverage (4 / 5) (waldInterval z) = (24866193408 : ℝ) / 30517578125 ∧
    intervalCoverage (4 / 5) (waldInterval z) < (19 : ℝ) / 20 ∧
    countProbability (4 / 5) (fun k => detectionProportion k - waldRadius z k ≤ 4 / 5) =
      (25417304461 : ℝ) / 30517578125 ∧
    countProbability (4 / 5) (fun k => detectionProportion k - waldRadius z k ≤ 4 / 5) <
      (19 : ℝ) / 20 := by
  exact AronowAudit.P040.wald_coverage_counterexample z hzlo hzhi

theorem wald_lower_failure_probability (z : ℝ)
    (hzlo : (19599 / 10000 : ℝ) ≤ z) (hzhi : z ≤ (19601 / 10000 : ℝ)) :
    countProbability (4 / 5) (fun k => (4 / 5 : ℝ) < detectionProportion k - waldRadius z k) =
        (5100273664 : ℝ) / 30517578125 ∧
    (1 : ℝ) / 20 < countProbability (4 / 5)
      (fun k => (4 / 5 : ℝ) < detectionProportion k - waldRadius z k) ∧
    (1 : ℝ) / 40 < countProbability (4 / 5)
      (fun k => (4 / 5 : ℝ) < detectionProportion k - waldRadius z k) := by
  exact AronowAudit.P040.wald_lower_failure_probability z hzlo hzhi

theorem observed_proportion_rounds : roundsTwo (detectionProportion 14) (93 / 100) := by
  exact AronowAudit.P040.observed_proportion_rounds

theorem observed_tail_identities (p : ℝ) :
    upperDetectionTail p 14 = observedUpperPolynomial p ∧
    lowerDetectionTail p 14 = 1 - p ^ 15 := by
  exact AronowAudit.P040.observed_tail_identities p

theorem observedUpper_continuous : Continuous observedUpperPolynomial := by
  exact AronowAudit.P040.observedUpper_continuous

theorem observedUpper_hasDerivAt (p : ℝ) :
    HasDerivAt observedUpperPolynomial (210 * p ^ 13 * (1 - p)) p := by
  exact AronowAudit.P040.observedUpper_hasDerivAt p

theorem observedUpper_strictMono : StrictMonoOn observedUpperPolynomial (Set.Icc 0 1) := by
  exact AronowAudit.P040.observedUpper_strictMono

theorem observedLower_strictAnti : StrictAntiOn (fun p : ℝ => 1 - p ^ 15) (Set.Icc 0 1) := by
  exact AronowAudit.P040.observedLower_strictAnti

theorem exact_binomial_coverage {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    intervalCoverage p exactDetectionInterval ≥ (19 : ℝ) / 20 ∧
    intervalCoverage p exactDetectionLowerSet ≥ (19 : ℝ) / 20 := by
  exact AronowAudit.P040.exact_binomial_coverage hp

theorem exact_interval_contains_eighty_percent :
    upperDetectionTail (4 / 5) 14 = (5100273664 : ℝ) / 30517578125 ∧
    lowerDetectionTail (4 / 5) 14 = (29443836301 : ℝ) / 30517578125 ∧
    (4 / 5 : ℝ) ∈ exactDetectionInterval 14 ∧
    (4 / 5 : ℝ) ∈ exactDetectionLowerSet 14 := by
  exact AronowAudit.P040.exact_interval_contains_eighty_percent

theorem corrected_binomial_endpoints :
    ∃ L U L_one : ℝ,
      (680515 / 1000000 : ℝ) < L ∧ L < (680516 / 1000000 : ℝ) ∧
      (998313 / 1000000 : ℝ) < U ∧ U < (998314 / 1000000 : ℝ) ∧
      (720603 / 1000000 : ℝ) < L_one ∧ L_one < (720604 / 1000000 : ℝ) ∧
      observedUpperPolynomial L = (1 : ℝ) / 40 ∧
      observedUpperPolynomial L_one = (1 : ℝ) / 20 ∧
      U ^ 15 = (39 : ℝ) / 40 ∧ U = (39 / 40 : ℝ) ^ ((15 : ℝ)⁻¹) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, observedUpperPolynomial p = (1 : ℝ) / 40 → p = L) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, observedUpperPolynomial p = (1 : ℝ) / 20 → p = L_one) ∧
      (∀ p ∈ Set.Icc (0 : ℝ) 1, (1 - p ^ 15 : ℝ) = (1 : ℝ) / 40 → p = U) ∧
      exactDetectionInterval 14 = Set.Icc L U ∧
      exactDetectionLowerSet 14 = Set.Icc L_one 1 ∧
      L < L_one ∧ L_one < (4 / 5 : ℝ) ∧
      roundsTwo L (68 / 100) ∧ roundsTwo U 1 := by
  exact AronowAudit.P040.corrected_binomial_endpoints

theorem observed_upper_boundary_values :
    observedUpperPolynomial 0 = 0 ∧ observedUpperPolynomial 1 = 1 := by
  exact AronowAudit.P040.observed_upper_boundary_values

theorem corrected_six_decimal_rounding {L U : ℝ}
    (hL01 : L ∈ Set.Icc (0 : ℝ) 1) (hU01 : U ∈ Set.Icc (0 : ℝ) 1)
    (hL : observedUpperPolynomial L = (1 : ℝ) / 40)
    (hU : U ^ 15 = (39 : ℝ) / 40) :
    (680515 / 1000000 - 1 / 2000000 : ℝ) ≤ L ∧
    L < (680515 / 1000000 + 1 / 2000000 : ℝ) ∧
    (998314 / 1000000 - 1 / 2000000 : ℝ) ≤ U ∧
    U < (998314 / 1000000 + 1 / 2000000 : ℝ) := by
  exact AronowAudit.P040.corrected_six_decimal_rounding hL01 hU01 hL hU

end SAP.P040.Bridge
