import SAP.P042.WH.W1.Leaves
import AronowAudit.P042.P042_Turnout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042.WH.W1.P.T6_L1

open Finset
open scoped BigOperators
open Classical

lemma assignment_probability {N m : ℕ} (hN : 0 < N)
    (hm : 1 ≤ m) (hmN : m ≤ N) (b : Bool) (i : Fin N) :
    AronowAudit.P042.finiteExpectation (AronowAudit.P042.completeAssignments N m)
        (fun S => if SAP.P042.assignmentIndicator S i = b then (1 : ℝ) else 0) =
      if b then (m : ℝ) / (N : ℝ) else ((N - m : ℕ) : ℝ) / (N : ℝ) := by
  have hsupport : (AronowAudit.P042.completeAssignments N m).Nonempty := by
    exact Finset.powersetCard_nonempty.mpr (by simpa using hmN)
  cases b with
  | false =>
      have hfun :
          (fun S : Finset (Fin N) =>
            if SAP.P042.assignmentIndicator S i = false then (1 : ℝ) else 0) =
          fun S => 1 - (if i ∈ S then (1 : ℝ) else 0) := by
        funext S
        by_cases hi : i ∈ S <;> simp [SAP.P042.assignmentIndicator, hi]
      have hsub : ((N - m : ℕ) : ℝ) = (N : ℝ) - (m : ℝ) := by
        exact_mod_cast (Nat.cast_sub (by omega : m ≤ N) :
          ((N - m : ℕ) : ℝ) = (N : ℝ) - (m : ℝ))
      have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      rw [hfun, AronowAudit.P042.finite_expectation_sub,
        AronowAudit.P042.finite_expectation_const _ hsupport,
        AronowAudit.P042.complete_inclusion_probability hN hm hmN i, hsub]
      simp only [Bool.false_eq_true, ↓reduceIte]
      field_simp [hNc]
  | true =>
      simpa [SAP.P042.assignmentIndicator] using
        (AronowAudit.P042.complete_inclusion_probability hN hm hmN i)

lemma joint_indicator_factor {N : ℕ} (S : Finset (Fin N)) (i : Fin N)
    {A : Type} (U : Fin N → A) (B : Set A) (b : Bool) :
    (if SAP.P042.assignmentIndicator S i = b ∧ U i ∈ B then (1 : ℝ) else 0) =
      (if U i ∈ B then (1 : ℝ) else 0) *
        (if SAP.P042.assignmentIndicator S i = b then (1 : ℝ) else 0) := by
  by_cases hassign : SAP.P042.assignmentIndicator S i = b <;>
    by_cases hattr : U i ∈ B <;> simp [hassign, hattr]

lemma populationMean_const {N : ℕ} (hN : 0 < N) (c : ℝ) :
    AronowAudit.P042.populationMean (fun _ : Fin N => c) = c := by
  unfold AronowAudit.P042.populationMean
  have hsum : (∑ _i : Fin N, c) = (N : ℝ) * c := by simp
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [hsum]
  field_simp [hNc]

end SAP.P042.WH.W1.P.T6_L1

theorem SAP.P042.WH.W1.T6_L1_proof : SAP.P042.WH.W1.T6_L1 := by
  classical
  change SAP.P042.SampledSubjectIndependence
  intro N m hN hm hmN A U B b
  let p : ℝ := if b then (m : ℝ) / (N : ℝ)
    else ((N - m : ℕ) : ℝ) / (N : ℝ)
  have hprob (i : Fin N) :
      AronowAudit.P042.finiteExpectation (AronowAudit.P042.completeAssignments N m)
          (fun S => if SAP.P042.assignmentIndicator S i = b then (1 : ℝ) else 0) = p := by
    simpa [p, SAP.P042.Bridge.finiteExpectation_eq,
      SAP.P042.Bridge.completeAssignments_eq] using
      (SAP.P042.WH.W1.P.T6_L1.assignment_probability
        (by omega : 0 < N) hm (by omega : m ≤ N) b i)
  have hjoint :
      SAP.P042.sampledAssignmentExpectation m (fun S i =>
        if SAP.P042.assignmentIndicator S i = b ∧ U i ∈ B then (1 : ℝ) else 0) =
        p * SAP.P042.populationMean (fun i => if U i ∈ B then (1 : ℝ) else 0) := by
    simp only [SAP.P042.Bridge.finiteExpectation_eq,
      SAP.P042.Bridge.populationMean_eq, SAP.P042.Bridge.completeAssignments_eq,
      SAP.P042.sampledAssignmentExpectation, AronowAudit.P042.populationMean]
    rw [AronowAudit.P042.finite_expectation_div, AronowAudit.P042.finite_expectation_sum]
    simp_rw [SAP.P042.WH.W1.P.T6_L1.joint_indicator_factor,
      AronowAudit.P042.finite_expectation_mul, hprob]
    rw [← Finset.sum_mul]
    ring
  have hmarg :
      SAP.P042.sampledAssignmentExpectation (N := N) m (fun (S : Finset (Fin N)) (i : Fin N) =>
        if SAP.P042.assignmentIndicator S i = b then (1 : ℝ) else 0) = p := by
    simp only [SAP.P042.Bridge.finiteExpectation_eq,
      SAP.P042.Bridge.populationMean_eq, SAP.P042.Bridge.completeAssignments_eq,
      SAP.P042.sampledAssignmentExpectation]
    unfold AronowAudit.P042.populationMean
    rw [AronowAudit.P042.finite_expectation_div, AronowAudit.P042.finite_expectation_sum]
    simp_rw [hprob]
    have hsum : (∑ _i : Fin N, p) = (N : ℝ) * p := by simp
    rw [hsum]
    have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < N))
    field_simp [hNc]
  rw [hjoint, hmarg]
