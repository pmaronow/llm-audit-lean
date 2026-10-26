import AronowAudit.P013.P013_Audit

open scoped BigOperators
open Filter
noncomputable section
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AronowAudit.P013.ConfidenceFollowup02
universe u

/-- Lift the four-atom assignment design to an arbitrary
assignment-space universe. -/
def signedLiftDesign : Design (ULift.{u} (Fin 4)) where
  weight := fun z => signedReplicationDesign.weight z.down
  positive := fun z => signedReplicationDesign.positive z.down
  total := (Equiv.ulift.sum_comp signedReplicationDesign.weight).trans signedReplicationDesign.total

def signedLiftPopulation : Population signedLiftDesign 2 2 where
  exposure := fun z => (signedReplicationPopulation 2).exposure z.down
  outcome := (signedReplicationPopulation 2).outcome

theorem signedLift_pi (i d : Fin 2) :
    pi signedLiftPopulation i d = pi (signedReplicationPopulation 2) i d := by
  unfold pi expectation
  exact Equiv.ulift.sum_comp (fun z => signedReplicationDesign.weight z *
    indicator (signedReplicationPopulation 2).exposure i d z)

theorem signedLift_positive : Positivity signedLiftPopulation 1 := by
  intro i
  rw [signedLift_pi]
  exact signed_replication_counterexample.1 i 1

theorem signedLift_minimum : IsMinimumPi signedLiftPopulation 1 (1/3) := by
  constructor
  · exact ⟨0,(signedLift_pi 0 1).trans signed_replication_counterexample.2.1⟩
  · intro i
    fin_cases i
    · change (1/3 : ℝ) ≤ pi signedLiftPopulation 0 1
      rw [signedLift_pi,signed_replication_counterexample.2.1]
    · change (1/3 : ℝ) ≤ pi signedLiftPopulation 1 1
      rw [signedLift_pi,signed_replication_counterexample.2.2.1]
      norm_num

theorem signedLift_total : potentialTotal signedLiftPopulation 1 = 1 :=
  signed_replication_counterexample.2.2.2.1

theorem signedLift_expectation :
    expectation (independentProduct signedLiftDesign (replicateDesign signedLiftDesign 1))
      (simulatedHTTotal signedLiftPopulation 1 1) = 2/9 := by
  rw [simulated_expectation signedLiftPopulation (by omega) 1 signedLift_positive 1 (by omega)]
  rw [signedLift_total]
  simp only [Fin.sum_univ_two, signedLift_pi]
  rw [signed_replication_counterexample.2.1,signed_replication_counterexample.2.2.1]
  norm_num [signedLiftPopulation,signedReplicationPopulation]

/-- Negation of the printed power bound, retaining an arbitrary
finite assignment-space type and universe. -/
theorem simulated_bias_as_printed_refuted :
    ¬ (∀ {Ω : Type u} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K),
      0 < N → ∀ (d : Fin K), Positivity F d → ∀ (R : ℕ) (p0 : ℝ),
      IsMinimumPi F d p0 → potentialTotal F d ≠ 0 →
      |(expectation (independentProduct P (replicateDesign P R)) (simulatedHTTotal F d R) -
        potentialTotal F d)/potentialTotal F d| ≤ (1-p0)^(R+1)) := by
  intro h
  have hh := h signedLiftPopulation (by omega) 1 signedLift_positive 1 (1/3)
    signedLift_minimum (by rw [signedLift_total]; norm_num)
  rw [signedLift_expectation,signedLift_total] at hh
  norm_num at hh

/-- Negation of the printed logarithmic rule on the signed-outcome
population: a replicate count satisfying the rule does not reach its bias target. -/
theorem simulated_rule_as_printed_refuted :
    ¬ (∀ {Ω : Type u} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K),
      0 < N → ∀ (d : Fin K), Positivity F d → ∀ (R : ℕ) (p0 : ℝ),
      IsMinimumPi F d p0 → potentialTotal F d ≠ 0 → ∀ b : ℝ, 0 < b →
      (R : ℝ) ≥ Real.log b/Real.log (1-p0)-1 →
      |(expectation (independentProduct P (replicateDesign P R)) (simulatedHTTotal F d R) -
        potentialTotal F d)/potentialTotal F d| ≤ b) := by
  intro h
  have hh := h signedLiftPopulation (by omega) 1 signedLift_positive 1 (1/3)
    signedLift_minimum (by rw [signedLift_total]; norm_num) (1/2) (by norm_num)
    (by simpa only [Nat.cast_one] using signed_log_rule_counterexample.1)
  rw [signedLift_expectation,signedLift_total] at hh
  norm_num at hh

end AronowAudit.P013.ConfidenceFollowup02

