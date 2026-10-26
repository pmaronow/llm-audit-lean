import AronowAudit.P005.P005_Formalization

open scoped BigOperators
open Filter
noncomputable section
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AronowAudit.P005.ConfidenceFollowup02

/-- Exact full printed covariance-lemma negation, using its genuine
six-unit complete-randomization variance witness. -/
theorem printed_covariance_lemma_refuted :
    ¬ (∀ {n m : ℕ}, 4 ≤ n → 0 < m → m < n →
      ∀ (t : Arm) (a b : Fin n → ℝ),
      expectation m (fun S => sampleCov (armSet t S) a b) =
        ((armSize n m t : ℝ)-1)*n/((armSize n m t : ℝ)*(n-1))*popCov a b ∧
      variance m (fun S => sampleCov (armSet t S) a b) ≤
        covarianceBound (armSize n m t) a b) := by
  intro h
  obtain ⟨hn,hm,hmn,hcard,ha,hb,hcov,hmean,hvar,hbound,hbad⟩ := covariance_counterexample
  have hh := (h (n := 6) (m := 4) hn (by omega) hmn .treated witnessA witnessB).2
  exact (not_le_of_gt hbad) (by simpa only [armSet,armSize] using hh)

/-- Exact full printed sign-identity negation. The population witness is standardized
and has invertible matrices in both arms. -/
theorem printed_interacted_third_bias_refuted :
    ¬ (∀ {n d m : ℕ} (P : Population n d),
      3 ≤ n → 0 < m → m < n → standardized P → interactedRegular P m →
      expectation m (fun S => dot (xMean P (control S)) (armNu3 P (control S) P.yC)) -
        expectation m (fun S => dot (xMean P S) (armNu3 P S P.yT)) =
          NCCC n m * leverageCov P P.yC - NTTT n m * leverageCov P P.yT) := by
  intro h
  obtain ⟨hstd,hreg,hyT,hyC,hp1,hp2,hcard,hleverageT,hleverageC,hL,hR,hneq⟩ :=
    interacted_sign_counterexample
  exact hneq (h signPopulation (by omega) (by omega) (by omega) hstd hreg)

end AronowAudit.P005.ConfidenceFollowup02

