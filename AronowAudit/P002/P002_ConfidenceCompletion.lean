import AronowAudit.P002.P002_Audit

/-! Counterexamples to printed Lemma 5, equation (E.10), and Theorem 1. -/
namespace AronowAudit.P002.ConfidenceFollowup
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Universal form of the printed Lemma 5 statement. -/
def PrintedLemma5 : Prop :=
  ∀ {n : ℕ} (P : Population n) (δ r A : ℝ),
    δ < 1 → (0 < r ∧ r ≤ 1/2) → 0 < A → Theta P δ r A →
    (1-δ) * (controlSize P/((n : ℝ)*(P.n1 : ℝ))*S2 P (late P) true +
      (P.n1 : ℝ)/((n : ℝ)*controlSize P)*S2 P (late P) false) ≤
      designVariance P (tau P (late P))

theorem printed_lemma5_refuted : ¬ PrintedLemma5 := by
  intro h
  obtain ⟨ht,hx,hl,hcard,hs1,hs0,hv,hvo,hbad,ho⟩ := negative_delta_counterexample
  have hh := h (negativeDeltaModel 1).pop (-1/2) (1/6) 2
    (by norm_num) (by constructor <;> norm_num) (by norm_num) ht
  rw [hl] at hh
  exact (not_le_of_gt hbad)
    (by simpa only [negativeDeltaModel, Nat.mul_one, Nat.cast_ofNat] using hh)

/-- Universal form of the printed (E.10) statement. -/
def PrintedE10 : Prop :=
  ∀ {n k : ℕ} (P : CovPopulation n k) (δ e A B r : ℝ),
    0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → Xi P δ e A B r →
    (1-δ) * (controlSize P.pop/((n : ℝ)*(P.pop.n1 : ℝ))*
      popVar (residual P true (late P.pop)) +
      (P.pop.n1 : ℝ)/((n : ℝ)*controlSize P.pop)*popVar (residual P false (late P.pop))) ≤
      designVariance P.pop (oracleTau P (late P.pop))

theorem printed_E10_refuted : ¬ PrintedE10 := by
  intro h
  obtain ⟨ht,hx,hl,hcard,hs1,hs0,hv,hvo,hbad,ho⟩ := negative_delta_counterexample
  have hh := h (negativeDeltaModel 1) (-1/2) (1/2) 2 2 (1/6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by constructor <;> norm_num) hx
  rw [hl] at hh
  exact (not_le_of_gt ho)
    (by simpa only [negativeDeltaModel, Nat.mul_one, Nat.cast_ofNat] using hh)

/-- Universal form of the printed Theorem 1 statement. -/
def PrintedTheorem1 : Prop :=
  ∀ (δ r A α : ℝ), δ < 1 → (0 < r ∧ r ≤ 1/2) → 0 < A →
    (0 < α ∧ α < 1) →
    Tendsto (fun n => infCoverageTheta n δ r A α) atTop (nhds (ENNReal.ofReal (1-α)))

theorem printed_theorem1_refuted : ¬ PrintedTheorem1 := by
  intro h
  have hα : (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 := by constructor <;> norm_num
  have hh := h 0 (1/4) (1/2) (1/2) (by norm_num)
    (by constructor <;> norm_num) (by norm_num) hα
  exact (theorem1_sharpness_counterexample (1/2) hα).2.2.2.2 hh


end
end AronowAudit.P002.ConfidenceFollowup
