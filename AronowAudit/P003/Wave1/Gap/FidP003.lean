import AronowAudit.P003.P003_ConfidenceCompletion

/-! Probability-only refutation of the literal printed Monte Carlo contract.
The existing `monteInterval false` convention assigns the empty interval when
an endpoint search fails. The paper leaves such an execution undefined. -/

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-- Both balanced assignments observe the same counts in the witness population. -/
theorem p003T28_observed :
    ∀ z : Assignment 2 1,
      canonicalObserved (⟨0,2,0,0⟩ : Counts) z.val = ⟨1,0,0,1⟩ := by
  decide +kernel

/-- The true table has exact p-value one and effect one. -/
theorem p003T28_accepted_one :
    (1 : ℝ) ∈ accepted (3/4) (⟨1,0,0,1⟩ : Counts) := by
  have hposs : (⟨0,2,0,0⟩ : Counts) ∈ possibleTables ⟨1,0,0,1⟩ := by
    decide +kernel
  have hp : pValue ⟨0,2,0,0⟩ ⟨1,0,0,1⟩ = 1 := by
    decide +kernel
  have ht : tau ⟨0,2,0,0⟩ = 1 := by
    norm_num [tau, tauQ, Counts.effect, Counts.total]
  apply Finset.mem_image.mpr
  refine ⟨⟨0,2,0,0⟩, List.mem_toFinset.mpr ?_, ht⟩
  apply List.mem_filter.mpr
  refine ⟨hposs, ?_⟩
  apply decide_eq_true
  rw [hp]
  norm_num

theorem p003T28_exact_one :
    (1 : ℝ) ∈ exactInterval (3/4) (⟨1,0,0,1⟩ : Counts) := by
  exact ⟨1, p003T28_accepted_one, 1, p003T28_accepted_one, le_rfl, le_rfl⟩

/-- The singleton upper search fails for arbitrary decisions and indices. -/
theorem p003T28_upper_none (reject : Counts → ℕ → Bool) (idx : ℕ) :
    (upperRun false ⟨1,0,0,1⟩ reject idx).value = none := by
  change (adaptiveSearch 5 false ⟨1,0,0,1⟩ 2 2 reject 2 2 idx).value = none
  exact ConfidenceFollowup.printed_singleton_no_endpoint
    5 ⟨1,0,0,1⟩ 2 2 2 reject idx

/-- This uses precisely the existing failure-as-empty convention. -/
theorem p003T28_interval_empty
    (pool : Fin (2*testBudget 2+1) → Fin 200 → Assignment 2 1) :
    monteInterval false (3/4) (1/4) ⟨1,0,0,1⟩ pool = ∅ := by
  have hu :
      (monteEndpoints false (3/4) (1/4) ⟨1,0,0,1⟩ pool).2.value = none :=
    p003T28_upper_none _ 0
  simp only [monteInterval, hu]
  cases (monteEndpoints false (3/4) (1/4) ⟨1,0,0,1⟩ pool).1.value <;> rfl

/-- The inclusion event is impossible pointwise, without enumerating the pool. -/
theorem p003T28_event_impossible (ω : MonteSpace 2 1 200) :
    ¬ (exactInterval (3/4) (canonicalObserved (⟨0,2,0,0⟩ : Counts) ω.1.val) ⊆
      monteInterval false (3/4) (1/4)
        (canonicalObserved (⟨0,2,0,0⟩ : Counts) ω.1.val) ω.2) := by
  rw [p003T28_observed ω.1, p003T28_interval_empty ω.2]
  intro h
  exact h p003T28_exact_one

theorem p003T28_probability_zero :
    uniformProb (fun ω : MonteSpace 2 1 200 =>
      exactInterval (3/4) (canonicalObserved (⟨0,2,0,0⟩ : Counts) ω.1.val) ⊆
        monteInterval false (3/4) (1/4)
          (canonicalObserved (⟨0,2,0,0⟩ : Counts) ω.1.val) ω.2) = 0 := by
  simp only [uniformProb, p003T28_event_impossible, Finset.filter_false,
    Finset.card_empty, Nat.cast_zero, zero_div]

/-- The experiment is inhabited, so the zero probability is not an empty-space artifact. -/
theorem p003T28_space_nonempty : Nonempty (MonteSpace 2 1 200) := by
  let z : Assignment 2 1 := ⟨{0}, by decide⟩
  exact ⟨(z, fun _ _ => z)⟩

/-- An exact exponential certificate for the strictly positive claimed bound. -/
theorem p003T28_positive_bound :
    0 < 1 - 2 * (testBudget 2 : ℝ) *
      Real.exp (-2 * (200 : ℝ) * (1/4 : ℝ)^2) := by
  have hb : testBudget 2 = 12 := by decide +kernel
  have he : -2 * (200 : ℝ) * (1/4 : ℝ)^2 = -25 := by norm_num
  have hexp : (26 : ℝ) ≤ Real.exp 25 := by
    linarith [Real.add_one_le_exp (25 : ℝ)]
  have hinv : Real.exp (-25 : ℝ) ≤ 1/26 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hexp
  rw [hb, he]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- The probability-only universal contract of Lemma B.15 fails for the literal
printed search under `monteInterval`'s failure-as-empty convention, which the
paper does not specify. At v=(0,2,0,0), m=1, K=200, α=3/4, ε=1/4, the first
inclusion has probability zero but its asserted lower bound is positive.
This does not refute the second bound or either corrected-search bound. -/
theorem printed_monte_probability_contract_refuted :
    ¬ (∀ (v : AronowAudit.P003.Counts) (m K : ℕ) (α ε : ℝ),
      0 < m → v.total = 2 * m → 0 < K →
      (0 < α ∧ α < 1) → (0 ≤ ε ∧ ε < α) →
      (AronowAudit.P003.uniformProb
        (fun ω : AronowAudit.P003.MonteSpace v.total m K =>
          AronowAudit.P003.exactInterval α
              (AronowAudit.P003.canonicalObserved v ω.1.val) ⊆
            AronowAudit.P003.monteInterval false α ε
              (AronowAudit.P003.canonicalObserved v ω.1.val) ω.2) ≥
        1 - 2 * (AronowAudit.P003.testBudget v.total : ℝ) *
          Real.exp (-2 * (K : ℝ) * ε ^ 2)) ∧
      (0 < α - 2 * ε →
        AronowAudit.P003.uniformProb
          (fun ω : AronowAudit.P003.MonteSpace v.total m K =>
            AronowAudit.P003.monteInterval false α ε
                (AronowAudit.P003.canonicalObserved v ω.1.val) ω.2 ⊆
              AronowAudit.P003.exactInterval (α - 2 * ε)
                (AronowAudit.P003.canonicalObserved v ω.1.val)) ≥
          1 - 2 * (AronowAudit.P003.testBudget v.total : ℝ) *
            Real.exp (-2 * (K : ℝ) * ε ^ 2))) := by
  intro h
  have hfirst := (h ⟨0,2,0,0⟩ 1 200 (3/4) (1/4)
    (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)).1
  change uniformProb (fun ω : MonteSpace 2 1 200 =>
      exactInterval (3/4) (canonicalObserved (⟨0,2,0,0⟩ : Counts) ω.1.val) ⊆
        monteInterval false (3/4) (1/4)
          (canonicalObserved (⟨0,2,0,0⟩ : Counts) ω.1.val) ω.2) ≥
    1 - 2 * (testBudget 2 : ℝ) *
      Real.exp (-2 * (200 : ℝ) * (1/4 : ℝ)^2) at hfirst
  rw [p003T28_probability_zero] at hfirst
  exact (not_le_of_gt p003T28_positive_bound) hfirst

end AronowAudit.P003.Wave1
