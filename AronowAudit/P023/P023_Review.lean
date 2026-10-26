import AronowAudit.P023.P023_Audit

/-!
These results complement the finite weight counterexamples: a nonzero distant
weight does not contradict convergence of two estimators to a common target.
The consistency hypotheses below are explicit. This file does not assert that
exact polynomial specification alone proves either sampling consistency result.
-/

namespace AronowAudit.P023

open MeasureTheory Filter
open scoped Topology

/-- Fixed-tolerance union bound, without an independence or measurability
assumption: an error in a difference requires an error in at least one term. -/
theorem difference_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : Ω → ℝ) (a b ε : ℝ) :
    P {ω | ε < |(A ω - B ω) - (a - b)|} ≤
      P {ω | ε / 2 < |A ω - a|} + P {ω | ε / 2 < |B ω - b|} := by
  apply le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  by_contra h
  have hA : |A ω - a| ≤ ε / 2 := le_of_not_gt (fun hA => h (Or.inl hA))
  have hB : |B ω - b| ≤ ε / 2 := le_of_not_gt (fun hB => h (Or.inr hB))
  have ht := abs_sub_le (A ω - a) 0 (B ω - b)
  have he : (A ω - B ω) - (a - b) = (A ω - a) - (B ω - b) := by ring
  change ε < |(A ω - B ω) - (a - b)| at hω
  rw [he] at hω
  simp only [sub_zero, zero_sub, abs_neg] at ht
  linarith

/-- Closure of the paper's explicit probability-event definition under
subtraction. The two estimators may use the same observations. -/
theorem convergesInProbability_sub {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : ℕ → Ω → ℝ) (a b : ℝ)
    (hA : ConvergesInProbability P A a) (hB : ConvergesInProbability P B b) :
    ConvergesInProbability P (fun N ω => A N ω - B N ω) (a - b) := by
  intro ε hε
  have ht := (hA (ε / 2) (by linarith)).add (hB (ε / 2) (by linarith))
  simp only [add_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) (fun N => difference_probability_bound P (A N) (B N) a b ε)

/-- P023-T3, common-target qualification: shared consistency implies
asymptotic equivalence at every fixed positive tolerance. -/
theorem shared_target_asymptotic_equivalence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : ℕ → Ω → ℝ) (β : ℝ)
    (hA : ConvergesInProbability P A β) (hB : ConvergesInProbability P B β) :
    ConvergesInProbability P (fun N ω => A N ω - B N ω) 0 := by
  simpa only [sub_self] using convergesInProbability_sub P A B β β hA hB

/-- The preceding positive result for the actual equation (2) estimator and
the actual shrinking-window RD estimator. Their consistency is required, not
inferred from the finite nonlocality witnesses or from their common label. -/
theorem polynomial_rd_shared_consistency {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (sample : ℕ → Ω → ℝ × ℝ) (J : ℕ) (k : ℕ → ℝ) (β : ℝ)
    (hOLS : ConvergesInProbability P (fun N => samplePolynomial sample N J) β)
    (hRD : ConvergesInProbability P (sampleRD sample k) β) :
    ConvergesInProbability P
      (fun N ω => samplePolynomial sample N J ω - sampleRD sample k N ω) 0 := by
  exact shared_target_asymptotic_equivalence P _ _ β hOLS hRD


end AronowAudit.P023

