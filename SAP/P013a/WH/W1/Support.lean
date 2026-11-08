import SAP.P013a.Defs.WholeW1
import SAP.P013a.Bridge
import AronowAudit.P013.Wave1.CorrectedCoverage
import AronowAudit.P013.Wave1.PrintedWald
import AronowAudit.P027.P027_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a.WH.W1

open scoped BigOperators Topology NNReal ENNReal
open Filter Finset Bridge
noncomputable section

/-- The general CLT and coverage donors never require stability of outcomes across sizes. -/
theorem whole_coverage : WholeWaldCoverage := by
  intro S hb h5 h6 hL
  let Q := toSequence S
  have hclt := AronowAudit.P013.Wave1.CorrectedCoverage.n5_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n1_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n3_proof
    (AronowAudit.P013.Wave1.CorrectedCoverage.n4_proof
      AronowAudit.P013.Wave1.CorrectedCoverage.n2_proof) Q hb h5 h6
  exact AronowAudit.P013.Wave1.CorrectedCoverage.n9_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n6_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n7_proof
    (AronowAudit.P013.seqLaw Q) (AronowAudit.P013.seqEstimate Q)
    (AronowAudit.P013.seqVarianceEstimate Q) (AronowAudit.P013.seqTarget Q)
    (AronowAudit.P013.seqTrueVariance Q) hclt
    (AronowAudit.P013.Wave1.CorrectedCoverage.eventually_pos_of_condition6 Q h6)
    (AronowAudit.P013.Wave1.CorrectedCoverage.n8_proof Q h6 hL)

/-- The all-size paired witness has genuine C5, not just the printed condition. -/
theorem whole_failure : WholeWaldFailure := by
  have h := AronowAudit.P013.Wave1.PrintedWald.assemble_witness
    AronowAudit.P013.Wave1.CorrectedCoverage.n1_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n2_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n3_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n4_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n5_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n6_proof
    AronowAudit.P013.Wave1.CorrectedCoverage.n7_proof
    AronowAudit.P013.Wave1.PrintedWald.n1_proof
    AronowAudit.P013.Wave1.PrintedWald.n2_proof
    AronowAudit.P013.Wave1.PrintedWald.n3_proof
    AronowAudit.P013.Wave1.PrintedWald.n4_proof
    AronowAudit.P013.Wave1.PrintedWald.n5_proof
    AronowAudit.P013.Wave1.PrintedWald.n6_proof
    AronowAudit.P013.Wave1.PrintedWald.n7_proof
    AronowAudit.P013.Wave1.PrintedWald.n8_proof
    AronowAudit.P013.Wave1.PrintedWald.n9_proof
    AronowAudit.P013.Wave1.PrintedWald.n10_proof
    AronowAudit.P013.Wave1.PrintedWald.n11_proof
    AronowAudit.P013.Wave1.PrintedWald.n12_proof
    AronowAudit.P013.Wave1.PrintedWald.n13_proof
    AronowAudit.P013.Wave1.PrintedWald.n14_proof
  obtain ⟨S, hn, hp, h3, _, h5, h6, hf⟩ := h
  exact ⟨fromSequence S, hn, hp, h3, h5, h6, hf⟩

/-- Chebyshev concentration, with the two spellings of the centered estimate identified. -/
theorem vanishes_concentration (S : ExperimentSequence) (h : ScaledVarianceVanishes S) :
    ScaledVarianceConcentration S := by
  have hc := AronowAudit.P013.variance_concentration
    (AronowAudit.P013.seqLaw (toSequence S))
    (fun (n : ℕ) z => (n+1 : ℝ)*AronowAudit.P013.seqVarianceEstimate (toSequence S) n z) h
  have heq : (fun (n : ℕ) z => (n+1 : ℝ)*AronowAudit.P013.seqVarianceEstimate (toSequence S) n z-
      AronowAudit.P013.expectation (AronowAudit.P013.seqLaw (toSequence S) n)
        (fun z => (n+1 : ℝ)*AronowAudit.P013.seqVarianceEstimate (toSequence S) n z)) =
      (fun (n : ℕ) z => (n+1 : ℝ)*(AronowAudit.P013.seqVarianceEstimate (toSequence S) n z-
        AronowAudit.P013.expectation (AronowAudit.P013.seqLaw (toSequence S) n)
          (AronowAudit.P013.seqVarianceEstimate (toSequence S) n))) := by
    funext n z
    rw [AronowAudit.P013.expectation_const_mul]
    ring
  rw [heq] at hc
  exact hc

/-- A rate with a diverging denominator gives the variance limit, hence concentration. -/
theorem rate_vanishes (S : ExperimentSequence) (a : ℕ → ℝ) (C : ℝ)
    (hr : ∀ᶠ n in atTop, variance (seqLaw S n)
      (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ C/a n)
    (ha : Tendsto a atTop atTop) : ScaledVarianceVanishes S := by
  have ht : Tendsto (fun n => C/a n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp ha) :
        Tendsto (fun n => C*(a n)⁻¹) atTop (𝓝 (C*0)))
  exact squeeze_zero'
    (Eventually.of_forall (fun n => AronowAudit.P013.variance_nonneg (toDesign (seqLaw S n)) _)) hr ht

/-- Positive literal reciprocal-sum exponents are Holder conjugates. -/
theorem conjugate_of_reciprocal (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : 1/a+1/b=1) : a.HolderConjugate b := by
  rw [Real.holderConjugate_iff]
  constructor
  · have hlt : 1/a < 1 := by have := one_div_pos.mpr hb; linarith
    have : 1 < a := (div_lt_one ha).mp hlt
    exact this
  · simpa only [one_div] using hab

def toSampling {U Ω : Type} [Fintype U] [Fintype Ω]
    (D : WholeSamplingDesign U Ω) : AronowAudit.P027.Design U Ω where
  weight := D.weight
  nonneg := D.nonneg
  total := D.total
  selected := D.selected

/-- Finite second-moment bound followed by a limit; no cross-size outcome premise is used. -/
theorem shrinking_rate (S : ExperimentSequence) (hc3 : ComparisonBounded S)
    (hc5 : Condition5Genuine S) (b : ℕ → ℝ)
    (hmin : ∀ n, PositiveJointDomain S n → IsMinimumPositiveJoint S n (b n)) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      variance (seqLaw S n) (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ C/((n+1 : ℝ)*b n)) ∧
    (Tendsto (fun n : ℕ => (n+1 : ℝ)*b n) atTop atTop → LowerTailCondition S) := by
  obtain ⟨c1,c2,hc1,hc2,hb⟩ := hc3
  obtain ⟨m,h,hh⟩ := hc5
  let A : ℝ := max 1 (max c1 c2)
  have hA : 1 ≤ A := le_max_left _ _
  have hc1A : c1 ≤ A := (le_max_left c1 c2).trans (le_max_right _ _)
  have hc2A : c2 ≤ A := (le_max_right c1 c2).trans (le_max_right _ _)
  have hbA : ∀ n i, |(seqPopulation S n).outcome i (S.treated n)| ≤ A ∧
      |(seqPopulation S n).outcome i (S.control n)| ≤ A ∧
      |1 / pi (seqPopulation S n) i (S.treated n)| ≤ A ∧
      |1 / pi (seqPopulation S n) i (S.control n)| ≤ A := by
    intro n i
    exact ⟨(hb n i).1.trans hc1A, (hb n i).2.1.trans hc1A,
      (hb n i).2.2.1.trans hc2A, (hb n i).2.2.2.trans hc2A⟩
  let C : ℝ := 1152*A^8*(m+1 : ℝ)^3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdom := AronowAudit.P013.Wave1.shrinking_eventual_domain (toSequence S) ⟨m,h,hh⟩
  have hr : ∀ᶠ n in atTop, variance (seqLaw S n)
      (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ C/((n+1 : ℝ)*b n) := by
    filter_upwards [hdom] with n hn
    have hmin' := AronowAudit.P013.Wave1.shrinking_minimum_bounds (toSequence S) n (b n) (hmin n hn)
    have hfinite := AronowAudit.P013.Wave1.shrinking_finite_variance_bound (toPopulation (seqPopulation S n)) (Nat.succ_pos n)
      (S.treated n) (S.control n) (S.distinct n) (S.positiveTreated n) (S.positiveControl n)
      (h n) (hh n).1 (hh n).2.1 m (hh n).2.2 A (b n) hA hmin'.1 hmin'.2.1
      (hbA n) hmin'.2.2
    simp only [Nat.cast_add, Nat.cast_one] at hfinite
    change variance (seqLaw S n) (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ _ at hfinite
    simpa only [C, Nat.cast_add, Nat.cast_one] using hfinite
  exact ⟨⟨C,hC,hr⟩, fun ht => AronowAudit.P013.Wave1.shrinking_rate_lower_tail (toSequence S)
    (fun (n : ℕ) => (n+1 : ℝ)*b n) C hr ht⟩

/-- Finite second-moment bound followed by a limit; no cross-size outcome premise is used. -/
theorem uniform_rate (S : ExperimentSequence) (hc3 : ComparisonBounded S)
    (hc5 : Condition5Genuine S) (b : ℝ) (hb : 0 < b) (hj : JointLowerBound S b) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      variance (seqLaw S n) (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ C/(n+1 : ℝ)) ∧
      LowerTailCondition S := by
  obtain ⟨c1,c2,hc1,hc2,hbounds⟩ := hc3
  obtain ⟨m,h,hh⟩ := hc5
  let A : ℝ := max 1 (max c1 c2)
  have hA : 1 ≤ A := le_max_left _ _
  have hc1A : c1 ≤ A := (le_max_left c1 c2).trans (le_max_right _ _)
  have hc2A : c2 ≤ A := (le_max_right c1 c2).trans (le_max_right _ _)
  have hbA : ∀ n i, |(seqPopulation S n).outcome i (S.treated n)| ≤ A ∧
      |(seqPopulation S n).outcome i (S.control n)| ≤ A ∧
      |1 / pi (seqPopulation S n) i (S.treated n)| ≤ A ∧
      |1 / pi (seqPopulation S n) i (S.control n)| ≤ A := by
    intro n i
    exact ⟨(hbounds n i).1.trans hc1A, (hbounds n i).2.1.trans hc1A,
      (hbounds n i).2.2.1.trans hc2A, (hbounds n i).2.2.2.trans hc2A⟩
  let β : ℝ := min b 1
  have hβ : 0 < β := lt_min hb zero_lt_one
  have hβ1 : β ≤ 1 := min_le_right _ _
  have hpos (p : ℝ) (hp : p = 0 ∨ b ≤ p) : 0 < p → β ≤ p := by
    intro hp0
    rcases hp with hp | hp
    · exact False.elim ((ne_of_gt hp0) hp)
    · exact (min_le_left _ _).trans hp
  have hlow : ∀ n i j, i ≠ j →
      (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.treated n) →
        β ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.treated n)) ∧
      (0 < jointPi (seqPopulation S n) i j (S.control n) (S.control n) →
        β ≤ jointPi (seqPopulation S n) i j (S.control n) (S.control n)) ∧
      (0 < jointPi (seqPopulation S n) i j (S.treated n) (S.control n) →
        β ≤ jointPi (seqPopulation S n) i j (S.treated n) (S.control n)) := by
    intro n i j hij
    exact ⟨hpos _ (hj n i j hij).1, hpos _ (hj n i j hij).2.1,
      hpos _ (hj n i j hij).2.2⟩
  let C : ℝ := (1152*A^8*(m+1 : ℝ)^3)/β
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hr : ∀ n, variance (seqLaw S n)
      (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ C/(n+1 : ℝ) := by
    intro n
    have hfinite := AronowAudit.P013.Wave1.shrinking_finite_variance_bound (toPopulation (seqPopulation S n)) (Nat.succ_pos n)
      (S.treated n) (S.control n) (S.distinct n) (S.positiveTreated n) (S.positiveControl n)
      (h n) (hh n).1 (hh n).2.1 m (hh n).2.2 A β hA hβ hβ1 (hbA n) (hlow n)
    have hfinite' : variance (seqLaw S n)
        (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤
        1152*A^8*(m+1 : ℝ)^3/((n+1 : ℝ)*β) := by
      simp only [Nat.cast_add, Nat.cast_one] at hfinite
      change variance (seqLaw S n) (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤ _ at hfinite
      simpa only [Nat.cast_add, Nat.cast_one] using hfinite
    calc
      _ ≤ 1152*A^8*(m+1 : ℝ)^3/((n+1 : ℝ)*β) := hfinite'
      _ = C/(n+1 : ℝ) := by
        dsimp [C]
        rw [div_div, mul_comm β]
  refine ⟨⟨C,hC,Eventually.of_forall hr⟩, ?_⟩
  apply AronowAudit.P013.Wave1.shrinking_rate_lower_tail (toSequence S) (fun (n : ℕ) => (n+1 : ℝ)) C (Eventually.of_forall hr)
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

end
end SAP.P013a.WH.W1
