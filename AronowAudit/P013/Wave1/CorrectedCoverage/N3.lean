import AronowAudit.P013.Wave1.CorrectedCoverageBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.CorrectedCoverage

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Finite centering, score-sum, second-moment and comparison-bound identities. -/
theorem n3_proof : N3 := by
  classical
  intro Ω _ N K P F d e hd he
  have hmean : ∀ i, expectation P (htScore F d e i) = 0 := by
    intro i
    change expectation P (fun z =>
      (indicator F.exposure i d z * (F.outcome i d / pi F i d) -
        indicator F.exposure i e z * (F.outcome i e / pi F i e)) -
      (F.outcome i d - F.outcome i e)) = 0
    rw [expectation_sub, expectation_sub, expectation_mul_const,
      expectation_mul_const, expectation_const]
    change pi F i d * (F.outcome i d / pi F i d) -
      pi F i e * (F.outcome i e / pi F i e) - (F.outcome i d - F.outcome i e) = 0
    rw [mul_div_cancel₀ _ (hd i).1.ne', mul_div_cancel₀ _ (he i).1.ne']
    ring
  have hsum : ∀ z, ∑ i, htScore F d e i z =
      (N : ℝ) * (htEffect F d e z - causalEffect F d e) := by
    intro z
    by_cases hN : N = 0
    · subst N
      simp [htScore, htEffect, causalEffect, potentialMean, potentialTotal, htTotal]
    · have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
      simp only [htScore, Finset.sum_sub_distrib, htEffect, causalEffect,
        potentialMean, potentialTotal, htTotal, mul_sub, mul_div_cancel₀ _ hNr]
  have hsecond : expectation P (fun z => (∑ i, htScore F d e i z) ^ 2) =
      (N : ℝ) ^ 2 * variance P (htEffect F d e) := by
    have hfun : (fun z => (∑ i, htScore F d e i z) ^ 2) =
        (fun z => (N : ℝ) ^ 2 * (htEffect F d e z - causalEffect F d e) ^ 2) := by
      funext z
      rw [hsum z, mul_pow]
    rw [hfun, expectation_const_mul, variance_centered, htEffect_unbiased F d e hd he]
  refine ⟨hmean, hsum, hsecond, ?_⟩
  intro c1 c2 hb i z
  -- These signs follow from the bounds at this unit.
  have hc1 : 0 ≤ c1 := (abs_nonneg (F.outcome i d)).trans (hb i).1
  have hc2 : 0 ≤ c2 := (abs_nonneg (1 / pi F i d)).trans (hb i).2.2.1
  have hterm (a : Fin K) (hy : |F.outcome i a| ≤ c1)
      (hp : |1 / pi F i a| ≤ c2) :
      |indicator F.exposure i a z * (F.outcome i a / pi F i a)| ≤ c1 * c2 := by
    have hdiv : |F.outcome i a / pi F i a| ≤ c1 * c2 := by
      calc
        |F.outcome i a / pi F i a| = |F.outcome i a| * |1 / pi F i a| := by
          simp only [div_eq_mul_inv, abs_mul, abs_one, one_mul]
        _ ≤ c1 * c2 := mul_le_mul hy hp (abs_nonneg _) hc1
    by_cases ha : F.exposure z i = a
    · simpa only [indicator, if_pos ha, one_mul] using hdiv
    · simp only [indicator, if_neg ha, zero_mul, abs_zero]
      exact mul_nonneg hc1 hc2
  let Td : ℝ := indicator F.exposure i d z * (F.outcome i d / pi F i d)
  let Te : ℝ := indicator F.exposure i e z * (F.outcome i e / pi F i e)
  change |(Td - Te) - (F.outcome i d - F.outcome i e)| ≤ 2 * c1 * (c2 + 1)
  calc
    |(Td - Te) - (F.outcome i d - F.outcome i e)| ≤
        |Td - Te| + |F.outcome i d - F.outcome i e| := abs_sub _ _
    _ ≤ (|Td| + |Te|) + (|F.outcome i d| + |F.outcome i e|) :=
      add_le_add (abs_sub _ _) (abs_sub _ _)
    _ ≤ (c1 * c2 + c1 * c2) + (c1 + c1) :=
      add_le_add
        (add_le_add (hterm d (hb i).1 (hb i).2.2.1)
          (hterm e (hb i).2.1 (hb i).2.2.2))
        (add_le_add (hb i).1 (hb i).2.1)
    _ = 2 * c1 * (c2 + 1) := by ring

end

end AronowAudit.P013.Wave1.CorrectedCoverage
