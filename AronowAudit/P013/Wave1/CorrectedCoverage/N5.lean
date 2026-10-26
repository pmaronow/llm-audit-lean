import AronowAudit.P013.Wave1.CorrectedCoverageBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.CorrectedCoverage

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Apply the raw-summand dependency CLT and identify its exact HT normalization. -/
theorem n5_proof : N5 := by
  classical
  intro h1 h3 hbridge S hc3 hc5 hc6
  obtain ⟨c1, c2, hc1, hc2, hb⟩ := hc3
  obtain ⟨c, hc, ht⟩ := hc6
  let μ : ∀ n : ℕ, MeasureTheory.Measure (Fin (S.experiment n).supportSize) :=
    fun n => designMeasure (seqLaw S n)
  letI (n : ℕ) : MeasureTheory.IsProbabilityMeasure (μ n) := (h1 (seqLaw S n)).1
  let X : ∀ n : ℕ, Fin (n + 1) → Fin (S.experiment n).supportSize → ℝ :=
    fun n => htScore (seqPopulation S n) (S.treated n) (S.control n)
  obtain ⟨Dmax, hgraphs⟩ := hbridge S hc5
  choose Dep hdeg using hgraphs
  have hscore (n : ℕ) := h3 (seqPopulation S n) (S.treated n) (S.control n)
    (S.positiveTreated n) (S.positiveControl n)
  let M : ℝ := 2 * c1 * (c2 + 1)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hbound : ∀ n i z, |X n i z| ≤ M := by
    intro n i z
    exact (hscore n).2.2.2 c1 c2 (hb n) i z
  have hmean : ∀ n i, (∫ z, X n i z ∂μ n) = 0 := by
    intro n i
    change (∫ z, htScore (seqPopulation S n) (S.treated n) (S.control n) i z
      ∂designMeasure (seqLaw S n)) = 0
    rw [integral_designMeasure]
    exact (hscore n).1 i
  let v : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ 2 * seqTrueVariance S n
  have hsecond : ∀ n,
      (∫ z, (Causalean.Mathlib.Probability.SteinMethod.depSum (X n) z) ^ 2 ∂μ n) = v n := by
    intro n
    change (∫ z, (∑ i, htScore (seqPopulation S n) (S.treated n) (S.control n) i z) ^ 2
      ∂designMeasure (seqLaw S n)) = ((n + 1 : ℕ) : ℝ) ^ 2 * seqTrueVariance S n
    rw [integral_designMeasure]
    exact (hscore n).2.2.1
  have hfloor0 : ∀ᶠ n : ℕ in atTop, c / 2 ≤ ((n : ℝ) + 1) * seqTrueVariance S n := by
    have hev : ∀ᶠ n : ℕ in atTop, c / 2 < ((n : ℝ) + 1) * seqTrueVariance S n :=
      ht.eventually (lt_mem_nhds (by linarith))
    filter_upwards [hev] with n hn
    exact hn.le
  have hfloor : ∀ᶠ n : ℕ in atTop,
      (c / 2) * (Fintype.card (Fin (n + 1)) : ℝ) ≤ v n := by
    filter_upwards [hfloor0] with n hn
    have hn' : c / 2 ≤ ((n + 1 : ℕ) : ℝ) * seqTrueVariance S n := by
      simpa only [Nat.cast_add, Nat.cast_one] using hn
    simp only [Fintype.card_fin]
    change (c / 2) * ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * seqTrueVariance S n
    calc
      (c / 2) * ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) * (c / 2) := mul_comm _ _
      _ ≤ ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * seqTrueVariance S n) :=
        mul_le_mul_of_nonneg_left hn' (Nat.cast_nonneg _)
      _ = ((n + 1 : ℕ) : ℝ) ^ 2 * seqTrueVariance S n := by ring
  have hcard : Tendsto (fun n : ℕ => Fintype.card (Fin (n + 1))) atTop atTop := by
    simpa only [Fintype.card_fin] using tendsto_add_atTop_nat 1
  intro x
  have hclt := Causalean.Mathlib.Probability.SteinMethod.bounded_degree_dependency_clt
    μ X Dep Dmax hdeg M hM hbound hmean v hsecond (c / 2) (by linarith) hfloor hcard x
  rw [← ProbabilityTheory.cdf_eq_real (ProbabilityTheory.gaussianReal 0 1) x] at hclt
  apply hclt.congr
  intro n
  rw [MeasureTheory.map_measureReal_apply (measurable_of_finite _) measurableSet_Iic]
  change (designMeasure (seqLaw S n)).real
      {z | Causalean.Mathlib.Probability.SteinMethod.depSum (X n) z / Real.sqrt (v n) ≤ x} =
    probability (seqLaw S n)
      (fun z => (seqEstimate S n z - seqTarget S n) / Real.sqrt (seqTrueVariance S n) ≤ x)
  rw [(h1 (seqLaw S n)).2]
  congr 1
  funext z
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt (v n) =
      ((n + 1 : ℕ) : ℝ) * Real.sqrt (seqTrueVariance S n) := by
    dsimp only [v]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  simp only [Causalean.Mathlib.Probability.SteinMethod.depSum, X,
    (hscore n).2.1 z, hsqrt, mul_div_mul_left _ _ hn]

end

end AronowAudit.P013.Wave1.CorrectedCoverage
