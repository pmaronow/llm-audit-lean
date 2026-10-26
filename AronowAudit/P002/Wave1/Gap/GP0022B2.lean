import AronowAudit.P002.P002_Audit
import AronowAudit.External.Causalean.Experimentation.FinitePopulationMoments
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
Finite design averages, affine variances, and the two-potential-response
contrast variance identity (P002-T29).
-/
namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/-! ## Finite design carrier and affine variance -/

private theorem NV_mem_assignments {n} (P : Population n) (S : Finset (Fin n)) :
    S ∈ assignments P ↔ S.card = P.n1 := by
  simp only [assignments, Finset.mem_powersetCard, Finset.subset_univ, true_and]

/-- This equality is independent of the validity/nonemptiness of the design. -/
theorem NV_sum_carrier {n} (P : Population n) (f : Finset (Fin n) → ℝ) :
    (∑ S ∈ assignments P, f S) =
      ∑ S : {S : Finset (Fin n) // S.card = P.n1}, f S.val := by
  exact Finset.sum_subtype (assignments P) (NV_mem_assignments P) f

/-- Uniform finite averages on the two representations of the assignment space. -/
theorem NV_expectation_carrier {n} (P : Population n) (h : ValidDesign P)
    (f : Finset (Fin n) → ℝ) :
    expectation P f =
      (Causalean.Experimentation.DesignBased.completeRandomization (V := Fin n) P.n1
        (by simpa only [Fintype.card_fin] using Nat.le_of_lt h.2.2)).E
        (fun S => f S.val) := by
  have hcard : (assignments P).card =
      Fintype.card {S : Finset (Fin n) // S.card = P.n1} := by
    rw [Causalean.Experimentation.DesignBased.completeRandomization_card]
    simp only [assignments, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  unfold expectation Causalean.Experimentation.DesignBased.FiniteDesign.E
  rw [hcard, NV_sum_carrier]
  simp only [Causalean.Experimentation.DesignBased.completeRandomization,
    ← Finset.mul_sum, one_div]
  ring

/-- Transport of the actual centered finite variance, not a formula-defined variance. -/
theorem NV_variance_carrier {n} (P : Population n) (h : ValidDesign P)
    (f : Finset (Fin n) → ℝ) :
    designVariance P f =
      (Causalean.Experimentation.DesignBased.completeRandomization (V := Fin n) P.n1
        (by simpa only [Fintype.card_fin] using Nat.le_of_lt h.2.2)).Var
        (fun S => f S.val) := by
  unfold designVariance Causalean.Experimentation.DesignBased.FiniteDesign.Var
  rw [NV_expectation_carrier P h f, NV_expectation_carrier P h]

private theorem NV_expectation_congr {n} (P : Population n)
    {f g : Finset (Fin n) → ℝ} (hfg : ∀ S ∈ assignments P, f S = g S) :
    expectation P f = expectation P g := by
  unfold expectation
  congr 1
  exact Finset.sum_congr rfl hfg

/-- Equality is needed only on the actual finite support. -/
theorem NV_variance_congr {n} (P : Population n)
    {f g : Finset (Fin n) → ℝ} (hfg : ∀ S ∈ assignments P, f S = g S) :
    designVariance P f = designVariance P g := by
  have he : expectation P f = expectation P g := NV_expectation_congr P hfg
  unfold designVariance
  rw [he]
  apply NV_expectation_congr
  intro S hS
  rw [hfg S hS]

/-- Both zero scales and nonzero intercept shifts are included. -/
theorem NV_variance_affine {n} (P : Population n) (h : ValidDesign P)
    (f : Finset (Fin n) → ℝ) (c d : ℝ) :
    designVariance P (fun S => c * f S - d) = c ^ 2 * designVariance P f := by
  have he : expectation P (fun S => c * f S - d) = c * expectation P f - d := by
    rw [expectation_sub, expectation_mul, expectation_const P h]
  unfold designVariance
  rw [he]
  calc
    expectation P (fun S => (c * f S - d - (c * expectation P f - d)) ^ 2) =
        expectation P (fun S => c ^ 2 * (f S - expectation P f) ^ 2) := by
      apply NV_expectation_congr
      intro S hS
      ring
    _ = c ^ 2 * expectation P (fun S => (f S - expectation P f) ^ 2) :=
      expectation_mul P _ _

/-- The vendored SRS result, transported to P002's finite assignment average. -/
theorem NV_groupMean_variance {n} (P : Population n) (h : ValidDesign P)
    (q : Fin n → ℝ) :
    designVariance P (fun S => groupMean S q) =
      (1 / (P.n1 : ℝ) - 1 / (n : ℝ)) * popVar q := by
  rw [NV_variance_carrier P h]
  have hfun :
      (fun S : {S : Finset (Fin n) // S.card = P.n1} => groupMean S.val q) =
      Causalean.Experimentation.FinitePopulationMoments.sampleMean P.n1 q := by
    funext S
    simp only [groupMean, S.property,
      Causalean.Experimentation.FinitePopulationMoments.sampleMean]
    congr 1
    simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hfun]
  have hv := Causalean.Experimentation.FinitePopulationMoments.Var_sampleMean
    (U := Fin n) P.n1
    (by simpa only [Fintype.card_fin] using Nat.le_of_lt h.2.2)
    h.2.1 (by simpa only [Fintype.card_fin] using h.1) q
  simpa only [Causalean.Experimentation.FinitePopulationMoments.popVar,
    Causalean.Experimentation.FinitePopulationMoments.popMean,
    Fintype.card_fin, popVar, mean] using hv

/-! The remaining identities are finite-sum algebra over arbitrary potential vectors. -/

private theorem NV_mean_add_mul {n} (a b : Fin n → ℝ) (t : ℝ) :
    mean (fun i => a i + t * b i) = mean a + t * mean b := by
  simp only [mean, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem NV_mean_sub {n} (a b : Fin n → ℝ) :
    mean (fun i => a i - b i) = mean a - mean b := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

/-- Population variance with its exact P002 divisor n-1. -/
theorem NV_popVar_add_mul {n} (a b : Fin n → ℝ) (t : ℝ) :
    popVar (fun i => a i + t * b i) =
      popVar a + 2 * t * popCov a b + t ^ 2 * popVar b := by
  have hpoint (i : Fin n) :
      (a i + t * b i - (mean a + t * mean b)) ^ 2 =
      (a i - mean a) ^ 2 + 2 * t * ((a i - mean a) * (b i - mean b)) +
        t ^ 2 * (b i - mean b) ^ 2 := by ring
  unfold popVar
  rw [NV_mean_add_mul]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, popCov]
  ring

private theorem NV_popVar_sub {n} (a b : Fin n → ℝ) :
    popVar (fun i => a i - b i) = popVar a + popVar b - 2 * popCov a b := by
  have hf : (fun i => a i - b i) = (fun i => a i + (-1 : ℝ) * b i) := by
    funext i
    ring
  rw [hf, NV_popVar_add_mul]
  ring

/-- A two-potential-response contrast as an affine SRS mean, on the support. -/
theorem NV_contrast_as_mean {n} (P : Population n) (h : ValidDesign P)
    (a b : Fin n → ℝ) (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    groupMean S a - groupMean Sᶜ b =
      groupMean S (fun i => a i + (P.n1 : ℝ) / controlSize P * b i) -
        (n : ℝ) / controlSize P * mean b := by
  have hScard : S.card = P.n1 := (NV_mem_assignments P S).mp hS
  have hCcard : ((Sᶜ).card : ℝ) = controlSize P := by
    simp only [Finset.card_compl, Fintype.card_fin, hScard]
    rw [Nat.cast_sub (Nat.le_of_lt h.2.2)]
    rfl
  have hm : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.2.1)
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < n by have := h.1; omega))
  have hc : controlSize P ≠ 0 := by
    have hmn : (P.n1 : ℝ) < n := by exact_mod_cast h.2.2
    unfold controlSize
    linarith
  have hsplit : (∑ i ∈ S, b i) + (∑ i ∈ Sᶜ, b i) = ∑ i, b i :=
    Finset.sum_add_sum_compl S b
  have hcomp : (∑ i ∈ Sᶜ, b i) = (∑ i, b i) - ∑ i ∈ S, b i := by
    linarith only [hsplit]
  unfold groupMean mean
  rw [hScard, hCcard]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hcomp]
  field_simp [hm, hc, hn]
  <;> ring

/-- Generic Neyman identity; reusable for oracle statistics with fixed coefficients. -/
theorem NV_contrast_variance {n} (P : Population n) (h : ValidDesign P)
    (a b : Fin n → ℝ) :
    designVariance P (fun S => groupMean S a - groupMean Sᶜ b) =
      popVar a / (P.n1 : ℝ) + popVar b / controlSize P -
        popVar (fun i => a i - b i) / (n : ℝ) := by
  have hm : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.2.1)
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < n by have := h.1; omega))
  have hc : controlSize P ≠ 0 := by
    have hmn : (P.n1 : ℝ) < n := by exact_mod_cast h.2.2
    unfold controlSize
    linarith
  calc
    designVariance P (fun S => groupMean S a - groupMean Sᶜ b) =
        designVariance P (fun S =>
          (1 : ℝ) * groupMean S (fun i => a i + (P.n1 : ℝ) / controlSize P * b i) -
            (n : ℝ) / controlSize P * mean b) := by
      apply NV_variance_congr
      intro S hS
      simpa only [one_mul] using NV_contrast_as_mean P h a b S hS
    _ = designVariance P
        (fun S => groupMean S (fun i => a i + (P.n1 : ℝ) / controlSize P * b i)) := by
      rw [NV_variance_affine P h]
      simp only [one_pow, one_mul]
    _ = _ := by
      rw [NV_groupMean_variance P h, NV_popVar_add_mul, NV_popVar_sub]
      unfold controlSize at *
      field_simp [hm, hn, hc]
      <;> ring

/-- Convert the observed-outcome statistic to the potential-response contrast. -/
theorem NV_tau_as_contrast {n} (P : Population n) (h : ValidDesign P)
    (β : ℝ) (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    tau P β S = fraction P * (1 - fraction P) *
      (groupMean S (w P true β) - groupMean Sᶜ (w P false β)) := by
  have hScard : S.card = P.n1 := (NV_mem_assignments P S).mp hS
  have hCcard : ((Sᶜ).card : ℝ) = controlSize P := by
    simp only [Finset.card_compl, Fintype.card_fin, hScard]
    rw [Nat.cast_sub (Nat.le_of_lt h.2.2)]
    rfl
  have hm : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h.2.1)
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < n by have := h.1; omega))
  have hc : controlSize P ≠ 0 := by
    have hmn : (P.n1 : ℝ) < n := by exact_mod_cast h.2.2
    unfold controlSize
    linarith
  have hpoint (i : Fin n) :
      observedW P β S i * ((if i ∈ S then 1 else 0) - fraction P) =
        (if i ∈ S then (1 - fraction P) * w P true β i else 0) +
          (if i ∈ Sᶜ then -fraction P * w P false β i else 0) := by
    by_cases hi : i ∈ S
    · simp [observedW, observedY, observedD, w, hi]
      <;> ring
    · simp [observedW, observedY, observedD, w, hi]
      <;> ring
  unfold tau rawTau
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    ← Finset.mul_sum]
  unfold groupMean
  rw [hScard, hCcard]
  unfold fraction controlSize at *
  field_simp [hm, hn, hc]
  <;> ring

/-- Statement of P002-T29. -/
theorem neyman_variance_proof {n} (P : Population n) (h : ValidDesign P) (β : ℝ) :
    designVariance P (tau P β) = S2 P β true / (P.n1 : ℝ) +
      S2 P β false / controlSize P - Sdiff2 P β / (n : ℝ) := by
  have hscaled : designVariance P (tau P β) =
      (fraction P * (1 - fraction P)) ^ 2 *
        designVariance P (fun S => groupMean S (w P true β) -
          groupMean Sᶜ (w P false β)) := by
    calc
      _ = designVariance P (fun S =>
          (fraction P * (1 - fraction P)) *
            (groupMean S (w P true β) - groupMean Sᶜ (w P false β)) - 0) := by
        apply NV_variance_congr
        intro S hS
        simpa only [sub_zero] using NV_tau_as_contrast P h β S hS
      _ = _ := NV_variance_affine P h _ _ 0
  have hdiff : popVar (fun i => w P true β i - w P false β i) =
      (∑ i, (v P true β i - v P false β i) ^ 2) / ((n : ℝ) - 1) := by
    unfold popVar
    rw [NV_mean_sub]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    unfold v
    ring
  rw [hscaled, NV_contrast_variance P h, hdiff]
  unfold S2 Sdiff2
  ring




/-- The absolute-standard-normal CDF at positive arguments. -/
def SH_absNormalCDF (t : ℝ) : ℝ :=
  2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t - 1




end
end AronowAudit.P002.Wave1
