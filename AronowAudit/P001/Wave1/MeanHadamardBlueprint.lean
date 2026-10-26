import AronowAudit.P001.P001_Foundations

/-!
# Counterexample to mean Hadamard differentiability (P001-T118)

Finite second moment alone does not make `cdfMeanFunctional` Hadamard differentiable
at every embedded CDF in `KolmogorovSpace`, with its sup norm, on the domain of
finite-second-moment CDFs with all bounded tangent directions.
`Target` is the negation of this universal assertion.

The base law is `ν₀ = (δ₀ + δ₂)/2`, with mean `1` and variance `1`.
For `r_n = n + 2`, `a_n = r_n⁻³`, and `t_n = r_n⁻²`, the finite-support contamination
`ν_n = (1 - a_n) ν₀ + a_n δ_{r_n + 1}` has mean `1 + t_n`, and its CDF differs from that of
`ν₀` by at most `a_n` in sup norm. The directions `h_n = t_n⁻¹ (F_n - F)` have norm
`≤ 1/r_n → 0`, and `F + t_n h_n = F_n` lies in the domain. Every mean difference quotient
equals `1`, whereas a Hadamard derivative would force the limit `L 0 = 0`.

The intermediate statements identify the functional with the actual law's mean,
construct the contamination laws, and bound the sup norm.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.MeanHadamard

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

/-- Negation of the universal assertion. -/
def Target : Prop :=
  ¬ ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], MemLp id 2 ν →
    ∃ L : KolmogorovSpace →L[ℝ] ℝ,
      HadamardAt {F | finiteSecondCDF F} Set.univ cdfMeanFunctional
        (kolmogorovEmbed (cdf ν id)) L

/-- The base law `ν₀ = (δ₀ + δ₂)/2`. -/
def baseLaw : Measure ℝ :=
  (1/2 : ℝ≥0∞) • Measure.dirac (0 : ℝ) + (1/2 : ℝ≥0∞) • Measure.dirac (2 : ℝ)

/-- `r_n = n + 2`. -/
def contR (n : ℕ) : ℝ := (n : ℝ) + 2

/-- The contamination weight `a_n = r_n⁻³`. -/
def contA (n : ℕ) : ℝ := (contR n)⁻¹ ^ 3

/-- The scale `t_n = r_n⁻²`. -/
def contT (n : ℕ) : ℝ := (contR n)⁻¹ ^ 2

/-- The contaminated law `ν_n = (1 - a_n) ν₀ + a_n δ_{r_n + 1}`. -/
def contam (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - contA n) • baseLaw + ENNReal.ofReal (contA n) • Measure.dirac (contR n + 1)

/-- The embedded base CDF `F`. -/
def baseCDF : KolmogorovSpace := kolmogorovEmbed (cdf baseLaw id)

/-- The embedded contaminated CDF `F_n`. -/
def contCDF (n : ℕ) : KolmogorovSpace := kolmogorovEmbed (cdf (contam n) id)

/-- The tangent directions `h_n = t_n⁻¹ (F_n - F)`. -/
def dirSeq (n : ℕ) : KolmogorovSpace := (contT n)⁻¹ • (contCDF n - baseCDF)

/-- For a probability law with finite second moment, its embedded CDF lies in
`finiteSecondCDF` and `cdfMeanFunctional` returns its mean. -/
def N1 : Prop :=
  ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], MemLp id 2 ν →
    finiteSecondCDF (kolmogorovEmbed (cdf ν id)) ∧
      cdfMeanFunctional (kolmogorovEmbed (cdf ν id)) = mean ν id

/-- The base and contamination laws are probability measures with finite second
moments and means `1` and `1 + contT n`, respectively. -/
def N2 : Prop :=
  IsProbabilityMeasure baseLaw ∧ MemLp id 2 baseLaw ∧ mean baseLaw id = 1 ∧
    ∀ n : ℕ, IsProbabilityMeasure (contam n) ∧ MemLp id 2 (contam n) ∧
      mean (contam n) id = 1 + contT n

/-- Under `N2`, the directions have sup norm at most `(contR n)⁻¹`. -/
def N3 : Prop :=
  N2 → ∀ n : ℕ, ‖dirSeq n‖ ≤ (contR n)⁻¹

theorem contR_pos (n : ℕ) : 0 < contR n := by unfold contR; positivity

theorem contT_pos (n : ℕ) : 0 < contT n := by
  unfold contT; have := contR_pos n; positivity

theorem tendsto_contR_inv : Tendsto (fun n : ℕ => (contR n)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => contR n) atTop atTop := by
    unfold contR
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp h

theorem tendsto_contT : Tendsto contT atTop (𝓝 0) := by
  have h := tendsto_contR_inv.pow 2
  rw [zero_pow two_ne_zero] at h
  exact h

/-- `F + t_n h_n = F_n`. -/
theorem base_add_dir (n : ℕ) : baseCDF + contT n • dirSeq n = contCDF n := by
  simp only [dirSeq, smul_smul, mul_inv_cancel₀ (contT_pos n).ne', one_smul,
    add_sub_cancel]

/-- The admissible sequences converge to the zero tangent while every mean
difference quotient equals `1`, contradicting the required limit `L 0 = 0`. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) : Target := by
  intro H
  have hp0 : IsProbabilityMeasure baseLaw := h2.1
  obtain ⟨L, hL⟩ := H baseLaw h2.2.1
  have hh : Tendsto dirSeq atTop (𝓝 0) :=
    squeeze_zero_norm (h3 h2) tendsto_contR_inv
  have hmem : ∀ n, baseCDF + contT n • dirSeq n ∈ {F | finiteSecondCDF F} := by
    intro n
    rw [base_add_dir]
    have := (h2.2.2.2 n).1
    exact (h1 (contam n) (h2.2.2.2 n).2.1).1
  have key := hL 0 (Set.mem_univ _) contT dirSeq contT_pos tendsto_contT hh hmem
  have hq : ∀ n : ℕ, (cdfMeanFunctional (baseCDF + contT n • dirSeq n) -
      cdfMeanFunctional baseCDF) / contT n = 1 := by
    intro n
    rw [base_add_dir]
    have := (h2.2.2.2 n).1
    have e1 : cdfMeanFunctional (contCDF n) = 1 + contT n :=
      ((h1 (contam n) (h2.2.2.2 n).2.1).2).trans (h2.2.2.2 n).2.2
    have e0 : cdfMeanFunctional baseCDF = 1 :=
      ((h1 baseLaw h2.2.1).2).trans h2.2.2.1
    rw [e1, e0, add_sub_cancel_left, div_self (contT_pos n).ne']
  have key' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (L 0)) := Tendsto.congr hq key
  rw [map_zero] at key'
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds key')

end

end AronowAudit.P001.Wave1.MeanHadamard
