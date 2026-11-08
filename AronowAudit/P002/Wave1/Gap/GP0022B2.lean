import AronowAudit.P002.P002_Audit
import AronowAudit.External.Causalean.Experimentation.FinitePopulationMoments
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
Draft dd-GP0022B2. Source inspection only; Lean has not been run.
Record 4: a complete proof draft, with its exact-type check.
Record 6: independent helpers, including the corrected referee contract SH.4.
The missing shared asymptotic coverage layer is described in the run report.
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

/-! ## Record 4: finite design carrier and affine variance -/

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

/-- Exact frozen statement of P002-T29. -/
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

example : type_of% @AronowAudit.P002.neyman_variance := neyman_variance_proof

/-! ## Record 6: independent constant-effect and sparse-filter steps -/

/-- SH.1: a constant receipt effect is the complier average receipt effect. -/
theorem SH_late_constant {n} (P : Population n) (β : ℝ)
    (hc : (compliers P).Nonempty) (hy : ∀ i, P.y i true = P.y i false + β) :
    late P = β := by
  have hcard : ((compliers P).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hc)
  simp [late, groupMean, hy, hcard]

/-- SH.1 at the actual LATE; no compliance-case averaging remains. -/
theorem SH_observedW_baseline {n} (P : Population n)
    (hc : (compliers P).Nonempty)
    (hy : ∃ β, ∀ i, P.y i true = P.y i false + β)
    (S : Finset (Fin n)) : observedW P (late P) S = fun i => P.y i false := by
  rcases hy with ⟨β, hβ⟩
  rw [SH_late_constant P β hc hβ]
  exact constant_effect_adjusted_outcomes P β hβ S

/-- The same baseline is the potential adjusted response in both assignment arms. -/
theorem SH_w_baseline {n} (P : Population n)
    (hc : (compliers P).Nonempty)
    (hy : ∃ β, ∀ i, P.y i true = P.y i false + β) (a : Bool) :
    w P a (late P) = fun i => P.y i false := by
  rcases hy with ⟨β, hβ⟩
  rw [SH_late_constant P β hc hβ]
  funext i
  unfold w
  cases hdi : P.d i a <;> simp [hdi, binary, hβ]

/-- Retain the actual attainable finite quantile in the fixed-baseline reduction. -/
theorem SH_coverage_baseline {n} (P : Population n)
    (hc : (compliers P).Nonempty)
    (hy : ∃ β, ∀ i, P.y i true = P.y i false + β) (α : ℝ) :
    coverage P (late P) α = probability P (fun S =>
      rawAR P (fun i => P.y i false) S ≤
        quantile P (rawAR P (fun i => P.y i false)) α) := by
  unfold coverage accepted
  simp_rw [SH_observedW_baseline P hc hy]

/-- Transfer the actual Theta moment premise to the fixed baseline vector. -/
theorem SH_baseline_moment_bound {n} (P : Population n) (δ r A : ℝ)
    (hP : Theta P δ r A)
    (hy : ∃ β, ∀ i, P.y i true = P.y i false + β) :
    fourthNorm (fun i => P.y i false - mean (fun j => P.y j false)) ≤
      A * Real.sqrt (popVar (fun i => P.y i false)) := by
  rcases hP with ⟨hv, hm, hc, hlo, hhi, hcov, hfourth⟩
  have hh := hfourth true
  unfold v at hh
  rw [SH_w_baseline P hc hy true] at hh
  exact hh

private theorem SH_probability_congr {n} (P : Population n)
    (E F : Finset (Fin n) → Prop)
    (hEF : ∀ S ∈ assignments P, E S ↔ F S) : probability P E = probability P F := by
  unfold probability
  have he : (assignments P).filter E = (assignments P).filter F := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hS, hE⟩
      exact ⟨hS, (hEF S hS).mp hE⟩
    · rintro ⟨hS, hF⟩
      exact ⟨hS, (hEF S hS).mpr hF⟩
  rw [he]

private theorem SH_probability_mono {n} (P : Population n)
    (E F : Finset (Fin n) → Prop)
    (hEF : ∀ S ∈ assignments P, E S → F S) : probability P E ≤ probability P F := by
  unfold probability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (assignments P).filter E ⊆
      (assignments P).filter F from by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hS, hE⟩
    exact Finset.mem_filter.mpr ⟨hS, hEF S hS hE⟩)

/-- Finite-support UC.4/SH.3 bracket, including an upper endpoint not itself attained.
This uses precisely the attainable-minimum quantile in P002, with no change to ties. -/
theorem SH_quantile_bracket {n} (P : Population n) (hP : ValidDesign P)
    (g : Finset (Fin n) → ℝ≥0∞) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (a b : ℝ≥0∞)
    (ha : probability P (fun S => g S ≤ a) < 1 - α)
    (hb : 1 - α ≤ probability P (fun S => g S ≤ b)) :
    a < quantile P g α ∧ quantile P g α ≤ b := by
  have hlower : a < quantile P g α := by
    by_contra hnot
    have hqa : quantile P g α ≤ a := le_of_not_gt hnot
    have hm : probability P (fun S => g S ≤ quantile P g α) ≤
        probability P (fun S => g S ≤ a) := by
      apply SH_probability_mono
      intro S hS hSq
      exact hSq.trans hqa
    have hv := quantile_valid P hP g α hα
    linarith
  let B := (assignments P).filter (fun S => g S ≤ b)
  have hB : B.Nonempty := by
    by_contra hnot
    have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hpzero : probability P (fun S => g S ≤ b) = 0 := by
      unfold probability
      change (B.card : ℝ) / ((assignments P).card : ℝ) = 0
      rw [he]
      simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    rw [hpzero] at hb
    linarith [hα.2]
  let L := B.image g
  have hL : L.Nonempty := hB.image g
  let t := L.max' hL
  have htL : t ∈ L := Finset.max'_mem L hL
  have htb : t ≤ b := by
    rcases Finset.mem_image.mp htL with ⟨S, hS, hgt⟩
    rw [← hgt]
    exact (Finset.mem_filter.mp hS).2
  have hCDF : probability P (fun S => g S ≤ t) =
      probability P (fun S => g S ≤ b) := by
    apply SH_probability_congr
    intro S hS
    constructor
    · exact fun hSt => hSt.trans htb
    · intro hSb
      have hSB : S ∈ B := Finset.mem_filter.mpr ⟨hS, hSb⟩
      exact Finset.le_max' L (g S) (Finset.mem_image.mpr ⟨S, hSB, rfl⟩)
  let C := ((assignments P).image g).filter (fun z =>
    1 - α ≤ probability P (fun S => g S ≤ z))
  have htC : t ∈ C := by
    apply Finset.mem_filter.mpr
    constructor
    · rcases Finset.mem_image.mp htL with ⟨S, hS, hgt⟩
      exact Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1, hgt⟩
    · rw [hCDF]
      exact hb
  have hC : C.Nonempty := ⟨t, htC⟩
  have hqt : quantile P g α ≤ t := by
    change (if h : C.Nonempty then C.min' h else ⊤) ≤ t
    rw [dif_pos hC]
    exact Finset.min'_le C t htC
  exact ⟨hlower, hqt.trans htb⟩

/-- SH.3: continuous-law CDF bracketing gives nominal probability at the actual
finite quantile. This is a generic analytic lemma, not an assumption that the
constant-effect population sequence has the required CDF limit. -/
theorem SH_nominal_of_cdf_limits (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j))
    (g : ∀ j, Finset (Fin (sizes j)) → ℝ≥0∞)
    (hP : ∀ j, ValidDesign (P j)) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (H : ℝ → ℝ)
    (hCDF : ∀ t : ℝ, 0 < t → Tendsto (fun j =>
      probability (P j) (fun S => g j S ≤ ENNReal.ofReal t)) atTop (nhds (H t)))
    (hbracket : ∀ ε : ℝ, 0 < ε → ∃ a b : ℝ,
      0 < a ∧ 0 < b ∧ H a < 1 - α ∧ 1 - α < H b ∧ H b < 1 - α + ε) :
    Tendsto (fun j => probability (P j) (fun S =>
      g j S ≤ quantile (P j) (g j) α)) atTop (nhds (1 - α)) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    exact Eventually.of_forall (fun j =>
      hx.trans_le (quantile_valid (P j) (hP j) (g j) α hα))
  · intro x hx
    rcases hbracket (x - (1 - α)) (sub_pos.mpr hx) with
      ⟨a, b, ha, hb, hHa, hHb, hHbx⟩
    have hl : ∀ᶠ j in atTop,
        probability (P j) (fun S => g j S ≤ ENNReal.ofReal a) < 1 - α :=
      (tendsto_order.1 (hCDF a ha)).2 _ hHa
    have hu : ∀ᶠ j in atTop,
        1 - α < probability (P j) (fun S => g j S ≤ ENNReal.ofReal b) :=
      (tendsto_order.1 (hCDF b hb)).1 _ hHb
    have hHx : H b < x := by linarith only [hHbx]
    have hxevent : ∀ᶠ j in atTop,
        probability (P j) (fun S => g j S ≤ ENNReal.ofReal b) < x :=
      (tendsto_order.1 (hCDF b hb)).2 _ hHx
    filter_upwards [hl, hu, hxevent] with j hlj huj hxj
    have hq : quantile (P j) (g j) α ≤ ENNReal.ofReal b :=
      (SH_quantile_bracket (P j) (hP j) (g j) α hα
        (ENNReal.ofReal a) (ENNReal.ofReal b) hlj huj.le).2
    have hp : probability (P j) (fun S => g j S ≤ quantile (P j) (g j) α) ≤
        probability (P j) (fun S => g j S ≤ ENNReal.ofReal b) := by
      apply SH_probability_mono
      intro S hS hg
      exact hg.trans hq
    exact hp.trans_lt hxj

/-- The absolute-standard-normal CDF at positive arguments. -/
def SH_absNormalCDF (t : ℝ) : ℝ :=
  2 * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t - 1

/-- The exact bracketing premise used by SH.3 for the absolute normal law.
Surjectivity of the normal CDF avoids a separate epsilon/delta cutoff argument. -/
theorem SH_normal_bracket (α : ℝ) (hα : 0 < α ∧ α < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ SH_absNormalCDF a < 1 - α ∧
      1 - α < SH_absNormalCDF b ∧ SH_absNormalCDF b < 1 - α + ε := by
  letI : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  let d : ℝ := min (α / 4) (ε / 4)
  have hd0 : 0 < d := lt_min (by linarith [hα.1]) (by linarith)
  have hdα : d ≤ α / 4 := min_le_left _ _
  have hdε : d ≤ ε / 4 := min_le_right _ _
  obtain ⟨a, ha⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (ProbabilityTheory.gaussianReal 0 1) (p := (3 : ℝ) / 4 - α / 4)
    (by linarith [hα.2]) (by linarith [hα.1])
  obtain ⟨b, hb⟩ := AronowAudit.P053.NormalCompletion.exists_cdf_eq
    (ProbabilityTheory.gaussianReal 0 1) (p := 1 - α / 2 + d)
    (by linarith [hα.2]) (by linarith [hα.1])
  have ha0 : 0 < a := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [AronowAudit.P053.NormalCompletion.normal_cdf_zero, ha]
    linarith [hα.2]
  have hb0 : 0 < b := by
    apply AronowAudit.P053.NormalCompletion.strictMono_normal_cdf.lt_iff_lt.mp
    rw [AronowAudit.P053.NormalCompletion.normal_cdf_zero, hb]
    linarith [hα.2]
  refine ⟨a, b, ha0, hb0, ?_, ?_, ?_⟩
  · unfold SH_absNormalCDF
    rw [ha]
    linarith [hα.2]
  · unfold SH_absNormalCDF
    rw [hb]
    linarith
  · unfold SH_absNormalCDF
    rw [hb]
    linarith

/-- All of SH.1/SH.3 and the ENNReal conversion, conditional only on the
studentized CDF limit that SH.2 must independently establish. -/
theorem SH_constant_nominal_of_cdf (sizes : ℕ → ℕ) (P : ∀ j, Population (sizes j))
    (δ r A α : ℝ) (hα : 0 < α ∧ α < 1) (hP : ∀ j, Theta (P j) δ r A)
    (hconstant : ∀ j, ∃ β, ∀ i, (P j).y i true = (P j).y i false + β)
    (hCDF : ∀ t : ℝ, 0 < t → Tendsto (fun j => probability (P j)
      (fun S => rawAR (P j) (fun i => (P j).y i false) S ≤ ENNReal.ofReal t))
      atTop (nhds (SH_absNormalCDF t))) :
    Tendsto (fun j => ENNReal.ofReal (coverage (P j) (late (P j)) α))
      atTop (nhds (ENNReal.ofReal (1 - α))) := by
  have hnom := SH_nominal_of_cdf_limits sizes P
    (fun j => rawAR (P j) (fun i => (P j).y i false))
    (fun j => (hP j).1) α hα SH_absNormalCDF hCDF
    (fun ε hε => SH_normal_bracket α hα ε hε)
  have hfun : (fun j => coverage (P j) (late (P j)) α) =
      (fun j => probability (P j) (fun S =>
        rawAR (P j) (fun i => (P j).y i false) S ≤
          quantile (P j) (rawAR (P j) (fun i => (P j).y i false)) α)) := by
    funext j
    exact SH_coverage_baseline (P j) (hP j).2.2.1 (hconstant j) α
  apply ENNReal.tendsto_ofReal
  rw [hfun]
  exact hnom

/-- SH.4, corrected as required by both referees.
The lower bound is explicitly by the SAME q as the sequential upper limit.
In particular, mere boundedness below of the full liminf is not a premise here. -/
theorem SH_sparse_liminf (E : Set ℕ) (a : ℕ → ℝ≥0∞) (q : ℝ≥0∞)
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes) (hE : ∀ j, sizes j ∈ E)
    (b : ℕ → ℝ≥0∞)
    (hlower : q ≤ Filter.liminf a (atTop ⊓ Filter.principal E))
    (hab : ∀ j, a (sizes j) ≤ b j) (hb : Tendsto b atTop (nhds q)) :
    Filter.liminf a (atTop ⊓ Filter.principal E) = q := by
  have hs : Tendsto sizes atTop (atTop ⊓ Filter.principal E) := by
    apply tendsto_inf.2
    refine ⟨hsizes.tendsto_atTop, ?_⟩
    exact tendsto_principal.2 (Eventually.of_forall hE)
  have hsub : Filter.liminf a (atTop ⊓ Filter.principal E) ≤
      Filter.liminf (a ∘ sizes) atTop := hs.liminf_le_liminf_comp
  have hbound : Filter.liminf (a ∘ sizes) atTop ≤ Filter.liminf b atTop := by
    exact Filter.liminf_le_liminf (Eventually.of_forall hab)
  apply le_antisymm
  · exact hsub.trans (hbound.trans_eq hb.liminf_eq)
  · exact hlower

/-- The nested beta/model infimum is bounded above by any admissible model. -/
theorem SH_infCoverage_le {n} (P : Population n) (δ r A α : ℝ)
    (hP : Theta P δ r A) :
    infCoverageTheta n δ r A α ≤ ENNReal.ofReal (coverage P (late P) α) := by
  unfold infCoverageTheta
  exact (iInf_le_of_le (late P)
    (iInf_le_of_le (⟨P, hP, rfl⟩ : {Q : Population n // Theta Q δ r A ∧ late Q = late P})
      le_rfl))

/-- SH.5's order-theoretic assembly. The two substantive statistical inputs are
explicit here; this helper does not claim the frozen unconditional theorem. -/
theorem SH_liminf_from_coverage (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (δ r A α : ℝ)
    (hP : ∀ j, Theta (P j) δ r A)
    (hlower : ENNReal.ofReal (1 - α) ≤ Filter.liminf
      (fun N => infCoverageTheta N δ r A α)
      (atTop ⊓ Filter.principal {N | ∃ Q : Population N, Theta Q δ r A}))
    (hseq : Tendsto (fun j => ENNReal.ofReal (coverage (P j) (late (P j)) α))
      atTop (nhds (ENNReal.ofReal (1 - α)))) :
    Filter.liminf (fun N => infCoverageTheta N δ r A α)
      (atTop ⊓ Filter.principal {N | ∃ Q : Population N, Theta Q δ r A}) =
        ENNReal.ofReal (1 - α) := by
  apply SH_sparse_liminf _ _ _ sizes hsizes
    (fun j => (⟨P j, hP j⟩ : ∃ Q : Population (sizes j), Theta Q δ r A))
    (fun j => ENNReal.ofReal (coverage (P j) (late (P j)) α)) hlower
  · intro j
    exact SH_infCoverage_le (P j) δ r A α (hP j)
  · exact hseq

/- The final corrected_remark3_sharpness_proof and its exact-type example are
intentionally not asserted: SH.2 needs the independently proved UC.3 CDF limit,
and SH.5 needs UC.9's full-class lower bound. The required statistical layer is absent in this
worktree. The held declarations are not used to fill those missing proofs.
See /Users/pmaronow/lean-work/runs/dd-GP0022B2/REPORT.md. -/

end
end AronowAudit.P002.Wave1
