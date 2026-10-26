/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedClass
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.MaximalBernstein
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.MaximalOrlicz
import Mathlib.Probability.IdentDistrib

/-!
# Bounds used in empirical-process chaining

This module retains two results: `tight_chain_level_bound_uniform` bounds the
expected supremum of a finite class at a prescribed scale, with a constant chosen
before the class, scale and sample size; `tendsto_envelope_tail_const_threshold`
shows that the scaled tail of a square-integrable envelope tends to zero.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §19.6.
-/

set_option linter.style.longFile 2500

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]


/-! ### A uniform bound for a finite class and envelope-tail convergence -/


/-- A uniform bound for the expected supremum of a finite empirical-process class.
The constant is chosen before the class, scale and sample size. The proof applies
`finite_sup_bound_uniform` with the stated envelope and second-moment bounds,
then combines its two terms into a single bound. -/
lemma tight_chain_level_bound_uniform
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι : Type*} [Fintype ι] [Nonempty ι]
        (g : ι → Ω → ℝ), (∀ i, Measurable (g i)) →
        ∀ {ε : ℝ}, 0 < ε → ∀ (n : ℕ), 1 ≤ n →
          (∀ i ω, |g i ω| ≤
            Real.sqrt n * ε / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))) →
          (∀ i, ∫ ω, (g i ω) ^ 2 ∂P ≤ (2 * ε) ^ 2) →
            ∫⁻ ω, ENNReal.ofReal
                (⨆ i : ι, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ
              ≤ ENNReal.ofReal
                  (K * ε * Real.sqrt (Real.log (1 + Fintype.card ι))) := by
  -- Obtain the uniform `finite_sup_bound_uniform` constant once; the
  -- chaining constant is `3 ·` that, hoisted before the class / scale / `n` args.
  obtain ⟨K, hK_pos, h_fsb⟩ :=
    finite_sup_bound_uniform P hX_meas hX_iindep hX_idem hX_law
  refine ⟨3 * K, by positivity, ?_⟩
  intro ι _ _ g hg_meas ε hε n hn hg_bdd hg_var
  -- Numerical preliminaries.
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsn_nn : 0 ≤ Real.sqrt n := hsn_pos.le
  have hN_pos_nat : 0 < Fintype.card ι := Fintype.card_pos
  have hN_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hN_pos_nat
  have hL_nn : 0 ≤ Real.log (1 + Fintype.card ι) :=
    Real.log_nonneg (by linarith)
  have hsL_nn : 0 ≤ Real.sqrt (Real.log (1 + Fintype.card ι)) :=
    Real.sqrt_nonneg _
  have h1psL_pos : (0 : ℝ) < 1 + Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    linarith
  have hM_nn : 0 ≤ Real.sqrt n * ε
      / (1 + Real.sqrt (Real.log (1 + Fintype.card ι))) := by positivity
  have hσ_nn : (0 : ℝ) ≤ 2 * ε := by positivity
  -- Apply the uniform finite-sup bound with the truncation `M`/`σ`.
  have h_bnd := h_fsb g hg_meas hM_nn hσ_nn hg_bdd hg_var n hn
  refine h_bnd.trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  -- Combine the envelope and second-moment terms.
  have hM_div_sqrt :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        = ε * Real.log (1 + Fintype.card ι)
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι))) := by
    field_simp
  have hLog_div_le :
      Real.log (1 + Fintype.card ι)
          / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
        ≤ Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    rw [div_le_iff₀ h1psL_pos]
    have hsq : Real.sqrt (Real.log (1 + Fintype.card ι))
              * Real.sqrt (Real.log (1 + Fintype.card ι))
            = Real.log (1 + Fintype.card ι) :=
      Real.mul_self_sqrt hL_nn
    nlinarith [hsq, hsL_nn, hL_nn]
  have hM_term_le :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        ≤ ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    rw [hM_div_sqrt, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hLog_div_le hε.le
  have h_sum_le :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        + 2 * ε * Real.sqrt (Real.log (1 + Fintype.card ι))
        ≤ 3 * ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    linarith [hM_term_le]
  calc K * (Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
              * Real.log (1 + Fintype.card ι) / Real.sqrt n
            + 2 * ε * Real.sqrt (Real.log (1 + Fintype.card ι)))
      ≤ K * (3 * ε * Real.sqrt (Real.log (1 + Fintype.card ι))) :=
        mul_le_mul_of_nonneg_left h_sum_le hK_pos.le
    _ = 3 * K * ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by ring


/-- **Envelope-tail convergence at a fixed positive threshold scale `a`.**

For `Φ ∈ L²(P)` and a fixed `a > 0`, the truncated envelope tail
`√n · ∫⁻ ω, |Φ ω| · 1_{a·√n < |Φ ω|} dP` tends to `0` as `n → ∞`.

The proof is the standard L¹ envelope-tail dominated-convergence argument: dominator
`|Φ|²/a` (on `{a·√n < |Φ|}`, `√n ≤ |Φ|/a`, so `√n·|Φ| ≤ |Φ|²/a`); pointwise
limit `0` (eventually `a·√n > |Φ ω|`, indicator vanishes); `|Φ|² ∈ L¹` from
`MemLp Φ 2 P`.

Together with the `ENNReal.tendsto_atTop_zero` extraction, this yields, for any
positive target `J > 0`, an `N` past which the tail is `≤ J`. -/
lemma tendsto_envelope_tail_const_threshold
    (P : Measure Ω) [IsProbabilityMeasure P] {Φ : Ω → ℝ}
    (hΦ_meas : Measurable Φ) (hΦ_L2 : MemLp Φ 2 P) {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.sqrt n)
        * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
            * Set.indicator {x | a * Real.sqrt n < |Φ x|} 1 ω ∂P)
      Filter.atTop (𝓝 0) := by
  have ha_ofReal_pos : (0 : ℝ≥0∞) < ENNReal.ofReal a := ENNReal.ofReal_pos.mpr ha
  have ha_inv_ne_top : (ENNReal.ofReal a)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr ha_ofReal_pos.ne'
  set T : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.sqrt n)
      * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
          * Set.indicator {x | a * Real.sqrt n < |Φ x|} 1 ω ∂P with hT_def
  set Fn : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (Real.sqrt n) * (ENNReal.ofReal (|Φ ω|) *
      Set.indicator {x | a * Real.sqrt n < |Φ x|} 1 ω) with hFn_def
  set g : Ω → ℝ≥0∞ := fun ω =>
    (ENNReal.ofReal a)⁻¹ * ENNReal.ofReal (Φ ω ^ 2) with hg_def
  -- First identify T n with ∫⁻ Fn n.
  have hT_eq : ∀ n, T n = ∫⁻ ω, Fn n ω ∂P := by
    intro n
    simp only [hT_def, hFn_def]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Each Fn n is measurable.
  have hΦ_abs_meas : Measurable (fun ω => |Φ ω|) :=
    _root_.continuous_abs.measurable.comp hΦ_meas
  have hFn_meas : ∀ n, Measurable (Fn n) := by
    intro n
    refine measurable_const.mul ?_
    refine hΦ_abs_meas.ennreal_ofReal.mul ?_
    exact Measurable.indicator measurable_const
      (measurableSet_lt measurable_const hΦ_abs_meas)
  -- Pointwise, Fn n ω ≤ g ω.
  have h_bound : ∀ n ω, Fn n ω ≤ g ω := by
    intro n ω
    simp only [hFn_def, hg_def]
    by_cases hω : ω ∈ {x | a * Real.sqrt n < |Φ x|}
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      have hω' : a * Real.sqrt n < |Φ ω| := hω
      have h_sqrt_le : Real.sqrt n ≤ |Φ ω| / a := by
        rw [le_div_iff₀ ha]; linarith
      have h_phi_nn : 0 ≤ |Φ ω| := abs_nonneg _
      have h_step : Real.sqrt n * |Φ ω| ≤ Φ ω ^ 2 / a := by
        calc Real.sqrt n * |Φ ω|
            ≤ (|Φ ω| / a) * |Φ ω| :=
              mul_le_mul_of_nonneg_right h_sqrt_le h_phi_nn
          _ = (|Φ ω| * |Φ ω|) / a := by rw [div_mul_eq_mul_div]
          _ = Φ ω ^ 2 / a := by rw [← sq, sq_abs]
      calc ENNReal.ofReal (Real.sqrt n * |Φ ω|)
          ≤ ENNReal.ofReal (Φ ω ^ 2 / a) := ENNReal.ofReal_le_ofReal h_step
        _ = (ENNReal.ofReal a)⁻¹ * ENNReal.ofReal (Φ ω ^ 2) := by
            rw [ENNReal.ofReal_div_of_pos ha, ENNReal.div_eq_inv_mul]
    · rw [Set.indicator_of_notMem hω]
      simp
  -- For every ω, Fn n ω tends to zero.
  have h_lim : ∀ ω, Filter.Tendsto (fun n => Fn n ω) Filter.atTop (𝓝 0) := by
    intro ω
    have h_sqrt_tendsto :
        Filter.Tendsto (fun n : ℕ => a * Real.sqrt n) Filter.atTop Filter.atTop := by
      refine Filter.Tendsto.const_mul_atTop ha ?_
      exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h_ev : ∀ᶠ n in Filter.atTop, Fn n ω = 0 := by
      filter_upwards [h_sqrt_tendsto.eventually_gt_atTop (|Φ ω|)] with n hn
      simp only [hFn_def]
      have h_not : ω ∉ {x | a * Real.sqrt n < |Φ x|} := by
        intro h
        exact lt_asymm (a := |Φ ω|) (b := a * Real.sqrt n) hn h
      rw [Set.indicator_of_notMem h_not]
      simp
    have h_evEq : (fun n => Fn n ω) =ᶠ[Filter.atTop] (fun _ => (0 : ℝ≥0∞)) := h_ev
    exact Filter.Tendsto.congr' h_evEq.symm tendsto_const_nhds
  -- The assumption MemLp Φ 2 P gives integrability of |Φ|².
  have h_phi_sq_int : ∫⁻ ω, ENNReal.ofReal (Φ ω ^ 2) ∂P ≠ ∞ := by
    have h_eLp : eLpNorm Φ 2 P < ∞ := hΦ_L2.eLpNorm_lt_top
    have h_rpow := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (μ := P) (f := Φ) (p := (2 : ℝ≥0∞))
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) h_eLp
    have h_two_toReal : (2 : ℝ≥0∞).toReal = (2 : ℕ) := by norm_num
    rw [h_two_toReal] at h_rpow
    have h_int_eq : ∫⁻ ω, ENNReal.ofReal (Φ ω ^ 2) ∂P
                   = ∫⁻ a, ‖Φ a‖ₑ ^ ((2 : ℕ) : ℝ) ∂P := by
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.rpow_natCast, Real.enorm_eq_ofReal_abs,
          ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [h_int_eq]; exact h_rpow.ne
  -- Hence g is integrable.
  have h_g_int : ∫⁻ ω, g ω ∂P ≠ ∞ := by
    simp only [hg_def]
    rw [lintegral_const_mul' _ _ ha_inv_ne_top]
    exact ENNReal.mul_ne_top ha_inv_ne_top h_phi_sq_int
  -- Conclude by dominated convergence.
  have h_dct :=
    MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := P) (F := Fn) (f := fun _ => (0 : ℝ≥0∞)) g hFn_meas
      (fun n => Filter.Eventually.of_forall (h_bound n)) h_g_int
      (Filter.Eventually.of_forall h_lim)
  simp only [lintegral_zero] at h_dct
  exact (Filter.tendsto_congr hT_eq).mpr h_dct


end AsymptoticStatistics.EmpiricalProcess
