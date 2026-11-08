import SAP.P022.Defs
import SAP.P022.Bridge
import SAP.P022.WH.W1.Proofs.T7
import SAP.P022.WH.W1.Proofs.T9
import SAP.P022.WH.W1.Proofs.T17
import SAP.P022.WH.W1.Proofs.T1
import SAP.P022.WH.W1.Proofs.T6

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P022 SAP.P022.Bridge Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal

-- P022-T1: transported existing declarations and glue.
theorem SAP.P022.T1 : SAP.P022.T1WholeStatement := SAP.P022.WH.W1.T1_whole

-- P022-T2: transported existing declarations and glue.
theorem SAP.P022.T2 : T2Statement := by
  exact @SAP.P022.Bridge.lemma2_corrected_explicit_proof

-- P022-T3: transported existing declarations and glue.
theorem SAP.P022.T3 : T3Statement := by
  exact ⟨@SAP.P022.Bridge.bounded_direct_finite_proof, @SAP.P022.Bridge.bounded_direct_asymptotic_final⟩

-- P022-T4: transported existing declarations and glue.
theorem SAP.P022.T4 : T4Statement := by
  intro d y1 y0 x
  have h := SAP.P022.Bridge.cdf_variance_corrected_proof d y1 y0 x
  dsimp only at h ⊢
  obtain ⟨a, b, c, e, f, g⟩ := h
  have hN : 0 < d.N := by have := d.population_min; omega
  exact ⟨a, b, c, e, f, g, indicator_population_variance hN y1 x, indicator_population_variance hN y0 x⟩

-- P022-T5: transported existing declarations and glue.
theorem SAP.P022.T5 : T5Statement := by
  exact ⟨SAP.P022.Bridge.equation11_counterexample, by norm_num [Nat.choose],
    SAP.P022.Bridge.cdf_quarter_eq_iff⟩

-- P022-T6: transported existing declarations and glue.
theorem SAP.P022.T6 : SAP.P022.T6WholeStatement := SAP.P022.WH.W1.T6_whole

-- P022-T7: transported existing declarations and glue.
theorem SAP.P022.T7 : SAP.P022.T7WholeStatement := SAP.P022.WH.W1.T7_whole

-- P022-T8: transported existing declarations and glue.
theorem SAP.P022.T8 : T8Statement := by
  intro m k hm hk a b
  obtain ⟨mass, ranks, meanA, meanB, cov, substitute, rows, cols, formula⟩ :=
    SAP.P022.Bridge.appendixB_corrected_proof hm hk a b
  exact ⟨mass, ranks, meanA, meanB, cov, (fun N _ B => substitute N B), rows, cols, formula⟩

-- P022-T9: transported existing declarations and glue.
theorem SAP.P022.T9 : SAP.P022.T9WholeStatement := SAP.P022.WH.W1.T9_whole

-- P022-T10: transported existing declarations and glue.
theorem SAP.P022.T10 : T10Statement := by
  refine ⟨@SAP.P022.Bridge.fixed_sample_identity, ?_, ?_⟩
  · intro m k hm hk a b B
    exact (SAP.P022.Bridge.fixed_sample_infinite_limit hm hk a b B).comp
      ((tendsto_add_atTop_iff_nat (m + k)).2 tendsto_id)
  · intro S m k _ _ hm hk hbounded
    exact SAP.P022.Bridge.fixed_arm_variance_limit_eventually S m k hm hk hbounded

-- P022-T11: transported existing declarations and glue.
theorem SAP.P022.T11 : T11Statement := by
  constructor
  · intro Va VH z L U LH UH hVa hVH hz hL hU hLH hUH haW hhW
    have haBin := SAP.P022.Bridge.half_width_rounding L U _ _ hL hU
    have hhBin := SAP.P022.Bridge.half_width_rounding LH UH _ _ hLH hUH
    change (192 / 1000 - (-1555 / 1000)) / 2 - 1 / 2000 ≤ (U-L)/2 ∧ (U-L)/2 ≤ (192 / 1000 - (-1555 / 1000)) / 2 + 1 / 2000 at haBin
    change (165 / 1000 - (-1528 / 1000)) / 2 - 1 / 2000 ≤ (UH-LH)/2 ∧ (UH-LH)/2 ≤ (165 / 1000 - (-1528 / 1000)) / 2 + 1 / 2000 at hhBin
    have ha : 0 < (U-L)/2 := by linarith [haBin.1]
    have haMax : (U-L)/2 ≤ (437/500 : ℝ) := by linarith [haBin.2]
    have hhMin : (423/500 : ℝ) ≤ (UH-LH)/2 := by linarith [hhBin.1]
    have haSq : ((U-L)/2)^2 = z^2 * Va := by rw [haW, mul_pow, Real.sq_sqrt hVa.le]
    have hhSq : ((UH-LH)/2)^2 = z^2 * VH := by rw [hhW, mul_pow, Real.sq_sqrt hVH.le]
    have hRatio : VH / Va = (((UH-LH)/2) / ((U-L)/2))^2 := by rw [div_pow, haSq, hhSq]; field_simp
    have hLow := SAP.P022.Bridge.table1_ratio_lower_bound _ _ ha haMax hhMin
    rw [← hRatio] at hLow
    constructor
    · norm_num at haBin hhBin
      exact ⟨by linarith [haBin.1], by linarith [haBin.2], by linarith [hhBin.1], by linarith [hhBin.2], by linarith, by norm_num, by linarith⟩
    · intro hVaBin hVHBin
      exact SAP.P022.Bridge.table1_corrected_reduction Va VH z L U LH UH hVa hVH hz hL hU hLH hUH haW hhW hVaBin hVHBin
  · exact SAP.P022.Bridge.displayed_variance_reduction

-- P022-T12: transported existing declarations and glue.
theorem SAP.P022.T12.{u} : T12Statement.{u} := by
  refine ⟨@SAP.P022.Bridge.sharp_null_neyman_bias_proof, @SAP.P022.Bridge.finite_wald_mean_width_squared_le, @SAP.P022.Bridge.table1_multiplier_bound, @SAP.P022.Bridge.reported_numbers_incompatible, @SAP.P022.Bridge.fixed_multiplier_mean_lower, ?_⟩
  intro V b hV hb
  linarith

-- P022-T13: transported existing declarations and glue.
theorem SAP.P022.T13 : T13Statement := by
  exact @SAP.P022.Bridge.sharp_bounds_variance_and_all_couplings

-- P022-T14: transported existing declarations and glue.
theorem SAP.P022.T14 : T14Statement := by
  exact @SAP.P022.Bridge.estimated_bound_ordering_proof

-- P022-T15: transported existing declarations and glue.
theorem SAP.P022.T15 : T15Statement := by
  exact @SAP.P022.Bridge.TailB_proposition1

-- P022-T16: transported existing declarations and glue.
theorem SAP.P022.T16 : T16Statement := by
  exact @SAP.P022.Bridge.proposition2_proof

-- P022-T17: transported existing declarations and glue.
theorem SAP.P022.T17 : SAP.P022.T17WholeStatement := SAP.P022.WH.W1.T17_whole

-- P022-T18: transported existing declarations and glue.
theorem SAP.P022.T18 : T18Statement := by
  classical
  have h := SAP.P022.Bridge.lemma2_as_printed_refuted
  push_neg at h
  exact h
