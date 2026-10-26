import AronowAudit.P022.Wave1.Gap.GP022B1b
import AronowAudit.P022.Wave1.Gap.GP022B2
import AronowAudit.P022.Wave1.SharpBounds.N5
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CDF

namespace AronowAudit.P022.Wave1

open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option autoImplicit false
noncomputable section

/-
The following generalized inverse and its specification are adapted from
`StatLean.AsymptoticStatistics.EmpiricalProcess.HalfLineQuantile`.
Copyright (c) 2026. All rights reserved. Released under Apache 2.0 license.
Modifications: local names and only the two quantile facts needed here.
See NOTICE at the repository root.
-/
open ProbabilityTheory Set

/-- Generalized CDF inverse `inf {x | u ≤ F(x)}`.

Edge behavior: this raw `sInf` definition is total. The textbook quantile
specification is asserted only for `0 < u < 1`, where the defining set is
nonempty and bounded below. -/
private def lemma2_corrected_explicit_quantile (P : Measure ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | u ≤ cdf P x}

private lemma lemma2_corrected_explicit_leftLim (P : Measure ℝ) [IsProbabilityMeasure P]
    (x : ℝ) :
    Function.leftLim (cdf P) x = P.real (Iio x) := by
  have hnonneg : 0 ≤ Function.leftLim (cdf P) x :=
    (cdf_nonneg P (x - 1)).trans ((monotone_cdf P).le_leftLim (sub_lt_self x one_pos))
  have hmeasure : P (Iio x) = ENNReal.ofReal (Function.leftLim (cdf P) x) := by
    calc
      P (Iio x) = (cdf P).measure (Iio x) := by rw [measure_cdf P]
      _ = _ := by rw [(cdf P).measure_Iio (tendsto_cdf_atBot P), sub_zero]
  rw [measureReal_def, hmeasure, ENNReal.toReal_ofReal hnonneg]

/-- Generalized-inverse specification, valid without CDF continuity:
`u ≤ F(q(u))` and `F(q(u)-) ≤ u`. The left limit is represented exactly by
`P.real (Iio q(u))`, so atoms at the quantile are not discarded. -/
private theorem lemma2_corrected_explicit_quantile_spec (P : Measure ℝ) [IsProbabilityMeasure P]
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    u ≤ cdf P (lemma2_corrected_explicit_quantile P u) ∧
      P.real (Iio (lemma2_corrected_explicit_quantile P u)) ≤ u := by
  let S : Set ℝ := {x | u ≤ cdf P x}
  have hS_nonempty : S.Nonempty := by
    have h_event : ∀ᶠ x in atTop, u < cdf P x :=
      (tendsto_cdf_atTop P).eventually (Ioi_mem_nhds hu1)
    obtain ⟨x, hx⟩ := h_event.exists
    exact ⟨x, hx.le⟩
  have hS_bdd : BddBelow S := by
    have h_event : ∀ᶠ x in atBot, cdf P x < u :=
      (tendsto_cdf_atBot P).eventually (Iio_mem_nhds hu0)
    obtain ⟨a, ha⟩ := eventually_atBot.mp h_event
    refine ⟨a, ?_⟩
    intro x hx
    by_contra hax
    have hxa : x ≤ a := le_of_not_ge hax
    exact (not_lt_of_ge hx) ((monotone_cdf P hxa).trans_lt (ha a le_rfl))
  change u ≤ cdf P (sInf S) ∧ P.real (Iio (sInf S)) ≤ u
  constructor
  · rw [← (cdf P).iInf_Ioi_eq (sInf S)]
    refine le_ciInf fun (r : Ioi (sInf S)) ↦ ?_
    obtain ⟨x, hxS, hxr⟩ := (csInf_lt_iff hS_bdd hS_nonempty).mp r.2
    exact hxS.trans (monotone_cdf P hxr.le)
  · rw [← lemma2_corrected_explicit_leftLim P]
    apply le_of_tendsto ((monotone_cdf P).tendsto_leftLim (sInf S))
    filter_upwards [self_mem_nhdsWithin] with x hx
    by_contra hxu
    have hxS : x ∈ S := le_of_not_ge hxu
    exact (not_lt_of_ge (csInf_le hS_bdd hxS)) hx

private def lemma2_corrected_explicit_empiricalLaw {N : ℕ} (hN : 0 < N)
    (y : Fin N → ℝ) : ProbabilityMeasure ℝ := by
  letI lemma2_corrected_explicit_neZero : NeZero N := ⟨hN.ne'⟩
  exact (SharpBounds.unitLaw N).map y

private lemma lemma2_corrected_explicit_empirical_integral {N : ℕ} (hN : 0 < N)
    (y : Fin N → ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(lemma2_corrected_explicit_empiricalLaw hN y : Measure ℝ)) =
      finiteMean (fun i => f (y i)) := by
  letI lemma2_corrected_explicit_neZeroInt : NeZero N := ⟨hN.ne'⟩
  rw [lemma2_corrected_explicit_empiricalLaw, ProbabilityMeasure.toMeasure_map,
    integral_map_of_stronglyMeasurable (measurable_of_finite _) hf.stronglyMeasurable,
    SharpBounds.integral_unitLaw]

private def lemma2_corrected_explicit_coord (t : Bool) (p : ℝ × ℝ) : ℝ :=
  if t then p.1 else p.2

private lemma lemma2_corrected_explicit_coord_continuous (t : Bool) :
    Continuous (lemma2_corrected_explicit_coord t) := by
  cases t <;> first | exact continuous_snd | exact continuous_fst

private def lemma2_corrected_explicit_marginal (H : JointLaw) (t : Bool) :
    ProbabilityMeasure ℝ := H.map (lemma2_corrected_explicit_coord t)

private def lemma2_corrected_explicit_side (P : Measure ℝ) (b : Bool) (x : ℝ) : ℝ :=
  if b then cdf P x else P.real (Iio x)

private lemma lemma2_corrected_explicit_side_marginal (H : JointLaw) (t b : Bool) (x : ℝ) :
    lemma2_corrected_explicit_side (lemma2_corrected_explicit_marginal H t) b x =
      if b then lawCDF H t x else lawLeftCDF H t x := by
  have hm := (lemma2_corrected_explicit_coord_continuous t).measurable
  cases b <;>
    simp only [lemma2_corrected_explicit_side, Bool.false_eq_true, if_false, if_true]
  · rw [measureReal_def, lemma2_corrected_explicit_marginal, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply hm measurableSet_Iio]
    rfl
  · rw [cdf_eq_real, measureReal_def, lemma2_corrected_explicit_marginal,
      ProbabilityMeasure.toMeasure_map, Measure.map_apply hm measurableSet_Iic]
    rfl

private lemma lemma2_corrected_explicit_side_empirical {N : ℕ} (hN : 0 < N)
    (y : Fin N → ℝ) (b : Bool) (x : ℝ) :
    lemma2_corrected_explicit_side (lemma2_corrected_explicit_empiricalLaw hN y) b x =
      finiteMean (fun i => if (if b then y i ≤ x else y i < x) then 1 else 0) := by
  classical
  letI lemma2_corrected_explicit_neZeroSide : NeZero N := ⟨hN.ne'⟩
  cases b <;>
    simp only [lemma2_corrected_explicit_side, Bool.false_eq_true, if_false, if_true]
  · rw [measureReal_def, lemma2_corrected_explicit_empiricalLaw, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (measurable_of_finite _) measurableSet_Iio, SharpBounds.measure_unitLaw]
    apply Finset.expect_congr rfl
    intro i _
    by_cases hi : y i < x <;> simp [hi]
  · rw [cdf_eq_real, measureReal_def, lemma2_corrected_explicit_empiricalLaw,
      ProbabilityMeasure.toMeasure_map, Measure.map_apply (measurable_of_finite _) measurableSet_Iic,
      SharpBounds.measure_unitLaw]
    apply Finset.expect_congr rfl
    intro i _
    by_cases hi : y i ≤ x <;> simp [hi]

private lemma lemma2_corrected_explicit_marginal_weak (S : ExperimentSequence) (H : JointLaw)
    (hw : weakPopulationConvergence S H) (t : Bool) :
    Tendsto (fun q => lemma2_corrected_explicit_empiricalLaw
      (by have := (S.design q).population_min; omega) (rowOutcomes S t q)) atTop
      (𝓝 (lemma2_corrected_explicit_marginal H t)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hf := hw (f.compContinuous ⟨lemma2_corrected_explicit_coord t,
    lemma2_corrected_explicit_coord_continuous t⟩)
  have heq (q : ℕ) :
      (∫ x, f x ∂(lemma2_corrected_explicit_empiricalLaw
        (by have := (S.design q).population_min; omega) (rowOutcomes S t q) : Measure ℝ)) =
        finiteMean (fun i : Fin (S.design q).N =>
          f (lemma2_corrected_explicit_coord t (S.y1 i.val, S.y0 i.val))) := by
    rw [lemma2_corrected_explicit_empirical_integral _ _ _ f.continuous.measurable]
    cases t <;> rfl
  simp_rw [heq]
  have hi : (∫ x, f x ∂(lemma2_corrected_explicit_marginal H t : Measure ℝ)) =
      ∫ p, f (lemma2_corrected_explicit_coord t p) ∂(H : Measure (ℝ × ℝ)) := by
    rw [lemma2_corrected_explicit_marginal, ProbabilityMeasure.toMeasure_map,
      integral_map_of_stronglyMeasurable
        (lemma2_corrected_explicit_coord_continuous t).measurable f.continuous.measurable.stronglyMeasurable]
  rw [hi]
  exact hf

private lemma lemma2_corrected_explicit_endpoint_convergence (S : ExperimentSequence)
    (H : JointLaw) (θ ρ : ℝ) (h : Conditions123 S H θ ρ)
    (hleft : AtomLeftConvergence S H) (t b : Bool) (x : ℝ) :
    Tendsto (fun q => lemma2_corrected_explicit_side
      (lemma2_corrected_explicit_empiricalLaw
        (by have := (S.design q).population_min; omega) (rowOutcomes S t q)) b x)
      atTop (𝓝 (lemma2_corrected_explicit_side (lemma2_corrected_explicit_marginal H t) b x)) := by
  rcases h with ⟨_, _, _, _, _, _, hw, hatom⟩
  by_cases hx : ContinuousAt (lawCDF H t) x
  · have hCDF : ContinuousAt (cdf (lemma2_corrected_explicit_marginal H t : Measure ℝ)) x := by
      have he : (cdf (lemma2_corrected_explicit_marginal H t : Measure ℝ)) = lawCDF H t := by
        funext z
        exact lemma2_corrected_explicit_side_marginal H t true z
      rw [he]
      exact hx
    have hsingle : (lemma2_corrected_explicit_marginal H t : Measure ℝ) {x} = 0 := by
      rw [← measure_cdf (lemma2_corrected_explicit_marginal H t : Measure ℝ),
        StieltjesFunction.measure_singleton, hCDF.continuousWithinAt.leftLim_eq]
      simp
    have hweak := lemma2_corrected_explicit_marginal_weak S H hw t
    cases b
    · have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
        hweak (E := Iio x) (by rw [frontier_Iio]; exact hsingle)
      exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hm
    · have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
        hweak (E := Iic x) (by rw [frontier_Iic]; exact hsingle)
      simpa only [lemma2_corrected_explicit_side, if_true, cdf_eq_real, measureReal_def,
        Function.comp_def] using (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hm
  · simp_rw [lemma2_corrected_explicit_side_empirical,
      lemma2_corrected_explicit_side_marginal]
    cases b
    · exact hleft t x hx
    · exact hatom t x hx

private def lemma2_corrected_explicit_level (R : ℕ) (i : Fin R) : ℝ :=
  ((i.val : ℝ) + 1) / ((R : ℝ) + 1)

private lemma lemma2_corrected_explicit_level_bounds {R : ℕ} (i : Fin R) :
    0 < lemma2_corrected_explicit_level R i ∧ lemma2_corrected_explicit_level R i < 1 := by
  have hi : (i.val : ℝ) < R := by exact_mod_cast i.isLt
  dsimp [lemma2_corrected_explicit_level]
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).2
    linarith

private lemma lemma2_corrected_explicit_level_lower (R : ℕ) (hR : 0 < R)
    (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    z ≤ 1 / ((R : ℝ) + 1) ∨ ∃ i : Fin R,
      lemma2_corrected_explicit_level R i ≤ z ∧
        z - lemma2_corrected_explicit_level R i ≤ 1 / ((R : ℝ) + 1) := by
  let n := Nat.floor (((R : ℝ) + 1) * z)
  have hd : 0 < (R : ℝ) + 1 := by positivity
  have hnle : (n : ℝ) ≤ ((R : ℝ) + 1) * z := Nat.floor_le (by positivity)
  have hnlt : ((R : ℝ) + 1) * z < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  by_cases hn0 : n = 0
  · left
    rw [hn0, Nat.cast_zero, zero_add] at hnlt
    exact le_of_lt ((lt_div_iff₀ hd).2 (by nlinarith))
  · right
    by_cases hnR : n ≤ R
    · have hn : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        exact_mod_cast (show n - 1 + 1 = n by omega)
      refine ⟨⟨n - 1, by omega⟩, ?_, ?_⟩
      · dsimp [lemma2_corrected_explicit_level]
        rw [hn]
        exact (div_le_iff₀ hd).2 (by nlinarith)
      · dsimp [lemma2_corrected_explicit_level]
        rw [hn]
        apply (le_div_iff₀ hd).2
        have he : ((n : ℝ) / ((R : ℝ) + 1)) * ((R : ℝ) + 1) = n :=
          div_mul_cancel₀ _ hd.ne'
        nlinarith
    · have hn : ((R - 1 : ℕ) : ℝ) + 1 = R := by
        exact_mod_cast (show R - 1 + 1 = R by omega)
      have hRn : (R : ℝ) + 1 ≤ n := by exact_mod_cast (show R + 1 ≤ n by omega)
      refine ⟨⟨R - 1, by omega⟩, ?_, ?_⟩
      · dsimp [lemma2_corrected_explicit_level]
        rw [hn]
        apply (div_le_iff₀ hd).2
        nlinarith
      · dsimp [lemma2_corrected_explicit_level]
        rw [hn]
        apply (le_div_iff₀ hd).2
        have he : ((R : ℝ) / ((R : ℝ) + 1)) * ((R : ℝ) + 1) = R :=
          div_mul_cancel₀ _ hd.ne'
        nlinarith

private lemma lemma2_corrected_explicit_level_upper (R : ℕ) (hR : 0 < R)
    (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - z ≤ 1 / ((R : ℝ) + 1) ∨ ∃ i : Fin R,
      z < lemma2_corrected_explicit_level R i ∧
        lemma2_corrected_explicit_level R i - z ≤ 1 / ((R : ℝ) + 1) := by
  let n := Nat.floor (((R : ℝ) + 1) * z)
  have hd : 0 < (R : ℝ) + 1 := by positivity
  have hnle : (n : ℝ) ≤ ((R : ℝ) + 1) * z := Nat.floor_le (by positivity)
  have hnlt : ((R : ℝ) + 1) * z < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  by_cases hnR : n < R
  · right
    refine ⟨⟨n, hnR⟩, ?_, ?_⟩
    · exact (lt_div_iff₀ hd).2 (by nlinarith)
    · apply (le_div_iff₀ hd).2
      have he : (((n : ℝ) + 1) / ((R : ℝ) + 1)) * ((R : ℝ) + 1) = (n : ℝ) + 1 :=
        div_mul_cancel₀ _ hd.ne'
      dsimp [lemma2_corrected_explicit_level]
      nlinarith
  · left
    have hRn : (R : ℝ) ≤ n := by exact_mod_cast (show R ≤ n by omega)
    apply (le_div_iff₀ hd).2
    nlinarith

private def lemma2_corrected_explicit_grid (P : Measure ℝ) (R : ℕ) (i : Fin R) : ℝ :=
  lemma2_corrected_explicit_quantile P (lemma2_corrected_explicit_level R i)

private lemma lemma2_corrected_explicit_grid_bound (P Q : Measure ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (R : ℕ) (hR : 0 < R)
    (e : ℝ) (he : 0 ≤ e)
    (hgrid : ∀ i : Fin R, ∀ b : Bool,
      |lemma2_corrected_explicit_side P b (lemma2_corrected_explicit_grid P R i) -
        lemma2_corrected_explicit_side Q b (lemma2_corrected_explicit_grid P R i)| ≤ e) :
    cdfDistance (cdf P) (cdf Q) ≤ 1 / ((R : ℝ) + 1) + e := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  apply abs_le.mpr
  constructor
  · rcases lemma2_corrected_explicit_level_upper R hR (cdf P x)
      (cdf_nonneg P x) (cdf_le_one P x) with htail | ⟨i, hzi, hiz⟩
    · have hb := cdf_le_one Q x
      linarith
    · have hspec := lemma2_corrected_explicit_quantile_spec P
        (lemma2_corrected_explicit_level_bounds i).1
        (lemma2_corrected_explicit_level_bounds i).2
      have hxq : x < lemma2_corrected_explicit_grid P R i := by
        by_contra hh
        have hm := monotone_cdf P (le_of_not_gt hh)
        exact (not_le_of_gt hzi) (hspec.1.trans hm)
      have hQ : cdf Q x ≤ Q.real (Iio (lemma2_corrected_explicit_grid P R i)) := by
        rw [cdf_eq_real]
        exact measureReal_mono (Iic_subset_Iio.mpr hxq)
      have hg := (abs_le.mp (hgrid i false)).1
      change -e ≤ P.real (Iio (lemma2_corrected_explicit_grid P R i)) -
        Q.real (Iio (lemma2_corrected_explicit_grid P R i)) at hg
      have hs2 : P.real (Iio (lemma2_corrected_explicit_grid P R i)) ≤
          lemma2_corrected_explicit_level R i := hspec.2
      linarith
  · rcases lemma2_corrected_explicit_level_lower R hR (cdf P x)
      (cdf_nonneg P x) (cdf_le_one P x) with htail | ⟨i, hiz, hzi⟩
    · have hb := cdf_nonneg Q x
      linarith
    · have hspec := lemma2_corrected_explicit_quantile_spec P
        (lemma2_corrected_explicit_level_bounds i).1
        (lemma2_corrected_explicit_level_bounds i).2
      have hqx : lemma2_corrected_explicit_grid P R i ≤ x := by
        exact csInf_le (by
          have h_event := (tendsto_cdf_atBot P).eventually
            (Iio_mem_nhds (lemma2_corrected_explicit_level_bounds i).1)
          obtain ⟨a, ha⟩ := eventually_atBot.mp h_event
          refine ⟨a, ?_⟩
          intro z hz
          by_contra hh
          have hm := monotone_cdf P (le_of_not_ge hh)
          exact (not_lt_of_ge hz) (hm.trans_lt (ha a le_rfl))) hiz
      have hQ := monotone_cdf Q hqx
      have hg := (abs_le.mp (hgrid i true)).2
      change cdf P (lemma2_corrected_explicit_grid P R i) -
        cdf Q (lemma2_corrected_explicit_grid P R i) ≤ e at hg
      have hs1 : lemma2_corrected_explicit_level R i ≤
          cdf P (lemma2_corrected_explicit_grid P R i) := hspec.1
      linarith

private lemma lemma2_corrected_explicit_distance_bounds (P Q : Measure ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    0 ≤ cdfDistance (cdf P) (cdf Q) ∧ cdfDistance (cdf P) (cdf Q) ≤ 1 := by
  have hp (x : ℝ) : |cdf P x - cdf Q x| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [cdf_nonneg P x, cdf_nonneg Q x, cdf_le_one P x, cdf_le_one Q x]
  have hb : BddAbove (range (fun x => |cdf P x - cdf Q x|)) :=
    ⟨1, by rintro _ ⟨x, rfl⟩; exact hp x⟩
  constructor
  · exact (abs_nonneg (cdf P 0 - cdf Q 0)).trans (le_csSup hb (mem_range_self 0))
  · exact csSup_le (range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hp x)

private lemma lemma2_corrected_explicit_cdf_marginal (H : JointLaw) (t : Bool) :
    (cdf (lemma2_corrected_explicit_marginal H t : Measure ℝ)) = lawCDF H t := by
  funext x
  exact lemma2_corrected_explicit_side_marginal H t true x

private lemma lemma2_corrected_explicit_cdf_empirical {N : ℕ} (hN : 0 < N)
    (y : Fin N → ℝ) :
    (cdf (lemma2_corrected_explicit_empiricalLaw hN y : Measure ℝ)) = empiricalCDF y := by
  funext x
  exact lemma2_corrected_explicit_side_empirical hN y true x

private lemma lemma2_corrected_explicit_uniform (S : ExperimentSequence) (H : JointLaw)
    (θ ρ : ℝ) (h : Conditions123 S H θ ρ) (hleft : AtomLeftConvergence S H) (t : Bool) :
    Tendsto (fun q => cdfDistance (lawCDF H t)
      (empiricalCDF (rowOutcomes S t q))) atTop (𝓝 0) := by
  let P : ProbabilityMeasure ℝ := lemma2_corrected_explicit_marginal H t
  let Q : ℕ → ProbabilityMeasure ℝ := fun q => lemma2_corrected_explicit_empiricalLaw
    (by have := (S.design q).population_min; omega) (rowOutcomes S t q)
  have heq (q : ℕ) : cdfDistance (lawCDF H t) (empiricalCDF (rowOutcomes S t q)) =
      cdfDistance (cdf P) (cdf (Q q)) := by
    rw [lemma2_corrected_explicit_cdf_marginal, lemma2_corrected_explicit_cdf_empirical]
  simp_rw [heq]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R, hR⟩ := exists_nat_gt (2 / ε)
  have hRp : 0 < R := by
    have hh : (0 : ℝ) < R := (by positivity : (0 : ℝ) < 2 / ε).trans hR
    exact_mod_cast hh
  have hδ : 1 / ((R : ℝ) + 1) < ε / 2 := by
    have hh := (div_lt_iff₀ hε).mp hR
    apply (div_lt_iff₀ (by positivity : 0 < (R : ℝ) + 1)).2
    nlinarith
  have hend (j : Fin R × Bool) : ∀ᶠ q in atTop,
      |lemma2_corrected_explicit_side P j.2 (lemma2_corrected_explicit_grid P R j.1) -
        lemma2_corrected_explicit_side (Q q) j.2
          (lemma2_corrected_explicit_grid P R j.1)| ≤ ε / 2 := by
    have hh := ((tendsto_const_nhds (x := lemma2_corrected_explicit_side P j.2
      (lemma2_corrected_explicit_grid P R j.1))).sub
      (lemma2_corrected_explicit_endpoint_convergence S H θ ρ h hleft t j.2
        (lemma2_corrected_explicit_grid P R j.1))).abs
    have hh' : Tendsto (fun q => |lemma2_corrected_explicit_side P j.2
        (lemma2_corrected_explicit_grid P R j.1) - lemma2_corrected_explicit_side
          (Q q) j.2 (lemma2_corrected_explicit_grid P R j.1)|) atTop (𝓝 0) := by
      simpa only [P, Q, sub_self, abs_zero] using hh
    exact ((hh'.eventually (Iio_mem_nhds (by positivity : 0 < ε / 2))).mono
      (fun _ hx => hx.le))
  have hall : ∀ᶠ q in atTop, ∀ j : Fin R × Bool,
      |lemma2_corrected_explicit_side P j.2 (lemma2_corrected_explicit_grid P R j.1) -
        lemma2_corrected_explicit_side (Q q) j.2
          (lemma2_corrected_explicit_grid P R j.1)| ≤ ε / 2 := Filter.eventually_all.mpr hend
  filter_upwards [hall] with q hq
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (lemma2_corrected_explicit_distance_bounds P (Q q)).1]
  exact (lemma2_corrected_explicit_grid_bound P (Q q) R hRp (ε / 2) (by positivity)
    (fun i b => hq (i, b))).trans_lt (by linarith)

private lemma lemma2_corrected_explicit_union_bound {I : Type*} [Fintype I]
    (d : Design) (E : Assignment d → Prop) (F : I → Assignment d → Prop)
    (h : ∀ π, E π → ∃ j, F j π) :
    designProbability d E ≤ ∑ j, designProbability d (F j) := by
  classical
  unfold designProbability designExpectation
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro π _
  by_cases hE : E π
  · rw [if_pos hE]
    obtain ⟨j, hj⟩ := h π hE
    calc
      (1 : ℝ) = if F j π then 1 else 0 := by rw [if_pos hj]
      _ ≤ ∑ i : I, if F i π then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun i : I => if F i π then (1 : ℝ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
  · rw [if_neg hE]
    apply Finset.sum_nonneg
    intro i _
    dsimp only
    split_ifs <;> norm_num

private lemma lemma2_corrected_explicit_indicator_moment (d : Design) {s : ℕ} (hs : 0 < s)
    (e : Fin s → Fin d.N) (he : Function.Injective e) (I : Fin d.N → Prop) [DecidablePred I] :
    designExpectation d (fun π =>
      (finiteMean (fun j => if I (π (e j)) then (1 : ℝ) else 0) -
        finiteMean (fun i => if I i then 1 else 0)) ^ 2) ≤
      ((d.N : ℝ) - s) / (4 * ((d.N : ℝ) - 1) * s) := by
  classical
  have hNp : 0 < d.N := by have := d.population_min; omega
  have hsN : s ≤ d.N := by simpa using Fintype.card_le_of_injective e he
  have hv : finiteVariance (fun i => if I i then (1 : ℝ) else 0) =
      finiteMean (fun i => if I i then (1 : ℝ) else 0) *
        (1 - finiteMean (fun i => if I i then (1 : ℝ) else 0)) := by
    rw [finite_variance_second_moment hNp]
    have heq : (fun i : Fin d.N => (if I i then (1 : ℝ) else 0) ^ 2) =
        (fun i => if I i then (1 : ℝ) else 0) := by
      funext i
      split_ifs <;> norm_num
    rw [heq]
    ring
  rw [(cdf_variance_corrected_block_moments d hs e he
    (fun i => if I i then (1 : ℝ) else 0)).2, hv]
  have hNR : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  simpa only [mul_assoc] using cdf_variance_corrected_bernoulli_upper d.N s
    (finiteMean (fun i => if I i then (1 : ℝ) else 0)) (by linarith) hsR hsN

private lemma lemma2_corrected_explicit_finite_tail (P : ProbabilityMeasure ℝ)
    (d : Design) (y : Fin d.N → ℝ) {s : ℕ} (hs : 0 < s)
    (e : Fin s → Fin d.N) (he : Function.Injective e) (R : ℕ) (hR : 0 < R)
    (η : ℝ) (hη : 0 < η) (hδ : 1 / ((R : ℝ) + 1) ≤ η / 4)
    (hgrid : ∀ i : Fin R, ∀ b : Bool,
      |lemma2_corrected_explicit_side P b (lemma2_corrected_explicit_grid P R i) -
        finiteMean (fun j => if (if b then y j ≤ lemma2_corrected_explicit_grid P R i
          else y j < lemma2_corrected_explicit_grid P R i) then 1 else 0)| ≤ η / 4) :
    designProbability d (fun π => η ≤ cdfDistance (cdf P)
      (empiricalCDF (fun i => y (π (e i))))) ≤
      (2 * R : ℕ) * ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s * η ^ 2) := by
  classical
  letI lemma2_corrected_explicit_nonemptyGrid : Nonempty (Fin R) := ⟨⟨0, hR⟩⟩
  let dev : Fin R × Bool → Assignment d → ℝ := fun j π =>
    finiteMean (fun i => if (if j.2 then y (π (e i)) ≤ lemma2_corrected_explicit_grid P R j.1
      else y (π (e i)) < lemma2_corrected_explicit_grid P R j.1) then 1 else 0) -
    finiteMean (fun i => if (if j.2 then y i ≤ lemma2_corrected_explicit_grid P R j.1
      else y i < lemma2_corrected_explicit_grid P R j.1) then 1 else 0)
  have hcontain (π : Assignment d) (hπ : η ≤ cdfDistance (cdf P)
      (empiricalCDF (fun i => y (π (e i))))) :
      ∃ j : Fin R × Bool, η / 2 ≤ |dev j π| := by
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun j => |dev j π|)
      Finset.univ_nonempty
    refine ⟨j, ?_⟩
    have hbound := lemma2_corrected_explicit_grid_bound P
      (lemma2_corrected_explicit_empiricalLaw hs (fun i => y (π (e i)))) R hR
      (η / 4 + |dev j π|) (by positivity) (by
        intro i b
        rw [lemma2_corrected_explicit_side_empirical]
        have hg := hgrid i b
        have hm := hj (i, b) (Finset.mem_univ _)
        have ht := abs_sub_le
          (lemma2_corrected_explicit_side P b (lemma2_corrected_explicit_grid P R i))
          (finiteMean (fun k => if (if b then y k ≤ lemma2_corrected_explicit_grid P R i
            else y k < lemma2_corrected_explicit_grid P R i) then 1 else 0))
          (finiteMean (fun k => if (if b then y (π (e k)) ≤ lemma2_corrected_explicit_grid P R i
            else y (π (e k)) < lemma2_corrected_explicit_grid P R i) then 1 else 0))
        rw [abs_sub_comm (finiteMean _) (finiteMean _)] at ht
        change _ ≤ |dev j π| at hm
        exact ht.trans (add_le_add hg hm))
    rw [lemma2_corrected_explicit_cdf_empirical] at hbound
    linarith
  apply (lemma2_corrected_explicit_union_bound d _ (fun j π => η / 2 ≤ |dev j π|) hcontain).trans
  calc
    (∑ j : Fin R × Bool, designProbability d (fun π => η / 2 ≤ |dev j π|)) ≤
        ∑ _j : Fin R × Bool,
          ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s * η ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      apply (finite_squared_markov d (dev j) (η / 2) (by positivity)).trans
      have hm := lemma2_corrected_explicit_indicator_moment d hs e he
        (fun i => if j.2 then y i ≤ lemma2_corrected_explicit_grid P R j.1
          else y i < lemma2_corrected_explicit_grid P R j.1)
      have hd : 0 < (d.N : ℝ) - 1 := by
        have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
        linarith
      have hsR : (0 : ℝ) < s := by exact_mod_cast hs
      calc
        _ ≤ (((d.N : ℝ) - s) / (4 * ((d.N : ℝ) - 1) * s)) / (η / 2) ^ 2 :=
          div_le_div_of_nonneg_right hm (sq_nonneg _)
        _ = _ := by
          field_simp
          <;> ring
    _ = _ := by simp [Fintype.card_prod, mul_div_assoc, mul_assoc] <;> ring


private lemma lemma2_corrected_explicit_tail (S : ExperimentSequence) (H : JointLaw)
    (θ ρ : ℝ) (h : Conditions123 S H θ ρ) (hleft : AtomLeftConvergence S H)
    (t : Bool) (s : ℕ → ℕ) (hs : ∀ q, 0 < s q)
    (e : (q : ℕ) → Fin (s q) → Fin (S.design q).N)
    (he : ∀ q, Function.Injective (e q)) (α : ℝ) (hα : 0 < α)
    (hratio : Tendsto (fun q => (s q : ℝ) / (S.design q).N) atTop (𝓝 α))
    (η : ℝ) (hη : 0 < η) :
    scaledProbabilityLimsup S (fun q π => η ≤ cdfDistance
      (cdf (lemma2_corrected_explicit_marginal H t : Measure ℝ))
      (empiricalCDF (fun i => rowOutcomes S t q (π (e q i))))) ≤
      ENNReal.ofReal ((1 - α) * correctedPartitionInteger η / (α * η ^ 2)) := by
  classical
  let P := lemma2_corrected_explicit_marginal H t
  by_cases hη1 : η ≤ 1
  · let R := Nat.ceil (4 / η)
    have hceil : 4 / η ≤ (R : ℝ) := Nat.le_ceil _
    have hR : 0 < R := by
      have hh : (0 : ℝ) < R := (by positivity : (0 : ℝ) < 4 / η).trans_le hceil
      exact_mod_cast hh
    have hδ : 1 / ((R : ℝ) + 1) ≤ η / 4 := by
      have hh := (div_le_iff₀ hη).mp hceil
      apply (div_le_iff₀ (by positivity : 0 < (R : ℝ) + 1)).2
      nlinarith
    have hend (j : Fin R × Bool) : ∀ᶠ q in atTop,
        |lemma2_corrected_explicit_side P j.2 (lemma2_corrected_explicit_grid P R j.1) -
          finiteMean (fun i => if (if j.2 then rowOutcomes S t q i ≤
            lemma2_corrected_explicit_grid P R j.1 else rowOutcomes S t q i <
            lemma2_corrected_explicit_grid P R j.1) then 1 else 0)| ≤ η / 4 := by
      have hh := ((tendsto_const_nhds (x := lemma2_corrected_explicit_side P j.2
        (lemma2_corrected_explicit_grid P R j.1))).sub
        (lemma2_corrected_explicit_endpoint_convergence S H θ ρ h hleft t j.2
          (lemma2_corrected_explicit_grid P R j.1))).abs
      have hh' : Tendsto (fun q => |lemma2_corrected_explicit_side P j.2
          (lemma2_corrected_explicit_grid P R j.1) -
          finiteMean (fun i => if (if j.2 then rowOutcomes S t q i ≤
            lemma2_corrected_explicit_grid P R j.1 else rowOutcomes S t q i <
            lemma2_corrected_explicit_grid P R j.1) then 1 else 0)|) atTop (𝓝 0) := by
        simpa only [P, sub_self, abs_zero, lemma2_corrected_explicit_side_empirical] using hh
      exact (hh'.eventually (Iio_mem_nhds (by positivity : 0 < η / 4))).mono
        (fun _ hx => hx.le)
    have hall : ∀ᶠ q in atTop, ∀ j : Fin R × Bool,
        |lemma2_corrected_explicit_side P j.2 (lemma2_corrected_explicit_grid P R j.1) -
          finiteMean (fun i => if (if j.2 then rowOutcomes S t q i ≤
            lemma2_corrected_explicit_grid P R j.1 else rowOutcomes S t q i <
            lemma2_corrected_explicit_grid P R j.1) then 1 else 0)| ≤ η / 4 :=
      Filter.eventually_all.mpr hend
    let G : ℕ → ℝ := fun q => (2 * R : ℕ) *
      ((1 - (s q : ℝ) / (S.design q).N) /
        ((1 - ((S.design q).N : ℝ)⁻¹) * ((s q : ℝ) / (S.design q).N))) / η ^ 2
    have hNpos (q : ℕ) : (0 : ℝ) < (S.design q).N := by
      have hh : (4 : ℝ) ≤ (S.design q).N := by exact_mod_cast (S.design q).population_min
      linarith
    have hspos (q : ℕ) : (0 : ℝ) < s q := by exact_mod_cast hs q
    have hNm1 (q : ℕ) : (0 : ℝ) < ((S.design q).N : ℝ) - 1 := by
      have hh : (4 : ℝ) ≤ (S.design q).N := by exact_mod_cast (S.design q).population_min
      linarith
    have hGeq (q : ℕ) : ((S.design q).N : ℝ) *
        ((2 * R : ℕ) * (((S.design q).N : ℝ) - s q) /
          ((((S.design q).N : ℝ) - 1) * s q * η ^ 2)) = G q := by
      dsimp [G]
      field_simp [ne_of_gt (hNpos q), ne_of_gt (hspos q), ne_of_gt (hNm1 q), ne_of_gt hη]
      <;> ring
    have hprob : ∀ᶠ q in atTop, ENNReal.ofReal (((S.design q).N : ℝ) *
        designProbability (S.design q) (fun π => η ≤ cdfDistance (cdf P)
          (empiricalCDF (fun i => rowOutcomes S t q (π (e q i)))))) ≤ ENNReal.ofReal (G q) := by
      filter_upwards [hall] with q hq
      apply ENNReal.ofReal_le_ofReal
      rw [← hGeq q]
      exact mul_le_mul_of_nonneg_left
        (lemma2_corrected_explicit_finite_tail P (S.design q) (rowOutcomes S t q)
          (hs q) (e q) (he q) R hR η hη hδ (fun i b => hq (i,b))) (hNpos q).le
    have hinv : Tendsto (fun q => ((S.design q).N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (GP022B1b_size_atTop S)
    have hG0 : Tendsto G atTop
        (𝓝 (((2 * R : ℕ) : ℝ) * ((1 - α) / ((1 - 0) * α)) / η ^ 2)) := by
      exact (tendsto_const_nhds.mul
        ((tendsto_const_nhds.sub hratio).div
          ((tendsto_const_nhds.sub hinv).mul hratio) (by simpa using hα.ne'))).div_const _
    have hG : Tendsto G atTop (𝓝 ((1 - α) * correctedPartitionInteger η / (α * η ^ 2))) := by
      have hK : correctedPartitionInteger η = 2 * R := by
        simp only [correctedPartitionInteger, min_eq_left hη1, R]
      have heq : (((2 * R : ℕ) : ℝ) * ((1 - α) / ((1 - 0) * α)) / η ^ 2) =
          (1 - α) * correctedPartitionInteger η / (α * η ^ 2) := by
        rw [hK]
        ring
      rw [heq] at hG0
      exact hG0
    calc
      _ ≤ Filter.limsup (fun q => ENNReal.ofReal (G q)) atTop :=
        Filter.limsup_le_limsup hprob (by isBoundedDefault) (by isBoundedDefault)
      _ = _ := (ENNReal.tendsto_ofReal hG).limsup_eq
  · have hlarge : 1 < η := lt_of_not_ge hη1
    have hp (q : ℕ) : designProbability (S.design q) (fun π => η ≤ cdfDistance (cdf P)
        (empiricalCDF (fun i => rowOutcomes S t q (π (e q i))))) = 0 := by
      unfold designProbability
      have hnot (π : Assignment (S.design q)) : ¬η ≤ cdfDistance (cdf P)
          (empiricalCDF (fun i => rowOutcomes S t q (π (e q i)))) := by
        have hh := (lemma2_corrected_explicit_distance_bounds P
          (lemma2_corrected_explicit_empiricalLaw (hs q)
            (fun i => rowOutcomes S t q (π (e q i))))).2
        rw [lemma2_corrected_explicit_cdf_empirical] at hh
        linarith
      simp only [if_neg (hnot _)]
      simp [designExpectation]
    have hz : scaledProbabilityLimsup S (fun q π => η ≤ cdfDistance (cdf P)
        (empiricalCDF (fun i => rowOutcomes S t q (π (e q i))))) = 0 := by
      simp [scaledProbabilityLimsup, hp]
    rw [hz]
    exact bot_le

theorem lemma2_corrected_explicit_proof (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hleft : AtomLeftConvergence S H) :
    (∀ η, 0 < η → 0 < correctedPartitionInteger η) ∧
    (∀ a b, 0 < a → a ≤ b → correctedPartitionInteger b ≤ correctedPartitionInteger a) ∧
    (∀ t, Tendsto (fun q => cdfDistance (lawCDF H t)
      (empiricalCDF (rowOutcomes S t q))) atTop (𝓝 0)) ∧
    (∀ η, 0 < η →
      scaledProbabilityLimsup S (fun q π => η ≤
        cdfDistance (lawCDF H true) (sampledCDF S true q π)) ≤
        ENNReal.ofReal ((1 - θ * ρ) * correctedPartitionInteger η / (θ * ρ * η ^ 2)) ∧
      scaledProbabilityLimsup S (fun q π => η ≤
        cdfDistance (lawCDF H false) (sampledCDF S false q π)) ≤
        ENNReal.ofReal ((1 - θ * (1 - ρ)) * correctedPartitionInteger η /
          (θ * (1 - ρ) * η ^ 2))) := by
  have hα1 : 0 < θ * ρ := mul_pos h.1 h.2.2.1
  have hα0 : 0 < θ * (1 - ρ) := mul_pos h.1 (sub_pos.mpr h.2.2.2.1)
  have hm := h.2.2.2.2.1
  have hn := h.2.2.2.2.2.1
  have hk := GP022B1b_control_ratio S θ ρ hm hn
  let e1 : (q : ℕ) → Fin (S.design q).m → Fin (S.design q).N := fun q i =>
    ⟨i.val, by have := i.isLt; have := (S.design q).sample_le; omega⟩
  let e0 : (q : ℕ) → Fin (S.design q).k → Fin (S.design q).N := fun q i =>
    ⟨(S.design q).m + i.val, by have := i.isLt; have := (S.design q).sample_le; omega⟩
  have he1 (q : ℕ) : Function.Injective (e1 q) := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (S.design q).N => z.val) hij)
  have he0 (q : ℕ) : Function.Injective (e0 q) := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg (fun z : Fin (S.design q).N => z.val) hij
    dsimp [e0] at hh
    omega
  refine ⟨corrected_partition_integer_properties.1, corrected_partition_integer_properties.2,
    lemma2_corrected_explicit_uniform S H θ ρ h hleft, ?_⟩
  intro η hη
  constructor
  · have hh := lemma2_corrected_explicit_tail S H θ ρ h hleft true (fun q => (S.design q).m)
      (fun q => by have := (S.design q).treatment_min; omega) e1 he1 (θ * ρ) hα1 hm η hη
    have hfun : (fun q π => η ≤ cdfDistance (lawCDF H true) (sampledCDF S true q π)) =
        (fun q π => η ≤ cdfDistance
          (cdf (lemma2_corrected_explicit_marginal H true : Measure ℝ))
          (empiricalCDF (fun i => rowOutcomes S true q (π (e1 q i))))) := by
      funext q π
      rw [lemma2_corrected_explicit_cdf_marginal]
      rfl
    rw [hfun]
    exact hh
  · have hh := lemma2_corrected_explicit_tail S H θ ρ h hleft false (fun q => (S.design q).k)
      (fun q => by have := (S.design q).control_min; omega) e0 he0 (θ * (1 - ρ)) hα0 hk η hη
    have hfun : (fun q π => η ≤ cdfDistance (lawCDF H false) (sampledCDF S false q π)) =
        (fun q π => η ≤ cdfDistance
          (cdf (lemma2_corrected_explicit_marginal H false : Measure ℝ))
          (empiricalCDF (fun i => rowOutcomes S false q (π (e0 q i))))) := by
      funext q π
      rw [lemma2_corrected_explicit_cdf_marginal]
      rfl
    rw [hfun]
    exact hh

private lemma bounded_direct_finite_allocation_bound (N s : ℕ) (hs : 0 < s) (hsN : s ≤ N)
    (hN : 4 ≤ N) (c : ℝ) (hc : 0 < c) (hm : c * N ≤ s) (C : ℝ) :
    C ^ 2 * ((N : ℝ) - s) / (((N : ℝ) - 1) * s) ≤ C ^ 2 / (c * N) := by
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsR1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsNR : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hn : (0 : ℝ) < N := by linarith
  have hNm1 : 0 < (N : ℝ) - 1 := by linarith
  have h1 : ((N : ℝ) - s) / (((N : ℝ) - 1) * s) ≤ 1 / (s : ℝ) := by
    apply (div_le_iff₀ (mul_pos hNm1 hsR)).2
    field_simp [ne_of_gt hsR]
    nlinarith
  have h2 : 1 / (s : ℝ) ≤ 1 / (c * N) :=
    one_div_le_one_div_of_le (mul_pos hc hn) hm
  calc
    _ = C ^ 2 * (((N : ℝ) - s) / (((N : ℝ) - 1) * s)) := by ring
    _ ≤ C ^ 2 * (1 / (c * N)) := mul_le_mul_of_nonneg_left (h1.trans h2) (sq_nonneg _)
    _ = _ := by ring

theorem bounded_direct_finite_proof (d : Design) (y1 y0 : Fin d.N → ℝ) (C c : ℝ)
    (hC : 0 ≤ C) (hy : ∀ i, |y1 i| ≤ C ∧ |y0 i| ≤ C)
    (hc : 0 < c) (hm : c * d.N ≤ d.m) (hk : c * d.N ≤ d.k)
    (hN : 2 / c ≤ (d.N : ℝ)) :
    let D1 := fun π => integratedCDFError C y1 (observedTreatment d y1 π)
    let D0 := fun π => integratedCDFError C y0 (observedControl d y0 π)
    designExpectation d (fun π => D1 π ^ 2) ≤ C ^ 2 * ((d.N : ℝ) - d.m) /
      (((d.N : ℝ) - 1) * d.m) ∧
    C ^ 2 * ((d.N : ℝ) - d.m) / (((d.N : ℝ) - 1) * d.m) ≤ C ^ 2 / (c * d.N) ∧
    designExpectation d (fun π => D0 π ^ 2) ≤ C ^ 2 * ((d.N : ℝ) - d.k) /
      (((d.N : ℝ) - 1) * d.k) ∧
    C ^ 2 * ((d.N : ℝ) - d.k) / (((d.N : ℝ) - 1) * d.k) ≤ C ^ 2 / (c * d.N) ∧
    designExpectation d (fun π => (D1 π + D0 π) ^ 2) ≤ 4 * C ^ 2 / (c * d.N) ∧
    (∀ B π, (d.N : ℝ) * |estimatedVariance d y1 y0 B π - populationBound d y1 y0 B| ≤
      (16 / c + 8) * C * (D1 π + D0 π) + 8 * C ^ 2 / (c ^ 2 * d.N)) ∧
    (∀ ε, 0 < ε → 16 * C ^ 2 / (c ^ 2 * ε) ≤ (d.N : ℝ) → ∀ B,
      designProbability d (fun π => ε ≤ (d.N : ℝ) *
        |estimatedVariance d y1 y0 B π - populationBound d y1 y0 B|) ≤
          16 * (16 / c + 8) ^ 2 * C ^ 4 / (c * d.N * ε ^ 2)) := by
  classical
  dsimp only
  have hmnat : 0 < d.m := by have := d.treatment_min; omega
  have hknat : 0 < d.k := by have := d.control_min; omega
  let e1 : Fin d.m → Fin d.N := fun i =>
    ⟨i.val, by have := i.isLt; have := d.sample_le; omega⟩
  let e0 : Fin d.k → Fin d.N := fun i =>
    ⟨d.m + i.val, by have := i.isLt; have := d.sample_le; omega⟩
  have he1 : Function.Injective e1 := by
    intro i j hij
    exact Fin.ext (congrArg (fun q : Fin d.N => q.val) hij)
  have he0 : Function.Injective e0 := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    dsimp [e0] at h
    omega
  have h1 := GP022B1b_integrated_moment d hmnat e1 he1 y1 C hC
  have h0 := GP022B1b_integrated_moment d hknat e0 he0 y0 C hC
  have ha1 := bounded_direct_finite_allocation_bound d.N d.m hmnat
    (by have := d.sample_le; omega) d.population_min c hc hm C
  have ha0 := bounded_direct_finite_allocation_bound d.N d.k hknat
    (by have := d.sample_le; omega) d.population_min c hc hk C
  refine ⟨h1, ha1, h0, ha0, ?_, ?_, ?_⟩
  · have hb : designExpectation d (fun π =>
        (integratedCDFError C y1 (observedTreatment d y1 π) +
          integratedCDFError C y0 (observedControl d y0 π)) ^ 2) ≤
        designExpectation d (fun π =>
          2 * integratedCDFError C y1 (observedTreatment d y1 π) ^ 2 +
          2 * integratedCDFError C y0 (observedControl d y0 π) ^ 2) := by
      apply Finset.expect_le_expect
      intro π _
      nlinarith [sq_nonneg (integratedCDFError C y1 (observedTreatment d y1 π) -
        integratedCDFError C y0 (observedControl d y0 π))]
    have hh1 : designExpectation d (fun π =>
        integratedCDFError C y1 (observedTreatment d y1 π) ^ 2) ≤ C ^ 2 / (c * d.N) := h1.trans ha1
    have hh0 : designExpectation d (fun π =>
        integratedCDFError C y0 (observedControl d y0 π) ^ 2) ≤ C ^ 2 / (c * d.N) := h0.trans ha0
    simp only [designExpectation, Finset.expect_add_distrib, ← Finset.mul_expect] at *
    linarith only [hb, hh1, hh0,
      (by ring : 4 * C ^ 2 / (c * d.N) = 4 * (C ^ 2 / (c * d.N)))]
  · exact GP022B1b_deterministic d y1 y0 C c hC hy hc hm hk
  · intro ε hε hT B
    exact GP022B1b_finite_rate d y1 y0 C c hC hy hc hm hk ε hε hT B

end
end AronowAudit.P022.Wave1
