import AronowAudit.P022.Wave1.SharpBounds
import AronowAudit.P022.Wave1.Gap.GP022B1b
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD

namespace AronowAudit.P022.Wave1

open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option autoImplicit false

noncomputable section

local instance instDecidableGLP022B4 (p : Prop) : Decidable p := Classical.propDecidable p

private lemma T7_sum_cycles (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (4 * n), f (i % 4)) =
      (n : ℝ) * (∑ i ∈ Finset.range 4, f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have he : (∑ i ∈ Finset.range 4, f ((4 * n + i) % 4)) =
        ∑ i ∈ Finset.range 4, f i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
      simp [Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
    rw [he]
    push_cast
    ring

private lemma T7_sum_prefix (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f (i % 4)) =
      (n / 4 : ℕ) * (∑ i ∈ Finset.range 4, f i) +
        ∑ i ∈ Finset.range (n % 4), f i := by
  conv_lhs => rw [← Nat.div_add_mod n 4]
  rw [Finset.sum_range_add, T7_sum_cycles]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi4 : i < 4 := (Finset.mem_range.mp hi).trans (Nat.mod_lt n (by decide))
  simp [Nat.add_mod, Nat.mod_eq_of_lt hi4]

private lemma T7_mean_cycles (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    finiteMean (fun i : Fin (4 * n) => f (i.val % 4)) =
      (∑ i ∈ Finset.range 4, f i) / 4 := by
  rw [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    (Fin.sum_univ_eq_sum_range (fun i => f (i % 4))), T7_sum_cycles]
  push_cast
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  <;> ring

private lemma T7_mean_limit (f : ℕ → ℝ) :
    Tendsto (fun q => finiteMean (fun i : Fin (q + 4) => f (i.val % 4))) atTop
      (𝓝 ((∑ i ∈ Finset.range 4, f i) / 4)) := by
  let A := (∑ i ∈ Finset.range 4, f i) / 4
  let B := (∑ i ∈ Finset.range 4, |f i|) + 4 * |A|
  have hb (q : ℕ) :
      |finiteMean (fun i : Fin (q + 4) => f (i.val % 4)) - A| ≤ B / (q + 4) := by
    have hN : (0 : ℝ) < (q : ℝ) + 4 := by positivity
    have hr : (q + 4) % 4 ≤ 4 := (Nat.mod_lt _ (by decide : 0 < 4)).le
    have htail : |∑ i ∈ Finset.range ((q + 4) % 4), f i| ≤
        ∑ i ∈ Finset.range 4, |f i| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hr)
          (fun i _ _ => abs_nonneg (f i)))
    have hrem : (((q + 4) % 4 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hr
    have hcast : (q : ℝ) + 4 =
        4 * (((q + 4) / 4 : ℕ) : ℝ) + (((q + 4) % 4 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod (q + 4) 4).symm
    have heq : finiteMean (fun i : Fin (q + 4) => f (i.val % 4)) - A =
        ((∑ i ∈ Finset.range ((q + 4) % 4), f i) -
          (((q + 4) % 4 : ℕ) : ℝ) * A) / ((q : ℝ) + 4) := by
      rw [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
        (Fin.sum_univ_eq_sum_range (fun i => f (i % 4))), T7_sum_prefix]
      push_cast
      dsimp [A]
      field_simp
      rw [hcast]
      ring
    rw [heq, abs_div, abs_of_pos hN]
    apply div_le_div_of_nonneg_right _ hN.le
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_nonneg (show 0 ≤ (((q + 4) % 4 : ℕ) : ℝ) by positivity)]
    dsimp [B]
    nlinarith [abs_nonneg A]
  have hzero : Tendsto (fun q : ℕ => B / ((q : ℝ) + 4)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (show Tendsto (fun q : ℕ => (q : ℝ) + 4) atTop atTop from
      tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop)
  have habs : Tendsto (fun q =>
      |finiteMean (fun i : Fin (q + 4) => f (i.val % 4)) - A|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hb hzero
  exact (tendsto_sub_nhds_zero_iff).mp ((tendsto_zero_iff_abs_tendsto_zero _).mpr habs)

private def T7_corner (i : ℕ) : ℝ × ℝ :=
  (if i < 2 then 0 else 1, if i % 2 = 0 then 0 else 1)

private lemma T7_corner_index (i : ℕ) :
    (cornerWitness.y1 i, cornerWitness.y0 i) = T7_corner (i % 4) := by
  simp only [cornerWitness, T7_corner]
  rw [Nat.mod_mod_of_dvd i (by decide : 2 ∣ 4)]

private lemma T7_corner_average (f : ℝ × ℝ → ℝ) :
    (∑ i ∈ Finset.range 4, f (T7_corner i)) / 4 =
      (f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1)) / 4 := by
  norm_num [Finset.sum_range_succ, T7_corner]

-- The four-atom integral calculation follows P001.four_atom_integral.
private lemma T7_corner_integral (f : ℝ × ℝ → ℝ) :
    (∫ p, f p ∂(cornerLaw : Measure (ℝ × ℝ))) =
      (f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1)) / 4 := by
  have hi (p : ℝ × ℝ) : Integrable f ((1 / 4 : ℝ≥0∞) • Measure.dirac p) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ p, f p ∂(_ + _ + _ + _)) = _
  rw [integral_add_measure (((hi (0, 0)).add_measure (hi (0, 1))).add_measure (hi (1, 0)))
    (hi (1, 1)), integral_add_measure ((hi (0, 0)).add_measure (hi (0, 1))) (hi (1, 0)),
    integral_add_measure (hi (0, 0)) (hi (0, 1))]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  ring

private lemma T7_corner_measure (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
    ((cornerLaw : Measure (ℝ × ℝ)) s).toReal =
      ((if (0, 0) ∈ s then 1 else 0) + (if (0, 1) ∈ s then 1 else 0) +
       (if (1, 0) ∈ s then 1 else 0) + (if (1, 1) ∈ s then 1 else 0) : ℝ) / 4 := by
  change (cornerLaw : Measure (ℝ × ℝ)).real s = _
  rw [← integral_indicator_one hs, T7_corner_integral]
  simp [Set.indicator_apply]

private lemma T7_corner_limits (f : ℝ × ℝ → ℝ) :
    Tendsto (fun q => finiteMean (fun i : Fin (cornerWitness.design q).N =>
      f (cornerWitness.y1 i.val, cornerWitness.y0 i.val))) atTop
      (𝓝 ((f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1)) / 4)) := by
  simp_rw [T7_corner_index]
  simpa only [cornerWitness, reciprocalWitness, T7_corner_average] using
    T7_mean_limit (fun i => f (T7_corner i))

private lemma T7_hypotheses :
    Conditions123 cornerWitness cornerLaw 1 (1 / 2) ∧
    AtomLeftConvergence cornerWitness cornerLaw ∧
    (∀ i, |cornerWitness.y1 i| ≤ 1 ∧ |cornerWitness.y0 i| ≤ 1) := by
  have hcdf (t : Bool) (x : ℝ) :
      Tendsto (fun q => empiricalCDF (rowOutcomes cornerWitness t q) x) atTop
        (𝓝 (lawCDF cornerLaw t x)) := by
    have h := T7_corner_limits (fun p => if (if t then p.1 else p.2) ≤ x then 1 else 0)
    rw [lawCDF, T7_corner_measure _ (by
      cases t <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
        exact measurableSet_le (by fun_prop) measurable_const)]
    cases t <;> simpa [empiricalCDF, rowOutcomes] using h
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
    · simpa [cornerWitness] using reciprocal_allocation_limit.1
    · exact reciprocal_allocation_limit.2
    · intro f
      rw [T7_corner_integral]
      exact T7_corner_limits f
    · intro t x _
      exact hcdf t x
  · intro t x _
    have h := T7_corner_limits (fun p => if (if t then p.1 else p.2) < x then 1 else 0)
    rw [lawLeftCDF, T7_corner_measure _ (by
      cases t <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
        exact measurableSet_lt (by fun_prop) measurable_const)]
    cases t <;> simpa [empiricalLeftCDF, rowOutcomes] using h
  · intro i
    simp only [cornerWitness]
    split_ifs <;> norm_num


private lemma T7_mean_exact (r : ℕ) (f : ℝ × ℝ → ℝ) :
    finiteMean (fun i : Fin (cornerWitness.design (4 * r)).N =>
      f (cornerWitness.y1 i.val, cornerWitness.y0 i.val)) =
      (f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1)) / 4 := by
  simp_rw [T7_corner_index]
  have hN : (cornerWitness.design (4 * r)).N = 4 * (r + 1) := by
    simp [cornerWitness, reciprocalWitness]; omega
  have h := T7_mean_cycles (fun i => f (T7_corner i)) (r + 1) (by omega)
  rw [← hN] at h
  exact h.trans (T7_corner_average f)

private lemma T7_marginal_perm (r : ℕ) :
    List.Perm (List.ofFn (rowOutcomes cornerWitness true (4 * r)))
      (List.ofFn (rowOutcomes cornerWitness false (4 * r))) := by
  have hN : (cornerWitness.design (4 * r)).N = (r + 1) * 4 := by
    simp [cornerWitness, reciprocalWitness]; omega
  let e : Fin (cornerWitness.design (4 * r)).N ≃ Fin (r + 1) × Fin 4 :=
    (finCongr hN).trans finProdFinEquiv.symm
  let σ : Equiv.Perm (Fin (cornerWitness.design (4 * r)).N) :=
    (e.trans (Equiv.prodCongr (Equiv.refl _) (Equiv.swap (1 : Fin 4) 2))).trans e.symm
  have heq : (fun i => rowOutcomes cornerWitness false (4 * r) (σ i)) =
      rowOutcomes cornerWitness true (4 * r) := by
    funext i
    obtain ⟨⟨j, l⟩, rfl⟩ := e.symm.surjective i
    simp only [σ, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodCongr_apply,
      Equiv.refl_apply]
    fin_cases l <;>
      norm_num [e, Equiv.symm_trans_apply, rowOutcomes, cornerWitness, finProdFinEquiv,
        Nat.add_mod, Nat.mul_mod, Equiv.swap_apply_def]
  simpa only [Function.comp_def, heq] using σ.ofFn_comp_perm (rowOutcomes cornerWitness false (4 * r))

private lemma T7_gap (r : ℕ) :
    ((cornerWitness.design (4 * r)).N : ℝ) *
      (populationBound (cornerWitness.design (4 * r))
        (rowOutcomes cornerWitness true (4 * r)) (rowOutcomes cornerWitness false (4 * r)) .H -
       trueVariance (cornerWitness.design (4 * r))
        (rowOutcomes cornerWitness true (4 * r)) (rowOutcomes cornerWitness false (4 * r))) ≥ 1 / 2 := by
  let d := cornerWitness.design (4 * r)
  let y1 := rowOutcomes cornerWitness true (4 * r)
  let y0 := rowOutcomes cornerWitness false (4 * r)
  have hN : (0 : ℝ) < d.N := by exact_mod_cast (show 0 < d.N by have := d.population_min; omega)
  have hN1 : (0 : ℝ) < (d.N : ℝ) - 1 := by
    have h := d.population_min; have : (4 : ℝ) ≤ d.N := by exact_mod_cast h
    linarith
  letI : NeZero d.N := ⟨by have := d.population_min; omega⟩
  have hm : (d.m : ℝ) = (d.N : ℝ) / 2 := by
    have hmN : 2 * d.m = d.N := by dsimp [d, cornerWitness, reciprocalWitness]; omega
    have hr : (2 : ℝ) * d.m = d.N := by exact_mod_cast hmN
    linarith
  have hk : (d.k : ℝ) = (d.N : ℝ) / 2 := by
    have hkN : 2 * d.k = d.N := by dsimp [d, cornerWitness, reciprocalWitness]; omega
    have hr : (2 : ℝ) * d.k = d.N := by exact_mod_cast hkN
    linarith
  have hμ1 : finiteMean y1 = 1 / 2 := by
    have h := T7_mean_exact r Prod.fst
    norm_num [y1, rowOutcomes] at h ⊢
    exact h
  have hμ0 : finiteMean y0 = 1 / 2 := by
    have h := T7_mean_exact r Prod.snd
    norm_num [y0, rowOutcomes] at h ⊢
    exact h
  have hv1 : finiteVariance y1 = 1 / 4 := by
    rw [finiteVariance, hμ1]
    have h := T7_mean_exact r (fun p => (p.1 - 1 / 2) ^ 2)
    norm_num [y1, rowOutcomes] at h ⊢
    exact h
  have hv0 : finiteVariance y0 = 1 / 4 := by
    rw [finiteVariance, hμ0]
    have h := T7_mean_exact r (fun p => (p.2 - 1 / 2) ^ 2)
    norm_num [y0, rowOutcomes] at h ⊢
    exact h
  have hc : finiteCovariance y1 y0 = 0 := by
    rw [finiteCovariance, hμ1, hμ0]
    have h := T7_mean_exact r (fun p => (p.1 - 1 / 2) * (p.2 - 1 / 2))
    norm_num [y1, y0, rowOutcomes] at h ⊢
    exact h
  have hsorted : sortedValues y0 = sortedValues y1 := by
    have hp := ((SharpBounds.n2_proof y0).1.trans (T7_marginal_perm r).symm).trans
      (SharpBounds.n2_proof y1).1.symm
    have he := hp.eq_of_sortedLE (by
      rw [SharpBounds.sortedValues_ofFn]; exact List.sortedLE_mergeSort)
      (by rw [SharpBounds.sortedValues_ofFn]; exact List.sortedLE_mergeSort)
    exact List.ofFn_injective he
  have hcov : sharpCovariance y1 y0 .H = 1 / 4 := by
    have hint : (∫ u in (0 : ℝ)..1, empiricalQuantile y1 u * empiricalQuantile y0 u) =
        finiteMean (fun i => (sortedValues y1 i) ^ 2) := by
      apply SharpBounds.n4_proof
      intro j u hl hu
      rw [(SharpBounds.n3_proof y1 j u hl hu).1,
        (SharpBounds.n3_proof y0 j u hl hu).1, hsorted]
      ring
    simp only [sharpCovariance, if_pos rfl, ite_true]
    rw [hint]
    rw [SharpBounds.n1_proof _ _ (SharpBounds.n2_proof y1).1 (fun x => x ^ 2), hμ1, hμ0]
    have hs : finiteMean (fun i => y1 i ^ 2) = 1 / 2 := by
      have h := T7_mean_exact r (fun p => p.1 ^ 2)
      norm_num [y1, rowOutcomes] at h ⊢
      exact h
    rw [hs]; norm_num
  have hvar := (sharp_bounds_variance_and_all_couplings d y1 y0).2.1
  change (d.N : ℝ) * (populationBound d y1 y0 .H - trueVariance d y1 y0) ≥ 1 / 2
  rw [hvar, populationBound, hv1, hv0, hc, hcov]
  unfold varianceExpression
  rw [hm, hk]
  have heq : (d.N : ℝ) *
      ((((d.N : ℝ) - (d.N : ℝ) / 2) / ((d.N : ℝ) / 2) * (1 / 4) +
        ((d.N : ℝ) - (d.N : ℝ) / 2) / ((d.N : ℝ) / 2) * (1 / 4) + 2 * (1 / 4)) /
        ((d.N : ℝ) - 1) -
       (((d.N : ℝ) - (d.N : ℝ) / 2) / ((d.N : ℝ) / 2) * (1 / 4) +
        ((d.N : ℝ) - (d.N : ℝ) / 2) / ((d.N : ℝ) / 2) * (1 / 4) + 2 * 0) /
        ((d.N : ℝ) - 1)) = (d.N : ℝ) / (2 * ((d.N : ℝ) - 1)) := by
    field_simp
    <;> ring
  rw [heq]
  apply (le_div_iff₀ (by positivity : 0 < 2 * ((d.N : ℝ) - 1))).2
  linarith


private lemma T7_wrong_tail (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ)) :
    Filter.limsup (fun r => ENNReal.ofReal
      (((cornerWitness.design (4 * r)).N : ℝ) *
        designProbability (cornerWitness.design (4 * r)) (fun π => ε ≤
          ((cornerWitness.design (4 * r)).N : ℝ) *
          |estimatedVariance (cornerWitness.design (4 * r))
            (rowOutcomes cornerWitness true (4 * r))
            (rowOutcomes cornerWitness false (4 * r)) .H π -
           trueVariance (cornerWitness.design (4 * r))
            (rowOutcomes cornerWitness true (4 * r))
            (rowOutcomes cornerWitness false (4 * r))|))) atTop = ⊤ := by
  let δ := (1 / 2 : ℝ) - ε
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hsize : Tendsto (fun r => ((cornerWitness.design (4 * r)).N : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (f := fun r : ℕ => (r : ℝ)) _ tendsto_natCast_atTop_atTop
    intro r
    change (r : ℝ) ≤ ((4 * r + 4 : ℕ) : ℝ)
    exact_mod_cast (show r ≤ 4 * r + 4 by omega)
  have heT := hsize.eventually (eventually_ge_atTop (64 / δ))
  have heP := hsize.eventually (eventually_ge_atTop (102400 / δ ^ 2))
  have hp : ∀ᶠ r in atTop,
      1 / 2 ≤ designProbability (cornerWitness.design (4 * r)) (fun π => ε ≤
        ((cornerWitness.design (4 * r)).N : ℝ) *
        |estimatedVariance (cornerWitness.design (4 * r))
          (rowOutcomes cornerWitness true (4 * r))
          (rowOutcomes cornerWitness false (4 * r)) .H π -
         trueVariance (cornerWitness.design (4 * r))
          (rowOutcomes cornerWitness true (4 * r))
          (rowOutcomes cornerWitness false (4 * r))|) := by
    filter_upwards [heT, heP] with r hT hP
    let d := cornerWitness.design (4 * r)
    let y1 := rowOutcomes cornerWitness true (4 * r)
    let y0 := rowOutcomes cornerWitness false (4 * r)
    have hN : (0 : ℝ) < d.N := by
      exact_mod_cast (show 0 < d.N by have := d.population_min; omega)
    have hm : (1 / 2 : ℝ) * d.N ≤ d.m := by
      have hh : d.N ≤ 2 * d.m := by dsimp [d, cornerWitness, reciprocalWitness]; omega
      have hhR : (d.N : ℝ) ≤ 2 * d.m := by exact_mod_cast hh
      linarith
    have hk : (1 / 2 : ℝ) * d.N ≤ d.k := by
      have hh : d.N ≤ 2 * d.k := by dsimp [d, cornerWitness, reciprocalWitness]; omega
      have hhR : (d.N : ℝ) ≤ 2 * d.k := by exact_mod_cast hh
      linarith
    have hrate := GP022B1b_finite_rate d y1 y0 1 (1 / 2) (by norm_num)
      (fun i => T7_hypotheses.2.2 i.val) (by norm_num) hm hk δ hδ (by
        norm_num
        convert hT using 1 <;> ring) .H
    have hrate' : designProbability d (fun π => δ ≤ (d.N : ℝ) *
        |estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H|) ≤ 1 / 2 := by
      apply hrate.trans
      norm_num
      have hpp := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hP
      apply (div_le_iff₀ (by positivity : 0 < 1 / 2 * (d.N : ℝ) * δ ^ 2)).2
      nlinarith
    have hcover : (1 : ℝ) ≤
        designProbability d (fun π => δ ≤ (d.N : ℝ) *
          |estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H|) +
        designProbability d (fun π => ε ≤ (d.N : ℝ) *
          |estimatedVariance d y1 y0 .H π - trueVariance d y1 y0|) := by
      rw [designProbability, designProbability, designExpectation, designExpectation,
        ← Finset.expect_add_distrib]
      have hc : (1 : ℝ) = (𝔼 _π : Assignment d, (1 : ℝ)) :=
        (Finset.expect_const Finset.univ_nonempty _).symm
      rw [hc]
      apply Finset.expect_le_expect
      intro π _
      by_cases hb : δ ≤ (d.N : ℝ) * |estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H|
      · simp only [hb, if_true]
        split_ifs <;> norm_num
      · have hsmall : (d.N : ℝ) * |estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H| < δ :=
          lt_of_not_ge hb
        have hgap := T7_gap r
        change (d.N : ℝ) * (populationBound d y1 y0 .H - trueVariance d y1 y0) ≥ 1 / 2 at hgap
        have hlow := neg_abs_le (estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H)
        have hlowN := mul_le_mul_of_nonneg_left hlow hN.le
        have habs := le_abs_self (estimatedVariance d y1 y0 .H π - trueVariance d y1 y0)
        have habsN := mul_le_mul_of_nonneg_left habs hN.le
        have hw : ε ≤ (d.N : ℝ) * |estimatedVariance d y1 y0 .H π - trueVariance d y1 y0| := by
          dsimp [δ] at hsmall
          nlinarith
        simp [hb, hw]
    change 1 / 2 ≤ designProbability d _
    linarith
  apply Filter.Tendsto.limsup_eq
  apply ENNReal.tendsto_ofReal_atTop.comp
  apply tendsto_atTop_mono' atTop _ (hsize.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hp] with r hr
  exact mul_le_mul_of_nonneg_left hr (by positivity)

theorem proposition2_printed_counterexample_proof :
    Conditions123 cornerWitness cornerLaw 1 (1 / 2) ∧
    AtomLeftConvergence cornerWitness cornerLaw ∧
    (∀ i, |cornerWitness.y1 i| ≤ 1 ∧ |cornerWitness.y0 i| ≤ 1) ∧
    scaledProbabilityLimsup cornerWitness (fun q π => (1 - 1 : ℝ) ≤
      |lastIntegralTerm (cornerWitness.design q) (rowOutcomes cornerWitness true q)
        (rowOutcomes cornerWitness false q) 1 π|) = ⊤ ∧
    (∀ ε, 0 < ε → ε < (1 / 2 : ℝ) →
      Filter.limsup (fun r => ENNReal.ofReal
        (((cornerWitness.design (4 * r)).N : ℝ) *
          designProbability (cornerWitness.design (4 * r)) (fun π => ε ≤
            ((cornerWitness.design (4 * r)).N : ℝ) *
            |estimatedVariance (cornerWitness.design (4 * r))
              (rowOutcomes cornerWitness true (4 * r))
              (rowOutcomes cornerWitness false (4 * r)) .H π -
             trueVariance (cornerWitness.design (4 * r))
              (rowOutcomes cornerWitness true (4 * r))
              (rowOutcomes cornerWitness false (4 * r))|))) atTop = ⊤) := by
  refine ⟨T7_hypotheses.1, T7_hypotheses.2.1, T7_hypotheses.2.2, ?_, T7_wrong_tail⟩
  simpa only [sub_self] using zero_tolerance_tail cornerWitness (fun q π =>
    lastIntegralTerm (cornerWitness.design q) (rowOutcomes cornerWitness true q)
      (rowOutcomes cornerWitness false q) 1 π)

-- Union-grid geometry and discrepancy bounds.
private def T8_grid (m k : ℕ) : Finset ℝ :=
  ((Finset.range (m + 1)).image (fun i : ℕ => (i : ℝ) / m)) ∪
    ((Finset.range (k + 1)).image (fun j : ℕ => (j : ℝ) / k))

private theorem T8_grid_bounds {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    {x : ℝ} (hx : x ∈ T8_grid m k) : 0 ≤ x ∧ x ≤ 1 := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    constructor
    · positivity
    · exact (div_le_one (by exact_mod_cast hm)).2 (by exact_mod_cast hi')
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    constructor
    · positivity
    · exact (div_le_one (by exact_mod_cast hk)).2 (by exact_mod_cast hi')

private theorem T8_grid_zero (m k : ℕ) : (0 : ℝ) ∈ T8_grid m k := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩

private theorem T8_grid_one {m k : ℕ} (hm : 0 < m) : (1 : ℝ) ∈ T8_grid m k := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨m, by simp, by simp [ne_of_gt hm]⟩

private theorem T8_point_get {m k i : ℕ} (hi : i < (partitionKnots m k).length) :
    partitionPoint m k i = (partitionKnots m k).get ⟨i, hi⟩ := by
  exact List.getD_eq_get (partitionKnots m k) 0 ⟨i, hi⟩

private theorem T8_point_mem {m k i : ℕ} (hi : i < (partitionKnots m k).length) :
    partitionPoint m k i ∈ T8_grid m k := by
  rw [T8_point_get hi]
  exact (Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)

private theorem T8_point_index {m k : ℕ} {x : ℝ} (hx : x ∈ T8_grid m k) :
    ∃ i, i < (partitionKnots m k).length ∧ partitionPoint m k i = x := by
  have hx' : x ∈ partitionKnots m k := (Finset.mem_sort (· ≤ ·)).mpr hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx'
  exact ⟨i.val, i.isLt, (T8_point_get i.isLt).trans hi⟩

private theorem T8_point_strict {m k i j : ℕ} (hij : i < j)
    (hj : j < (partitionKnots m k).length) :
    partitionPoint m k i < partitionPoint m k j := by
  have hi : i < (partitionKnots m k).length := hij.trans hj
  rw [T8_point_get hi, T8_point_get hj]
  exact (Finset.sortedLT_sort (T8_grid m k)).strictMono_get
    (show (⟨i, hi⟩ : Fin (partitionKnots m k).length) < ⟨j, hj⟩ from hij)

private theorem T8_point_mono {m k i j : ℕ} (hij : i ≤ j)
    (hj : j < (partitionKnots m k).length) :
    partitionPoint m k i ≤ partitionPoint m k j := by
  rcases hij.eq_or_lt with h | h
  · subst j; exact le_rfl
  · exact (T8_point_strict h hj).le

private theorem T8_endpoints {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    0 < partitionCells m k ∧
    partitionCells m k + 1 = (partitionKnots m k).length ∧
    partitionPoint m k 0 = 0 ∧ partitionPoint m k (partitionCells m k) = 1 := by
  obtain ⟨i0, hi0, h0⟩ := T8_point_index (T8_grid_zero m k)
  obtain ⟨i1, hi1, h1⟩ := T8_point_index (T8_grid_one (k := k) hm)
  have hne : i0 ≠ i1 := by intro heq; subst i1; linarith
  have hlen : 2 ≤ (partitionKnots m k).length := by omega
  have hP : partitionCells m k + 1 = (partitionKnots m k).length := by
    unfold partitionCells
    omega
  have hPlt : partitionCells m k < (partitionKnots m k).length := by omega
  have h0lt : 0 < (partitionKnots m k).length := by omega
  have hlow := (T8_grid_bounds hm hk (T8_point_mem h0lt)).1
  have hupp := (T8_grid_bounds hm hk (T8_point_mem hPlt)).2
  have h0le := T8_point_mono (m := m) (k := k) (Nat.zero_le i0) hi0
  have h1le := T8_point_mono (m := m) (k := k)
    (show i1 ≤ partitionCells m k by omega) hPlt
  refine ⟨by omega, hP, ?_, ?_⟩
  · linarith
  · linarith

private theorem T8_no_interior_knot {m k r : ℕ}
    (hr : r < partitionCells m k) {x : ℝ} (hx : x ∈ T8_grid m k) :
    ¬ (partitionPoint m k r < x ∧ x < partitionPoint m k (r + 1)) := by
  obtain ⟨i, hi, hix⟩ := T8_point_index hx
  have hright : r + 1 < (partitionKnots m k).length := by
    unfold partitionCells at hr
    omega
  intro h
  by_cases hir : i ≤ r
  · have hh := T8_point_mono (m := m) (k := k) hir (by omega)
    linarith
  · have hh := T8_point_mono (m := m) (k := k) (show r + 1 ≤ i by omega) hi
    linarith

private theorem T8_cell_bounds {m k r : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hr : r < partitionCells m k) {u : ℝ}
    (hu : partitionPoint m k r < u ∧ u < partitionPoint m k (r + 1)) :
    0 < u ∧ u < 1 := by
  have hl : r < (partitionKnots m k).length := by unfold partitionCells at hr; omega
  have hh : r + 1 < (partitionKnots m k).length := by unfold partitionCells at hr; omega
  have h0 := (T8_grid_bounds hm hk (T8_point_mem hl)).1
  have h1 := (T8_grid_bounds hm hk (T8_point_mem hh)).2
  constructor <;> linarith [hu.1, hu.2]

private theorem T8_rank_grid {m k s : ℕ} (hs : s = m ∨ s = k)
    (j : ℕ) (hj : j ≤ s) : (j : ℝ) / s ∈ T8_grid m k := by
  rcases hs with rfl | rfl
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

private theorem T8_ceil_cell {m k s r : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hs : s = m ∨ s = k) (hr : r < partitionCells m k) {u v : ℝ}
    (hu : partitionPoint m k r < u ∧ u < partitionPoint m k (r + 1))
    (hv : partitionPoint m k r < v ∧ v < partitionPoint m k (r + 1)) :
    Nat.ceil ((s : ℝ) * u) = Nat.ceil ((s : ℝ) * v) := by
  have hsN : 0 < s := by rcases hs with rfl | rfl <;> assumption
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hsN
  have hu01 := T8_cell_bounds hm hk hr hu
  have hv01 := T8_cell_bounds hm hk hr hv
  have hdir : ∀ {x y : ℝ},
      partitionPoint m k r < x ∧ x < partitionPoint m k (r + 1) →
      partitionPoint m k r < y ∧ y < partitionPoint m k (r + 1) →
      x < 1 → y < 1 → Nat.ceil ((s : ℝ) * x) ≤ Nat.ceil ((s : ℝ) * y) := by
    intro x y hx hy hx1 hy1
    by_contra hnle
    have hlt : Nat.ceil ((s : ℝ) * y) < Nat.ceil ((s : ℝ) * x) := by omega
    let j := Nat.ceil ((s : ℝ) * y)
    have hj : j ≤ s := Nat.ceil_le.mpr (by
      have hh := mul_lt_mul_of_pos_left hy1 hsR
      nlinarith [hh])
    have hleft : partitionPoint m k r < (j : ℝ) / s := by
      have hle : y ≤ (j : ℝ) / s := (le_div_iff₀ hsR).2 (by
        nlinarith [Nat.le_ceil ((s : ℝ) * y)])
      exact hy.1.trans_le hle
    have hright : (j : ℝ) / s < partitionPoint m k (r + 1) := by
      have hlt' : (j : ℝ) < (s : ℝ) * x := Nat.lt_ceil.mp hlt
      have hlt'' : (j : ℝ) / s < x := (div_lt_iff₀ hsR).2 (by nlinarith)
      exact hlt''.trans hx.2
    exact T8_no_interior_knot hr (T8_rank_grid hs j hj) ⟨hleft, hright⟩
  exact le_antisymm (hdir hu hv hu01.2 hv01.2) (hdir hv hu hv01.2 hu01.2)

private theorem T8_reflected_rank {m k s r : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hs : s = m ∨ s = k) (hr : r < partitionCells m k) {u : ℝ}
    (hu : partitionPoint m k r < u ∧ u < partitionPoint m k (r + 1)) :
    Nat.ceil ((s : ℝ) * (1 - u)) = s + 1 - Nat.ceil ((s : ℝ) * u) := by
  have hsN : 0 < s := by rcases hs with rfl | rfl <;> assumption
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hsN
  have hu01 := T8_cell_bounds hm hk hr hu
  let j := Nat.ceil ((s : ℝ) * u)
  have hjpos : 0 < j := Nat.one_le_ceil_iff.mpr (mul_pos hsR hu01.1)
  have hjle : j ≤ s := Nat.ceil_le.mpr (by
    have hh := mul_lt_mul_of_pos_left hu01.2 hsR
    nlinarith [hh])
  have hjspec : ((j - 1 : ℕ) : ℝ) < (s : ℝ) * u ∧ (s : ℝ) * u ≤ (j : ℝ) :=
    (Nat.ceil_eq_iff (by omega : j ≠ 0)).mp rfl
  have hstrict : (s : ℝ) * u < (j : ℝ) := by
    apply lt_of_le_of_ne hjspec.2
    intro heq
    have huj : (j : ℝ) / s = u := (div_eq_iff hsR.ne').2 (by nlinarith [heq])
    exact T8_no_interior_knot hr (T8_rank_grid hs j hjle) (by simpa [huj] using hu)
  have hcastj : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ j)]; norm_num
  have hcastl : ((s + 1 - j : ℕ) : ℝ) = (s : ℝ) + 1 - j := by
    rw [Nat.cast_sub (by omega : j ≤ s + 1)]; push_cast; rfl
  have hcastlm : (((s + 1 - j) - 1 : ℕ) : ℝ) = (s : ℝ) - j := by
    rw [Nat.cast_sub (by omega : 1 ≤ s + 1 - j), hcastl]
    push_cast
    ring
  apply (Nat.ceil_eq_iff (by omega : s + 1 - j ≠ 0)).2
  rw [hcastlm, hcastl]
  constructor <;> nlinarith [hjspec.1]


private lemma T8_grid_reflect {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    {x : ℝ} (hx : x ∈ T8_grid m k) : 1 - x ∈ T8_grid m k := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    apply Finset.mem_union_left
    refine Finset.mem_image.mpr ⟨m - i, by simp, ?_⟩
    rw [Nat.cast_sub hi']
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨k - i, by simp, ?_⟩
    rw [Nat.cast_sub hi']
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp

private lemma T8_point_reflect {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (r : ℕ) (hr : r ≤ partitionCells m k) :
    partitionPoint m k (partitionCells m k - r) = 1 - partitionPoint m k r := by
  let L := partitionKnots m k
  have hnodup : L.Nodup := Finset.sort_nodup _ _
  have hsorted : L.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hmap : (L.reverse.map (fun x => 1 - x)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map, List.pairwise_reverse]
    exact hsorted.imp (by intros; linarith)
  have hperm : (L.reverse.map (fun x => 1 - x)).Perm L := by
    apply (List.perm_ext_iff_of_nodup
      (List.Nodup.map (by intro x y h; linarith) (List.nodup_reverse.mpr hnodup)) hnodup).2
    intro x
    simp only [List.mem_map, List.mem_reverse]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Finset.mem_sort _).mpr (T8_grid_reflect hm hk ((Finset.mem_sort _).mp hy))
    · intro hx
      refine ⟨1 - x, ?_, by ring⟩
      exact (Finset.mem_sort _).mpr (T8_grid_reflect hm hk ((Finset.mem_sort _).mp hx))
  have hL : L.reverse.map (fun x => 1 - x) = L := hperm.eq_of_pairwise' hmap hsorted
  have hlen := (T8_endpoints hm hk).2.1
  have hrL : r < L.length := by dsimp [L]; omega
  have hd : L.getD r 1 = L.getD r 0 := by
    rw [List.getD_eq_get L 1 ⟨r, hrL⟩, List.getD_eq_get L 0 ⟨r, hrL⟩]
  have hh := congrArg (fun l : List ℝ => l.getD r 1) hL
  have hmapD : (L.reverse.map (fun x => 1 - x)).getD r 1 = 1 - L.reverse.getD r 0 := by
    simpa only [sub_zero] using (List.getD_map (l := L.reverse) (d := (0 : ℝ)) (n := r)
      (fun x : ℝ => 1 - x))
  rw [hmapD, List.getD_reverse r hrL, hd] at hh
  have hsub : L.length - 1 - r = partitionCells m k - r := by rfl
  rw [hsub] at hh
  change 1 - partitionPoint m k (partitionCells m k - r) = partitionPoint m k r at hh
  linarith

private lemma T8_ceil_endpoint {m k s r : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hs : s = m ∨ s = k) (hr : r < partitionCells m k) {u : ℝ}
    (hu : partitionPoint m k r < u ∧ u < partitionPoint m k (r + 1)) :
    Nat.ceil ((s : ℝ) * u) = Nat.ceil ((s : ℝ) * partitionPoint m k (r + 1)) := by
  have hsN : 0 < s := by rcases hs with rfl | rfl <;> assumption
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hsN
  have hu01 := T8_cell_bounds hm hk hr hu
  apply le_antisymm (Nat.ceil_mono (mul_le_mul_of_nonneg_left hu.2.le hsR.le))
  by_contra h
  have hlt : Nat.ceil ((s : ℝ) * u) < Nat.ceil ((s : ℝ) * partitionPoint m k (r + 1)) := by omega
  let j := Nat.ceil ((s : ℝ) * u)
  have hj : j ≤ s := Nat.ceil_le.mpr (by
    nlinarith [mul_lt_mul_of_pos_left hu01.2 hsR])
  have hleft : partitionPoint m k r < (j : ℝ) / s := by
    have hle : u ≤ (j : ℝ) / s := (le_div_iff₀ hsR).2 (by nlinarith [Nat.le_ceil ((s : ℝ) * u)])
    exact hu.1.trans_le hle
  have hright : (j : ℝ) / s < partitionPoint m k (r + 1) := by
    apply (div_lt_iff₀ hsR).2
    nlinarith [Nat.lt_ceil.mp hlt]
  exact T8_no_interior_knot hr (T8_rank_grid hs j hj) ⟨hleft, hright⟩

private lemma T8_rank_cells {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (r : ℕ) (hr : r < partitionCells m k) (u : ℝ)
    (hl : partitionPoint m k r < u) (hu : u < partitionPoint m k (r + 1)) :
    Nat.ceil ((m : ℝ) * u) = Nat.ceil ((m : ℝ) * partitionPoint m k (r + 1)) ∧
    Nat.ceil ((k : ℝ) * u) = Nat.ceil ((k : ℝ) * partitionPoint m k (r + 1)) ∧
    k + 1 - Nat.ceil ((k : ℝ) * u) =
      Nat.ceil ((k : ℝ) * partitionPoint m k (partitionCells m k - r)) := by
  refine ⟨T8_ceil_endpoint hm hk (Or.inl rfl) hr ⟨hl, hu⟩,
    T8_ceil_endpoint hm hk (Or.inr rfl) hr ⟨hl, hu⟩, ?_⟩
  rw [← T8_reflected_rank hm hk (Or.inr rfl) hr ⟨hl, hu⟩]
  have hr' : partitionCells m k - 1 - r < partitionCells m k := by omega
  have hp0 := T8_point_reflect hm hk (r + 1) (by omega)
  have hp1 := T8_point_reflect hm hk r (by omega)
  have he0 : partitionCells m k - 1 - r = partitionCells m k - (r + 1) := by omega
  have he1 : partitionCells m k - 1 - r + 1 = partitionCells m k - r := by omega
  have h := T8_ceil_endpoint hm hk (Or.inr rfl) hr' (u := 1 - u) (by
    rw [he1, he0, hp0, hp1]
    constructor <;> linarith)
  simpa only [he1] using h

private lemma T8_midpoint_inside {m k r : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hr : r < partitionCells m k) :
    partitionPoint m k r < cellMidpoint m k r ∧
    cellMidpoint m k r < partitionPoint m k (r + 1) := by
  have he := T8_endpoints hm hk
  have hh := T8_point_strict (m := m) (k := k) (Nat.lt_succ_self r) (by omega)
  unfold cellMidpoint
  constructor <;> linarith

private lemma T8_quadrature {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (F : ℝ → ℝ) (hc : ∀ r < partitionCells m k, ∀ u,
      partitionPoint m k r < u → u < partitionPoint m k (r + 1) →
      F u = F (cellMidpoint m k r)) :
    (∫ u in (0 : ℝ)..1, F u) =
      ∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r * F (cellMidpoint m k r) := by
  have he := T8_endpoints hm hk
  have hpr : ∀ r < partitionCells m k,
      partitionPoint m k r ≤ partitionPoint m k (r + 1) := by
    intro r hr
    exact (T8_point_strict (Nat.lt_succ_self r) (by omega)).le
  have hint : ∀ r < partitionCells m k, IntervalIntegrable F volume
      (partitionPoint m k r) (partitionPoint m k (r + 1)) := by
    intro r hr
    apply (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => F (cellMidpoint m k r)) volume
        (partitionPoint m k r) (partitionPoint m k (r + 1))).congr_uIoo
    rw [Set.uIoo_of_le (hpr r hr)]
    intro u hu
    exact (hc r hr u hu.1 hu.2).symm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := partitionPoint m k) hint
  rw [he.2.2.1, he.2.2.2] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [intervalIntegral.integral_congr_Ioo_of_le (hpr r (Finset.mem_range.mp hr))
    (fun u hu => hc r (Finset.mem_range.mp hr) u hu.1 hu.2)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, cellWidth]

private lemma T8_quantile_cell {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide)
    (r : ℕ) (hr : r < partitionCells m k) (u : ℝ)
    (hl : partitionPoint m k r < u) (hu : u < partitionPoint m k (r + 1)) :
    empiricalQuantile a u = empiricalQuantile a (cellMidpoint m k r) ∧
    empiricalQuantile b (if B = .H then u else 1 - u) =
      empiricalQuantile b (if B = .H then cellMidpoint m k r else 1 - cellMidpoint m k r) := by
  have hmid := T8_midpoint_inside hm hk hr
  have ha := T8_ceil_cell hm hk (Or.inl rfl) hr ⟨hl, hu⟩ hmid
  have hb := T8_ceil_cell hm hk (Or.inr rfl) hr ⟨hl, hu⟩ hmid
  constructor
  · exact congrArg (orderStatistic a) ha
  · cases B with
    | H => simpa only [ite_true, empiricalQuantile] using congrArg (orderStatistic b) hb
    | L =>
      simp only [BoundSide.noConfusion, reduceCtorEq, if_false, empiricalQuantile]
      rw [T8_reflected_rank hm hk (Or.inr rfl) hr ⟨hl, hu⟩,
        T8_reflected_rank hm hk (Or.inr rfl) hr hmid, hb]


private lemma T8_common_cell {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (j : Fin (m * k)) (u : ℝ)
    (hl : (j : ℝ) / (m * k) < u) (hu : u < ((j : ℝ) + 1) / (m * k)) :
    empiricalQuantile a u = sortedValues a
      ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩ ∧
    empiricalQuantile a (1 - u) = sortedValues a
      (⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩ : Fin m).rev := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlow : ((j.val / k : ℕ) : ℝ) * k ≤ j := by
    exact_mod_cast Nat.div_mul_le_self j.val k
  have hupp : (j : ℝ) + 1 ≤ (((j.val / k : ℕ) : ℝ) + 1) * k := by
    exact_mod_cast (show j.val + 1 ≤ (j.val / k + 1) * k by
      rw [Nat.add_mul, one_mul, Nat.mul_comm (j.val / k) k]
      have := Nat.mod_lt j.val hk
      have := Nat.mod_add_div j.val k
      omega)
  have hl' := (div_lt_iff₀ (mul_pos hmR hkR)).mp hl
  have hu' := (lt_div_iff₀ (mul_pos hmR hkR)).mp hu
  apply SharpBounds.n3_proof a _ u
  · apply (div_lt_iff₀ hmR).mpr
    nlinarith
  · apply (lt_div_iff₀ hmR).mpr
    nlinarith


private def T8_left {m k : ℕ} (hk : 0 < k) (l : Fin (m * k)) : Fin m :=
  ⟨l.val / k, (Nat.div_lt_iff_lt_mul hk).mpr l.isLt⟩

private def T8_right {m k : ℕ} (hm : 0 < m) (l : Fin (m * k)) : Fin k :=
  ⟨l.val / m, (Nat.div_lt_iff_lt_mul hm).mpr (by simpa [Nat.mul_comm] using l.isLt)⟩

private lemma T8_common_quad {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide) (F : ℝ → ℝ → ℝ) :
    (∫ u in (0 : ℝ)..1, F (empiricalQuantile a u)
      (empiricalQuantile b (if B = .H then u else 1 - u))) =
    finiteMean (fun l : Fin (m * k) => F (sortedValues a (T8_left hk l))
      (sortedValues b (if B = .H then T8_right hm l else (T8_right hm l).rev))) := by
  letI : NeZero (m * k) := ⟨(Nat.mul_pos hm hk).ne'⟩
  apply SharpBounds.n4_proof
  intro l u hl hu
  have ha := T8_common_cell hm hk a l u (by exact_mod_cast hl) (by exact_mod_cast hu)
  have hb := T8_common_cell hk hm b (Fin.cast (Nat.mul_comm m k) l) u
    (by simpa only [Fin.coe_cast, Nat.cast_mul, mul_comm] using hl)
    (by simpa only [Fin.coe_cast, Nat.cast_mul, mul_comm] using hu)
  cases B <;> simpa only [if_pos rfl, ite_true, reduceCtorEq, if_false,
    T8_left, T8_right, Fin.coe_cast, ha.1, hb.1, hb.2]

private lemma T8_div_cell (s l i : ℕ) (hs : 0 < s) :
    l / s = i ↔ i * s ≤ l ∧ l < (i + 1) * s := by
  constructor
  · intro h
    rw [← h]
    exact ⟨Nat.div_mul_le_self l s, by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ l hs⟩
  · rintro ⟨hl, hu⟩
    exact Nat.div_eq_of_lt_le hl hu

private lemma T8_fiber_card {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (i : Fin m) (j : Fin k) :
    ((Finset.univ : Finset (Fin (m * k))).filter
      (fun l => T8_left hk l = i ∧ T8_right hm l = j)).card =
      min ((i.val + 1) * k) ((j.val + 1) * m) - max (i.val * k) (j.val * m) := by
  have hcard : ((Finset.univ : Finset (Fin (m * k))).filter
      (fun l => T8_left hk l = i ∧ T8_right hm l = j)).card =
      (Finset.Ico (max (i.val * k) (j.val * m))
        (min ((i.val + 1) * k) ((j.val + 1) * m))).card := by
    apply Finset.card_bij
      (s := (Finset.univ : Finset (Fin (m * k))).filter
        (fun l => T8_left hk l = i ∧ T8_right hm l = j))
      (t := Finset.Ico (max (i.val * k) (j.val * m))
        (min ((i.val + 1) * k) ((j.val + 1) * m))) (fun l _ => l.val)
    · intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, List.mem_filter, List.mem_finRange,
        decide_eq_true_eq, true_and, T8_left, T8_right, Fin.ext_iff,
        T8_div_cell _ _ _ hk, T8_div_cell _ _ _ hm] at hl
      simp only [Finset.mem_Ico, max_le_iff, lt_min_iff]
      exact ⟨⟨hl.1.1, hl.2.1⟩, hl.1.2, hl.2.2⟩
    · intro l _ l' _ h
      exact Fin.ext h
    · intro l hl
      simp only [Finset.mem_Ico, max_le_iff, lt_min_iff] at hl
      have hlt : l < m * k := hl.2.1.trans_le (Nat.mul_le_mul_right k i.isLt)
      refine ⟨⟨l, hlt⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, List.mem_filter, List.mem_finRange,
        decide_eq_true_eq, true_and, T8_left, T8_right, Fin.ext_iff]
      exact ⟨(T8_div_cell k l i.val hk).2 ⟨hl.1.1, hl.2.1⟩,
        (T8_div_cell m l j.val hm).2 ⟨hl.1.2, hl.2.2⟩⟩
  rw [hcard, Nat.card_Ico]

private lemma T8_weight_card {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (i : Fin m) (j : Fin k) :
    overlapWeight m k i j =
      (((Finset.univ : Finset (Fin (m * k))).filter
        (fun l => T8_left hk l = i ∧ T8_right hm l = j)).card : ℝ) / (m * k) := by
  rw [T8_fiber_card hm hk]
  unfold overlapWeight
  have hh : (max 0 (min (((i.val : ℝ) + 1) * k) (((j.val : ℝ) + 1) * m) -
      max ((i.val : ℝ) * k) ((j.val : ℝ) * m))) =
      ((min ((i.val + 1) * k) ((j.val + 1) * m) - max (i.val * k) (j.val * m) : ℕ) : ℝ) := by
    have hc (x y : ℕ) : ((x - y : ℕ) : ℝ) = max 0 ((x : ℝ) - y) := by
      by_cases h : y ≤ x
      · rw [Nat.cast_sub h, max_eq_right]
        exact sub_nonneg.mpr (by exact_mod_cast h)
      · rw [Nat.sub_eq_zero_of_le (by omega : x ≤ y), Nat.cast_zero, max_eq_left]
        exact sub_nonpos.mpr (by exact_mod_cast (show x ≤ y by omega))
    rw [hc]
    push_cast
    rfl
  rw [hh]

private lemma T8_group_sum {p m k : ℕ} (f : Fin p → Fin m) (g : Fin p → Fin k)
    (A : Fin m → ℝ) (B : Fin k → ℝ) :
    (∑ l, A (f l) * B (g l)) = ∑ i, ∑ j,
      (((Finset.univ : Finset (Fin p)).filter (fun l => f l = i ∧ g l = j)).card : ℝ) * A i * B j := by
  have hpoint (l : Fin p) : A (f l) * B (g l) =
      ∑ i, ∑ j, if f l = i ∧ g l = j then A i * B j else 0 := by
    simp [ite_and]
  calc
    _ = ∑ l, ∑ i, ∑ j, if f l = i ∧ g l = j then A i * B j else 0 :=
      Finset.sum_congr rfl (fun l _ => hpoint l)
    _ = ∑ i, ∑ j, ∑ l, if f l = i ∧ g l = j then A i * B j else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      simp [mul_assoc]

private lemma T8_weighted_mean {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (A : Fin m → ℝ) (B : Fin k → ℝ) :
    finiteMean (fun l : Fin (m * k) => A (T8_left hk l) * B (T8_right hm l)) =
      ∑ i, ∑ j, overlapWeight m k i j * A i * B j := by
  rw [finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin, T8_group_sum]
  simp_rw [T8_weight_card hm hk]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

private lemma T8_projection_mean {m k N : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hN : N = m * k) (A : Fin m → ℝ) :
    finiteMean (fun l : Fin N => A ⟨l.val / k,
      (Nat.div_lt_iff_lt_mul hk).mpr (by rw [← hN]; exact l.isLt)⟩) = finiteMean A := by
  subst N
  rw [finiteMean, finiteMean, Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card,
    Fintype.card_fin, Fintype.card_fin]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin k ≃ Fin (m * k))]
  have he (i : Fin m) (j : Fin k) :
      (finProdFinEquiv (i, j)).val / k = i.val := by
    change (j.val + k * i.val) / k = i.val
    rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt j.isLt]
    simp
  simp only [Fintype.sum_prod_type, he]
  change (∑ i : Fin m, ∑ _j : Fin k, A i) / ((m * k : ℕ) : ℝ) =
    (∑ i, A i) / (m : ℝ)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, Nat.cast_mul]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp
  <;> ring

private lemma T8_overlap_masses {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    (∀ i, (∑ j, overlapWeight m k i j) = 1 / (m : ℝ)) ∧
    (∀ j, (∑ i, overlapWeight m k i j) = 1 / (k : ℝ)) := by
  constructor
  · intro i
    have hw := T8_weighted_mean hm hk (fun i' => if i' = i then 1 else 0) (fun _ => 1)
    have hp := T8_projection_mean hm hk rfl (fun i' => if i' = i then 1 else 0)
    simp only [mul_one] at hw
    change finiteMean (fun l : Fin (m * k) => if T8_left hk l = i then 1 else 0) = _ at hp
    rw [hp] at hw
    simpa [finiteMean, Fintype.expect_eq_sum_div_card, Finset.sum_ite, mul_ite] using hw.symm
  · intro j
    have hw := T8_weighted_mean hm hk (fun _ => 1) (fun j' => if j' = j then 1 else 0)
    have hp := T8_projection_mean hk hm (Nat.mul_comm m k) (fun j' => if j' = j then 1 else 0)
    simp only [one_mul, mul_one] at hw
    change finiteMean (fun l : Fin (m * k) => if T8_right hm l = j then 1 else 0) = _ at hp
    rw [hp] at hw
    simpa [finiteMean, Fintype.expect_eq_sum_div_card, Finset.sum_ite, mul_ite, Finset.sum_comm] using hw.symm


private lemma T8_quantile_integral {s : ℕ} (hs : 0 < s) (a : Fin s → ℝ) :
    (∫ u in (0 : ℝ)..1, empiricalQuantile a u) = finiteMean a := by
  letI : NeZero s := ⟨hs.ne'⟩
  calc
    _ = finiteMean (sortedValues a) := by
      apply SharpBounds.n4_proof
      intro j u hl hu
      exact (SharpBounds.n3_proof a j u hl hu).1
    _ = _ := SharpBounds.n1_proof _ _ (SharpBounds.n2_proof a).1 id

private lemma T8_common_means {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide) :
    finiteMean (fun l : Fin (m * k) => sortedValues a (T8_left hk l)) = finiteMean a ∧
    finiteMean (fun l : Fin (m * k) => sortedValues b
      (if B = .H then T8_right hm l else (T8_right hm l).rev)) = finiteMean b := by
  constructor
  · exact (T8_projection_mean hm hk rfl (sortedValues a)).trans
      (SharpBounds.n1_proof _ _ (SharpBounds.n2_proof a).1 id)
  · have h := T8_projection_mean hk hm (Nat.mul_comm m k)
      (fun j => sortedValues b (if B = .H then j else j.rev))
    change finiteMean (fun l : Fin (m * k) => sortedValues b
      (if B = .H then T8_right hm l else (T8_right hm l).rev)) = _ at h
    rw [h]
    cases B with
    | H =>
      simpa only [ite_true, id_eq] using SharpBounds.n1_proof _ _ (SharpBounds.n2_proof b).1 id
    | L =>
      simpa only [reduceCtorEq, if_false, id_eq] using
        SharpBounds.n1_proof _ _ (SharpBounds.n2_proof b).2.1 id

private lemma T8_centered_mean {n : ℕ} (hn : 0 < n) (X Y : Fin n → ℝ) :
    finiteMean (fun i => (X i - finiteMean X) * (Y i - finiteMean Y)) =
      finiteMean (fun i => X i * Y i) - finiteMean X * finiteMean Y := by
  letI : NeZero n := ⟨hn.ne'⟩
  calc
    _ = finiteMean (fun i => X i * Y i - finiteMean Y * X i -
        finiteMean X * Y i + finiteMean X * finiteMean Y) := by
      apply Finset.expect_congr rfl
      intro i _
      ring
    _ = _ := by
      unfold finiteMean
      rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
        Finset.expect_sub_distrib, ← Finset.mul_expect, ← Finset.mul_expect,
        Finset.expect_const Finset.univ_nonempty]
      ring

private lemma T8_centered_integral {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide) :
    (∫ u in (0 : ℝ)..1, (empiricalQuantile a u - finiteMean a) *
      (empiricalQuantile b (if B = .H then u else 1 - u) - finiteMean b)) =
      sharpCovariance a b B := by
  have hmeans := T8_common_means hm hk a b B
  rw [T8_common_quad hm hk a b B (fun x y => (x - finiteMean a) * (y - finiteMean b)),
    sharpCovariance, T8_common_quad hm hk a b B (fun x y => x * y)]
  have h := T8_centered_mean (Nat.mul_pos hm hk)
    (fun l => sortedValues a (T8_left hk l))
    (fun l => sortedValues b (if B = .H then T8_right hm l else (T8_right hm l).rev))
  rw [hmeans.1, hmeans.2] at h
  exact h

private lemma T8_overlap_covariance {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide) :
    sharpCovariance a b B = ∑ i, ∑ j, overlapWeight m k i j *
      (orderStatistic a (i.val + 1) - finiteMean a) *
      (orderStatistic b (if B = .H then j.val + 1 else k - j.val) - finiteMean b) := by
  rw [← T8_centered_integral hm hk a b B,
    T8_common_quad hm hk a b B (fun x y => (x - finiteMean a) * (y - finiteMean b))]
  have hw := T8_weighted_mean hm hk (fun i => sortedValues a i - finiteMean a)
    (fun j => sortedValues b (if B = .H then j else j.rev) - finiteMean b)
  rw [hw]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  cases B with
  | H => simp [sortedValues, orderStatistic]
  | L =>
    have hj : j.rev.val = k - j.val - 1 := by rw [Fin.val_rev]; omega
    simp only [reduceCtorEq, if_false, sortedValues, orderStatistic,
      Nat.add_sub_cancel, hj]

theorem appendixB_corrected_proof {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) :
    (∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r) = 1 ∧
    (∀ r < partitionCells m k, ∀ u,
      partitionPoint m k r < u → u < partitionPoint m k (r + 1) →
      Nat.ceil ((m : ℝ) * u) = Nat.ceil ((m : ℝ) * partitionPoint m k (r + 1)) ∧
      Nat.ceil ((k : ℝ) * u) = Nat.ceil ((k : ℝ) * partitionPoint m k (r + 1)) ∧
      k + 1 - Nat.ceil ((k : ℝ) * u) =
        Nat.ceil ((k : ℝ) * partitionPoint m k (partitionCells m k - r))) ∧
    (∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r *
      empiricalQuantile a (cellMidpoint m k r)) = finiteMean a ∧
    (∀ B, (∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r *
      empiricalQuantile b (if B = BoundSide.H then cellMidpoint m k r else
        1 - cellMidpoint m k r)) = finiteMean b) ∧
    (∀ B, midpointCovariance a b B = sharpCovariance a b B) ∧
    (∀ N B, varianceExpression N m k (marginalVarianceEstimate N a)
      (marginalVarianceEstimate N b) (midpointCovariance a b B) = estimateBound N a b B) ∧
    (∀ i, (∑ j, overlapWeight m k i j) = 1 / (m : ℝ)) ∧
    (∀ j, (∑ i, overlapWeight m k i j) = 1 / (k : ℝ)) ∧
    (∀ B, sharpCovariance a b B = ∑ i, ∑ j, overlapWeight m k i j *
      (orderStatistic a (i.val + 1) - finiteMean a) *
      (orderStatistic b (if B = BoundSide.H then j.val + 1 else k - j.val) - finiteMean b)) := by
  have hm0 : 0 < m := by omega
  have hk0 : 0 < k := by omega
  have hwidth : (∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r) = 1 := by
    simpa using (T8_quadrature hm0 hk0 (fun _ => (1 : ℝ)) (by intros; rfl)).symm
  have hmeanA : (∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r *
      empiricalQuantile a (cellMidpoint m k r)) = finiteMean a := by
    rw [← T8_quadrature hm0 hk0 (empiricalQuantile a) (by
      intro r hr u hl hu
      exact (T8_quantile_cell hm0 hk0 a b .H r hr u hl hu).1)]
    exact T8_quantile_integral hm0 a
  have hmeanB (B : BoundSide) :
      (∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r *
        empiricalQuantile b (if B = .H then cellMidpoint m k r else 1 - cellMidpoint m k r)) =
      finiteMean b := by
    rw [← T8_quadrature hm0 hk0 (fun u => empiricalQuantile b (if B = .H then u else 1 - u)) (by
      intro r hr u hl hu
      exact (T8_quantile_cell hm0 hk0 a b B r hr u hl hu).2)]
    cases B with
    | H => simpa only [ite_true] using T8_quantile_integral hk0 b
    | L =>
      simp only [reduceCtorEq, if_false]
      rw [intervalIntegral.integral_comp_sub_left]
      norm_num only [sub_self, sub_zero]
      exact T8_quantile_integral hk0 b
  have hcov (B : BoundSide) : midpointCovariance a b B = sharpCovariance a b B := by
    have hq := T8_quadrature hm0 hk0 (fun u =>
      (empiricalQuantile a u - finiteMean a) *
        (empiricalQuantile b (if B = .H then u else 1 - u) - finiteMean b)) (by
      intro r hr u hl hu
      have hh := T8_quantile_cell hm0 hk0 a b B r hr u hl hu
      rw [hh.1, hh.2])
    rw [T8_centered_integral hm0 hk0 a b B] at hq
    unfold midpointCovariance
    simpa only [mul_assoc] using hq.symm
  refine ⟨hwidth, T8_rank_cells hm0 hk0, hmeanA, hmeanB, hcov, ?_,
    (T8_overlap_masses hm0 hk0).1, (T8_overlap_masses hm0 hk0).2,
    T8_overlap_covariance hm0 hk0 a b⟩
  intro N B
  rw [hcov]
  rfl

end
end AronowAudit.P022.Wave1
