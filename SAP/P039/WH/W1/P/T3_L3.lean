import SAP.P039.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.WH.W1.P.T3_L3

open scoped BigOperators Matrix NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory Set Topology

lemma density4_simplify (x : ℝ) :
    wholeStudentDensity 4 x = (3 / 8 : ℝ) * (1 + x ^ 2 / 4) ^ (-(5 / 2 : ℝ)) := by
  unfold wholeStudentDensity
  have hg : Real.Gamma (5 / 2 : ℝ) = (3 / 4 : ℝ) * Real.sqrt Real.pi := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0),
      show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
    ring
  have hg2 : Real.Gamma (2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (1 : ℝ) ≠ 0), Real.Gamma_one]
    norm_num
  have hs : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hg' : Real.Gamma ((((4 : ℕ) : ℝ) + 1) / 2) =
      (3 / 4 : ℝ) * Real.sqrt Real.pi := by
    convert hg using 1 <;> norm_num
  have hg2' : Real.Gamma (((4 : ℕ) : ℝ) / 2) = 1 := by
    convert hg2 using 1 <;> norm_num
  have hs' : Real.sqrt (((4 : ℕ) : ℝ) * Real.pi) = 2 * Real.sqrt Real.pi := by
    convert hs using 1 <;> norm_num
  rw [hg', hg2', hs']
  congr 1
  · have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    field_simp
    <;> ring
  · norm_num

noncomputable def z4 (x : ℝ) : ℝ := x / Real.sqrt (4 + x ^ 2)

noncomputable def primitive4 (x : ℝ) : ℝ := (3 * z4 x - (z4 x) ^ 3) / 4

lemma density4_explicit (x : ℝ) :
    wholeStudentDensity 4 x = 12 / Real.sqrt (4 + x ^ 2) ^ 5 := by
  rw [density4_simplify]
  have hs : Real.sqrt (1 + x ^ 2 / 4) = Real.sqrt (4 + x ^ 2) / 2 := by
    have h1 := Real.sq_sqrt (show 0 ≤ (1 : ℝ) + x ^ 2 / 4 by positivity)
    have h2 := Real.sq_sqrt (show 0 ≤ (4 : ℝ) + x ^ 2 by positivity)
    have hsq : (Real.sqrt (1 + x ^ 2 / 4)) ^ 2 =
        (Real.sqrt (4 + x ^ 2) / 2) ^ 2 := by
      rw [h1, div_pow, h2]
      ring
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2 / 4),
      div_nonneg (Real.sqrt_nonneg (4 + x ^ 2)) (by norm_num : (0 : ℝ) ≤ 2)]
  have hr : (1 + x ^ 2 / 4) ^ (-(5 / 2 : ℝ)) =
      (Real.sqrt (1 + x ^ 2 / 4) ^ 5)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_div_two_eq_sqrt 5 (by positivity)]
    norm_num
  rw [hr, hs]
  have hn : Real.sqrt (4 + x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp
  <;> ring

lemma density4_nonneg (x : ℝ) : 0 ≤ wholeStudentDensity 4 x := by
  rw [density4_explicit]
  positivity

lemma density4_even (x : ℝ) : wholeStudentDensity 4 (-x) = wholeStudentDensity 4 x := by
  rw [density4_explicit, density4_explicit]
  congr 1
  ring

lemma primitive4_hasDerivAt (x : ℝ) :
    HasDerivAt primitive4 (wholeStudentDensity 4 x) x := by
  have hinner : HasDerivAt (fun y : ℝ => 4 + y ^ 2) (2 * x) x := by
    simpa [pow_two, mul_comm] using ((hasDerivAt_id x).pow 2).const_add 4
  have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt (4 + y ^ 2))
      (x / Real.sqrt (4 + x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt (show 0 < 4 + x ^ 2 by positivity))).comp x
      hinner using 1
    · ext y
      rfl
    · field_simp
      <;> ring
  have hz : HasDerivAt z4 (4 / Real.sqrt (4 + x ^ 2) ^ 3) x := by
    unfold z4
    convert (hasDerivAt_id x).div hsqrt
      (ne_of_gt (Real.sqrt_pos.2 (show 0 < 4 + x ^ 2 by positivity))) using 1
    · rfl
    have hr := Real.sq_sqrt (show 0 ≤ (4 : ℝ) + x ^ 2 by positivity)
    have hn : Real.sqrt (4 + x ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (show 0 < 4 + x ^ 2 by positivity))
    simp only [id_eq]
    field_simp [hn]
    nlinarith [hr]
  have hpoly := ((hz.const_mul 3).sub (hz.pow 3)).div_const 4
  have hcalc :
      (3 * (4 / Real.sqrt (4 + x ^ 2) ^ 3) -
        3 * (x / Real.sqrt (4 + x ^ 2)) ^ 2 *
          (4 / Real.sqrt (4 + x ^ 2) ^ 3)) / 4 =
        12 / Real.sqrt (4 + x ^ 2) ^ 5 := by
    have hr := Real.sq_sqrt (show 0 ≤ (4 : ℝ) + x ^ 2 by positivity)
    have hn : Real.sqrt (4 + x ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (show 0 < 4 + x ^ 2 by positivity))
    field_simp
    nlinarith [hr]
  convert hpoly using 1
  · funext y
    rfl
  · rw [density4_explicit]
    simpa [z4] using hcalc.symm

lemma z4_tendsto : Tendsto z4 atTop (𝓝 1) := by
  have hpow : Tendsto (fun x : ℝ => x ^ (-(2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hsum : Tendsto (fun x : ℝ => 1 + 4 * x ^ (-(2 : ℝ))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hpow)
  have hroot : Tendsto (fun x : ℝ => Real.sqrt (1 + 4 * x ^ (-(2 : ℝ))))
      atTop (𝓝 1) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hsum using 1
    · ext x
      rfl
    · norm_num
  have hinv : Tendsto (fun x : ℝ => (Real.sqrt (1 + 4 * x ^ (-(2 : ℝ))))⁻¹)
      atTop (𝓝 1) := by
    simpa using hroot.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have heq : z4 =ᶠ[atTop] fun x : ℝ => (Real.sqrt (1 + 4 * x ^ (-(2 : ℝ))))⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have harg : (4 : ℝ) + x ^ 2 = x ^ 2 * (1 + 4 * x ^ (-(2 : ℝ))) := by
      have hr : x ^ (2 : ℝ) = x ^ (2 : ℕ) := Real.rpow_natCast x 2
      have hp : x ^ (-(2 : ℝ)) = (x ^ (2 : ℕ))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hx), hr]
      rw [hp]
      field_simp [hx.ne']
      ring
    rw [z4, harg, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_pos hx]
    field_simp [ne_of_gt hx]
  exact Tendsto.congr' heq.symm hinv

lemma primitive4_tendsto : Tendsto primitive4 atTop (𝓝 (1 / 2 : ℝ)) := by
  have hz := z4_tendsto
  have hpoly : Tendsto (fun x : ℝ => (3 * z4 x - (z4 x) ^ 3) / 4) atTop
      (𝓝 ((3 * 1 - (1 : ℝ) ^ 3) / 4)) := by
    simpa using ((tendsto_const_nhds.mul hz).sub (hz.pow 3)).div_const 4
  change Tendsto (fun x : ℝ => (3 * z4 x - (z4 x) ^ 3) / 4) atTop
    (𝓝 (1 / 2 : ℝ))
  convert hpoly using 1 <;> norm_num

lemma four_integral_Ioi (t : ℝ) :
    IntegrableOn (fun x : ℝ => wholeStudentDensity 4 x) (Ioi t) ∧
    (∫ x in Ioi t, wholeStudentDensity 4 x) = 1 / 2 - primitive4 t := by
  have hd : ∀ x ∈ Ici t, HasDerivAt primitive4 (wholeStudentDensity 4 x) x := by
    intro x hx
    exact primitive4_hasDerivAt x
  have hp : ∀ x ∈ Ioi t, 0 ≤ wholeStudentDensity 4 x := by
    intro x hx
    exact density4_nonneg x
  have hl := primitive4_tendsto
  exact ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp hl,
    integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_Ioi_deriv_of_nonneg' hd hp hl) hl⟩

noncomputable def fourDensityMeasure : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (wholeStudentDensity 4 x))

lemma fourDensityMeasure_Ioi (t : ℝ) :
    fourDensityMeasure (Ioi t) = ENNReal.ofReal (1 / 2 - primitive4 t) := by
  rw [fourDensityMeasure, withDensity_apply _ measurableSet_Ioi]
  calc
    _ = ENNReal.ofReal (∫ x in Ioi t, wholeStudentDensity 4 x) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal (four_integral_Ioi t).1
        (ae_of_all _ (fun x => density4_nonneg x))
    _ = ENNReal.ofReal (1 / 2 - primitive4 t) := by rw [(four_integral_Ioi t).2]

lemma four_integrable_Iic (t : ℝ) :
    IntegrableOn (fun x : ℝ => wholeStudentDensity 4 x) (Iic (-t)) := by
  have hpos := (integrableOn_Ici_iff_integrableOn_Ioi).2 (four_integral_Ioi t).1
  have hcomp : IntegrableOn (fun x : ℝ => wholeStudentDensity 4 (-x)) (Ici t) := by
    refine hpos.congr ?_
    exact ae_of_all _ (fun x => (density4_even x).symm)
  have hpre : IntegrableOn
      ((fun x : ℝ => wholeStudentDensity 4 x) ∘ Neg.neg)
      (Neg.neg ⁻¹' Iic (-t)) := by
    simpa [Function.comp_def, neg_preimage, neg_Iic, neg_neg] using hcomp
  exact (MeasurePreserving.integrableOn_comp_preimage
    (Measure.measurePreserving_neg (volume : Measure ℝ))
    (Homeomorph.neg ℝ).measurableEmbedding).mp hpre

lemma fourDensityMeasure_Iic (t : ℝ) :
    fourDensityMeasure (Iic (-t)) = ENNReal.ofReal (1 / 2 - primitive4 t) := by
  rw [fourDensityMeasure, withDensity_apply _ measurableSet_Iic]
  have hleft := four_integrable_Iic t
  have hconv := ofReal_integral_eq_lintegral_ofReal hleft
    (ae_of_all _ (fun x => density4_nonneg x))
  have hreflect :
      (∫ x in Iic (-t), wholeStudentDensity 4 x) =
        ∫ x in Ioi t, wholeStudentDensity 4 x := by
    calc
      _ = ∫ x in Iic (-t), wholeStudentDensity 4 (-x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x hx
        simpa only [neg_neg] using density4_even (-x)
      _ = ∫ x in Ioi t, wholeStudentDensity 4 x := by
        simpa using integral_comp_neg_Iic (-t) (fun x : ℝ => wholeStudentDensity 4 x)
  calc
    _ = ENNReal.ofReal (∫ x in Iic (-t), wholeStudentDensity 4 x) := hconv.symm
    _ = ENNReal.ofReal (1 / 2 - primitive4 t) := by
      rw [hreflect, (four_integral_Ioi t).2]

lemma fourDensityMeasure_tail (t : ℝ) (ht : 0 ≤ t) :
    fourDensityMeasure {s : ℝ | t ≤ |s|} = ENNReal.ofReal (studentFourTail t) := by
  let A : Set ℝ := Iic (-t)
  let B : Set ℝ := Ioi t
  let U : Set ℝ := A ∪ B
  have hsub : U ⊆ {s : ℝ | t ≤ |s|} := by
    intro s hs
    change s ∈ Iic (-t) ∪ Ioi t at hs
    change t ≤ |s|
    rcases hs with hs | hs
    · change s ≤ -t at hs
      have hs0 : s ≤ 0 := le_trans hs (neg_nonpos.mpr ht)
      rw [abs_of_nonpos hs0]
      linarith
    · change t < s at hs
      have hs0 : 0 ≤ s := le_of_lt (lt_of_le_of_lt ht hs)
      rw [abs_of_nonneg hs0]
      exact le_of_lt hs
  have hsubsetSingleton : ({s : ℝ | t ≤ |s|} \ U) ⊆ {t} := by
    intro s hs
    simp only [Set.mem_diff, Set.mem_setOf_eq] at hs
    rcases hs with ⟨hsE, hsnot⟩
    change ¬ (s ∈ Iic (-t) ∨ s ∈ Ioi t) at hsnot
    by_cases hs0 : s ≤ 0
    · have hsabs : |s| = -s := abs_of_nonpos hs0
      have hleft : s ≤ -t := by rw [hsabs] at hsE; linarith
      exact (hsnot (Or.inl hleft)).elim
    · have hspos : 0 ≤ s := le_of_not_ge hs0
      have hsabs : |s| = s := abs_of_nonneg hspos
      have hsge : t ≤ s := by rw [hsabs] at hsE; exact hsE
      have hsle : s ≤ t := le_of_not_gt (fun h => hsnot (Or.inr h))
      have : s = t := le_antisymm hsle hsge
      simp [this]
  have hsingle : fourDensityMeasure ({t} : Set ℝ) = 0 := by
    simp [fourDensityMeasure]
  have hdiff : fourDensityMeasure ({s : ℝ | t ≤ |s|} \ U) = 0 :=
    measure_mono_null hsubsetSingleton hsingle
  have hmeasure :
      fourDensityMeasure ({s : ℝ | t ≤ |s|}) = fourDensityMeasure U := by
    exact (measure_eq_measure_of_null_sdiff hsub hdiff).symm
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro s hsA hsB
    change s ≤ -t at hsA
    change t < s at hsB
    linarith
  have hside : 0 ≤ 1 / 2 - primitive4 t := by
    rw [← (four_integral_Ioi t).2]
    exact integral_nonneg_of_ae (ae_of_all _ (fun x => density4_nonneg x))
  have hformula :
      (1 / 2 - primitive4 t) + (1 / 2 - primitive4 t) = studentFourTail t := by
    dsimp [studentFourTail, primitive4, z4]
    ring
  calc
    fourDensityMeasure {s : ℝ | t ≤ |s|} = fourDensityMeasure U := hmeasure
    _ = fourDensityMeasure A + fourDensityMeasure B := measure_union hdisj measurableSet_Ioi
    _ = ENNReal.ofReal (1 / 2 - primitive4 t) +
          ENNReal.ofReal (1 / 2 - primitive4 t) := by
      rw [fourDensityMeasure_Iic, fourDensityMeasure_Ioi]
    _ = ENNReal.ofReal ((1 / 2 - primitive4 t) + (1 / 2 - primitive4 t)) := by
      rw [ENNReal.ofReal_add hside hside]
    _ = ENNReal.ofReal (studentFourTail t) := by rw [hformula]

lemma studentFourTail_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ studentFourTail t := by
  let z : ℝ := t / Real.sqrt (4 + t ^ 2)
  have hz0 : 0 ≤ z := by
    dsimp [z]
    exact div_nonneg ht (Real.sqrt_nonneg _)
  have hroot : t ≤ Real.sqrt (4 + t ^ 2) := by
    have hs := Real.sq_sqrt (show 0 ≤ (4 : ℝ) + t ^ 2 by positivity)
    nlinarith [Real.sqrt_nonneg (4 + t ^ 2)]
  have hz1 : z ≤ 1 := by
    dsimp [z]
    exact (div_le_one (Real.sqrt_pos.2 (by positivity))).2 hroot
  have hfactor : studentFourTail t = (1 - z) ^ 2 * (1 + z / 2) := by
    dsimp [studentFourTail, z]
    ring
  rw [hfactor]
  have hleft : 0 ≤ 1 - z := by linarith
  positivity

end SAP.P039.WH.W1.P.T3_L3

theorem SAP.P039.WH.W1.T3_L3_proof : SAP.P039.WH.W1.T3_L3 := by
  intro t ht
  constructor
  · exact SAP.P039.WH.W1.P.T3_L3.fourDensityMeasure_tail t ht
  · exact SAP.P039.WH.W1.P.T3_L3.studentFourTail_nonneg t ht
