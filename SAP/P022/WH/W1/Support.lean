import SAP.P022.Defs.WholeW1
import SAP.P022.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1
open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

theorem mean_const {N : ℕ} (hN : 0 < N) (c : ℝ) :
    finiteMean (fun _ : Fin N => c) = c :=
  AronowAudit.P022.finiteMean_const hN c

theorem probability_certain (d : Design) (E : Assignment d → Prop) (h : ∀ π, E π) :
    designProbability d E = 1 := by
  classical
  simp only [designProbability, if_pos (h _)]
  exact (AronowAudit.P022.design_constant (Bridge.toDesign d) 1).1

theorem size_pos (S : ExperimentSequence) (q : ℕ) : 0 < rowSize S q := by
  unfold rowSize
  have := (S.design q).population_min
  exact_mod_cast (show 0 < (S.design q).N by omega)

theorem size_tendsto (S : ExperimentSequence) : Tendsto (rowSize S) atTop atTop := by
  change Tendsto (fun q => ((S.design q).N : ℝ)) atTop atTop
  simp_rw [S.size]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds :
      Tendsto (fun q : ℕ => (q : ℝ) + 4) atTop atTop)

theorem convergence_const (d : ℕ → Design) (v : ℝ) :
    designConvergence d (fun _ _ => v) v := by
  intro η hη
  have hz (q : ℕ) : designProbability (d q) (fun _ => η ≤ |v - v|) = 0 := by
    simp [designProbability, designExpectation, not_le.mpr hη]
  simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem marginal_rate_nonneg (θ ρ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (t : Bool) (η : ℝ) :
    0 ≤ marginalTailRate θ ρ t η := by
  have hf : 0 < allocationFraction θ ρ t ∧ allocationFraction θ ρ t < 1 := by
    cases t <;> simp only [allocationFraction, Bool.false_eq_true, ite_false, ite_true]
    · constructor
      · positivity
      · nlinarith [mul_le_mul_of_nonneg_right hθ1 (by linarith : 0 ≤ 1 - ρ)]
    · constructor
      · positivity
      · nlinarith [mul_le_mul_of_nonneg_right hθ1 hρ.le]
  exact div_nonneg (mul_nonneg (by linarith [hf.2]) (Nat.cast_nonneg _))
    (mul_nonneg hf.1.le (sq_nonneg η))

theorem scaled_certain (S : ExperimentSequence)
    (E : (q : ℕ) → Assignment (S.design q) → Prop)
    (h : ∀ q π, E q π) : scaledProbabilityLimsup S E = ⊤ := by
  have he : (fun q => ENNReal.ofReal ((S.design q).N *
      designProbability (S.design q) (E q))) = (fun q => ENNReal.ofReal (rowSize S q)) := by
    funext q
    rw [probability_certain _ _ (h q), mul_one]
    rfl
  unfold scaledProbabilityLimsup
  rw [he]
  exact (ENNReal.tendsto_ofReal_atTop.comp (size_tendsto S)).limsup_eq

theorem certain_cdf (S : ExperimentSequence) (H : JointLaw) (η : ℝ)
    (h : ∀ t q π, η ≤ cdfDistance (lawCDF H t) (sampledCDF S t q π)) :
    CertainCDFError S H η := by
  intro t q
  have hp := probability_certain (S.design q) _ (h t q)
  exact ⟨hp, by rw [hp, mul_one]⟩

theorem certain_refutes_lemma2 (S : ExperimentSequence) (H : JointLaw) (η : ℝ)
    (hη : 0 < η) (h : ∀ q π, η ≤ cdfDistance (lawCDF H true) (sampledCDF S true q π)) :
    ¬Lemma2Conclusions S H 1 (1 / 2) := by
  rintro ⟨_, K1, K0, _, _, hK1, _⟩
  have htop := scaled_certain S _ h
  have hbound := hK1 η hη
  rw [htop] at hbound
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hbound)

/-- Four finite atoms make every displayed integral an actual integrable integral. -/
theorem corner_integral (f : ℝ × ℝ → ℝ) :
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

theorem corner_nonsingular : NonsingularLaw cornerLaw := by
  intro a b c hab hae
  change ∀ᵐ p : ℝ × ℝ ∂(_ + _ + _ + _), a * p.1 + b * p.2 = c at hae
  simp only [ae_add_measure_iff, Measure.ae_ennreal_smul_measure_iff
    (by norm_num : (1 / 4 : ℝ≥0∞) ≠ 0)] at hae
  have hm : MeasurableSet {p : ℝ × ℝ | a * p.1 + b * p.2 = c} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have h00 := (ae_dirac_iff hm).mp hae.1.1.1
  have h01 := (ae_dirac_iff hm).mp hae.1.1.2
  have h10 := (ae_dirac_iff hm).mp hae.1.2
  simp only at h00 h01 h10
  rcases hab with ha | hb
  · apply ha
    linarith
  · apply hb
    linarith

theorem corner_law_facts : CornerLawFacts := by
  refine ⟨?_, ?_, ?_, corner_nonsingular⟩
  · intro t x
    have hm : MeasurableSet {p : ℝ × ℝ | (if t then p.1 else p.2) ≤ x} := by
      cases t <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
        exact measurableSet_le (by fun_prop) measurable_const
    unfold lawCDF
    change (cornerLaw : Measure (ℝ × ℝ)).real _ = _
    rw [← integral_indicator_one hm, corner_integral]
    cases t <;> simp only [Set.indicator_apply, Set.mem_setOf_eq, Bool.false_eq_true,
      ite_false, ite_true, bernoulliHalfCDF] <;>
      split_ifs <;> norm_num <;> linarith
  · intro t
    have hmean : lawMean cornerLaw t = 1 / 2 := by
      unfold lawMean
      rw [corner_integral]
      cases t <;> norm_num
    refine ⟨hmean, ?_⟩
    unfold lawVariance
    rw [hmean, corner_integral]
    cases t <;> norm_num
  · unfold lawCovariance
    have hm (t : Bool) : lawMean cornerLaw t = 1 / 2 := by
      unfold lawMean
      rw [corner_integral]
      cases t <;> norm_num
    rw [hm true, hm false, corner_integral]
    norm_num

theorem corner_third_moments : BoundedThirdMoments cornerWitness := by
  refine ⟨1, ?_⟩
  intro q t
  have hc := Bridge.proposition2_printed_counterexample_proof.2.2.1
  calc
    _ ≤ finiteMean (fun _ : Fin (cornerWitness.design q).N => (1 : ℝ)) := by
      apply Finset.expect_le_expect
      intro i _
      cases t <;> simp only [Bool.false_eq_true, if_false, if_true]
      · exact pow_le_one₀ (abs_nonneg _) (hc i.val).2
      · exact pow_le_one₀ (abs_nonneg _) (hc i.val).1
    _ = 1 := mean_const (by have := (cornerWitness.design q).population_min; omega) 1

theorem bounded_one_UI (S : ExperimentSequence)
    (hy : ∀ i, |S.y1 i| ≤ 1 ∧ |S.y0 i| ≤ 1) : UniformSquareIntegrability S := by
  intro t
  have hsq (i : ℕ) : (if t then S.y1 else S.y0) i ^ 2 ≤ 1 := by
    have ha : |(if t then S.y1 else S.y0) i| ≤ 1 := by
      cases t <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact (hy i).2
      · exact (hy i).1
    nlinarith [sq_abs ((if t then S.y1 else S.y0) i), abs_nonneg ((if t then S.y1 else S.y0) i)]
  have hb (β : ℝ) (q : ℕ) :
      finiteMean (fun i : Fin (S.design q).N =>
        if β ≤ (if t then S.y1 else S.y0) i.val ^ 2 then
          (if t then S.y1 else S.y0) i.val ^ 2 else 0) ≤ 1 := by
    calc
      _ ≤ finiteMean (fun _ : Fin (S.design q).N => (1 : ℝ)) := by
        apply Finset.expect_le_expect
        intro i _
        by_cases h : β ≤ (if t then S.y1 else S.y0) i.val ^ 2
        · simpa only [ite_true, h] using hsq i.val
        · simp only [h, ite_false]
          norm_num
      _ = 1 := mean_const (by have := (S.design q).population_min; omega) 1
  refine ⟨?_, fun β => ⟨1, by rintro _ ⟨q, rfl⟩; exact hb β q⟩⟩
  have he : ∀ᶠ β : ℝ in atTop,
      sSup (Set.range (fun q => finiteMean (fun i : Fin (S.design q).N =>
        if β ≤ (if t then S.y1 else S.y0) i.val ^ 2 then
          (if t then S.y1 else S.y0) i.val ^ 2 else 0))) = 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hβ
    have hf (q : ℕ) : finiteMean (fun i : Fin (S.design q).N =>
        if β ≤ (if t then S.y1 else S.y0) i.val ^ 2 then
          (if t then S.y1 else S.y0) i.val ^ 2 else 0) = 0 := by
      have hn (i : Fin (S.design q).N) :
          ¬β ≤ (if t then S.y1 else S.y0) i.val ^ 2 := by linarith [hsq i.val]
      simp only [hn, ite_false]
      exact mean_const (by have := (S.design q).population_min; omega) 0
    simp only [hf, Set.range_const, csSup_singleton]
  exact (tendsto_congr' he).2 tendsto_const_nhds

theorem reciprocal_extras : ReciprocalExtraFacts := by
  have hb (i : ℕ) : |reciprocalWitness.y1 i| ≤ 1 ∧ |reciprocalWitness.y0 i| ≤ 1 := by
    have hp : 0 < (i : ℝ) + 1 := by positivity
    have he : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_one hp).2 (by linarith [Nat.cast_nonneg (α := ℝ) i])
    simpa only [reciprocalWitness, abs_neg, abs_div, abs_one, abs_of_pos hp] using And.intro he he
  refine ⟨hb, bounded_one_UI reciprocalWitness hb, ?_, ?_⟩
  · intro q t
    exact AronowAudit.P022.reciprocal_atom_values q t
  · intro q t
    have hbelow (i : Fin (reciprocalWitness.design q).N) :
        rowOutcomes reciprocalWitness t q i ≤ reciprocalThreshold q := by
      have h := (AronowAudit.P022.reciprocal_below_threshold q i).1.le
      cases t <;> exact h
    have hpop : empiricalCDF (rowOutcomes reciprocalWitness t q) (reciprocalThreshold q) = 1 := by
      simp only [empiricalCDF, ite_eq_left_iff, hbelow, implies_true]
      exact mean_const (by change 0 < q + 4; omega) 1
    have hlim : lawCDF originLaw t (reciprocalThreshold q) = 0 := by
      have ht := (AronowAudit.P022.reciprocal_below_threshold q ⟨0, by omega⟩).2
      have ho := AronowAudit.P022.origin_cdf t (reciprocalThreshold q)
      change lawCDF originLaw t (reciprocalThreshold q) =
        (if 0 ≤ reciprocalThreshold q then 1 else 0) at ho
      rw [if_neg (not_le.mpr (show reciprocalThreshold q < 0 from ht))] at ho
      exact ho
    refine ⟨hpop, hlim, ?_⟩
    intro π
    cases t
    · change empiricalCDF (observedControl _ _ π) _ = 1
      have hc (i) : observedControl (reciprocalWitness.design q)
          (rowOutcomes reciprocalWitness false q) π i ≤ reciprocalThreshold q := hbelow _
      simp only [empiricalCDF, ite_eq_left_iff, hc, implies_true]
      exact mean_const (by have := (reciprocalWitness.design q).control_min; omega) 1
    · change empiricalCDF (observedTreatment _ _ π) _ = 1
      have hc (i) : observedTreatment (reciprocalWitness.design q)
          (rowOutcomes reciprocalWitness true q) π i ≤ reciprocalThreshold q := hbelow _
      simp only [empiricalCDF, ite_eq_left_iff, hc, implies_true]
      exact mean_const (by have := (reciprocalWitness.design q).treatment_min; omega) 1

theorem retained_T6 : T6Statement := by
  refine ⟨?_, ?_, @Bridge.corrected_allocation_sum, ?_, @Bridge.proposition2_corrected_limit_proof⟩
  · intro d y1 y0 C hC hy
    obtain ⟨identity, budget, bound, threshold⟩ :=
      Bridge.proposition2_corrected_finite_proof d y1 y0 C hC hy
    exact ⟨identity, budget, bound, (fun _ => threshold)⟩
  · intro d y1 y0 C hC hy a ε ha hbudget π hlarge
    have hid := (Bridge.proposition2_corrected_finite_proof d y1 y0 C hC hy).1 π
    apply Bridge.seven_term_budget (sevenTerms d y1 y0 C π) a ε ha hbudget
    rw [← hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg d.N)]
    exact hlarge
  · intro ν ε1 hν
    simp [Fin.sum_univ_succ] at hν
    linarith

set_option maxHeartbeats 2000000 in
theorem code_example_details : CodeExampleDetails := by
  have hp : partitionKnots 2 2 = [0, 1 / 2, 1] := AronowAudit.P022.partition_two
  have hq0 : Nat.ceil ((2 : ℝ) * codeEpsilon) = 1 := by
    apply (Nat.ceil_eq_iff (by omega : 1 ≠ 0)).2
    norm_num [codeEpsilon]
  have hq1 : Nat.ceil ((2 : ℝ) * (1 / 2 - codeEpsilon)) = 1 := by
    apply (Nat.ceil_eq_iff (by omega : 1 ≠ 0)).2
    norm_num [codeEpsilon]
  have hq2 : Nat.ceil ((2 : ℝ) * (1 - codeEpsilon)) = 2 := by
    apply (Nat.ceil_eq_iff (by omega : 2 ≠ 0)).2
    norm_num [codeEpsilon]
  refine ⟨by decide, ?_, ?_, ?_, ?_, hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro π
    refine ⟨rfl, rfl, ?_⟩
    norm_num [estimatedEffect, observedTreatment, observedControl, finiteMean,
      fourUnitDesign, Fintype.expect_eq_sum_div_card]
  · norm_num [sampleVariance, finiteMean]
  · norm_num [marginalVarianceEstimate, sampleVariance, finiteMean]
  · intro B
    cases B
    · exact (Bridge.sharpCovariance_eq _ _ .H) ▸ AronowAudit.P022.sharp_covariance_two_ones .H
    · exact (Bridge.sharpCovariance_eq _ _ .L) ▸ AronowAudit.P022.sharp_covariance_two_ones .L
  · rfl
  · norm_num [codePoint, partitionPoint, hp]
  · norm_num [codePoint, partitionPoint, hp]
  · intro r hr
    interval_cases r <;> apply AronowAudit.P022.quantile_two_ones <;>
      norm_num [codePoint, partitionPoint, hp, codeEpsilon]
  · intro r hr
    interval_cases r <;>
      norm_num [codePoint, partitionPoint, hp, hq0, hq1, hq2,
        orderStatistic, sortedOutcomes, List.ofFn_succ, List.mergeSort]
  · norm_num [codePoint, partitionPoint, hp]
    ring
  · norm_num [codePoint, partitionPoint, hp]
  · norm_num [codeEpsilon]
  · norm_num [codeEpsilon]
  · norm_num

end
end SAP.P022.WH.W1
