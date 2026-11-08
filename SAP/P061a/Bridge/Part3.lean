import SAP.P061a.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a.Bridge

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

theorem divergent_correspondence : T7Statement := by
  let D := fromProject AronowAudit.P061.realGeometricDesign
  have hterm (k : ℕ) : integerResponseTerm D k = (-1 : ℝ)^k := by
    simpa only [integerResponseTerm, D, fromProject, AronowAudit.P061.realGeometricDesign,
      AronowAudit.P061.extendDesign, AronowAudit.P061.geometricDesign, integerResponse,
      alternatingResponse, AronowAudit.P061.divergentNaturalOutcome,
      Function.Injective.extend_apply Nat.cast_injective] using
      AronowAudit.P061.divergent_weighted_term k
  have hestimator (k : ℕ) : integerEstimatorTerm D k = 2*(-1 : ℝ)^k := by
    change AronowAudit.P061.realGeometricDesign.p ((k+1 : ℕ) : ℝ) *
      AronowAudit.P061.ht AronowAudit.P061.realGeometricDesign
        AronowAudit.P061.divergentExposure AronowAudit.P061.divergentOutcome 1 ((k+1 : ℕ) : ℝ) = _
    rw [AronowAudit.P061.divergent_ht_formula]
    have hg : AronowAudit.P061.divergentExposure 0 ((k+1 : ℕ) : ℝ) = 1 := by
      simp only [AronowAudit.P061.divergentExposure,
        Function.Injective.extend_apply Nat.cast_injective, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, ite_false]
    rw [hg, if_pos rfl, mul_one]
    calc
      _ = 2 * integerResponseTerm D k := by
        change AronowAudit.P061.realGeometricDesign.p ((k+1 : ℕ) : ℝ) *
          (2 * AronowAudit.P061.divergentOutcome 0 ((k+1 : ℕ) : ℝ)) =
          2 * (AronowAudit.P061.realGeometricDesign.p ((k+1 : ℕ) : ℝ) *
            AronowAudit.P061.divergentOutcome 0 ((k+1 : ℕ) : ℝ))
        ring
      _ = _ := by rw [hterm]
  have hzero : HasMean D (fun z => if integerExposure 0 z=0 then integerResponse 0 z else 0) := by
    apply (AronowAudit.P061.constant_cell AronowAudit.P061.realGeometricDesign
      AronowAudit.P061.divergentExposure AronowAudit.P061.divergentOutcome 0 0 0
      (by rw [AronowAudit.P061.missing_moment_counterexample.2.1]; norm_num) ?_).1
    intro z hz hg
    obtain ⟨k, rfl⟩ := (AronowAudit.P061.geometric_real_support z).mp hz
    have hk : k=0 := by
      by_contra hk
      simpa only [AronowAudit.P061.divergentExposure,
        Function.Injective.extend_apply Nat.cast_injective, hk, ite_false, one_ne_zero] using hg
    subst k
    simp only [AronowAudit.P061.divergentOutcome,
      Function.Injective.extend_apply Nat.cast_injective, AronowAudit.P061.divergentNaturalOutcome,
      ite_true]
  have hparts := AronowAudit.P061.divergent_parts_not_summable
  have hscaled (f : ℕ → ℝ) (hf : ¬Summable (fun k => max (f k) 0)) :
      ¬Summable (fun k => max (2*f k) 0) := by
    intro hs
    apply hf
    apply (summable_mul_left_iff (by norm_num : (2 : ℝ) ≠ 0)).mp
    simpa only [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), mul_zero] using hs
  refine ⟨D, rfl, AronowAudit.P061.geometric_real_support,
    AronowAudit.P061.Refutations.divergent_exposure_one_positive,
    AronowAudit.P061.Refutations.divergent_exposure_zero_positive,
    AronowAudit.P061.missing_moment_counterexample, hzero, hterm, ?_, ?_, ?_,
    AronowAudit.P061.divergent_ht_formula, hestimator, ?_, ?_⟩
  · intro m
    simpa only [hterm] using AronowAudit.P061.divergent_partial_sums m
  · simpa only [hterm] using hparts.1
  · simpa only [hterm] using hparts.2
  · simpa only [hestimator] using hscaled (fun k => (-1 : ℝ)^k) hparts.1
  · simpa only [hestimator, neg_mul_eq_mul_neg] using hscaled (fun k => -((-1 : ℝ)^k)) hparts.2

/-- Extensional equality of the bundled data; all remaining fields are propositions. -/
theorem project_design_ext {Ω : Type} (D D' : AronowAudit.P061.Design Ω)
    (h : D.p = D'.p) : D = D' := by
  cases D
  cases D'
  cases h
  rfl

theorem sampling_correspondence : T9Statement := by
  obtain ⟨D, D', hD, hD', hp, hn, hn', ht, ht', hs⟩ :=
    AronowAudit.P061.sampling_treatment_designs_differ
  have eD : D = AronowAudit.P061.samplingTreatmentDesign 2 (Or.inl rfl) :=
    project_design_ext _ _ (funext hD)
  have eD' : D' = AronowAudit.P061.samplingTreatmentDesign 3 (Or.inr rfl) :=
    project_design_ext _ _ (funext hD')
  subst D
  subst D'
  have h2 := AronowAudit.P061.sampling_treatment_properties 2 (Or.inl rfl)
  have h3 := AronowAudit.P061.sampling_treatment_properties 3 (Or.inr rfl)
  refine ⟨fromProject (AronowAudit.P061.samplingTreatmentDesign 2 (Or.inl rfl)),
    fromProject (AronowAudit.P061.samplingTreatmentDesign 3 (Or.inr rfl)),
    hD, hD', h2.1, h3.1, ?_, hp, hn, hn', ?_, ht, ht', hs⟩
  · intro i
    have hi2 := h2.2.1 i
    have hi3 := h3.2.1 i
    norm_num at hi2 hi3
    exact ⟨hi2.1, hi2.2, hi3.1, hi3.2⟩
  · intro i
    exact ⟨(h2.2.2.2 i).1, (h2.2.2.2 i).2,
      (h3.2.2.2 i).1, (h3.2.2.2 i).2⟩

end SAP.P061a.Bridge
