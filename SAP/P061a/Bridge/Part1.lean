import SAP.P061a.Defs
import AronowAudit.P061.P061_Foundations
import AronowAudit.P061.P061_PaperDomains
import AronowAudit.P061.P061_Refutations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a.Bridge

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

/-- Structural adapter; the masses and normalization certificates are unchanged. -/
def toProject {Ω : Type} (D : AtomicDesign Ω) : AronowAudit.P061.Design Ω :=
  ⟨D.mass, D.mass_nonnegative, D.mass_summable, D.mass_total⟩

def fromProject {Ω : Type} (D : AronowAudit.P061.Design Ω) : AtomicDesign Ω :=
  ⟨D.p, D.nonneg, D.summable, D.total⟩

theorem to_from {Ω : Type} (D : AronowAudit.P061.Design Ω) :
    toProject (fromProject D) = D := rfl

theorem from_to {Ω : Type} (D : AtomicDesign Ω) : fromProject (toProject D) = D := rfl

theorem probability_correspondence {Ω : Type} (D : AtomicDesign Ω) (A : Ω → Prop) :
    eventProbability D A = AronowAudit.P061.probability (toProject D) A := rfl

theorem mean_correspondence {Ω : Type} (D : AtomicDesign Ω) (X : Ω → ℝ) :
    mean D X = AronowAudit.P061.expectation (toProject D) X := rfl

theorem moment_correspondence {Ω : Type} (D : AtomicDesign Ω) (X : Ω → ℝ) :
    HasMean D X ↔ AronowAudit.P061.Integrable (toProject D) X := Iff.rfl

theorem targets_correspondence {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) (d d' : ℝ) :
    populationContrast D g y d d' = AronowAudit.P061.aeed (toProject D) g y d d' := rfl

theorem estimator_correspondence {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) (d d' : ℝ) :
    estimateContrast D g y d d' = AronowAudit.P061.htContrast (toProject D) g y d d' := rfl

theorem version_correspondence : T1Statement := by
  refine ⟨fun N => fromProject (AronowAudit.P061.ternaryDesign N), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N z
    simp only [fromProject, AronowAudit.P061.ternaryDesign,
      AronowAudit.P061.productDesign, AronowAudit.P061.uniformDesign,
      Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    norm_num
  · intro N hN
    refine ⟨AronowAudit.P061.coarsened_version_counterexample N hN, ?_, ?_,
      AronowAudit.P061.coarsened_two_direct_averages N hN,
      AronowAudit.P061.coarsened_ht_moments N hN⟩
    · exact AronowAudit.P061.ternary_marginals N
    · intro i
      change AronowAudit.P061.eed (AronowAudit.P061.ternaryDesign N)
        AronowAudit.P061.ternaryExposure AronowAudit.P061.ternaryOutcome i 1 0 = 3/2
      simp only [AronowAudit.P061.eed, (AronowAudit.P061.ternary_marginals N i).2.2.1,
        (AronowAudit.P061.ternary_marginals N i).2.2.2, sub_zero]
  · exact AronowAudit.P061.coarsened_no_exposure_schedule
  · intro i
    fin_cases i <;> norm_num [versionExposure, coarsenVersion]
  · norm_num [versionResponse]
  · norm_num [versionResponse]
  · exact AronowAudit.P061.coarsened_nonvanishing_gap

theorem edge_correspondence : T2Statement := by
  constructor
  · refine ⟨fromProject (AronowAudit.P061.uniformDesign BitPair), fun _ => rfl, ?_⟩
    refine ⟨AronowAudit.P061.network_domain_counterexample,
      AronowAudit.P061.network_image, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num [edgeExposureVector, edgeExposure, ownBit, partnerBit]
    · norm_num [edgeExposureVector, edgeExposure, ownBit, partnerBit]
    · norm_num [edgeExposureVector, edgeExposure, ownBit, partnerBit]
    · norm_num [edgeExposureVector, edgeExposure, ownBit, partnerBit]
    · refine ⟨1/4, by norm_num, ?_⟩
      intro i
      change 1/4 ≤ AronowAudit.P061.pi (AronowAudit.P061.uniformDesign BitPair)
        AronowAudit.P061.networkExposure i 1
      have h := AronowAudit.P061.network_domain_counterexample.1 i (1 : Fin 4)
      norm_num at h
      exact h.ge
    · refine ⟨1/4, by norm_num, ?_⟩
      intro i
      change 1/4 ≤ AronowAudit.P061.pi (AronowAudit.P061.uniformDesign BitPair)
        AronowAudit.P061.networkExposure i 0
      have h := AronowAudit.P061.network_domain_counterexample.1 i (0 : Fin 4)
      norm_num at h
      exact h.ge
    · exact AronowAudit.P061.sutva_implies_nurva (AronowAudit.P061.uniformDesign BitPair)
        AronowAudit.P061.networkExposure AronowAudit.P061.pairAssignment
        AronowAudit.P061.network_domain_counterexample.2.2.2.1
    · rintro ⟨x,y⟩
      fin_cases x <;> fin_cases y <;> norm_num [inBitDomain, edgeExposure, ownBit, partnerBit]
  · intro K hK
    refine ⟨fromProject (AronowAudit.P061.productDesign K
      (fun _ => AronowAudit.P061.uniformDesign BitPair)), fun _ => rfl, ?_⟩
    exact AronowAudit.P061.network_domain_all_even K hK

theorem comparison_correspondence : T3Statement := by
  constructor
  · intro N S D y d d' hN hp hm hm' hi
    exact AronowAudit.P061.corrected_coordinate_comparison S (toProject D) y d d' hN hp hm hm' hi
  · intro Ω N D g y H d d' hN hp hm hm' hi hc
    exact AronowAudit.P061.corrected_exposure_schedule_comparison (toProject D) g y H d d'
      hN hp hm hm' hi hc

theorem pair_direct_eq (m : ℕ) :
    pairDirectContrast m (fromProject (AronowAudit.P061.localDesign m)) =
      AronowAudit.P061.localDirectEffect m := rfl

theorem pair_estimator_eq (m : ℕ) :
    pairEstimator m (fromProject (AronowAudit.P061.localDesign m)) =
      AronowAudit.P061.localEstimator m := rfl

theorem pair_error_eq (m : ℕ) :
    pairStandardError m (fromProject (AronowAudit.P061.localDesign m)) =
      AronowAudit.P061.localStandardError m := rfl

theorem pair_contrast_eq (m : ℕ) :
    populationContrast (fromProject (AronowAudit.P061.localDesign m))
      (pairedOwnBit (m^8)) (pairResponses m) 1 0 =
      AronowAudit.P061.aeed (AronowAudit.P061.localDesign m)
        (AronowAudit.P061.pairedAssignment (m^8)) (AronowAudit.P061.localOutcome m) 1 0 := rfl

theorem pair_variance_eq (m : ℕ) :
    designVariance (fromProject (AronowAudit.P061.localDesign m))
      (pairEstimator m (fromProject (AronowAudit.P061.localDesign m))) =
      AronowAudit.P061.variance (AronowAudit.P061.localDesign m)
        (AronowAudit.P061.localEstimator m) := rfl

theorem probability_from {Ω : Type} (D : AronowAudit.P061.Design Ω) (A : Ω → Prop) :
    eventProbability (fromProject D) A = AronowAudit.P061.probability D A := rfl

theorem variance_from {Ω : Type} (D : AronowAudit.P061.Design Ω) (X : Ω → ℝ) :
    designVariance (fromProject D) X = AronowAudit.P061.variance D X := rfl

set_option maxHeartbeats 1600000 in
theorem pair_inference_correspondence : T4Statement := by
  refine ⟨fun m => fromProject (AronowAudit.P061.localDesign m), fun _ _ => rfl, ?_, ?_⟩
  · intro m hm
    refine ⟨AronowAudit.P061.local_inference_counterexample m hm, ?_⟩
    apply Real.sqrt_pos.mpr
    change 0 < AronowAudit.P061.variance (AronowAudit.P061.localDesign m)
      (AronowAudit.P061.localEstimator m)
    rw [(AronowAudit.P061.local_finite_moments m hm).2.2.2]
    have hV := (AronowAudit.P061.local_variance_polynomial_bounds m hm).1
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    exact div_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) hV) (by positivity)
  · obtain ⟨h1, h2, h3, h4⟩ := AronowAudit.P061.local_inference_limits
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [pair_contrast_eq, pair_direct_eq, pair_variance_eq, pair_estimator_eq,
        pair_error_eq, probability_from, variance_from, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h1.comp (tendsto_add_atTop_nat 2)
    · simpa only [pair_contrast_eq, pair_direct_eq, pair_variance_eq, pair_estimator_eq,
        pair_error_eq, probability_from, variance_from, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h2.comp (tendsto_add_atTop_nat 2)
    · simpa only [pair_contrast_eq, pair_direct_eq, pair_variance_eq, pair_estimator_eq,
        pair_error_eq, probability_from, variance_from, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h3.comp (tendsto_add_atTop_nat 2)
    · simpa only [pair_contrast_eq, pair_direct_eq, pair_variance_eq, pair_estimator_eq,
        pair_error_eq, probability_from, variance_from, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h4.comp (tendsto_add_atTop_nat 2)

end SAP.P061a.Bridge
