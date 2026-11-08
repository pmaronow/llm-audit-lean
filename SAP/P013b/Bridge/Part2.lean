import SAP.P013b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b.Bridge
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

theorem covarianceHT_conservative {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e)
    (hj : ∀ i j, i ≠ j → 0 < jointPi F i j d e) :
    expectation P (covarianceHT F d e) ≤ covariance P (htTotal F d) (htTotal F e) := by
  exact AronowAudit.P013.covarianceHT_conservative (toPopulation F) d e hne hd he hj

theorem covarianceHT_unbiased_no_effect {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e)
    (hj : ∀ i j, i ≠ j → 0 < jointPi F i j d e) (hy : ∀ i, F.outcome i d = F.outcome i e) :
    expectation P (covarianceHT F d e) = covariance P (htTotal F d) (htTotal F e) := by
  exact AronowAudit.P013.covarianceHT_unbiased_no_effect (toPopulation F) d e hne hd he hj hy

theorem covarianceA_conservative {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e) :
    expectation P (covarianceA F d e) ≤ covariance P (htTotal F d) (htTotal F e) := by
  exact AronowAudit.P013.covarianceA_conservative (toPopulation F) d e hne hd he

theorem effectVariance_conservative {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (hne : d ≠ e) (hd : Positivity F d) (he : Positivity F e) :
    variance P (htEffect F d e) ≤ expectation P (effectVariance F d e) := by
  exact AronowAudit.P013.effectVariance_conservative (toPopulation F) d e hne hd he

theorem differenceTotal_unbiased {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (g : Fin N → ℝ) (hd : Positivity F d) :
    expectation P (differenceTotal F d g) = potentialTotal F d := by
  exact AronowAudit.P013.differenceTotal_unbiased (toPopulation F) d g hd

theorem differenceTotal_residual {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (g : Fin N → ℝ) (z : Ω) :
    differenceTotal F d g z =
      (∑ i, indicator F.exposure i d z * ((observed F z i - g i) / pi F i d)) + ∑ i, g i := by
  exact AronowAudit.P013.differenceTotal_residual (toPopulation F) d g z

theorem htCount_unbiased {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (d : Fin K) (hd : Positivity F d) :
    expectation P (htCount F d) = (N : ℝ) := by
  exact AronowAudit.P013.htCount_unbiased (toPopulation F) d hd

theorem hajek_bias_bound {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (hN : 0 < N) (d : Fin K) (hd : Positivity F d) :
    |expectation P (hajek F d) - potentialMean F d| ≤
      Real.sqrt (variance P (fun z => htCount F d z / (N : ℝ)) * variance P (hajek F d)) := by
  exact AronowAudit.P013.hajek_bias_bound (toPopulation F) hN d hd

theorem misspecified_expectation {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (yr : Fin N → Ω → ℝ) (d : Fin K) (_hm : Misspecified F yr) (_hd : Positivity F d) :
    expectation P (htRandomizationTotal F yr d) = conditionalPotentialTotal F yr d := by
  exact AronowAudit.P013.misspecified_expectation (toPopulation F) yr d _hm _hd

theorem misspecified_contrast {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (yr : Fin N → Ω → ℝ) (d e : Fin K) (_hne : d ≠ e) (hm : Misspecified F yr)
    (hd : Positivity F d) (he : Positivity F e) :
    expectation P (fun z => (htRandomizationTotal F yr d z - htRandomizationTotal F yr e z) /
      (N : ℝ)) = (conditionalPotentialTotal F yr d - conditionalPotentialTotal F yr e) / (N : ℝ) := by
  exact AronowAudit.P013.misspecified_contrast (toPopulation F) yr d e _hne hm hd he

theorem htEffect_consistency (S : ExperimentSequence) (hnested : NestedPopulationSetup S) (hp : StandingPositivity S)
    (hc3 : Condition3 S) (hc4 : Condition4 S) :
    ConvergesInProbability (seqLaw S) (fun (n : ℕ) z => seqEstimate S n z-seqTarget S n) 0 := by
  exact AronowAudit.P013.htEffect_consistency (toSequence S) hnested hp hc3 hc4

theorem public_reconstruction_factors  :
    2050 - 342 = (1708 : ℕ) ∧ 2050 - 151 = (1899 : ℕ) ∧
    (1708 : ℝ) / 2050 = 854 / 1025 ∧
    (342 : ℝ) / 2050 = 171 / 1025 ∧
    (1899 : ℝ) / 2050 + 151 / 2050 = 1 ∧
    1034 + 157 + 348 + 199 + 312 = (2050 : ℕ) ∧
    198 + 25 + 51 + 25 + 43 = (342 : ℕ) ∧
    78 + 11 + 26 + 13 + 23 = (151 : ℕ) := by
  exact AronowAudit.P013.public_reconstruction_factors

theorem school_supports_nonempty  :
    schoolBSupport.Nonempty ∧ schoolCSupport.Nonempty := by
  exact AronowAudit.P013.school_supports_nonempty

theorem uniform_school_probability_mean {α : Type*} (S : Finset α) (A : α → Prop) [DecidablePred A] :
    uniformSchoolProbability S A = uniformSchoolMean S (fun z => if A z then 1 else 0) := by
  exact AronowAudit.P013.uniform_school_probability_mean S A

theorem school_local_mean {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (hosts : α → School → Bool) (a : School) (X : Bool → ℝ)
    (ha : uniformSchoolProbability S (fun z => hosts z a = true) = 1/2) :
    uniformSchoolMean S (fun z => X (hosts z a)) = (X false + X true)/2 := by
  exact AronowAudit.P013.school_local_mean S hS hosts a X ha

theorem location_counterexample_hypotheses  :
    (∀ i, pi locationPopulation i 1 = locationDesign.weight i) ∧
    (∀ i, pi locationPopulation i 0 = 1 - locationDesign.weight i) ∧
    (∀ d, Positivity locationPopulation d) ∧
    (∀ i d, locationPopulation.outcome i d = locationPrediction i) ∧
    (∀ i, covariance locationDesign (fun _ => locationPrediction i)
      (fun z => indicator locationPopulation.exposure i 1 z) = 0) ∧
    (∀ z, (∑ i, indicator locationPopulation.exposure i 1 z) = 1 ∧
      (∑ i, indicator locationPopulation.exposure i 0 z) = 2) := by
  exact AronowAudit.P013.location_counterexample_hypotheses

theorem location_counterexample_targets  :
    (∀ d, potentialTotal locationPopulation d = 10 ∧
      potentialTotal (shiftPopulation locationPopulation 1) d = 13) ∧
    causalEffect locationPopulation 1 0 = 0 ∧
    causalEffect (shiftPopulation locationPopulation 1) 1 0 = 0 ∧
    (∀ z d, differenceTotal locationPopulation d locationPrediction z = 10) ∧
    (∀ z, differenceEffect locationPopulation 1 0 locationPrediction locationPrediction z = 0) := by
  exact AronowAudit.P013.location_counterexample_targets

theorem location_counterexample_enumeration  :
    ∀ z : Fin 3,
      htCount locationPopulation 1 z = (if z = 2 then 2 else 4) ∧
      htCount locationPopulation 0 z = (if z = 2 then 8/3 else 10/3) ∧
      differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction z =
        (if z = 2 then 12 else 14) ∧
      differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction z =
        (if z = 2 then 38/3 else 40/3) ∧
      differenceEffect (shiftPopulation locationPopulation 1) 1 0
        locationPrediction locationPrediction z = (if z = 2 then -2/9 else 2/9) := by
  exact AronowAudit.P013.location_counterexample_enumeration

theorem location_translation_counterexample  :
    (∀ d, Positivity locationPopulation d) ∧
    (∀ i, covariance locationDesign (fun _ => locationPrediction i)
      (fun z => indicator locationPopulation.exposure i 1 z) = 0) ∧
    (∀ z, (∑ i, indicator locationPopulation.exposure i 1 z) = 1 ∧
      (∑ i, indicator locationPopulation.exposure i 0 z) = 2) ∧
    causalEffect (shiftPopulation locationPopulation 1) 1 0 = causalEffect locationPopulation 1 0 ∧
    (∀ z, differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction z ≠
      differenceTotal locationPopulation 1 locationPrediction z + 1 * (3 : ℝ) ∧
      differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction z ≠
        differenceTotal locationPopulation 0 locationPrediction z + 1 * (3 : ℝ) ∧
      differenceEffect (shiftPopulation locationPopulation 1) 1 0 locationPrediction locationPrediction z ≠
        differenceEffect locationPopulation 1 0 locationPrediction locationPrediction z) := by
  exact AronowAudit.P013.location_translation_counterexample

theorem location_counterexample_moments  :
    expectation locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction) = 13 ∧
    expectation locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction) = 13 ∧
    expectation locationDesign (differenceEffect (shiftPopulation locationPopulation 1) 1 0
      locationPrediction locationPrediction) = 0 ∧
    variance locationDesign (differenceTotal locationPopulation 1 locationPrediction) = 0 ∧
    variance locationDesign (differenceTotal locationPopulation 0 locationPrediction) = 0 ∧
    variance locationDesign (differenceEffect locationPopulation 1 0 locationPrediction locationPrediction) = 0 ∧
    variance locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 1 locationPrediction) = 1 ∧
    variance locationDesign (differenceTotal (shiftPopulation locationPopulation 1) 0 locationPrediction) = 1/9 ∧
    variance locationDesign (differenceEffect (shiftPopulation locationPopulation 1) 1 0
      locationPrediction locationPrediction) = 4/81 := by
  exact AronowAudit.P013.location_counterexample_moments

theorem location_counterexample_joint_repair  :
    ∀ z, (∀ d, differenceTotal (shiftPopulation locationPopulation 1) d
      (fun i => locationPrediction i + 1) z = 13) ∧
    differenceEffect (shiftPopulation locationPopulation 1) 1 0
      (fun i => locationPrediction i + 1) (fun i => locationPrediction i + 1) z = 0 := by
  exact AronowAudit.P013.location_counterexample_joint_repair

theorem differenceTotal_shift_change {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d) :
    differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z -
      differenceTotal F d g z =
        c * htCount F d z + ∑ i, (1 - exposureWeight F d z i) * h i := by
  exact AronowAudit.P013.differenceTotal_shift_change (toPopulation F) d g h c z hN hd

theorem differenceTotal_shift_error {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d) :
    differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z -
      differenceTotal F d g z - c * N = translationError F d h c z := by
  exact AronowAudit.P013.differenceTotal_shift_error (toPopulation F) d g h c z hN hd

theorem differenceTotal_equivariance_iff {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g h : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d) :
    (differenceTotal (shiftPopulation F c) d (fun i => g i + h i) z =
      differenceTotal F d g z + c * N) ↔ translationError F d h c z = 0 := by
  exact AronowAudit.P013.differenceTotal_equivariance_iff (toPopulation F) d g h c z hN hd

theorem differenceTotal_joint_translation {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (g : Fin N → ℝ) (c : ℝ) (z : Ω) (hN : 0 < N) (hd : ∀ i, 0 < pi F i d) :
    differenceTotal (shiftPopulation F c) d (fun i => g i + c) z =
      differenceTotal F d g z + c * N := by
  exact AronowAudit.P013.differenceTotal_joint_translation (toPopulation F) d g c z hN hd

theorem difference_joint_translation_properties {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K)
    (gk gl : Fin N → ℝ) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e) :
    (differenceTotal (shiftPopulation F c) d (fun i => gk i + c) z / N =
      differenceTotal F d gk z / N + c) ∧
    (differenceTotal (shiftPopulation F c) e (fun i => gl i + c) z / N =
      differenceTotal F e gl z / N + c) ∧
    (∀ i, F.exposure z i = d → observed (shiftPopulation F c) z i - (gk i + c) = observed F z i - gk i) ∧
    (∀ i, F.exposure z i = e → observed (shiftPopulation F c) z i - (gl i + c) = observed F z i - gl i) ∧
    differenceEffect (shiftPopulation F c) d e (fun i => gk i + c) (fun i => gl i + c) z =
      differenceEffect F d e gk gl z ∧
    potentialTotal (shiftPopulation F c) d = potentialTotal F d + c * N ∧
    potentialTotal (shiftPopulation F c) e = potentialTotal F e + c * N ∧
    causalEffect (shiftPopulation F c) d e = causalEffect F d e := by
  exact AronowAudit.P013.difference_joint_translation_properties (toPopulation F) hN d e gk gl c z hd he hne

theorem differenceEffect_shift_error {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K)
    (gk gl hk hl : Fin N → ℝ) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e) :
    differenceEffect (shiftPopulation F c) d e (fun i => gk i + hk i)
        (fun i => gl i + hl i) z - differenceEffect F d e gk gl z =
      (translationError F d hk c z - translationError F e hl c z) / N ∧
    (differenceEffect (shiftPopulation F c) d e (fun i => gk i + hk i)
        (fun i => gl i + hl i) z = differenceEffect F d e gk gl z ↔
      translationError F d hk c z = translationError F e hl c z) := by
  exact AronowAudit.P013.differenceEffect_shift_error (toPopulation F) hN d e gk gl hk hl c z hd he hne

theorem difference_fixed_prediction_translation {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K)
    (gk gl : Fin N → ℝ) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e) :
    differenceTotal (shiftPopulation F c) d gk z - differenceTotal F d gk z =
      c * htCount F d z ∧
    differenceTotal (shiftPopulation F c) d gk z - differenceTotal F d gk z - c * N =
      c * (htCount F d z - N) ∧
    differenceEffect (shiftPopulation F c) d e gk gl z - differenceEffect F d e gk gl z =
      c * (htCount F d z - htCount F e z) / N ∧
    (c ≠ 0 → (differenceTotal (shiftPopulation F c) d gk z =
      differenceTotal F d gk z + c * N ↔ htCount F d z = N) ∧
      (differenceEffect (shiftPopulation F c) d e gk gl z = differenceEffect F d e gk gl z ↔
        htCount F d z = htCount F e z)) := by
  exact AronowAudit.P013.difference_fixed_prediction_translation (toPopulation F) hN d e gk gl c z hd he hne

theorem exposureWeight_unbiased {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (i : Fin N) (hi : 0 < pi F i d) :
    expectation P (fun z => exposureWeight F d z i) = 1 := by
  exact AronowAudit.P013.exposureWeight_unbiased (toPopulation F) d i hi

theorem ht_fixed_translation {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (hN : 0 < N) (d e : Fin K) (c : ℝ) (z : Ω) (hd : ∀ i, 0 < pi F i d)
    (he : ∀ i, 0 < pi F i e) (hne : d ≠ e) :
    differenceTotal F d (fun _ => 0) z = htTotal F d z ∧
    differenceEffect F d e (fun _ => 0) (fun _ => 0) z = htEffect F d e z ∧
    htTotal (shiftPopulation F c) d z - htTotal F d z = c * htCount F d z ∧
    htEffect (shiftPopulation F c) d e z - htEffect F d e z =
      c * (htCount F d z - htCount F e z) / N := by
  exact AronowAudit.P013.ht_fixed_translation (toPopulation F) hN d e c z hd he hne

end
end SAP.P013b.Bridge
