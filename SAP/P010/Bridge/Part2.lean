import SAP.P010.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P010.Bridge

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Classical Topology BigOperators

theorem T1_correspondence : T1Statement ↔
    (type_of% @AronowAudit.P010.empirical_overlap_counterexample) := Iff.rfl

theorem T2_correspondence : T2Statement ↔
    (type_of% @AronowAudit.P010.empirical_exact_certificate) ∧ (type_of% @AronowAudit.P010.empirical_cutoff_certificate) ∧ (type_of% @AronowAudit.P010.empirical_overlap_corrected) := Iff.rfl

theorem T3_correspondence : T3Statement ↔
    (type_of% @AronowAudit.P010.Wave1.missing_passing_condition_counterexample_proof) := Iff.rfl

theorem T4_correspondence : T4Statement ↔
    (type_of% @AronowAudit.P010.Wave1.proposition_one_finite_proof) := Iff.rfl

theorem T5_correspondence : T5Statement ↔
    (type_of% @AronowAudit.P010.Wave1.infinite_sharp_bounds_counterexample_proof) := Iff.rfl

theorem T6_correspondence : T6Statement ↔
    (type_of% @AronowAudit.P010.Wave1.proposition_one_else_proof) := Iff.rfl

theorem T7_correspondence : T7Statement ↔
    (type_of% @AronowAudit.P010.joint_independence_step_counterexample) := Iff.rfl

theorem T8_correspondence : T8Statement ↔
    (type_of% @AronowAudit.P010.corollary_one_corrected_proof) := Iff.rfl

theorem T9_correspondence : T9Statement ↔
    (type_of% @AronowAudit.P010.Wave1.simulation_width_counterexample_proof) := Iff.rfl

theorem T10_correspondence : T10Statement ↔
    (type_of% @AronowAudit.P010.Wave1.simulation_invariance_corrected_proof) := Iff.rfl

theorem T11_correspondence : T11Statement ↔
    (type_of% @AronowAudit.P010.transport_logistic_certificate) ∧ (type_of% @AronowAudit.P010.transport_odds_counterexample) := Iff.rfl

theorem T13_correspondence : T13Statement ↔
    (type_of% @AronowAudit.P010.Wave1.lower_tail_upper_bound_counterexample_proof) := Iff.rfl

theorem T14_correspondence : T14Statement ↔
    (type_of% @AronowAudit.P010.Wave1.upper_tail_proof_corrected_proof) := Iff.rfl

theorem T15_correspondence : T15Statement ↔ (
∀ {K d : ℕ} (μ : Measure (AronowAudit.P010.State K d))
    (h : AronowAudit.P010.Assumptions μ) (a : Fin K) (hA : 0 < μ AronowAudit.P010.alwaysPass)
    (hc : AronowAudit.P010.Atomless (μ.map AronowAudit.P010.observedY))
    (hi : Integrable AronowAudit.P010.observedY (μ.restrict (AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent a))),
    AronowAudit.P010.eventLaw μ (AronowAudit.P010.potentialY a) (AronowAudit.P010.potentialPass a) = AronowAudit.P010.passerLaw μ a ∧
    (∀ b, (μ (AronowAudit.P010.potentialPass b)).toReal = AronowAudit.P010.passingRate μ b) ∧
    AronowAudit.P010.potentialTrim μ a = AronowAudit.P010.trimRatio μ a ∧
    (AronowAudit.P010.trimRatio μ a < 1 →
      AronowAudit.P010.tailUpper (AronowAudit.P010.eventLaw μ (AronowAudit.P010.potentialY a) (AronowAudit.P010.potentialPass a)) (AronowAudit.P010.trimRatio μ a) = AronowAudit.P010.upperBound μ a ∧
      AronowAudit.P010.eventMean μ (AronowAudit.P010.potentialY a) AronowAudit.P010.alwaysPass = AronowAudit.P010.eventMean μ (AronowAudit.P010.potentialY a) (AronowAudit.P010.otherPass a ∩ AronowAudit.P010.potentialPass a) ∧
      AronowAudit.P010.eventMean μ (AronowAudit.P010.potentialY a) AronowAudit.P010.alwaysPass ≤ AronowAudit.P010.upperBound μ a)) := Iff.rfl

theorem T16_correspondence : T16Statement ↔
    (type_of% @AronowAudit.P010.selection_counterexample_corrected) := Iff.rfl

theorem T17_correspondence : T17Statement ↔ (
    ∀ {K d : ℕ} (μ : Measure (AronowAudit.P010.State K d))
    (hp : IsProbabilityMeasure μ) (h : AronowAudit.P010.Ignorability μ)
    (hP : ∀ a, 0 < μ (AronowAudit.P010.potentialPass a)),
    AronowAudit.P010.NonzeroPassing μ) := Iff.rfl

theorem T18_correspondence : T18Statement ↔
    (type_of% @AronowAudit.P010.corollary_one) := Iff.rfl

theorem T19_correspondence : T19Statement ↔
    (type_of% @AronowAudit.P010.lemma_one) := Iff.rfl

theorem T20_correspondence : T20Statement ↔
    (type_of% @AronowAudit.P010.corollary_two) := Iff.rfl

theorem T21_correspondence : T21Statement ↔ (
∃ μ : Measure (AronowAudit.P010.State 2 1), AronowAudit.P010.Assumptions μ ∧
    IndepFun AronowAudit.P010.observedS AronowAudit.P010.assignment μ ∧ 0 < μ AronowAudit.P010.alwaysPass ∧
    0 < μ (AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 1) ∧ 0 < μ (AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 0) ∧
    Integrable AronowAudit.P010.observedY (μ.restrict (AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 1)) ∧
    Integrable AronowAudit.P010.observedY (μ.restrict (AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 0)) ∧
    Integrable (fun ω => AronowAudit.P010.potentialY 1 ω - AronowAudit.P010.potentialY 0 ω) (μ.restrict AronowAudit.P010.alwaysPass) ∧
    AronowAudit.P010.eventMean μ AronowAudit.P010.observedY (AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 1) - AronowAudit.P010.eventMean μ AronowAudit.P010.observedY (AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 0) ≠
      AronowAudit.P010.eventMean μ (fun ω => AronowAudit.P010.potentialY 1 ω - AronowAudit.P010.potentialY 0 ω) AronowAudit.P010.alwaysPass) := Iff.rfl

theorem T22_correspondence : T22Statement ↔
    (type_of% @AronowAudit.P010.corollary_four) := Iff.rfl

theorem T23_correspondence : T23Statement ↔ (
∃ μ : Measure (AronowAudit.P010.State 2 1),
    IsProbabilityMeasure μ ∧ AronowAudit.P010.NonzeroPassing μ ∧ AronowAudit.P010.CovariateIgnorability μ ∧
    AronowAudit.P010.CovariateBalance μ ∧ 0 < μ (AronowAudit.P010.alwaysPass ∩ {ω | AronowAudit.P010.covariates ω = fun _ => 0}) ∧
    0 < μ ((AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 1) ∩ {ω | AronowAudit.P010.covariates ω = fun _ => 0}) ∧
    0 < μ ((AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 0) ∩ {ω | AronowAudit.P010.covariates ω = fun _ => 0}) ∧
    Integrable AronowAudit.P010.observedY (μ.restrict ((AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 1) ∩ {ω | AronowAudit.P010.covariates ω = fun _ => 0})) ∧
    Integrable AronowAudit.P010.observedY (μ.restrict ((AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 0) ∩ {ω | AronowAudit.P010.covariates ω = fun _ => 0})) ∧
    Integrable (fun ω => AronowAudit.P010.potentialY 1 ω - AronowAudit.P010.potentialY 0 ω)
      (μ.restrict (AronowAudit.P010.alwaysPass ∩ {ω | AronowAudit.P010.covariates ω = fun _ => 0})) ∧
    AronowAudit.P010.eventMean μ AronowAudit.P010.observedY ((AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 1) ∩ {ω | AronowAudit.P010.covariates ω = fun _ => 0}) -
      AronowAudit.P010.eventMean μ AronowAudit.P010.observedY ((AronowAudit.P010.passEvent ∩ AronowAudit.P010.armEvent 0) ∩ {ω | AronowAudit.P010.covariates ω = fun _ => 0}) ≠
      AronowAudit.P010.eventMean μ (fun ω => AronowAudit.P010.potentialY 1 ω - AronowAudit.P010.potentialY 0 ω)
        (AronowAudit.P010.alwaysPass ∩ {ω | AronowAudit.P010.covariates ω = fun _ => 0})) := Iff.rfl

theorem T12_correspondence {Ω : Type*} [MeasurableSpace Ω] :
    T12Statement Ω ↔ (
∀ (ν : Measure Ω) (π : ℝ) (fR fO : Ω → ℝ),
    0 < π → π < 1 →
    (∀ᵐ x ∂ν, 0 < fR x) → (∀ᵐ x ∂ν, 0 < fO x) →
    Integrable fR ν → Integrable fO ν →
    (∫ x, fR x ∂ν) = 1 → (∫ x, fO x ∂ν) = 1 →
    (∀ᵐ x ∂ν,
      0 < AronowAudit.P010.studyPropensity π (fR x) (fO x) ∧ AronowAudit.P010.studyPropensity π (fR x) (fO x) < 1 ∧
      AronowAudit.P010.printedOdds (AronowAudit.P010.studyPropensity π (fR x) (fO x)) = π/(1-π)*(fR x/fO x) ∧
      fO x/fR x = π/(1-π)*AronowAudit.P010.correctedOdds (AronowAudit.P010.studyPropensity π (fR x) (fO x))) ∧
    (∫ x, fR x*AronowAudit.P010.correctedOdds (AronowAudit.P010.studyPropensity π (fR x) (fO x)) ∂ν) = (1-π)/π ∧
    ((fun x => AronowAudit.P010.reweightedDensity ν fR
      (fun u => AronowAudit.P010.correctedOdds (AronowAudit.P010.studyPropensity π (fR u) (fO u))) x) =ᵐ[ν] fO) ∧
    (∀ c : ℝ, 0 < c →
      (fun x => AronowAudit.P010.reweightedDensity ν fR
        (fun u => c*AronowAudit.P010.correctedOdds (AronowAudit.P010.studyPropensity π (fR u) (fO u))) x) =ᵐ[ν] fO) ∧
    (Integrable (fun x => (fR x)^2/fO x) ν →
      0 < (∫ x, (fR x)^2/fO x ∂ν) ∧
      ((fun x => AronowAudit.P010.reweightedDensity ν fR
        (fun u => AronowAudit.P010.printedOdds (AronowAudit.P010.studyPropensity π (fR u) (fO u))) x) =ᵐ[ν]
        (fun x => (fR x)^2/fO x / ∫ u, (fR u)^2/fO u ∂ν)) ∧
      (((fun x => AronowAudit.P010.reweightedDensity ν fR
        (fun u => AronowAudit.P010.printedOdds (AronowAudit.P010.studyPropensity π (fR u) (fO u))) x) =ᵐ[ν] fO) ↔ fR =ᵐ[ν] fO))) := Iff.rfl

end SAP.P010.Bridge
