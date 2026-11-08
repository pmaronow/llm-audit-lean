import SAP.P037b.Defs
import AronowAudit.P037.P037_Design
import AronowAudit.P037.P037_Inference
import AronowAudit.P037.P037_Network
import AronowAudit.P037.P037_Sample
import AronowAudit.P037.Wave1.Gap.GLP037B2
import AronowAudit.P037.Wave1.Gap.GP037B1
import AronowAudit.P037.Wave1.Gap.GP037B2
import AronowAudit.P037.Wave1.Gap.GP037B3
import AronowAudit.P037.Wave1.Gap.GP037B4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037b
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Bridge

/-- Copy only the data and support certificates into the project record. -/
def toProject {Ω : Type*} [Fintype Ω] (P : ProbabilityDesign Ω) :
    AronowAudit.P037.SupportedDesign Ω := ⟨P.mass, P.positive, P.total⟩

/-- Both probability sums use the same weights and indicator. -/
theorem probability_correspondence {Ω : Type*} [Fintype Ω]
    (P : ProbabilityDesign Ω) (E : Ω → Prop) :
    eventProbability P E = AronowAudit.P037.sampleProb (toProject P) E := rfl

/-- Both expectations use the same finite weighted sum. -/
theorem expectation_correspondence {Ω : Type*} [Fintype Ω]
    (P : ProbabilityDesign Ω) (Y : Ω → ℝ) :
    finiteExpectation P Y = AronowAudit.P037.sampleMean (toProject P) Y := rfl

end Bridge

theorem Bridge.T18_correspondence : T18Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Ω inst1 μ inst3 n k X y hX v h1 h2 hmean hmom
    exact @AronowAudit.P037.wild_bootstrap_is_hc0 Ω inst1 μ inst3 n k X y hX v h1 h2 hmean hmom
  · intro n k X hX hn
    exact @AronowAudit.P037.school_leverage_facts n k X hX hn
  · intro Ω inst1 μ inst3 n k X hX β σ2 hσ u h1 h2 hmean hmom
    exact @AronowAudit.P037.hc0_homoskedastic_shortfall Ω inst1 μ inst3 n k X hX β σ2 hσ u h1 h2 hmean hmom
  · intro n a h hh ha
    exact @AronowAudit.P037.hc0_row_bias_factor n a h hh ha

theorem Bridge.T19_correspondence : T19Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact @AronowAudit.P037.outcome_selection_finite_counterexample 
  · intro ε hε
    exact @AronowAudit.P037.Wave1.outcome_selection_regression_limit_proof ε hε
  · intro nT nC yT yC ht hc
    exact @AronowAudit.P037.selected_block_crossproducts nT nC yT yC ht hc
  · intro S hS
    have h : ∀ i, potentialOutcome4 i true - potentialOutcome4 i false = 3/100 :=
      AronowAudit.P037.outcome_selection_finite_counterexample.1
    simp_rw [h]
    have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hS)
    simp [nsmul_eq_mul, hc]

theorem Bridge.T20_correspondence : T20Statement := by
  refine ⟨?_, ?_⟩
  · intro Ω I K inst1 inst2 inst3 P D A y a
    exact @AronowAudit.P037.selection_ipw_identities Ω I K inst1 inst2 inst3 (Bridge.toProject P) D A y a
  · intro Ω I Y h
    exact @AronowAudit.P037.threshold_assignment_invariant Ω I Y h

theorem Bridge.T21_correspondence : T21Statement := by
  refine ⟨?_, ?_, ?_⟩
  · exact @AronowAudit.P037.Wave1.positivity_cutoff_counterexamples_proof 
  · exact @AronowAudit.P037.Wave1.cutoff_simulated_sequence_proof 
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact AronowAudit.P037.Wave1.positivity_w1_counts
    · exact AronowAudit.P037.Wave1.positivity_w2_counts
    · norm_num [Fin.sum_univ_succ]
    · norm_num [Fin.sum_univ_succ]
    · intro k; fin_cases k <;> norm_num
    · norm_num

theorem Bridge.T22_correspondence : T22Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Ω I inst1 P D J hJ draws seed outcome baseline screen z
    exact @AronowAudit.P037.Wave1.analysis_set_inclusions_proof Ω I inst1 (Bridge.toProject P) D J hJ draws seed outcome baseline screen z
  · intro Ω inst1 P E hp hq
    exact @AronowAudit.P037.Wave1.estimated_cutoff_random_proof Ω inst1 (Bridge.toProject P) E hp hq
  · intro Ω I inst1 P estimated seed outcome baseline screen i
    exact @AronowAudit.P037.code_analysis_seed_exclusion Ω I inst1 (Bridge.toProject P) estimated seed outcome baseline screen i
  · intro r hr
    exact @AronowAudit.P037.cutoff_integer_rule r hr

theorem Bridge.T23_correspondence : T23Statement := by
  refine ⟨?_, ?_, ?_⟩
  · exact @AronowAudit.P037.band_ols_hc0_certificate 
  · exact @AronowAudit.P037.band_counterexample_values 
  · exact @AronowAudit.P037.band_centered_refit_certificate

theorem Bridge.T24_correspondence : T24Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro p zbar b c
    exact @AronowAudit.P037.interaction_prediction_rows p zbar b c
  · intro k V hV l0 d
    exact @AronowAudit.P037.prediction_mean_contrast_variance k V hV l0 d
  · intro n p T C z y c
    exact @AronowAudit.P037.centered_refit_is_contrast n p T C z y c

theorem Bridge.T25_correspondence : T25Statement := by
  refine ⟨?_, ?_⟩
  · exact @AronowAudit.P037.Wave1.nomination_union_counterexamples_proof 
  · have h : indegreeQuantile90 nominationGraph10=11/10 ∧ referentStudents nominationGraph10={1} ∧
    networkExposureLabel nominationGraph10 (referentStudents nominationGraph10) {1} 0=0 ∧
    networkExposureLabel (peerUnion nominationGraph10) (referentStudents nominationGraph10) {1} 0=2 ∧
    indegreeQuantile90 nominationGraph20=3/2 ∧ referentStudents nominationGraph20={1,2} ∧
    (∀ k, graphExposureProbability20 nominationGraph20 k=(![1/2,1/10,3/20,1/4] : Fin 4 → ℝ) k) ∧
    (∀ k, graphExposureProbability20 (peerUnion nominationGraph20) k=(![1/2,1/40,3/40,2/5] : Fin 4 → ℝ) k) ∧
    (∀ k, 0 < graphExposureProbability20 nominationGraph20 k ∧ graphExposureProbability20 nominationGraph20 k < 1 ∧
      0 < graphExposureProbability20 (peerUnion nominationGraph20) k ∧
      graphExposureProbability20 (peerUnion nominationGraph20) k < 1) :=
      AronowAudit.P037.Wave1.nomination_union_counterexamples_proof
    have d10 : directedIndegree nominationGraph10 = (![1,2,0,0,0,0,0,0,0,0] : Fin 10 → ℕ) :=
      AronowAudit.P037.Wave1.nomination_degrees10
    have d20 : directedIndegree nominationGraph20 =
        (![1,6,7,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : Fin 20 → ℕ) :=
      AronowAudit.P037.Wave1.nomination_degrees20
    obtain ⟨q10, _, _, _, q20, _, pB, pS, _⟩ := h
    refine ⟨d10, d20, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num [nominationGraph10]
    · intro i; fin_cases i <;> norm_num [nominationGraph20]
    · intro i; rw [q10, d10]; fin_cases i <;> norm_num
    · intro i; rw [q20, d20]; fin_cases i <;> norm_num
    · norm_num [seedPeerCount, nominationGraph10]
    · norm_num [referentSeedPeerCount, nominationGraph10]
    · norm_num [seedPeerCount, nominationGraph10, peerUnion, Finset.filter_singleton]
    · norm_num [referentSeedPeerCount, nominationGraph10, peerUnion, Finset.filter_singleton]
    · ext j; fin_cases j <;> norm_num [nominationGraph20]
    · ext j; fin_cases j <;> norm_num [nominationGraph20, peerUnion]
    · norm_num [Finset.card_powersetCard, Nat.choose]
    · exact AronowAudit.P037.Wave1.nomination_count_direct
    · exact AronowAudit.P037.Wave1.nomination_count_union
    · intro k; rw [pB, pS]; fin_cases k <;> norm_num

theorem Bridge.T26_correspondence : T26Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n B hdiag
    exact @AronowAudit.P037.either_direction_properties n B hdiag
  · intro n B z γ i
    exact @AronowAudit.P037.either_direction_count_identities n B z γ i
  · intro c b r q hr hq
    exact @AronowAudit.P037.exposure_rows_equal_iff c b r q hr hq
  · intro Ω inst1 p hp c b r q hr hq total
    exact @AronowAudit.P037.exposure_probability_monotone Ω inst1 p hp c b r q hr hq

theorem Bridge.T29_correspondence : T29Statement := by
  refine ⟨?_, ?_⟩
  · exact @AronowAudit.P037.Wave1.rare_probability_design_counterexample_proof 
  · exact @AronowAudit.P037.rare_exposure_frequency_counterexample

theorem Bridge.T30_correspondence : T30Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Ω inst1 P E J hJ
    exact @AronowAudit.P037.Wave1.exposure_monte_carlo_law_proof Ω inst1 (Bridge.toProject P) E J hJ
  · intro Ω inst1 P m J hJ E ε hε
    exact @AronowAudit.P037.Wave1.monte_carlo_simultaneous_bound_proof Ω inst1 (Bridge.toProject P) m J hJ E ε hε
  · intro b n t peers ht
    exact @AronowAudit.P037.Wave1.blocked_school_exposure_formula_proof b n t peers ht
  · obtain ⟨_, _, _, _, h1, h2, h3, h4, _, _⟩ := @AronowAudit.P037.blocked_school_probability_examples
    exact ⟨h1, h2, h3, h4⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro Ω inst P E J hJ draws
      dsimp only
      let count := (Finset.univ.filter (fun j => E (draws j))).card
      refine ⟨⟨count, ?_, rfl⟩, ?_, ?_⟩
      · exact le_trans (Finset.card_filter_le _ _) (by simp)
      · intro hp hsmall
        exact AronowAudit.P037.frequency_resolution J count hJ (eventProbability P E) hp hsmall
      · intro hp
        have h := AronowAudit.P037.Wave1.exposure_monte_carlo_law_proof
          (Bridge.toProject P) E J hJ
        have hz := h.2.2.2.2.2.2.1 hp draws
        simp only [hz, Nat.cast_zero, zero_div]
    · intro Ω I inst P D J hJ draws
      exact (AronowAudit.P037.Wave1.analysis_set_inclusions_proof
        (Bridge.toProject P) D J hJ draws (fun _ _ => False) (fun _ _ => False)
        (fun _ _ => False) (fun _ _ => False) (draws ⟨0,hJ⟩)).2.2.2.1
    · exact AronowAudit.P037.Wave1.rare_probability_design_counterexample_proof.2.2.1
    · have h := AronowAudit.P037.Wave1.rare_probability_design_counterexample_proof
      obtain ⟨_, _, _, _, hm, hbound, _⟩ := h
      have hzero := hm.2.1
      have hex : ∃ draws : Fin 10000 → RareSeedAssignments,
          (Finset.univ.filter (fun j => rareExposure (draws j) = 1)).card = 0 := by
        by_contra hn
        have hnone := not_exists.mp hn
        change (∑ draws : Fin 10000 → RareSeedAssignments,
          (∏ j, rareAssignmentMass (draws j)) *
          (if (Finset.univ.filter (fun j => rareExposure (draws j) = 1)).card = 0
            then (1:ℝ) else 0)) = _ at hzero
        simp only [hnone, ite_false, mul_zero, Finset.sum_const_zero] at hzero
        rw [← hzero] at hbound
        norm_num at hbound
      obtain ⟨draws, hz⟩ := hex
      refine ⟨draws, ?_⟩
      intro hall
      have hpos := hall 1
      simp only [hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hpos

theorem Bridge.T31_correspondence : T31Statement := by
  refine ⟨?_, ?_⟩
  · exact @AronowAudit.P037.Wave1.school_sampler_counterexample_proof 
  · intro Ω inst1 n p hp htotal S half y m hm
    exact @AronowAudit.P037.Wave1.school_statistic_variance_proof Ω inst1 n p hp htotal S half y m hm

theorem Bridge.T32_correspondence : T32Statement := by
  refine ⟨?_, ?_⟩
  · intro B n m hn hm
    exact @AronowAudit.P037.Wave1.school_randomization_laws_proof B n m hn hm
  · intro Ω U K inst1 inst2 inst3 p q S half total f k hp hq qtotal
    exact @AronowAudit.P037.school_local_exposure_invariance Ω U K inst1 inst2 inst3 p q S half total f k

end SAP.P037b
