import SAP.P023.Defs
import AronowAudit.P023.P023_Audit
import AronowAudit.P023.Wave1.Gap.GLP023B1
import AronowAudit.P023.P023_Review
import AronowAudit.P023.Wave1.Gap.GP023B1b
import AronowAudit.P023.Wave1.Gap.GP023B2b
import AronowAudit.P023.Wave1.Gap.GLP023B2
import AronowAudit.P023.Wave1.ContinuityCounterexampleTailC
import AronowAudit.P023.Wave1.Gap.GLP023B3
import AronowAudit.P023.Wave1.Gap.GLP023B4c
import AronowAudit.P023.Wave1.PrintedPropositionTwoRefutedTailC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P023.Bridge
open SAP.P023

theorem linearWitness : LinearWitness := by
  exact @AronowAudit.P023.linear_counterexample

theorem degreeSevenWitness : DegreeSevenWitness := by
  exact @AronowAudit.P023.degree7_counterexample

theorem uniformIllustration : UniformIllustration := by
  exact @AronowAudit.P023.Wave1.uniform_common_target_distant_information_proof

theorem printedBinEquivalence : PrintedBinEquivalence := by
  exact @AronowAudit.P023.coarsened_ols_printed_equivalence

theorem coarsenedWeights : CoarsenedWeights := by
  exact @AronowAudit.P023.corrected_coarsened_weights

theorem conditionalMoments : ConditionalMoments := by
  exact @AronowAudit.P023.corrected_finite_conditional_moments

theorem finiteNonlocality : FiniteNonlocality := by
  intro ι _ _ J hJ k hk x d hdata hfull hboth _ _
  exact AronowAudit.P023.corrected_finite_nonlocality J hJ k hk x d hdata hfull hboth

theorem finitePolynomialWeights : FinitePolynomialWeights := by
  exact @AronowAudit.P023.corrected_finite_polynomial_weights

theorem sharedConsistency : SharedConsistency := by
  intro Ω _ P sample J k β _ _ _ _ _ hOLS hRD
  exact AronowAudit.P023.polynomial_rd_shared_consistency P sample J k β hOLS hRD

theorem sigmoidPopulation : SigmoidPopulation := by
  exact @AronowAudit.P023.Wave1.sigmoid_counterexample_proof

theorem sigmoidFit : SigmoidFit := by
  exact @AronowAudit.P023.Wave1.sigmoid_fit_criterion_proof

theorem sigmoidSampling : SigmoidSampling := by
  intro Ω _ P sample hiid k hpos hk hnk _ _ _
  exact AronowAudit.P023.Wave1.sigmoid_sample_separation_proof P sample hiid k hpos hk hnk

theorem uniformSymmetry : UniformSymmetry := by
  exact @AronowAudit.P023.Wave1.uniform_residual_symmetry_proof

theorem clusteredPopulation : ClusteredPopulation := by
  exact @AronowAudit.P023.Wave1.clustered_counterexample_proof

theorem clusteredFit : ClusteredFit := by
  exact @AronowAudit.P023.Wave1.clustered_fit_bound_proof

theorem continuityWitness : ContinuityWitness := by
  obtain ⟨hdiv, hlog, hnorm, h, degrees, hc, h0, hb, hmono, hgrow,
    hfwl, hlim, hnot, hrd, hy, hnonlip⟩ :=
    AronowAudit.P023.Wave1.continuity_only_counterexample_proof
  refine ⟨hdiv, hlog, hnorm, h, degrees, hc, h0, hb, hmono, hgrow, hfwl,
    ?_, ?_, continuousOn_const.add hc, by simp [h0], hlim, hnot, hrd, hy, hnonlip⟩
  · intro m hm
    exact (hgrow m hm).trans (hfwl (degrees m) (hm.trans (hmono.id_le m))).ge
  · intro B J₀
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hlim.eventually_ge_atTop B)
    exact ⟨degrees (max M J₀), (Nat.le_max_right M J₀).trans (hmono.id_le _),
      hM _ (Nat.le_max_left M J₀)⟩

theorem noLipschitzContinuityCounterexample : NoLipschitzContinuityCounterexample := by
  intro h degrees _ _ _ hdegrees hgrow
  exact AronowAudit.P023.Wave1.tc11_growing_bias_not_lipschitz h degrees hdegrees hgrow

theorem populationBias : PopulationBias := by
  exact @AronowAudit.P023.Wave1.corrected_population_bias_proof

theorem uniformConstants : UniformConstants := by
  exact @AronowAudit.P023.Wave1.uniform_residual_constants_proof

theorem finiteConditionalBias : FiniteConditionalBias := by
  exact @AronowAudit.P023.finite_conditional_bias

theorem correctedAsymptotics : CorrectedAsymptotics := by
  intro Ω _ P ν sample α β h c δ L σ2 hr hiid k hkpos hk0 hnk _ _ _
  exact AronowAudit.P023.Wave1.corrected_proposition2_proof
    P ν sample α β h c δ L σ2 hr hiid k hkpos hk0 hnk

theorem pairIndexedAppendix : PairIndexedAppendix := by
  exact @AronowAudit.P023.corrected_appendix_pairs

theorem coarsenedLocalization : CoarsenedLocalization := by
  exact @AronowAudit.P023.coarsened_localization

theorem polynomialLocalizationRefutation : PolynomialLocalizationRefutation := by
  intro h
  obtain ⟨hdata, hcondition, hfull, hmodel,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbounded, hnonlocal⟩ := linearWitness
  apply hnonlocal
  apply h 6 1 linearX linearD (1 / 200) (by decide) (by norm_num) (by norm_num)
    hdata hcondition hfull
  refine ⟨linearExact, ?_⟩
  intro i
  rw [← hmodel]
  exact ⟨(hbounded i).1, (hbounded i).2.1⟩

theorem propositionOne : PropositionOne := by
  exact @AronowAudit.P023.printed_coarsened_proposition1

theorem propositionTwoRefutation : ¬ PrintedPropositionTwo := by
  exact @AronowAudit.P023.Wave1.printed_proposition2_refuted.{0}

theorem uniformLaw : ProbabilityLaw uniformMargins ∧ MarginSupport uniformMargins := by
  exact AronowAudit.P023.uniform_law_normalized

end SAP.P023.Bridge
