import SAP.P001b.Defs
import SAP.P001b.Bridge
import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.Wave1.TotalProbabilityCountable
import AronowAudit.P001.Wave1.Gap.GLP0012B3
import AronowAudit.P001.Wave1.Gap.GLP0012B5
import AronowAudit.P001.Wave1.IrrationalRange
import AronowAudit.P001.Wave1.Gap.GLP0013B1
import AronowAudit.P001.Wave1.Gap.FidP001
import SAP.P001b.WH.W1.Proofs.T37
import SAP.P001b.WH.W1.Proofs.T20
import SAP.P001b.WH.W1.Proofs.T22
import SAP.P001b.WH.W1.Proofs.T26
import SAP.P001b.WH.W1.Proofs.T27
import SAP.P001b.WH.W2.Proofs.T30

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section

 theorem T20 : SAP.P001b.T20WholeStatement := SAP.P001b.WH.W1.T20_whole

 theorem T21 : T21Statement := by
  obtain ⟨_, _, hcount, hmodel, hbounds, heffect, hD1, hm1, hm0, hci⟩ :=
    AronowAudit.P001.complete_coding_not_ignorability
  have hm1' : finiteConditionalMean voterMass observedVoteShare displayedGender 1 = 55 := hm1
  have hm0' : finiteConditionalMean voterMass observedVoteShare displayedGender 0 = 30 := hm0
  have hci' : ¬ FiniteConditionalIndependence voterMass
      (fun i => (potentialVoteShare 0 i, potentialVoteShare 1 i)) displayedGender
      (fun _ => (0 : ℝ)) := by
    simpa only [Bridge.voterMass_eq, Bridge.potentialVoteShare_eq, Bridge.displayedGender_eq,
      Bridge.finiteConditionalIndependence_eq] using hci
  refine ⟨AronowAudit.P001.binaryJoint.nonneg, AronowAudit.P001.binaryJoint.total,
    (fun _ => ⟨rfl, rfl, rfl⟩), hcount, hmodel, hbounds, ?_, heffect, hD1,
    ?_, ?_, ?_, ?_, ?_, hci', hm1', hm0', ?_, ?_, by norm_num⟩
  · intro i; fin_cases i <;>
      norm_num [observedVoteShare, potentialVoteShare, electorateType, displayedGender]
  · norm_num [finiteProbability, voterMass, displayedGender, Fin.sum_univ_succ]
  · norm_num [finiteConditionalMean, finiteProbability, voterMass, displayedGender, Fin.sum_univ_succ]
  · norm_num [finiteProbability, voterMass, potentialVoteShare, electorateType,
      displayedGender, Fin.sum_univ_succ]
  · norm_num [finiteProbability, voterMass, potentialVoteShare, electorateType, Fin.sum_univ_succ]
  · norm_num [finiteProbability, voterMass, potentialVoteShare, electorateType,
      displayedGender, Fin.sum_univ_succ]
  · rw [hm1', hm0']; norm_num
  · have heffect' : ∀ i, potentialVoteShare 1 i - potentialVoteShare 0 i = 5 := heffect
    simp only [finiteMean, heffect']
    norm_num [voterMass, Fin.sum_univ_succ]

 theorem T22 : SAP.P001b.T22WholeStatement := SAP.P001b.WH.W1.T22_whole

 theorem T23 : T23Statement := by
  intro Ω _ μ _ A B hA hB
  obtain ⟨hsub, hempty, hbound, hcomp, hadd⟩ :=
    AronowAudit.P001.basic_probability_rules μ A B hA hB
  refine ⟨Iff.rfl, (fun h => (AronowAudit.P001.probability_monotonicity μ A B h).2),
    hsub, hempty, hbound, hcomp, hadd, ?_⟩
  intro hAB hne hBA
  exact hne (Set.Subset.antisymm hAB hBA)

 theorem T24 : T24Statement := by
  refine ⟨?_, ?_, by norm_num⟩
  · intro Ω _ μ _ ι _ A hA hne hdis hcover B hB
    obtain ⟨ht, hc, hbinary, hempty⟩ :=
      AronowAudit.P001.Wave1.total_probability_complete_correction μ A hA hne hdis hcover B hB
    exact ⟨ht, hc, (fun C hC => ⟨ENNReal.toReal_nonneg, hbinary C hC⟩), hempty⟩
  · intro Ω A
    refine ⟨(fun C hC => hC.1), ?_, ?_⟩
    · intro C hC D hD hne
      rcases hC.2 with rfl | rfl <;> rcases hD.2 with rfl | rfl <;>
        first | exact (hne rfl).elim | exact disjoint_compl_right | exact disjoint_compl_left
    · apply Set.eq_univ_of_forall
      intro x
      apply Set.mem_sUnion.mpr
      by_cases hx : x ∈ A
      · exact ⟨A, ⟨⟨x, hx⟩, Or.inl rfl⟩, hx⟩
      · exact ⟨Aᶜ, ⟨⟨x, hx⟩, Or.inr rfl⟩, hx⟩

 theorem T25 : T25Statement := by
  obtain ⟨hleft, hright, hne⟩ := AronowAudit.P001.integer_cdf_missing_zero_counterexample
  have hright' : (∑ k ∈ Finset.Icc (1 : ℤ) 3,
      finiteProbability zeroMass (fun _ => (0 : ℤ) = k)) = 0 := by
    simpa only [Bridge.zeroMass_eq, Bridge.finiteProbability_eq] using hright
  have hleft' : finiteProbability zeroMass (fun _ => (0 : ℝ) < 4) = 1 := hleft
  refine ⟨hleft', hright', ?_⟩
  rw [hleft', hright']
  exact hne

 theorem T26 : SAP.P001b.T26WholeStatement := SAP.P001b.WH.W1.T26_whole

 theorem T27 : SAP.P001b.T27WholeStatement := SAP.P001b.WH.W1.T27_whole

 theorem T28 : T28Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact @AronowAudit.P001.discrete_cdf_jump_sum
  · intro m w hn ht X hX
    exact AronowAudit.P001.ordered_finite_cdf_formula (Bridge.asFiniteLaw w hn ht) X hX
  · intro n w hn ht X a b hab hgap
    exact AronowAudit.P001.finite_cdf_constant_between_values (Bridge.asFiniteLaw w hn ht) X a b hab hgap
  · exact AronowAudit.P001.fair_die_cdf_examples

 theorem T29 : T29Statement := by
  obtain ⟨hints, h12, h13, h23, h0, h1⟩ := AronowAudit.P001.uniform_pdf_versions_counterexample
  refine ⟨?_, hints, h12, h13, h23, h0, h1, ?_, by norm_num [closedUniformDensity],
    by norm_num [closedUniformDensity]⟩
  · intro x
    dsimp [closedUniformDensity, openUniformDensity, modifiedUniformDensity]
    split_ifs <;> norm_num
  · intro h hh hh1
    have hn : uniformDistributionFunction (-h) = 0 := by
      simp [uniformDistributionFunction, min_eq_right (show -h ≤ 1 by linarith),
        max_eq_left (show -h ≤ 0 by linarith)]
    have hp : uniformDistributionFunction h = h := by
      simp [uniformDistributionFunction, min_eq_right hh1, max_eq_right hh.le]
    have hm : uniformDistributionFunction (1-h) = 1-h := by
      simp [uniformDistributionFunction, min_eq_right (show 1-h ≤ 1 by linarith),
        max_eq_right (show 0 ≤ 1-h by linarith)]
    have ha : uniformDistributionFunction (1+h) = 1 := by
      simp [uniformDistributionFunction, min_eq_left (show 1 ≤ 1+h by linarith)]
    rw [hn, hp, hm, ha]
    norm_num [uniformDistributionFunction, hh.ne', neg_ne_zero.mpr hh.ne']

 theorem T30 : SAP.P001b.T30WholeStatement := SAP.P001b.WH.W2.T30_whole

 theorem T31 : T31Statement := by
  obtain ⟨hclosed, hvol, hprob, hpdf, hrange, hno⟩ := Bridge.cantor_facts
  refine ⟨hclosed, hvol, hprob, measurable_subtype_coe, hpdf, hrange, ?_, hno⟩
  ext x
  by_cases hx : x ∈ fatCantorSet <;> simp [cantorDensity, hx]

 theorem T32 : T32Statement := by
  constructor
  · exact @AronowAudit.P001.continuous_rv_range_uncountable
  · obtain ⟨_, _, hprob, hpdf, _, _⟩ := Bridge.cantor_facts
    letI : IsProbabilityMeasure cantorProbability := hprob
    have h := AronowAudit.P001.Wave1.continuous_range_complete_correction
      cantorProbability (fun x : fatCantorSet => x.val) measurable_subtype_coe cantorDensity hpdf
    exact h.2.2.2

 theorem T33 : T33Statement := by
  exact @AronowAudit.P001.functions_equal_on_range

 theorem T34 : T34Statement := by
  obtain ⟨ht, he, hi⟩ := AronowAudit.P001.triangular_event_counterexample
  have hint : Integrable negativeRectangleDensity volume := by
    by_contra hn
    have hz := integral_undef hn
    change (∫ z : ℝ × ℝ, AronowAudit.P001.rectanglePDF z) = 0 at hz
    linarith
  refine ⟨?_, hint, ht, he, hi, ?_⟩
  · intro z; dsimp [negativeRectangleDensity]; split_ifs <;> norm_num
  · simpa only [Bridge.negativeRectangleDensity_eq, he, hi] using (by norm_num : (1 : ℝ) ≠ 0)

 theorem T35 : T35Statement := by
  intro ν _ f hf
  obtain ⟨hcorrect, hsplit⟩ := AronowAudit.P001.triangular_region_correction ν f hf
  refine ⟨hcorrect, hsplit, ?_⟩
  simp only [Bridge.probability_eq]
  rw [hsplit]
  exact add_eq_left

 theorem T36 : T36Statement := by
  exact AronowAudit.P001.Wave1.infinite_marginal_slice_counterexample_proof

 theorem T37 : SAP.P001b.T37WholeStatement := SAP.P001b.WH.W1.T37_whole

 theorem T38 : T38Statement := by
  obtain ⟨hmap, hnormal, hdeg⟩ := AronowAudit.P001.zero_normal_combination_counterexample
  obtain ⟨hplus, hminus, hdplus, hdminus, hzero, hi1, hi2, hne⟩ :=
    AronowAudit.P001.bivariate_normal_endpoint_counterexample
  refine ⟨⟨hmap, ?_, ?_, hnormal⟩, (fun x => zero_mul x), hplus, hminus, hdeg,
    ?_, hdplus, hdminus, hzero, hi1, hi2, hne⟩
  · rw [hmap]; simp
  · rintro ⟨f, hf⟩
    have hz := (AronowAudit.P001.continuous_rv_range_uncountable (gaussianReal 0 1)
      (fun _ : ℝ => (0 : ℝ)) measurable_const f hf).1 0
    simpa using hz
  · constructor <;> norm_num

end
end SAP.P001b
