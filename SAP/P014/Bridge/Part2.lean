import SAP.P014.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014.Bridge
open scoped BigOperators
noncomputable section
universe u

theorem T2_proof : T2Statement := by
  intro N L hL S y m hm hmn hc hp
  obtain ⟨hf, hpos⟩ := fixed_propensity_arms L hL S m hm hmn hp
  have main := AronowAudit.P014.weighted_unbiasedness (toAudit L hL) S y m hm hmn hc hp
  change expectation L (differenceOfMeans S y) = windowContrast S (conditionalAverage L y) ∧
    windowContrast S (conditionalAverage L y) = _ at main
  have moment (i : Fin N) (hi : i ∈ S) (a : Bool) :
      armMoment L y i a = armProbability L i a * conditionalAverage L y i a :=
    AronowAudit.P014.moment_identity (toAudit L hL) y i a (hpos i hi a).ne'
  refine ⟨hpos, ?_, hf, ?_, ?_, ?_, ?_, ?_, main⟩
  · intro i _ a
    exact AronowAudit.P014.armMass_as_prob (toAudit L hL) i a
  · intro z hz
    have he := AronowAudit.P014.armCounts_add S z
    change armSize S z true + armSize S z false = S.card at he
    have hfalse : armSize S z false = (S.card : ℝ) - m := by rw [hc z hz] at he; linarith
    refine ⟨hfalse, ?_⟩
    unfold differenceOfMeans
    rw [hc z hz, hfalse]
  · intro i hi a
    refine ⟨?_, moment i hi a⟩
    simp only [expectation, armMoment, armAssignments, Finset.sum_filter, mul_ite, mul_zero]
  · intro i hi
    exact ⟨(moment i hi true).trans (by rw [hp i hi]),
      (moment i hi false).trans (by rw [hf i hi])⟩
  · exact AronowAudit.P014.expectation_fixed_counts (toAudit L hL) S y m hc
  · rw [main.1]
    have hn : (0 : ℝ) < S.card := by exact_mod_cast lt_trans hm hmn
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hmn' : (m : ℝ) < S.card := by exact_mod_cast hmn
    unfold windowContrast
    rw [Finset.sum_sub_distrib]
    field_simp [hn.ne', hm'.ne', (sub_pos.mpr hmn').ne']

theorem T3_conditional : T3ConditionalPart := by
  intro N L hL S y m hm hmn hc hp hU
  have hpos := (fixed_propensity_arms L hL S m hm hmn hp).2
  refine ⟨?_, ?_, ?_⟩
  · intro i hi a
    exact ⟨AronowAudit.P014.arm_nonempty_of_mass_ne_zero (toAudit L hL) i a (hpos i hi a).ne',
      AronowAudit.P014.means_equal_of_conditional_uniform (toAudit L hL) S hU y i hi a⟩
  · exact AronowAudit.P014.printed_unbiasedness_under_U (toAudit L hL) S y m hm hmn hc hp hU
  · exact AronowAudit.P014.bracketed_contrast S (supportAverage L y)
      (Finset.card_pos.mp (lt_trans hm hmn))

theorem T3_uniform : T3UniformPart := by
  intro N L hL S hfull
  exact AronowAudit.P014.conditional_uniform_of_full_uniform (toAudit L hL) S hfull

theorem T3_fixed_outside : T3FixedOutsidePart.{u} := by
  intro Ω mΩ N μ hμ X b S v A hA c y m hb hv hw hm hmn hdef hl hlink hout
  exact AronowAudit.P014.fixed_outside_uniform_assignments μ X b S v (toAudit A hA)
    c y m hb hv hw hm hmn hdef hl hlink hout

theorem T3_noninterference : T3NoninterferencePart := by
  intro N L hL S y m hm hmn hc hp hno
  have hpos := (fixed_propensity_arms L hL S m hm hmn hp).2
  refine ⟨?_, AronowAudit.P014.printed_unbiasedness_no_interference
    (toAudit L hL) S y m hm hmn hc hp hno⟩
  intro i hi a z hz
  apply AronowAudit.P014.constant_arm_means (toAudit L hL) y i a (y i z) (hpos i hi a).ne'
  intro z' hz'
  exact hno i hi z' z ((Finset.mem_filter.mp hz').2.trans hz.symm)

theorem T3_necessity : T3NecessityPart := by
  intro N L hL i a _ hall
  exact AronowAudit.P014.conditional_uniform_necessary (toAudit L hL) i a hall

theorem T3_proof : T3Statement.{u} :=
  ⟨T3_conditional, T3_uniform, T3_fixed_outside, T3_noninterference, T3_necessity⟩

theorem T8_proof : T8Statement := by
  intro N S f hS
  exact AronowAudit.P014.bracketed_contrast S f hS

end
end SAP.P014.Bridge
