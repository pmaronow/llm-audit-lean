import SAP.P014.Bridge.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014.Bridge
open scoped BigOperators
noncomputable section
universe u

theorem T6_general : T6GeneralPart.{u} := by
  intro Ω mΩ N μ hμ X b S v m hb hn hv hw hm hmn hdef hl
  have h := AronowAudit.P014.corrected_local_randomization μ X b S v m
    hb hn hv hw hm hmn hdef hl
  refine ⟨⟨?_, h.2⟩, ?_⟩
  · filter_upwards [h.1] with ω hω
    change armSize S (thresholdAssignment (X ω)) true = m ∧
      windowSubjects b (X ω) = S ∧ _ at hω
    refine ⟨hω.1, ?_, ?_, hω.2.1, congrArg Finset.card hω.2.1, hω.2.2⟩
    · rw [hω.1]; exact_mod_cast hm
    · rw [hω.1]; exact_mod_cast hmn
  · intro g hout
    obtain ⟨A,hcard,hmass,hlink⟩ :=
      AronowAudit.P014.outside_function_gives_discrete_full_law μ X b S v g hv hl hout
    exact ⟨fromAudit A, fromAudit_valid A, hcard, hmass, hlink⟩

theorem T6_example : T6OutsideExample := by
  obtain ⟨hwin,hlocal,hmass,hne⟩ := AronowAudit.P014.corrected_law_allows_outside_randomness
  obtain ⟨hcard,hneg,hpos,hind⟩ := AronowAudit.P014.extended_law_support_and_outside
  refine ⟨fromAudit_valid AronowAudit.P014.extendedLaw,hwin,hlocal,?_,?_,
    by norm_num [localThree],hcard,hmass,hne,hneg,hpos,hind⟩
  · intro σ
    obtain ⟨a,rfl⟩ := AronowAudit.P014.rows_exhaust_permutations.2 σ
    change AronowAudit.P014.extendedLaw.prob (fun ω => ∀ i : Fin 3,
      AronowAudit.P014.extendedX ω (Fin.castSucc i) =
        (![-2,-1,1] : Fin 3 → ℝ) (AronowAudit.P014.rowPermutation a i)) = 1/6
    simpa only [funext_iff, AronowAudit.P014.score_rows_are_permutations.1] using hlocal a
  · rintro ⟨a,t⟩
    fin_cases a <;> cases t <;>
      norm_num [armSize, localThree, thresholdAssignment, extendedScores, scores1,
        Finset.filter_insert, Finset.filter_singleton]

theorem T6_proof : T6Statement.{u} := ⟨T6_general, T6_example⟩

theorem T7_general : T7GeneralPart.{u} := by
  intro Ω mΩ N μ hμ X S
  refine ⟨AronowAudit.P014.no_ties_diagonal_general μ X S, ?_,
    AronowAudit.P014.no_ties_quantifier_decomposition μ X S, ?_⟩
  · intro i _
    norm_num [eventProbability]
  · intro m hm hmn
    refine ⟨by omega, Finset.card_pos.mp (lt_trans hm hmn), ?_⟩
    intro h
    have he := (AronowAudit.P014.no_ties_diagonal_general μ X S).mp h
    simp [he] at hmn

theorem T7_local : T7LocalPart.{u} := by
  intro Ω mΩ N μ hμ X b S v m hb hn hv hw hm hmn hdef hl
  exact (AronowAudit.P014.corrected_local_randomization μ X b S v m
    hb hn hv hw hm hmn hdef hl).2.2

theorem T7_proof : T7Statement.{u} :=
  ⟨T7_general, T7_local, AronowAudit.P014.corrected_no_ties_witnesses⟩

theorem T10_general : T10GeneralPart := by
  intro N L hL S y hS hp
  have hpos := interior_arms L hL S hp
  refine ⟨?_, AronowAudit.P014.corrected_target_hh_sign (toAudit L hL) S y hS hp, ?_⟩
  · intro i hi a
    have hother := AronowAudit.P014.hhMean_eq_weighted (toAudit L hL) y i a (hpos i hi a)
    have hfull := AronowAudit.P014.conditional_full_average_eq_weighted
      (toAudit L hL) y i a (hpos i hi a)
    exact ⟨hother.trans hfull.symm, hfull⟩
  · intro m hm hmn hc hprop
    exact AronowAudit.P014.estimator_hh_sign (toAudit L hL) S y m hm hmn hc hprop

theorem T10_failure : T10FailurePart := by
  obtain ⟨_,hA,hM,_,_,_,_,_⟩ := AronowAudit.P014.t9_counterexample
  obtain ⟨_,hn1,hn2,_⟩ := AronowAudit.P014.t9_hudgens_halloran_comparison
  refine ⟨witness_valid,witness_positive,?_,hn1,hn2⟩
  change AronowAudit.P014.printedMean AronowAudit.P014.witnessLaw
    AronowAudit.P014.spilloverOne 0 false ≠
      AronowAudit.P014.hhMean AronowAudit.P014.witnessLaw AronowAudit.P014.spilloverOne 0 false
  rw [AronowAudit.P014.hhMean_eq_weighted AronowAudit.P014.witnessLaw
    AronowAudit.P014.spilloverOne 0 false
    (witness_positive 0 (by simp [localThree]) false), hA, hM]
  norm_num

theorem T10_proof : T10Statement := ⟨T10_general, T10_failure⟩

end
end SAP.P014.Bridge
