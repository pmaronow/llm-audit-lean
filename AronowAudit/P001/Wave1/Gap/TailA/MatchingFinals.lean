import AronowAudit.P001.Wave1.Lib.TailA.MatchingEndpoints

/-! Exact held-statement matching finals and universal assurance refutations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open AronowAudit.P001.TailA

namespace AronowAudit.P001.Wave1.TailA

universe u

theorem hot_deck_bootstrap_counterexample_final :
    type_of% @AronowAudit.P001.hot_deck_bootstrap_counterexample := by
  intro Ω _ μ _ Z hiid hlaw
  exact (matching_failure_both μ Z hiid hlaw).1

example : type_of% @AronowAudit.P001.hot_deck_bootstrap_counterexample := AronowAudit.P001.Wave1.TailA.hot_deck_bootstrap_counterexample_final

theorem hot_deck_bootstrap_correction_final :
    type_of% @AronowAudit.P001.hot_deck_bootstrap_correction := by
  intro Ω _ μ _ Z hiid hlaw
  exact (matching_failure_both μ Z hiid hlaw).1

example : type_of% @AronowAudit.P001.hot_deck_bootstrap_correction := AronowAudit.P001.Wave1.TailA.hot_deck_bootstrap_correction_final

theorem matching_bootstrap_counterexample_supporting_final :
    type_of% @AronowAudit.P001.matching_bootstrap_counterexample_supporting := by
  intro Ω _ μ _ Z hiid hlaw
  exact (matching_failure_both μ Z hiid hlaw).2

example : type_of% @AronowAudit.P001.matching_bootstrap_counterexample_supporting := AronowAudit.P001.Wave1.TailA.matching_bootstrap_counterexample_supporting_final

theorem matching_bootstrap_correction_supporting_final :
    type_of% @AronowAudit.P001.matching_bootstrap_correction_supporting := by
  intro Ω _ μ _ Z hiid hlaw
  exact (matching_failure_both μ Z hiid hlaw).2

example : type_of% @AronowAudit.P001.matching_bootstrap_correction_supporting := AronowAudit.P001.Wave1.TailA.matching_bootstrap_correction_supporting_final

theorem estimated_matching_bootstrap_failure_final :
    type_of% @AronowAudit.P001.estimated_matching_bootstrap_failure := by
  intro Ω _ μ _ Z hiid hlaw
  simpa only [MatchingFailure,ite_true,estimated_matching_statistic_equal,bootVar,bootMean]
    using (matching_failure_both μ Z hiid hlaw).2

example : type_of% @AronowAudit.P001.estimated_matching_bootstrap_failure := AronowAudit.P001.Wave1.TailA.estimated_matching_bootstrap_failure_final

theorem matching_bootstrap_counterexample_final :
    type_of% @AronowAudit.P001.matching_bootstrap_counterexample :=
  estimated_matching_bootstrap_failure_final

example : type_of% @AronowAudit.P001.matching_bootstrap_counterexample := AronowAudit.P001.Wave1.TailA.matching_bootstrap_counterexample_final

theorem matching_bootstrap_correction_final :
    type_of% @AronowAudit.P001.matching_bootstrap_correction :=
  estimated_matching_bootstrap_failure_final

example : type_of% @AronowAudit.P001.matching_bootstrap_correction := AronowAudit.P001.Wave1.TailA.matching_bootstrap_correction_final

theorem printed_hot_deck_bootstrap_assurance_refutation :
    ¬ (type_of% @AronowAudit.P001.printed_hot_deck_bootstrap_assurance.{u}) := by
  intro h
  have hf := (matching_failure_both matchingCanonicalLiftedLaw.{u}
    (fun n ω => ω.down n) matching_endpoint_canonical_lifted_iid
    (matching_endpoint_canonical_lifted_law 0)).1
  exact hf.2.2.2.2.2 (h matchingCanonicalLiftedLaw.{u} (fun n ω => ω.down n)
    matching_endpoint_canonical_lifted_iid (matching_endpoint_canonical_lifted_law 0))

example : ¬ (type_of% @AronowAudit.P001.printed_hot_deck_bootstrap_assurance) := AronowAudit.P001.Wave1.TailA.printed_hot_deck_bootstrap_assurance_refutation

theorem printed_matching_bootstrap_assurance_refutation :
    ¬ (type_of% @AronowAudit.P001.printed_matching_bootstrap_assurance.{u}) := by
  intro h
  have hf := (matching_failure_both matchingCanonicalLiftedLaw.{u}
    (fun n ω => ω.down n) matching_endpoint_canonical_lifted_iid
    (matching_endpoint_canonical_lifted_law 0)).2
  exact hf.2.2.2.2.2 (h matchingCanonicalLiftedLaw.{u} (fun n ω => ω.down n)
    matching_endpoint_canonical_lifted_iid (matching_endpoint_canonical_lifted_law 0))

example : ¬ (type_of% @AronowAudit.P001.printed_matching_bootstrap_assurance) := AronowAudit.P001.Wave1.TailA.printed_matching_bootstrap_assurance_refutation

end AronowAudit.P001.Wave1.TailA
