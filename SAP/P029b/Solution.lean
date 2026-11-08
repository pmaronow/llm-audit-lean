import SAP.P029b.Defs
import SAP.P029b.Bridge
import SAP.P029b.WH.W1.Proofs.T14
import SAP.P029b.WH.W1.Proofs.T15
import SAP.P029b.WH.W1.Proofs.T16
import SAP.P029b.WH.W1.Proofs.T17
import SAP.P029b.WH.W1.Proofs.T18
import SAP.P029b.WH.W2.Proofs.T19
import SAP.P029b.WH.W2.Proofs.T27

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P029b MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology

namespace SAP.P029b

/-- Bias, finite error control, consistency, and the one-sided specialization. -/
theorem T14 : SAP.P029b.T14WholeStatement := SAP.P029b.WH.W1.T14_whole

/-- The constant-score law and its type-7 cutoff counterexample. -/
theorem T15 : SAP.P029b.T15WholeStatement := SAP.P029b.WH.W1.T15_whole

/-- Quantile count control, bounded mean changes, and the corrected limits. -/
theorem T16 : SAP.P029b.T16WholeStatement := SAP.P029b.WH.W1.T16_whole

/-- The corrected likelihood, its optimizer correspondence, and the interior countercheck. -/
theorem T17 : SAP.P029b.T17WholeStatement := SAP.P029b.WH.W1.T17_whole

/-- Conditional receipt identities, range, cancellation, and a misconditioning witness. -/
theorem T18 : SAP.P029b.T18WholeStatement := SAP.P029b.WH.W1.T18_whole

/-- The pointwise simulation correction and the printed equation's failure. -/
theorem T19 : SAP.P029b.T19WholeStatement := SAP.P029b.WH.W2.T19_whole

/-- The printed ordering fails, and baseline selection gives the other direction's witness. -/
theorem T20 : T20Statement := by
  exact ⟨Bridge.printed_ignorability_ordering_refuted, Bridge.baseline_selection_counterexample⟩

/-- Constant effects under overlap, and refutations of both independence implications. -/
theorem T21 : T21Statement := by
  exact ⟨@Bridge.constant_effect_population_limits_proof,
    Bridge.printed_marginal_sufficiency_refuted, Bridge.printed_conditional_sufficiency_refuted⟩

/-- The scoring convention for a supplied benchmark of five over 2500 replicates. -/
theorem T22 : T22Statement := by
  exact Bridge.homogeneous_rmse_rule

/-- An interior nested Bernoulli counterexample to the package's weighting contract. -/
theorem T23 : T23Statement := by
  exact Bridge.package_fit_counterexample

/-- The population identity, sample coefficient identity, and the gender calculations. -/
theorem T25 : T25Statement := by
  refine ⟨?_, @Bridge.sample_wald_bivariate_2sls, Bridge.gender_worked_example⟩
  intro Ω X _ _ μ _ U Z hiv
  obtain ⟨hD, hY, hCM, hLATE⟩ := Bridge.late_identity_paper_scope μ U Z hiv
  refine ⟨hD, hY, hCM, hLATE, ?_⟩
  have hC : mP μ {ω | (U ω).complier} ≠ 0 := by
    rw [← hD]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hstage⟩ := hiv
    exact hstage
  rw [hY, hD, hCM]
  field_simp [hC]

/-- Population identities and consistency under maximum sample score consistency. -/
theorem T26 : T26Statement := by
  refine ⟨@Bridge.appendix_population_identities_proof, ?_⟩
  intro Ω X _ _ _ _ _ μ _ U Z c m s h a ha haVersion hA1 hA3 _
  exact Bridge.icsw_consistency_proof μ U Z c m s h a ha haVersion hA1 hA3

/-- The complier law, the strengthened-hypothesis limit, and constant-score equivalence. -/
theorem T27 : SAP.P029b.T27WholeStatement := SAP.P029b.WH.W2.T27_whole

end SAP.P029b
