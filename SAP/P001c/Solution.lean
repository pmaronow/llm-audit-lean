import SAP.P001c.WH.W1.Proofs.T57
import SAP.P001c.WH.W1.Proofs.T49
import SAP.P001c.WH.W1.Proofs.T51
import SAP.P001c.WH.W1.Proofs.T53
import SAP.P001c.WH.W1.Proofs.T54
import SAP.P001c.WH.W2.Proofs.T55
import SAP.P001c.WH.W2.Proofs.T39
import SAP.P001c.WH.W2.Proofs.T43
import SAP.P001c.WH.W2.Proofs.T46
import SAP.P001c.WH.W2.Proofs.T47
import SAP.P001c.Defs
import SAP.P001c.Bridge
import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.Wave1.Gap.GLP0013B2
import AronowAudit.P001.Wave1.Gap.GLP0013B3
import AronowAudit.P001.Wave1.QuadraticUniqueBlp
import AronowAudit.P001.Wave1.FinitePopulationPlugin
import AronowAudit.P001.Wave1.Gap.RepairT55
import AronowAudit.P001.Wave1.Gap.TailA.CDFDelta
import AronowAudit.P001.Wave1.Gap.DecisionT47

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001c

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001 AronowAudit.P001.Wave1
open scoped BigOperators ENNReal NNReal Topology Classical

theorem T39 : SAP.P001c.T39WholeStatement := SAP.P001c.WH.W2.T39_whole

theorem T40 {Ω : Type*} [mΩ : MeasurableSpace Ω] : T40Statement Ω := by
  obtain ⟨hc, hl, hr, hh⟩ := coin_mse_scale_correction
  refine ⟨?_, hc, hl, hr, hh, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ _ X h2
    exact mse_general_identity_and_unique_minimum μ X h2
  · norm_num [finiteMean, signWeights, Fin.sum_univ_succ]
  · norm_num [finiteVariance, finiteMean, signWeights, Fin.sum_univ_succ]
  · intro c
    simp [fairCoinLoss, finiteMean, signWeights, Fin.sum_univ_succ]; ring
  · intro c
    rw [Bridge.fairCoinLoss_eq]
    nlinarith [(hc c).1]
  all_goals norm_num [fairCoinLoss]

theorem T41 : T41Statement := by
  obtain ⟨hvX, hvY, hvZ, hcY, hcZ, -, -⟩ := correlation_not_pointwise_dependence
  obtain ⟨hrY, hrZ, hpX, hpY, hpZ, hAY, hAZ, hnY, hnZ⟩ :=
    finite_correlation_counterexample_full
  refine ⟨?_, ?_, ?_, hvX, hvY, hvZ, hcY, hcZ, hrY, hrZ, hpX, hpY, hpZ,
    hAY, hAZ, hnY, hnZ⟩
  all_goals norm_num [finiteMean, nullWeights, Fin.sum_univ_succ]

theorem T42 {Ω : Type*} [mΩ : MeasurableSpace Ω] : T42Statement Ω := by
  intro μ _ X Y hX hY hvX hvY
  simpa only [Bridge.correlationCoefficient_eq] using
    correlation_linear_dependence_ae μ X Y hX hY hvX hvY

theorem T43 : SAP.P001c.T43WholeStatement := SAP.P001c.WH.W2.T43_whole

theorem T44 : T44Statement := by
  obtain ⟨hv, hc, hc', hM, hne⟩ := covariance_does_not_fix_intercept
  exact ⟨hv, hc, hc', hM, hne, by simp [finiteMean]⟩

theorem T45 {Ω : Type*} [mΩ : MeasurableSpace Ω] : T45Statement Ω := by
  intro μ _ X Y hX hY hv
  exact ⟨fun a b => blp_two_equation_characterization μ X Y hX hY hv a b,
    (blp_corrected_derivatives_and_minimum μ X Y hX hY hv).2.2⟩

theorem T46 : SAP.P001c.T46WholeStatement := SAP.P001c.WH.W2.T46_whole

theorem T47 : SAP.P001c.T47WholeStatement := SAP.P001c.WH.W2.T47_whole

theorem T48 {Ω : Type*} [mΩ : MeasurableSpace Ω] : T48Statement Ω := by
  intro μ _ K X h2
  have hmatrix := covariance_matrix_symmetry_and_diagonal μ X h2
  refine ⟨fun _ _ => rfl, hmatrix.1, hmatrix.2, ?_⟩
  exact (multivariate_variance_rule μ (fun k ω => X ω k) h2).2.2

theorem T49 : SAP.P001c.T49WholeStatement := SAP.P001c.WH.W1.T49_whole

theorem T50 {Ω : Type*} [mΩ : MeasurableSpace Ω] : T50Statement Ω := by
  obtain ⟨hgeneral, h3, h4, h10, hm, hv⟩ := finite_population_example_moments
  refine ⟨hgeneral, ?_, h3, h4, h10, hm, hv, ?_, ?_⟩
  · ext t
    simp [or_assoc, or_comm]
  · intro μ _ Z hZ2
    have h := variance_functional_minus_sign μ Z hZ2
    exact ⟨h, by
      change mean μ (fun ω => (Z ω)^2)+(mean μ Z)^2-var μ Z=2*(mean μ Z)^2
      linarith⟩
  · intro x n hn
    exact empirical_variance_identity x n hn

theorem T51 : SAP.P001c.T51WholeStatement := SAP.P001c.WH.W1.T51_whole

theorem T52 {Ω : Type*} [mΩ : MeasurableSpace Ω] : T52Statement Ω := by
  intro μ _
  exact ⟨fun X hX D hD => indicator_expectation μ X hX D hD,
    fun X hiid x => empirical_cdf_consistency μ X hiid x⟩

theorem T53 : SAP.P001c.T53WholeStatement := SAP.P001c.WH.W1.T53_whole

theorem T54 : SAP.P001c.T54WholeStatement := SAP.P001c.WH.W1.T54_whole

theorem T55 : SAP.P001c.T55WholeStatement := SAP.P001c.WH.W2.T55_whole

theorem T56 {Ω : Type*} [mΩ : MeasurableSpace Ω] : T56Statement Ω := by
  intro μ _ X hiid hlaw
  have hc := constant_plugin_degenerate μ
  have hq := quadratic_plugin_degenerate_counterexample_proof μ X hiid hlaw
  exact ⟨constant_functional_hadamard cdfSet Set.univ (embedCDF (cdfAt μ (X 0))),
    constant_cdf_functional_hadamard (cdfAt μ (X 0)), hc.1, hc.2,
    hq.1, hq.2.1, hq.2.2.1, hq.2.2.2⟩

theorem T57 : SAP.P001c.T57WholeStatement := SAP.P001c.WH.W1.T57_whole

end SAP.P001c
