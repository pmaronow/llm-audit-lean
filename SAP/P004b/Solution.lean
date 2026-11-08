import SAP.P004b.Defs
import SAP.P004b.Bridge
import AronowAudit.P004.Wave1.Gap.GP0041B1
import AronowAudit.P004.Wave1.Gap.GLP0041B2
import AronowAudit.P004.Wave1.Gap.GP0041B2
import AronowAudit.P004.Wave1.Gap.GP0041B3
import AronowAudit.P004.P004_DependencyCompletion
import AronowAudit.P004.P004_VarianceCompletion
import AronowAudit.P004.P004_RegressionCompletion
import AronowAudit.P004.Wave1.Gap.GP0042B1
import AronowAudit.P004.Wave1.Gap.GLP0042B2
import AronowAudit.P004.Wave1.Gap.TailBNedHac
import AronowAudit.P004.P004_HACCompletion
import AronowAudit.P004.P004_ConditioningCompletion
import SAP.P004b.WH.W1.Proofs.T22
import SAP.P004b.WH.W1.Proofs.T23
import SAP.P004b.WH.W1.Proofs.T24
import SAP.P004b.WH.W1.Proofs.T25
import SAP.P004b.WH.W1.Proofs.T26
import SAP.P004b.WH.W2.Proofs.T16
import SAP.P004b.WH.W2.Proofs.T18
import SAP.P004b.WH.W2.Proofs.T19
import SAP.P004b.WH.W2.Proofs.T20
import SAP.P004b.WH.W2.Proofs.T21
import SAP.P004b.WH.W3.Proofs.T27
import SAP.P004b.WH.W3.Proofs.T28
import SAP.P004b.WH.W3.Proofs.T30

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology

namespace SAP.P004b
universe u
noncomputable section

theorem T16 : SAP.P004b.T16WholeStatement := SAP.P004b.WH.W2.T16_whole

theorem T17 : T17Statement.{u} := by
  refine ⟨?_, AronowAudit.P004.Wave1.no_polygon_cutoff_from_range_alone_proof, ?_,
    AronowAudit.P004.Wave1.polygon_spacing_counterexample_proof, Bridge.thin_count⟩
  · intro N A _ _ P hc d db D hd hb hD hband hWD hrange hdiam
    have hcut : ∀ i j, i ≠ j → sharesSource (circleAverage P d) i j →
        nodeSeparation P i j ≤ 2*db+2*d+D :=
      AronowAudit.P004.Wave1.diameter_interference_cutoff_proof
        (Bridge.population P) hc d db D hd hb hD hband hWD hrange hdiam
    refine ⟨hcut, ?_⟩
    intro i j hsep hshare
    by_cases hij : i = j
    · subst j
      have hs : nodeSeparation P i i = 0 :=
        AronowAudit.P004.CLTCompletion.nodeSeparation_self (Bridge.population P) i
      rw [hs] at hsep
      linarith
    · exact (not_lt_of_ge (hcut i j hij hshare)) hsep
  · intro N P a D r ha hD hr hpoly hdis harea hdiam
    exact AronowAudit.P004.Wave1.polygon_count_bound_proof
      (Bridge.population P) a D r ha hD hr hpoly hdis harea hdiam

theorem T18 : SAP.P004b.T18WholeStatement := SAP.P004b.WH.W2.T18_whole

theorem T19 : SAP.P004b.T19WholeStatement := SAP.P004b.WH.W2.T19_whole

theorem T20 : SAP.P004b.T20WholeStatement := SAP.P004b.WH.W2.T20_whole

theorem T21 : SAP.P004b.T21WholeStatement := SAP.P004b.WH.W2.T21_whole

theorem T22 : SAP.P004b.T22WholeStatement := SAP.P004b.WH.W1.T22_whole

theorem T23 : SAP.P004b.T23WholeStatement := SAP.P004b.WH.W1.T23_whole

theorem T24 : SAP.P004b.T24WholeStatement := SAP.P004b.WH.W1.T24_whole

theorem T25 : SAP.P004b.T25WholeStatement := SAP.P004b.WH.W1.T25_whole

theorem T26 : SAP.P004b.T26WholeStatement := SAP.P004b.WH.W1.T26_whole

theorem T27 : SAP.P004b.T27WholeStatement := SAP.P004b.WH.W3.T27_whole

theorem T28 : SAP.P004b.T28WholeStatement := SAP.P004b.WH.W3.T28_whole

theorem T29 : T29Statement.{u} := by
  refine ⟨?_, ?_, @AronowAudit.P004.epsilon_product_difference, @AronowAudit.P004.ned_epsilon_means⟩
  · intro Space _ _ P p d K ψ bw hp hb hmetric hspacing hK hψ hanti hNED hWD hband
    exact (AronowAudit.P004.Wave1.ned_far_covariance_under_uniform_spacing
      (Bridge.sequence P) p d K ψ bw hp hb hmetric hspacing hK hψ hanti hNED
      (Eventually.of_forall hWD) (Eventually.of_forall hband)).2
  · intro N R D K b p z hb hK hD hdiag hpos h1 h0
    exact (AronowAudit.P004.hac_expansion R D K b p z hb hK hD hdiag hpos h1 h0).1

theorem T30 : SAP.P004b.T30WholeStatement := SAP.P004b.WH.W3.T30_whole

end
end SAP.P004b
