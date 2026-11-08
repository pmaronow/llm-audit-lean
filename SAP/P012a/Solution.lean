import SAP.P012a.Defs
import SAP.P012a.Bridge
import AronowAudit.P012.P012_Identification
import SAP.P012a.WH.W1.Proofs.T7
import SAP.P012a.WH.W1.Proofs.T9
import SAP.P012a.WH.W1.Proofs.T10
import SAP.P012a.WH.W1.Proofs.T11
import SAP.P012a.WH.W1.Proofs.T1
import SAP.P012a.WH.W2.Proofs.T2
import SAP.P012a.WH.W2.Proofs.T3
import SAP.P012a.WH.W2.Proofs.T6

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P012a
open scoped Classical

namespace SAP.P012a

-- This only rewrites the exported additive formula as the displayed quotient.
private theorem lower_quotient (D : Data)
    (hreg : 0 < totalSpare D ∨ (0 < 2*a D + cR D ∧ 0 < 2*b D + cR D)) :
    hLower D = lowerQuotient D := by
  have hx : (0 : ℝ) < 2*(a D : ℝ) + ((cR D : ℝ) + totalSpare D) := by
    exact_mod_cast (show 0 < 2*a D + (cR D + totalSpare D) by omega)
  have hy : (0 : ℝ) < 2*(b D : ℝ) + ((cR D : ℝ) + totalSpare D) := by
    exact_mod_cast (show 0 < 2*b D + (cR D + totalSpare D) by omega)
  simpa only [hLower, lowerQuotient, add_assoc] using
    Bridge.phi_formula (a D) (b D) (cR D + totalSpare D) (ne_of_gt hx) (ne_of_gt hy)

private theorem pvalue_of_some (D : Data) (H : State) (r : ℝ)
    (h : preferential D H = some r) : pValue D H = r := by
  unfold preferential at h
  split at h
  · exact Option.some.inj h
  · contradiction

end SAP.P012a

theorem SAP.P012a.T1 : SAP.P012a.T1WholeStatement :=
  SAP.P012a.WH.W1.T1_whole

theorem SAP.P012a.T2 : SAP.P012a.T2WholeStatement :=
  SAP.P012a.WH.W2.T2_whole

theorem SAP.P012a.T3 : SAP.P012a.T3WholeStatement :=
  SAP.P012a.WH.W2.T3_whole

theorem SAP.P012a.T4 : T4Statement := by
  exact ⟨Bridge.corrected_table_bound, Bridge.table_degree_converse⟩

theorem SAP.P012a.T5 : T5Statement := by
  constructor
  · intro D hD hreg
    obtain ⟨hmin, hc, hv⟩ := Bridge.exact_h_lower D hD hreg
    refine ⟨hmin, hc, hv, SAP.P012a.lower_quotient D hreg, ?_⟩
    intro H hH hdef
    apply hmin.2
    exact ⟨H, hH, by simp [homophily, hdef]⟩
  · intro D hD hn hM hd
    obtain ⟨hc, hs, hcounts, hdef, heq, hreal, hint, hsex, hcrack, hhome⟩ :=
      Bridge.table_counterexample D hD hn hM hd
    exact ⟨hs, hcounts, heq ▸ hreal, heq ▸ hint⟩

theorem SAP.P012a.T6 : SAP.P012a.T6WholeStatement :=
  SAP.P012a.WH.W2.T6_whole

theorem SAP.P012a.T7 : SAP.P012a.T7WholeStatement :=
  SAP.P012a.WH.W1.T7_whole

theorem SAP.P012a.T8 : T8Statement := by
  exact ⟨Bridge.result1_proof_counterexample, by decide⟩

theorem SAP.P012a.T9 : SAP.P012a.T9WholeStatement :=
  SAP.P012a.WH.W1.T9_whole

theorem SAP.P012a.T10 : SAP.P012a.T10WholeStatement :=
  SAP.P012a.WH.W1.T10_whole

theorem SAP.P012a.T11 : SAP.P012a.T11WholeStatement :=
  SAP.P012a.WH.W1.T11_whole

theorem SAP.P012a.T12 : T12Statement := by
  have h := Bridge.a2_counterexample
  obtain ⟨hD, hH, hK, hd, hp, hu, hS2, hS3, hv1, hv2, hdiff, hne1, hne2⟩ := h
  have hN : (nonseeds a2Data).card = 2 := by decide
  refine ⟨Bridge.a2_counterexample, SAP.P012a.pvalue_of_some _ _ _ hv1,
    SAP.P012a.pvalue_of_some _ _ _ hv2, hN, ?_, ?_⟩
  · rw [hS2, hN]
    norm_num [s, u]
  · rw [hS3, hN]
    norm_num [s, u]
