import SAP.P011c.Defs
import SAP.P011c.Bridge
import AronowAudit.P011.P011_Audit
import AronowAudit.P011.P011_Review
import AronowAudit.P011.P011_CorollariesCompletion
import AronowAudit.P011.P011_ProbabilityCompletion
import AronowAudit.P011.P011_HomoskedasticCompletion
import AronowAudit.P011.P011_CoverageCompletion
import AronowAudit.P011.Wave1.PropositionOne
import AronowAudit.P011.Wave1.CorollaryOne
import AronowAudit.P011.Wave1.CorollaryThree
import AronowAudit.P011.Wave1.PackageOLS
import SAP.P011c.WH.W1.Proofs.T38
import SAP.P011c.WH.W1.Proofs.T39
import SAP.P011c.WH.W1.Proofs.T40
import SAP.P011c.WH.W1.Proofs.T41
import SAP.P011c.WH.W1.Proofs.T34
import SAP.P011c.WH.W2.Proofs.T35
import SAP.P011c.WH.W2.Proofs.T36
import SAP.P011c.WH.W2.Proofs.T37

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

theorem T29 : T29Statement := by
  constructor
  · intro n p hn m D b hrank hmean
    exact AronowAudit.P011.ols_linear_unbiased hn (Bridge.toModel m) D b hrank hmean
  · intro n hn m hL2
    exact AronowAudit.P011.linear_variance_identity hn (Bridge.toModel m) hL2

theorem T30 : T30Statement := by
  intro n hn forced d x S
  have hf (T : Finset (Edge n)) := Bridge.incidenceFeasible_iff forced d T
  have hpos : 0 < (n : ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr hn)
  have ho (T : Finset (Edge n)) :
      edgeProgramVariance x T ≤ edgeProgramVariance x S ↔
        edgeProfit x T ≤ edgeProfit x S := by
    unfold edgeProgramVariance
    rw [div_le_div_iff_of_pos_right hpos]
    constructor <;> intro h <;> linarith
  constructor
  · rintro ⟨hS, hm⟩
    exact ⟨(hf S).mpr hS, fun T hT => (ho T).mp (hm T ((hf T).mp hT))⟩
  · rintro ⟨hS, hm⟩
    exact ⟨(hf S).mp hS, fun T hT => (ho T).mpr (hm T ((hf T).mpr hT))⟩

theorem T31 : T31Statement := by
  intro h
  apply AronowAudit.P011.Wave1.printed_proposition_one_refuted
  intro F c1 c2 c3 c4 hs
  exact h (Bridge.fromFamily F) c1 c2 c3 c4 hs

theorem T32 : T32Statement := by
  intro h
  apply AronowAudit.P011.Wave1.printed_corollary_one_refuted
  intro F c1 c2 c3 c4 hs hv A hm
  exact h (Bridge.fromFamily F) c1 c2 c3 c4 hs hv A hm

theorem T33 : T33Statement := by
  intro h
  apply AronowAudit.P011.Wave1.printed_corollary_three_refuted
  intro F c1 c2 c3 c4 hs hv A hm
  exact h (Bridge.fromFamily F) c1 c2 c3 c4 hs hv A hm

theorem T34 : SAP.P011c.T34WholeStatement := SAP.P011c.WH.W1.T34_whole

theorem T35 : SAP.P011c.T35WholeStatement := SAP.P011c.WH.W2.T35_whole

theorem T36 : SAP.P011c.T36WholeStatement := SAP.P011c.WH.W2.T36_whole

theorem T37 : SAP.P011c.T37WholeStatement := SAP.P011c.WH.W2.T37_whole

theorem T38 : SAP.P011c.T38WholeStatement := SAP.P011c.WH.W1.T38_whole

theorem T39 : SAP.P011c.T39WholeStatement := SAP.P011c.WH.W1.T39_whole

theorem T40 : SAP.P011c.T40WholeStatement := SAP.P011c.WH.W1.T40_whole

theorem T41 : SAP.P011c.T41WholeStatement := SAP.P011c.WH.W1.T41_whole

end
end SAP.P011c
