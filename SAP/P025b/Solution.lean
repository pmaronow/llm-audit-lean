import SAP.P025b.Defs
import SAP.P025b.Bridge
import AronowAudit.P025.P025_Interval
import SAP.P025b.WH.W1.Proofs.T20
import SAP.P025b.WH.W1.Proofs.T12
import SAP.P025b.WH.W1.Proofs.T14
import SAP.P025b.WH.W1.Proofs.T15
import SAP.P025b.WH.W1.Proofs.T16
import SAP.P025b.WH.W2.Proofs.T19

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem T12 : SAP.P025b.T12WholeStatement := SAP.P025b.WH.W1.T12_whole

theorem T13 : T13Statement := by
  intro N J hN hJ κ _ _ _ d cls hcls y hy α β hα hab hb1 hπ
  have h := (Bridge.convergence_eq d cls y α β).mpr
    (AronowAudit.P025.corrected_proposition_three hN hJ (Bridge.toAudit d)
      cls hcls y hy α β hα hab hb1 hπ)
  exact ⟨h, fun _ => h⟩

theorem T14 : SAP.P025b.T14WholeStatement := SAP.P025b.WH.W1.T14_whole

theorem T15 : SAP.P025b.T15WholeStatement := SAP.P025b.WH.W1.T15_whole

theorem T16 : SAP.P025b.T16WholeStatement := SAP.P025b.WH.W1.T16_whole

theorem T17 : T17Statement := by
  refine ⟨AronowAudit.P025.reported_counts_unique, AronowAudit.P025.table_six_exact,
    AronowAudit.P025.table_all_cells, AronowAudit.P025.table_grid_comparison, ?_, ?_, ?_⟩
  · intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [binaryLower, binaryUpper]
  all_goals norm_num [binaryLower, binaryUpper, Set.mem_inter_iff, Set.mem_Icc]

theorem T18 : T18Statement := by
  intro n hn y α β α' β' hα hab hb1 hα' hab' hb1' heq
  have he := (AronowAudit.P025.ratio_only_and_equal_probabilities
    hn y α β α' β' hα hab hb1 hα' hab' hb1' heq).1
  have hβ : 0 < β := hα.trans_le hab
  have hnorm := (AronowAudit.P025.ratio_only_and_equal_probabilities
    hn y α β (α/β) 1 hα hab hb1 (div_pos hα hβ)
    ((div_le_one hβ).mpr hab) le_rfl (by simp)).1
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · simpa only [AronowAudit.P025.attainable, AronowAudit.P025.weightBox,
      attainable, normAttainable, normBox, weightBox, div_one, one_div_div, ← Bridge.ratio_eq] using hnorm
  · exact congrArg sInf he
  · exact congrArg sSup he
  · intro hγ
    exact AronowAudit.P025.equal_probability_box_and_endpoints hn y α β hα hab hb1 hγ

theorem T19 : SAP.P025b.T19WholeStatement := SAP.P025b.WH.W2.T19_whole

theorem T20 : SAP.P025b.T20WholeStatement := SAP.P025b.WH.W1.T20_whole

theorem T21 : T21Statement := by
  intro N J hN hJ κ _ _ _ d cls hcls y hy α β hα hab hb1 hπ hsep
  exact (Bridge.convergence_eq d cls y α β).mpr
    (AronowAudit.P025.printed_proposition_three hN hJ (Bridge.toAudit d)
      cls hcls y hy α β hα hab hb1 hπ hsep)

end SAP.P025b
