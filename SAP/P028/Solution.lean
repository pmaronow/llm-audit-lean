import SAP.P028.Defs
import SAP.P028.Bridge
import AronowAudit.P028.P028_Results
import AronowAudit.P028.P028_MissingOutcomes
import SAP.P028.WH.W1.Proofs.T10
import SAP.P028.WH.W1.Proofs.T1
import SAP.P028.WH.W1.Proofs.T2
import SAP.P028.WH.W1.Proofs.T5
import SAP.P028.WH.W1.Proofs.T6
import SAP.P028.WH.W2.Proofs.T9

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SAP.P028 SAP.P028.Bridge

theorem SAP.P028.T1 : SAP.P028.T1WholeStatement :=
  SAP.P028.WH.W1.T1_whole

theorem SAP.P028.T2 : SAP.P028.T2WholeStatement :=
  SAP.P028.WH.W1.T2_whole

theorem SAP.P028.T4 : SAP.P028.T4Statement := by
  constructor
  · intro p e0 e1 x0 x1 hp hp1
    have hr : mixtureSystem p e0 e1 x0 x1 ↔ correctedSystem p e0 e1 x0 x1 :=
      AronowAudit.P028.corrected_reframing p e0 e1 x0 x1 hp hp1
    have ht := AronowAudit.P028.endpoint_translation p e0 e1 hp
    refine ⟨hr, ?_, AronowAudit.P028.control_substitution p e0 e1 x0 x1 hp, ?_,
      AronowAudit.P028.contribution_interval p e1 x1 hp,
      AronowAudit.P028.third_lower_identity p e1 hp,
      hr.trans (AronowAudit.P028.corrected_interval_system p e0 e1 x0 x1 hp),
      ht.1, ht.2, AronowAudit.P028.printed_contribution_interval p e1 x1 hp, ?_, ?_⟩
    · intro n h
      exact AronowAudit.P028.noncomplier_mean_from_equation p e1 x1 n hp1 h
    · intro h
      simpa only [h] using AronowAudit.P028.control_unit_interval x1 (effect p e0 e1)
    · intro he hx
      have hl := AronowAudit.P028.printed_lower_redundant p e1 x1 hp he hx
      have hi := AronowAudit.P028.printed_contribution_interval p e1 x1 hp
      exact ⟨hl, ⟨fun h => (hi.mp h).2, fun h => hi.mpr ⟨hl, h⟩⟩⟩
    · intro h
      rcases hr.mp h with ⟨he, h0, h01, h1, h11, hm, hm1⟩
      exact ⟨he, h0, h01, h1, h11, hm, by linarith⟩
  · constructor
    · norm_num [printedSystem]
    · rw [show mixtureSystem (1/2) (3/4) (3/4) 0 0 ↔
          correctedSystem (1/2) (3/4) (3/4) 0 0 from
          AronowAudit.P028.corrected_reframing _ _ _ _ _ (by norm_num) (by norm_num)]
      norm_num [correctedSystem]

theorem SAP.P028.T5 : SAP.P028.T5WholeStatement :=
  SAP.P028.WH.W1.T5_whole

theorem SAP.P028.T6 : SAP.P028.T6WholeStatement :=
  SAP.P028.WH.W1.T6_whole

theorem SAP.P028.T7 : SAP.P028.T7Statement := by
  refine ⟨AronowAudit.P028.full_compliance_counterexample, ?_, ?_, ?_,
    AronowAudit.P028.full_compliance_witness_intervals⟩
  · intro E z
    exact AronowAudit.P028.full_compliance_independent (fun a => E (fromAuditAtom a)) z
  · intro z; cases z <;> exact ⟨rfl, rfl⟩
  · norm_num [twoAtomProb, fullPotential, fd, Fintype.sum_bool]

theorem SAP.P028.T8 {Ω : Type*} [MeasurableSpace Ω] : SAP.P028.T8Statement Ω := by
  constructor
  · intro M hb
    exact ⟨(AronowAudit.P028.first_stage_population (toAudit M)).2,
      AronowAudit.P028.proposition1_valid (toAudit M) hb⟩
  · intro p e0 e1 hp he0 he1 hcompat
    have ht : lowerTreated p e0 e1-effect p e0 e1 = lowerControl p e0 e1 ∧
        upperTreated p e0 e1-effect p e0 e1 = upperControl p e0 e1 :=
      AronowAudit.P028.endpoint_translation p e0 e1 hp.1
    have hne : lowerTreated p e0 e1 ≤ upperTreated p e0 e1 :=
      (AronowAudit.P028.proposition1_interval_nonempty p e0 e1 hp he0 he1).mpr hcompat
    refine ⟨by linarith [ht.1, ht.2], hne, ?_, ?_⟩
    · intro x1 hx
      obtain ⟨M, h⟩ := AronowAudit.P028.proposition1_sharp p e0 e1 hp he0 he1 hcompat x1 hx
      exact ⟨fromAudit M, h⟩
    · intro x0 hx
      have hx1 : lowerTreated p e0 e1 ≤ x0+effect p e0 e1 ∧
          x0+effect p e0 e1 ≤ upperTreated p e0 e1 :=
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
      obtain ⟨M, hb, hpc, h0, h1, hc1, hc0⟩ :=
        AronowAudit.P028.proposition1_sharp p e0 e1 hp he0 he1 hcompat (x0+effect p e0 e1) hx1
      refine ⟨fromAudit M, hb, hpc, h0, h1, ?_, hc1⟩
      change AronowAudit.P028.complierMean M false = x0
      simpa only [AronowAudit.P028.effect, effect, add_sub_cancel_right] using hc0

theorem SAP.P028.T9 : SAP.P028.T9WholeStatement :=
  SAP.P028.WH.W2.T9_whole

theorem SAP.P028.T10 : SAP.P028.T10WholeStatement :=
  SAP.P028.WH.W1.T10_whole
