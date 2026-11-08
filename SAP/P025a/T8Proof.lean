import SAP.P025a.Defs.Part6
import SAP.P025a.WH.W1.Proofs.T10
import AronowAudit.P025.P025_Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem SAP.P025a.T8_realizable_counterexample :
    SAP.P025a.T8RealizableCounterexample := by
  rcases SAP.P025a.WH.W1.T10_whole with ⟨hT10, _, hdesign⟩
  rcases hT10 with ⟨⟨hmono, _, _, _, hcut0, _, _, _⟩,
    ⟨hprob, htotal, _, hclass, _, _⟩, hvalue0, _, _⟩
  rcases hdesign with ⟨hincBound, hconsistent, _, hmin, _⟩
  refine ⟨by norm_num, hmono, hcut0, hvalue0, hmin, ?_, hprob, htotal,
    hincBound, hconsistent, hclass⟩
  intro hleast
  have hgap : (7 / 6 : ℝ) < lowerValue SAP.P025a.fourOutcomes
      (fun _ => 1) 2 0 := by
    rw [hvalue0]
    norm_num
  exact (not_le_of_gt hgap) (hleast.2 hmin.1)

theorem SAP.P025a.T8_not_printedClassFormulaClaim :
    ¬ SAP.P025a.printedClassFormulaClaim := by
  intro hclaim
  rcases SAP.P025a.T8_realizable_counterexample with
    ⟨_, hmono, hcut0, _, hmin, hnotleast, _, _, _, _, _⟩
  obtain ⟨kL, kH, hcutL, _, hleast, _, _, _⟩ :=
    hclaim (by norm_num : 0 < 4) SAP.P025a.fourOutcomes
      (fun _ => 1) hmono (by intro j; norm_num) (1 / 2 : ℝ) 1
      (by norm_num) (by norm_num) (by norm_num)
  have hratio : (1 : ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
  rw [hratio] at hcutL hleast
  have hk : kL = (0 : Fin 4) := by
    apply le_antisymm
    · exact hcutL.2 hcut0.1
    · exact hcut0.2 hcutL.1
  rw [hk] at hleast
  exact hnotleast hleast

theorem SAP.P025a.T8_luna_assembly : SAP.P025a.T8Statement := by
  exact ⟨SAP.P025a.T8_not_printedClassFormulaClaim,
    SAP.P025a.T8_realizable_counterexample,
    by simp [SAP.P025a.printedLowerExpression],
    @AronowAudit.P025.printed_proposition_two_upper⟩

