import SAP.P043.Defs
import SAP.P043.Bridge
import AronowAudit.P043.P043_Formalization
import AronowAudit.P043.P043_Strata
import AronowAudit.P043.Wave1.Gap.FidP043
import SAP.P043.WH.W1.Proofs.T1
import SAP.P043.WH.W1.Proofs.T4

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P043

theorem SAP.P043.T1 : SAP.P043.T1WholeStatement := SAP.P043.WH.W1.T1_whole

theorem SAP.P043.T2.{u} : T2Statement.{u} := by
  constructor
  · intro Ω inst μ probability p hp m hint
    exact Bridge.mediationRepair μ p hp m hint
  · obtain ⟨_, _, hτ, hM, hD, _⟩ := Bridge.mediationWitnesses
    refine ⟨hτ, hM, hD, ?_⟩
    rw [hM]
    norm_num

theorem SAP.P043.T4 : SAP.P043.T4WholeStatement := SAP.P043.WH.W1.T4_whole

theorem SAP.P043.T5.{u} : T5Statement.{u} := by
  intro Ω inst P p hp m J hb hm hfirst
  exact Bridge.ivRepair P p hp m J hb hm hfirst

theorem SAP.P043.T6 : T6Statement := by
  exact Bridge.correctedStrata
