import SAP.P005b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005b.Bridge

theorem standardized_eq {n d : ℕ} (P : SAP.P005b.Population n d)  :
    SAP.P005b.standardized P  = AronowAudit.P005.standardized (toProject P)  := rfl

theorem gram_eq {n d : ℕ} (P : SAP.P005b.Population n d)  :
    SAP.P005b.gram P  = AronowAudit.P005.gram (toProject P)  := rfl

theorem xMean_eq {n d : ℕ} (P : SAP.P005b.Population n d) (S : Finset (Fin n)) :
    SAP.P005b.xMean P S = AronowAudit.P005.xMean (toProject P) S := rfl

theorem leverage_eq {n d : ℕ} (P : SAP.P005b.Population n d) (i : Fin n) :
    SAP.P005b.leverage P i = AronowAudit.P005.leverage (toProject P) i := rfl

theorem kappa_eq {n d : ℕ} (P : SAP.P005b.Population n d)  :
    SAP.P005b.kappa P  = AronowAudit.P005.kappa (toProject P)  := rfl

theorem ate_eq {n d : ℕ} (P : SAP.P005b.Population n d)  :
    SAP.P005b.ate P  = AronowAudit.P005.ate (toProject P)  := rfl

theorem N_eq {n d : ℕ} (P : SAP.P005b.Population n d) (m : ℕ) :
    SAP.P005b.N P m = AronowAudit.P005.N (toProject P) m := rfl

theorem Lhat_eq {n d : ℕ} (P : SAP.P005b.Population n d) (m : ℕ) (S : Finset (Fin n)) :
    SAP.P005b.Lhat P m S = AronowAudit.P005.Lhat (toProject P) m S := rfl

theorem Nhat_eq {n d : ℕ} (P : SAP.P005b.Population n d) (m : ℕ) (S : Finset (Fin n)) :
    SAP.P005b.Nhat P m S = AronowAudit.P005.Nhat (toProject P) m S := rfl

theorem noninteractedRegular_eq {n d : ℕ} (P : SAP.P005b.Population n d) (m : ℕ) :
    SAP.P005b.noninteractedRegular P m = AronowAudit.P005.noninteractedRegular (toProject P) m := rfl

theorem interactedRegular_eq {n d : ℕ} (P : SAP.P005b.Population n d) (m : ℕ) :
    SAP.P005b.interactedRegular P m = AronowAudit.P005.interactedRegular (toProject P) m := rfl

theorem adjustedATE_eq {n d : ℕ} (P : SAP.P005b.Population n d) (m : ℕ) (S : Finset (Fin n)) :
    SAP.P005b.adjustedATE P m S = AronowAudit.P005.adjustedATE (toProject P) m S := rfl

theorem interactedATE_eq {n d : ℕ} (P : SAP.P005b.Population n d) (S : Finset (Fin n)) :
    SAP.P005b.interactedATE P S = AronowAudit.P005.interactedATE (toProject P) S := rfl

theorem biasEstimate_eq {n d : ℕ} (P : SAP.P005b.Population n d) (m : ℕ) (S : Finset (Fin n)) :
    SAP.P005b.biasEstimate P m S = AronowAudit.P005.biasEstimate (toProject P) m S := rfl

theorem debiasedATE_eq {n d : ℕ} (P : SAP.P005b.Population n d) (m : ℕ) (S : Finset (Fin n)) :
    SAP.P005b.debiasedATE P m S = AronowAudit.P005.debiasedATE (toProject P) m S := rfl

theorem interactedBiasEstimate_eq {n d : ℕ} (P : SAP.P005b.Population n d) (m : ℕ) (S : Finset (Fin n)) :
    SAP.P005b.interactedBiasEstimate P m S = AronowAudit.P005.interactedBiasEstimate (toProject P) m S := rfl

theorem interactedDebiasedATE_eq {n d : ℕ} (P : SAP.P005b.Population n d) (m : ℕ) (S : Finset (Fin n)) :
    SAP.P005b.interactedDebiasedATE P m S = AronowAudit.P005.interactedDebiasedATE (toProject P) m S := rfl

theorem commonLeading_eq {n d : ℕ} (P : SAP.P005b.Population n d) (m : ℕ) (S : Finset (Fin n)) :
    SAP.P005b.commonLeading P m S = AronowAudit.P005.commonLeading (toProject P) m S := rfl

theorem armLeading_eq {n d : ℕ} (P : SAP.P005b.Population n d) (S : Finset (Fin n)) :
    SAP.P005b.armLeading P S = AronowAudit.P005.armLeading (toProject P) S := rfl

theorem standingAssumptions_eq (d m : ℕ → ℕ) (P : (n : ℕ) → SAP.P005b.Population n (d n)) :
    SAP.P005b.standingAssumptions d m P =
      AronowAudit.P005.standingAssumptions d m (fun n => toProject (P n)) := rfl

end SAP.P005b.Bridge
