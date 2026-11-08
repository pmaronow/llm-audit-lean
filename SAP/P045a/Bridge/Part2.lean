import SAP.P045a.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a.Bridge
noncomputable section

@[simp] theorem pairExposureProb_eq (A : Fin 10 → Fin 10 → Bool) (i : Fin 10)
    (d : AronowAudit.P045.Exposure) :
    AronowAudit.P045.pairExposureProb A i d = SAP.P045a.pairExposureProb A i (decode d) := by
  unfold AronowAudit.P045.pairExposureProb SAP.P045a.pairExposureProb
  simp only [exposure_pred]
  rfl

@[simp] theorem cycleOut_eq (i : Fin 10) (d : AronowAudit.P045.Exposure) :
    AronowAudit.P045.cycleOut i d = SAP.P045a.cycleOut i (decode d) := by
  cases d <;> rfl

@[simp] theorem cycleL_eq (e : Fin 10 × Fin 10) :
    AronowAudit.P045.cycleL e = SAP.P045a.cycleL e := by
  unfold AronowAudit.P045.cycleL SAP.P045a.cycleL
  simp only [cycleOut_eq, exposure_decode]
  rfl

@[simp] theorem cycleR_eq (e : Fin 10 × Fin 10) :
    AronowAudit.P045.cycleR e = SAP.P045a.cycleR e := by
  unfold AronowAudit.P045.cycleR SAP.P045a.cycleR
  simp only [exposure_pred, pairExposureProb_eq, decode]
  rfl

@[simp] theorem cancellingOut2_eq :
    AronowAudit.P045.cancellingOut2 = outcome SAP.P045a.cancellingOut2 := by
  funext i d
  cases d <;> rfl

@[simp] theorem dilated_eq (b : ℝ) (d : AronowAudit.P045.Exposure) :
    AronowAudit.P045.dilated b d = SAP.P045a.dilated b (decode d) := by
  cases d <;> rfl

@[simp] theorem pairHT_dilated (A : Fin 10 → Fin 10 → Bool) (b : ℝ)
    (d : AronowAudit.P045.Exposure) (e : Fin 10 × Fin 10) :
    AronowAudit.P045.pairHT A (fun _ => AronowAudit.P045.dilated b) d e =
      SAP.P045a.pairHT A (fun _ => SAP.P045a.dilated b) (decode d) e := by
  unfold AronowAudit.P045.pairHT SAP.P045a.pairHT
  simp only [exposure_pred, pairExposureProb_eq, dilated_eq]
  rfl

@[simp] theorem pairCellNonempty_eq (d : AronowAudit.P045.Exposure) :
    AronowAudit.P045.pairCellNonempty d = SAP.P045a.pairCellNonempty (decode d) := by
  funext e
  apply propext
  unfold AronowAudit.P045.pairCellNonempty SAP.P045a.pairCellNonempty
  simp only [exposure_pred]
  rfl

@[simp] theorem printedContrast_eq (e : Fin 10 × Fin 10) :
    AronowAudit.P045.printedContrast e = SAP.P045a.printedContrast e := by
  unfold AronowAudit.P045.printedContrast SAP.P045a.printedContrast
  simp only [pairHT_dilated, decode]
  rfl

@[simp] theorem cycleL_fun : AronowAudit.P045.cycleL = SAP.P045a.cycleL := by
  funext e
  exact cycleL_eq e

@[simp] theorem cycleR_fun : AronowAudit.P045.cycleR = SAP.P045a.cycleR := by
  funext e
  exact cycleR_eq e

@[simp] theorem printedContrast_fun :
    AronowAudit.P045.printedContrast = SAP.P045a.printedContrast := by
  funext e
  exact printedContrast_eq e

@[simp] theorem pairHT_dilated_fun (A : Fin 10 → Fin 10 → Bool) (b : ℝ)
    (d : AronowAudit.P045.Exposure) :
    AronowAudit.P045.pairHT A (fun _ => AronowAudit.P045.dilated b) d =
      SAP.P045a.pairHT A (fun _ => SAP.P045a.dilated b) (decode d) := by
  funext e
  exact pairHT_dilated A b d e

@[simp] theorem naiveTreated_fun {n : ℕ} (p : SAP.P045a.Assignment n → ℝ)
    (A : Fin n → Fin n → Bool) (y : Fin n → SAP.P045a.Exposure → ℝ) :
    AronowAudit.P045.naiveTreated p A (outcome y) = SAP.P045a.naiveTreated p A y := by
  funext z
  exact naiveTreated_eq p A y z

end
end SAP.P045a.Bridge
