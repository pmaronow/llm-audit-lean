import SAP.P044.Bridge.Part2
import AronowAudit.P044.Wave1.Gap.GP044B1
import AronowAudit.P044.Wave1.Gap.GP044B2
import AronowAudit.P044.Wave1.Gap.GP044B3
import AronowAudit.P044.Wave1.Gap.GP044B4
import AronowAudit.P044.Wave1.Checks.Fid2P044Contracts
import AronowAudit.P044.P044_IndependentBank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044.Bridge

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

@[simp] theorem cliqueF_eq : AronowAudit.P044.cliqueF =
    fun r i => labels (SAP.P044.cliqueF r i) := by
  funext r i
  dsimp only [AronowAudit.P044.cliqueF, SAP.P044.cliqueF]
  simp only [cliquePairs_eq]
  by_cases h : i = (SAP.P044.cliquePairs r).1 ∨ i = (SAP.P044.cliquePairs r).2 <;>
    by_cases h2 : (SAP.P044.cliquePairs r).1.val / 4 = (SAP.P044.cliquePairs r).2.val / 4 <;>
    by_cases h3 : i.val / 4 = (SAP.P044.cliquePairs r).1.val / 4 ∨
      i.val / 4 = (SAP.P044.cliquePairs r).2.val / 4 <;>
      simp only [h, h2, h3, ↓reduceIte] <;> (try split_ifs) <;> rfl

@[simp] theorem cliqueY_eq : AronowAudit.P044.cliqueY =
    fun i a => SAP.P044.cliqueY i (labels.symm a) := rfl

@[simp] theorem retainedF_eq (t : Fin 66) : AronowAudit.P044.retainedF t =
    fun r i => labels (SAP.P044.retainedF t r i) := by
  change (fun r => AronowAudit.P044.cliqueF (t.succAbove r)) = _
  rw [cliqueF_eq]
  rfl

@[simp] theorem cliqueFullCount_eq (a : AronowAudit.P044.Exposure) :
    AronowAudit.P044.cliqueFullCount a = SAP.P044.cliqueFullCount (labels.symm a) := by
  cases a <;> rfl

@[simp] theorem cliqueFullJoint_eq (i j : Fin 12) (a b : AronowAudit.P044.Exposure) :
    AronowAudit.P044.cliqueFullJoint i j a b =
      SAP.P044.cliqueFullJoint i j (labels.symm a) (labels.symm b) := by
  cases a <;> cases b <;>
    simp [AronowAudit.P044.cliqueFullJoint, SAP.P044.cliqueFullJoint]

@[simp] theorem cliqueWeights_eq (t : Fin 66) : AronowAudit.P044.cliqueWeights t =
    fun i a => SAP.P044.cliqueWeights t i (labels.symm a) := by
  funext i a
  simp only [AronowAudit.P044.cliqueWeights, SAP.P044.cliqueWeights,
    cliqueFullCount_eq, cliqueF_eq, labels_eq]

@[simp] theorem cliqueJoints_eq (t : Fin 66) : AronowAudit.P044.cliqueJoints t =
    fun i j a b => SAP.P044.cliqueJoints t i j (labels.symm a) (labels.symm b) := by
  funext i j a b
  have he : a = b ↔ labels.symm a = labels.symm b := labels.symm.injective.eq_iff.symm
  simp only [AronowAudit.P044.cliqueJoints, SAP.P044.cliqueJoints,
    cliqueFullJoint_eq, cliqueF_eq, labels_eq, he]

@[simp] theorem cliqueT_eq : AronowAudit.P044.cliqueT = SAP.P044.cliqueT := by
  funext t z
  simp only [AronowAudit.P044.cliqueT, SAP.P044.cliqueT, htContrast_eq,
    cliqueF_eq, cliqueY_eq, cliqueWeights_eq, contrast_lift, back_d01, back_d00]

@[simp] theorem cliqueV_eq : AronowAudit.P044.cliqueV = SAP.P044.cliqueV := by
  funext t z
  simp only [AronowAudit.P044.cliqueV, SAP.P044.cliqueV, varianceEstimate_eq,
    cliqueF_eq, cliqueY_eq, cliqueWeights_eq, cliqueJoints_eq, variance_lift, back_d01, back_d00]

@[simp] theorem cliqueObservationMarginal_eq (t : Fin 66) (included : Bool) :
    AronowAudit.P044.cliqueObservationMarginal t included =
      fun i a => SAP.P044.cliqueObservationMarginal t included i (labels.symm a) := by
  funext i a
  simp only [AronowAudit.P044.cliqueObservationMarginal, SAP.P044.cliqueObservationMarginal,
    cliqueFullCount_eq, cliqueF_eq, labels_eq]

/-- Encoding both sides preserves equality of exposure-valued functions. -/
theorem mapped_functions_equal {I : Type*} (f g : I → SAP.P044.Exposure)
    (h : (fun i => labels (f i)) = (fun i => labels (g i))) : f = g := by
  funext i
  exact labels.injective (congrFun h i)

end
end SAP.P044.Bridge
