import SAP.P045a.Defs
import AronowAudit.P045.P045_Spillover

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a.Bridge
noncomputable section

def design {Ω : Type*} [Fintype Ω] (p : SAP.P045a.Design Ω) :
    AronowAudit.P045.Design Ω := ⟨p.mass, p.nonneg, p.total⟩

def network {n : ℕ} (A : SAP.P045a.Network n) :
    AronowAudit.P045.Network n := ⟨A.adj, A.symmetric, A.loopless⟩

def encode : SAP.P045a.Exposure → AronowAudit.P045.Exposure
  | .d11 => .d11 | .d10 => .d10 | .d01 => .d01 | .d00 => .d00

def decode : AronowAudit.P045.Exposure → SAP.P045a.Exposure
  | .d11 => .d11 | .d10 => .d10 | .d01 => .d01 | .d00 => .d00

@[simp] theorem decode_d11 : decode .d11 = .d11 := rfl
@[simp] theorem decode_d10 : decode .d10 = .d10 := rfl
@[simp] theorem decode_d01 : decode .d01 = .d01 := rfl
@[simp] theorem decode_d00 : decode .d00 = .d00 := rfl

@[simp] theorem decode_encode (d : SAP.P045a.Exposure) : decode (encode d) = d := by
  cases d <;> rfl

@[simp] theorem encode_decode (d : AronowAudit.P045.Exposure) : encode (decode d) = d := by
  cases d <;> rfl

theorem decode_injective : Function.Injective decode := by
  intro a b h
  simpa only [encode_decode] using congrArg encode h

@[simp] theorem decode_eq (a b : AronowAudit.P045.Exposure) :
    decode a = decode b ↔ a = b := decode_injective.eq_iff

@[simp] theorem forall_decode (P : SAP.P045a.Exposure → Prop) :
    (∀ d : AronowAudit.P045.Exposure, P (decode d)) ↔ ∀ d, P d := by
  constructor
  · intro h d
    simpa only [decode_encode] using h (encode d)
  · intro h d
    exact h (decode d)

theorem project_forall (P : AronowAudit.P045.Exposure → Prop) :
    (∀ d, P d) ↔ P .d11 ∧ P .d10 ∧ P .d01 ∧ P .d00 := by
  constructor
  · intro h
    exact ⟨h .d11, h .d10, h .d01, h .d00⟩
  · rintro ⟨h11,h10,h01,h00⟩ d
    cases d <;> assumption

theorem sap_forall (P : SAP.P045a.Exposure → Prop) :
    (∀ d, P d) ↔ P .d11 ∧ P .d10 ∧ P .d01 ∧ P .d00 := by
  constructor
  · intro h
    exact ⟨h .d11, h .d10, h .d01, h .d00⟩
  · rintro ⟨h11,h10,h01,h00⟩ d
    cases d <;> assumption

@[simp] theorem exposure_decode {n : ℕ} (A : Fin n → Fin n → Bool)
    (z : SAP.P045a.Assignment n) (i : Fin n) :
    decode (AronowAudit.P045.exposure A z i) = SAP.P045a.exposure A z i := by
  unfold AronowAudit.P045.exposure SAP.P045a.exposure
  split_ifs <;> rfl

@[simp] theorem exposure_pred {n : ℕ} (A : Fin n → Fin n → Bool)
    (z : SAP.P045a.Assignment n) (i : Fin n) (d : AronowAudit.P045.Exposure) :
    (AronowAudit.P045.exposure A z i = d) ↔ (SAP.P045a.exposure A z i = decode d) := by
  rw [← decode_eq, exposure_decode]

@[simp] theorem matrixExposure_pred {n : ℕ} (M : ℕ → ℕ → ℝ)
    (z : SAP.P045a.Assignment n) (i : Fin n) (d : AronowAudit.P045.Exposure) :
    (AronowAudit.P045.matrixExposure M z i = d) ↔
      (SAP.P045a.matrixExposure M z i = decode d) := by
  rw [← decode_eq]
  have h : decode (AronowAudit.P045.matrixExposure M z i) =
      SAP.P045a.matrixExposure M z i := by
    unfold AronowAudit.P045.matrixExposure SAP.P045a.matrixExposure
      AronowAudit.P045.bit SAP.P045a.bit
    split_ifs <;> rfl
  rw [h]

def outcome {n : ℕ} (y : Fin n → SAP.P045a.Exposure → ℝ) :
    Fin n → AronowAudit.P045.Exposure → ℝ := fun i d => y i (decode d)

@[simp] theorem exposureProb_eq {n : ℕ} (p : SAP.P045a.Assignment n → ℝ)
    (A : Fin n → Fin n → Bool) (i : Fin n) (d : AronowAudit.P045.Exposure) :
    AronowAudit.P045.exposureProb p (AronowAudit.P045.exposure A) i d =
      SAP.P045a.exposureProb p (SAP.P045a.exposure A) i (decode d) := by
  change SAP.P045a.prob p (fun z => AronowAudit.P045.exposure A z i = d) = _
  simp only [exposure_pred]
  rfl

@[simp] theorem htTotal_eq {n : ℕ} (p : SAP.P045a.Assignment n → ℝ)
    (A : Fin n → Fin n → Bool) (y : Fin n → SAP.P045a.Exposure → ℝ)
    (d : AronowAudit.P045.Exposure) (z : SAP.P045a.Assignment n) :
    AronowAudit.P045.htTotal p (AronowAudit.P045.exposure A) (outcome y) d z =
      SAP.P045a.htTotal p (SAP.P045a.exposure A) y (decode d) z := by
  unfold AronowAudit.P045.htTotal SAP.P045a.htTotal
    AronowAudit.P045.observed SAP.P045a.observed outcome
  simp only [exposure_pred, exposure_decode, exposureProb_eq]

@[simp] theorem htObserved_eq {n : ℕ} (p : SAP.P045a.Assignment n → ℝ)
    (A : Fin n → Fin n → Bool) (Y : Fin n → SAP.P045a.Assignment n → ℝ)
    (d : AronowAudit.P045.Exposure) (z : SAP.P045a.Assignment n) :
    AronowAudit.P045.htObserved p (AronowAudit.P045.exposure A) Y d z =
      SAP.P045a.htObserved p (SAP.P045a.exposure A) Y (decode d) z := by
  unfold AronowAudit.P045.htObserved SAP.P045a.htObserved
  simp only [exposure_pred, exposureProb_eq]

@[simp] theorem naiveTreated_eq {n : ℕ} (p : SAP.P045a.Assignment n → ℝ)
    (A : Fin n → Fin n → Bool) (y : Fin n → SAP.P045a.Exposure → ℝ)
    (z : SAP.P045a.Assignment n) :
    AronowAudit.P045.naiveTreated p A (outcome y) z = SAP.P045a.naiveTreated p A y z := by
  unfold AronowAudit.P045.naiveTreated SAP.P045a.naiveTreated outcome
  simp only [exposure_decode]
  rfl

@[simp] theorem repairedExpansion_eq {n : ℕ} (p : SAP.P045a.Assignment n → ℝ)
    (A : Fin n → Fin n → Bool) (y : Fin n → SAP.P045a.Exposure → ℝ)
    (z : SAP.P045a.Assignment n) :
    AronowAudit.P045.repairedExpansion p A (outcome y) z =
      SAP.P045a.repairedExpansion p A y z := by
  unfold AronowAudit.P045.repairedExpansion SAP.P045a.repairedExpansion outcome
  simp only [exposure_pred, decode]
  rfl

end
end SAP.P045a.Bridge
