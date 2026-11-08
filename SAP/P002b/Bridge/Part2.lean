import SAP.P002b.Bridge.Part1
import AronowAudit.P002.Wave1.Algorithm2
import AronowAudit.P002.Wave1.H1
import AronowAudit.P002.Wave1.QuantileIndexInterval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b.Bridge
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory

/-- Coefficients and recorded intervals are carried field for field. -/
def toQuadratic (Q : QuadraticAR) : AronowAudit.P002.QuadraticAR :=
  ⟨Q.a, Q.b, Q.c, Q.d, Q.e, Q.f⟩

def toPiece {M : ℕ} (p : RecordedPiece M) : AronowAudit.P002.RecordedPiece M :=
  ⟨p.left, p.right, p.index⟩

def fromPiece {M : ℕ} (p : AronowAudit.P002.RecordedPiece M) : RecordedPiece M :=
  ⟨p.left, p.right, p.index⟩

@[simp] theorem to_fromPiece {M : ℕ} (p : AronowAudit.P002.RecordedPiece M) :
    toPiece (fromPiece p) = p := rfl

@[simp] theorem from_toPiece {M : ℕ} (p : RecordedPiece M) :
    fromPiece (toPiece p) = p := rfl

@[simp] theorem dataCoefficients_to {n k : ℕ} (P : CovPopulation n k) (a : Bool)
    (O T : Finset (Fin n)) :
    toQuadratic (dataCoefficients P a O T) =
      AronowAudit.P002.dataCoefficients (toCovPopulation P) a O T := by
  cases a <;> rfl

/-- The common-data witness is preserved; no coefficient identity is assumed. -/
theorem dataGenerated_to {M : ℕ} (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR)
    (h : DataGeneratedCoefficients Qf Qg) :
    AronowAudit.P002.DataGeneratedCoefficients (toQuadratic Qf) (fun m => toQuadratic (Qg m)) := by
  rcases h with ⟨n, k, P, a, O, T, hv, hm, hc, hO, hT, ha, hf, hg⟩
  refine ⟨n, k, toCovPopulation P, a, O, T, hv, hm, hc, hO, hT, ha, ?_, ?_⟩
  · rw [hf, dataCoefficients_to]
  · intro m
    change toQuadratic (Qg m) = _
    rw [hg m, dataCoefficients_to]

@[simp] theorem algorithm1Run_map {M : ℕ} (g : Fin M → ℝ → ℝ) (α : ℝ)
    (J : List ℝ) (pieces : List (RecordedPiece M)) :
    AronowAudit.P002.Algorithm1Run g α J (pieces.map toPiece) ↔
      Algorithm1Run g α J pieces := by
  simp [AronowAudit.P002.Algorithm1Run, Algorithm1Run, List.map_map,
    toPiece, Function.comp_def]
  rfl

@[simp] theorem algorithm2Step_to {M : ℕ} (g : Fin M → ℝ → ℝ) (α : ℝ)
    (J : List ℝ) (p : RecordedPiece M) (q : Option (RecordedPiece M)) :
    AronowAudit.P002.Algorithm2Step g α J (toPiece p) (q.map toPiece) ↔
      Algorithm2Step g α J p q := by
  cases q <;> rfl

@[simp] theorem algorithm2Run_map {M : ℕ} (g : Fin M → ℝ → ℝ) (α : ℝ)
    (J : List ℝ) (pieces : List (RecordedPiece M)) :
    AronowAudit.P002.Algorithm2Run g α J (pieces.map toPiece) ↔
      Algorithm2Run g α J pieces := by
  unfold AronowAudit.P002.Algorithm2Run Algorithm2Run
  constructor
  · rintro ⟨hJ, hne, hps, hhead, hsteps⟩
    refine ⟨hJ, hne, ?_, ?_, ?_⟩
    · intro hn
      exact hps (by simp [hn])
    · intro p hp
      exact hhead (toPiece p) (by simp [List.head?_map, hp])
    · intro i
      have H := hsteps ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
      apply (algorithm2Step_to g α J (pieces.get i) (pieces[i.val+1]?)).mp
      simpa only [List.get_eq_getElem, List.getElem_map, List.getElem?_map] using H
  · rintro ⟨hJ, hne, hps, hhead, hsteps⟩
    refine ⟨hJ, hne, ?_, ?_, ?_⟩
    · intro hn
      cases pieces with
      | nil => exact hps rfl
      | cons p ps => cases hn
    · intro p hp
      rw [List.head?_map, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact hhead q hq
    · intro i
      have hi : i.val < pieces.length := by simpa only [List.length_map] using i.isLt
      have H := (algorithm2Step_to g α J
        (pieces.get ⟨i.val, hi⟩) (pieces[i.val+1]?)).mpr (hsteps ⟨i.val, hi⟩)
      simpa only [List.get_eq_getElem, List.getElem_map, List.getElem?_map] using H

@[simp] theorem returnedSet_map {M : ℕ} (f : ℝ → ℝ) (g : Fin M → ℝ → ℝ)
    (pieces : List (RecordedPiece M)) :
    AronowAudit.P002.returnedSet f g (pieces.map toPiece) = returnedSet f g pieces := by
  ext β
  simp [AronowAudit.P002.returnedSet, returnedSet, AronowAudit.P002.pieceSet,
    pieceSet, toPiece]
  rfl

end
end SAP.P002b.Bridge
