import SAP.P022.Defs
import AronowAudit.P022.P022_Numerical
import AronowAudit.P022.Wave1.Gap.GP022B1
import AronowAudit.P022.Wave1.Gap.GP022B2
import AronowAudit.P022.Wave1.Gap.GP022B3
import AronowAudit.P022.Wave1.Gap.GLP022B3
import AronowAudit.P022.Wave1.Gap.GLP022B4
import AronowAudit.P022.Wave1.Gap.GP022B2b
import AronowAudit.P022.Wave1.Gap.GP022B3b
import AronowAudit.P022.Wave1.Gap.TailA.BoundedAsymptotic
import AronowAudit.P022.Wave1.FixedArm
import AronowAudit.P022.Wave1.PrintedLemma2
import AronowAudit.P022.Wave1.Gap.TailBCorollaryCoverage

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.Bridge
open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

/-- Preserve all design data and validity fields. -/
def toDesign (d : Design) : AronowAudit.P022.Design :=
  ⟨d.N, d.m, d.k, d.population_min, d.treatment_min, d.control_min, d.sample_le⟩

def fromDesign (d : AronowAudit.P022.Design) : Design :=
  ⟨d.N, d.m, d.k, d.population_min, d.treatment_min, d.control_min, d.sample_le⟩

theorem toDesign_fromDesign (d : AronowAudit.P022.Design) : toDesign (fromDesign d) = d := rfl
theorem fromDesign_toDesign (d : Design) : fromDesign (toDesign d) = d := rfl
theorem toDesign_N (d : Design) : (toDesign d).N = d.N := rfl
theorem toDesign_m (d : Design) : (toDesign d).m = d.m := rfl
theorem toDesign_k (d : Design) : (toDesign d).k = d.k := rfl

/-- The assignment type is the same permutation type on the same population size. -/
theorem assignment_eq (d : Design) : AronowAudit.P022.Assignment (toDesign d) = Assignment d := rfl

/-- Preserve the row designs, nesting certificate, and both fixed outcome sequences. -/
def toSequence (S : ExperimentSequence) : AronowAudit.P022.ExperimentSequence where
  design q := toDesign (S.design q)
  size q := S.size q
  y1 := S.y1
  y0 := S.y0

def fromSequence (S : AronowAudit.P022.ExperimentSequence) : ExperimentSequence where
  design q := fromDesign (S.design q)
  size q := S.size q
  y1 := S.y1
  y0 := S.y0

theorem toSequence_fromSequence (S : AronowAudit.P022.ExperimentSequence) :
    toSequence (fromSequence S) = S := rfl
theorem fromSequence_toSequence (S : ExperimentSequence) : fromSequence (toSequence S) = S := rfl
theorem toSequence_design (S : ExperimentSequence) (q : ℕ) :
    (toSequence S).design q = toDesign (S.design q) := rfl
theorem toSequence_y1 (S : ExperimentSequence) : (toSequence S).y1 = S.y1 := rfl
theorem toSequence_y0 (S : ExperimentSequence) : (toSequence S).y0 = S.y0 := rfl

def toSide : BoundSide → AronowAudit.P022.BoundSide
  | .H => .H
  | .L => .L

def fromSide : AronowAudit.P022.BoundSide → BoundSide
  | .H => .H
  | .L => .L

theorem fromSide_toSide (B : BoundSide) : fromSide (toSide B) = B := by cases B <;> rfl
theorem toSide_fromSide (B : AronowAudit.P022.BoundSide) : toSide (fromSide B) = B := by cases B <;> rfl
theorem fromSide_H : fromSide .H = .H := rfl
theorem fromSide_L : fromSide .L = .L := rfl
theorem side_eq_H (B : BoundSide) : (toSide B = .H) ↔ B = .H := by cases B <;> simp [toSide]

/-- Changing the universal design variable along the inverse adapters is pure logic. -/
theorem forall_design (P : AronowAudit.P022.Design → Prop) :
    (∀ d, P d) ↔ ∀ d : Design, P (toDesign d) := by
  constructor
  · intro h d; exact h (toDesign d)
  · intro h d; exact h (fromDesign d)

theorem forall_sequence (P : AronowAudit.P022.ExperimentSequence → Prop) :
    (∀ S, P S) ↔ ∀ S : ExperimentSequence, P (toSequence S) := by
  constructor
  · intro h S; exact h (toSequence S)
  · intro h S; exact h (fromSequence S)

theorem forall_side (P : AronowAudit.P022.BoundSide → Prop) :
    (∀ B, P B) ↔ ∀ B : BoundSide, P (toSide B) := by
  constructor
  · intro h B; exact h (toSide B)
  · intro h B
    have hp := h (fromSide B)
    cases B <;> exact hp

theorem reciprocalWitness_eq : AronowAudit.P022.reciprocalWitness = toSequence reciprocalWitness := rfl
theorem cornerWitness_eq : AronowAudit.P022.cornerWitness = toSequence cornerWitness := rfl
theorem fourUnitDesign_eq : AronowAudit.P022.fourUnitDesign = toDesign fourUnitDesign := rfl
theorem originLaw_eq : AronowAudit.P022.originLaw = originLaw := rfl
theorem cornerLaw_eq : AronowAudit.P022.cornerLaw = cornerLaw := rfl

end
end SAP.P022.Bridge
