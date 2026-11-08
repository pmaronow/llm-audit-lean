import SAP.P037a.Defs
import AronowAudit.P037.P037_FiniteDesign
import AronowAudit.P037.P037_ReportedNumbers
import AronowAudit.P037.P037_Bootstrap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.Bridge

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

/-- Preserve the weights and their two probability-law certificates. -/
def toDesign {Ω : Type*} [Fintype Ω] (d : Design Ω) :
    AronowAudit.P037.FiniteDesign Ω :=
  ⟨d.weight, d.nonneg, d.total⟩

theorem mean_eq {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) :
    mean d X = AronowAudit.P037.designMean (toDesign d) X := rfl

theorem variance_eq {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) :
    variance d X = AronowAudit.P037.designVariance (toDesign d) X := rfl

theorem covariance_eq {Ω : Type*} [Fintype Ω] (d : Design Ω) (X Y : Ω → ℝ) :
    covariance d X Y = AronowAudit.P037.designCovariance (toDesign d) X Y := rfl

theorem probability_eq {Ω : Type*} [Fintype Ω] (d : Design Ω) (E : Ω → Prop) :
    probability d E = AronowAudit.P037.designProbability (toDesign d) E := rfl

theorem independentDesign_eq {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (d : ∀ i, Design (Ω i)) :
    toDesign (independentDesign d) =
      AronowAudit.P037.productDesign (fun i => toDesign (d i)) := rfl

theorem blockDesign_eq : toDesign blockDesign = AronowAudit.P037.oneBlockDesign := rfl

theorem doubleBlockDesign_eq :
    toDesign doubleBlockDesign = AronowAudit.P037.twoBlockDesign := rfl

def toData (x : ExposureData) : AronowAudit.P037.ExposureConfiguration :=
  ⟨x.school, x.seed, x.peers, x.referentPeers⟩

def fromData (x : AronowAudit.P037.ExposureConfiguration) : ExposureData :=
  ⟨x.school, x.seed, x.peers, x.referentPeers⟩

def toCase : ExposureCase → AronowAudit.P037.Exposure
  | .control => .control
  | .school => .school
  | .nonreferent => .nonreferent
  | .referent => .referent
  | .direct => .direct

def fromCase : AronowAudit.P037.Exposure → ExposureCase
  | .control => .control
  | .school => .school
  | .nonreferent => .nonreferent
  | .referent => .referent
  | .direct => .direct

@[simp] theorem to_from_case (e : AronowAudit.P037.Exposure) :
    toCase (fromCase e) = e := by cases e <;> rfl

@[simp] theorem from_to_case (e : ExposureCase) :
    fromCase (toCase e) = e := by cases e <;> rfl

theorem case_injective : Function.Injective toCase :=
  fun _ _ h => by simpa only [from_to_case] using congrArg fromCase h

theorem feasible_iff (x : ExposureData) :
    (toData x).Feasible ↔ x.Feasible := Iff.rfl

theorem printed_iff (x : ExposureData) (e : ExposureCase) :
    AronowAudit.P037.printedExposureCondition (toData x) (toCase e) ↔
      printedCase x e := by cases e <;> exact Iff.rfl

theorem printed_back (x : AronowAudit.P037.ExposureConfiguration)
    (e : AronowAudit.P037.Exposure) :
    printedCase (fromData x) (fromCase e) ↔
      AronowAudit.P037.printedExposureCondition x e := by cases e <;> exact Iff.rfl

theorem corrected_iff (x : ExposureData) (e : ExposureCase) :
    AronowAudit.P037.correctedExposureCondition (toData x) (toCase e) ↔
      correctedCase x e := by cases e <;> exact Iff.rfl

theorem corrected_back (x : ExposureData) (e : AronowAudit.P037.Exposure) :
    AronowAudit.P037.correctedExposureCondition (toData x) e ↔
      correctedCase x (fromCase e) := by cases e <;> exact Iff.rfl

end SAP.P037a.Bridge
