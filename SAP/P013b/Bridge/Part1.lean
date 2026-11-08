import SAP.P013b.Defs
import AronowAudit.P013.P013_Audit
import AronowAudit.P013.P013_Later
import AronowAudit.P013.Wave1.PrintedWald

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b.Bridge
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
variable {Ω : Type*} [Fintype Ω]

def toDesign (P : Design Ω) : AronowAudit.P013.Design Ω :=
  ⟨P.weight, P.positive, P.total⟩

def fromDesign (P : AronowAudit.P013.Design Ω) : Design Ω :=
  ⟨P.weight, P.positive, P.total⟩

def toPopulation {N K : ℕ} {P : Design Ω} (F : Population P N K) :
    AronowAudit.P013.Population (toDesign P) N K := ⟨F.exposure, F.outcome⟩

def fromPopulation {N K : ℕ} {P : AronowAudit.P013.Design Ω}
    (F : AronowAudit.P013.Population P N K) : Population (fromDesign P) N K :=
  ⟨F.exposure, F.outcome⟩

def toExperiment {N : ℕ} (E : Experiment N) : AronowAudit.P013.Experiment N :=
  ⟨E.supportSize, E.exposureSize, toDesign E.design, toPopulation E.population⟩

def fromExperiment {N : ℕ} (E : AronowAudit.P013.Experiment N) : Experiment N :=
  ⟨E.supportSize, E.exposureSize, fromDesign E.design, fromPopulation E.population⟩

def toSequence (S : ExperimentSequence) : AronowAudit.P013.ExperimentSequence :=
  ⟨fun n => toExperiment (S.experiment n), S.treated, S.control, S.distinct,
    S.positiveTreated, S.positiveControl⟩

def fromSequence (S : AronowAudit.P013.ExperimentSequence) : ExperimentSequence :=
  ⟨fun n => fromExperiment (S.experiment n), S.treated, S.control, S.distinct,
    S.positiveTreated, S.positiveControl⟩

theorem expectation_to (P : Design Ω) (X : Ω → ℝ) :
    expectation P X = AronowAudit.P013.expectation (toDesign P) X := rfl

theorem pi_to {N K : ℕ} {P : Design Ω} (F : Population P N K) (i : Fin N) (d : Fin K) :
    pi F i d = AronowAudit.P013.pi (toPopulation F) i d := rfl

theorem htTotal_to {N K : ℕ} {P : Design Ω} (F : Population P N K) (d : Fin K) :
    htTotal F d = AronowAudit.P013.htTotal (toPopulation F) d := rfl

theorem condition3_to (S : ExperimentSequence) :
    Condition3 S ↔ AronowAudit.P013.Condition3 (toSequence S) := Iff.rfl

theorem condition4_to (S : ExperimentSequence) :
    Condition4 S ↔ AronowAudit.P013.Condition4 (toSequence S) := Iff.rfl

theorem coverage_from (S : AronowAudit.P013.ExperimentSequence) (α : ℝ) :
    seqCoverage (fromSequence S) α = AronowAudit.P013.seqCoverage S α := rfl

theorem normalCritical_eq : normalCritical = AronowAudit.P013.normalCritical := rfl

theorem schoolBSupport_eq : schoolBSupport = AronowAudit.P013.schoolBSupport := rfl

theorem schoolCSupport_eq : schoolCSupport = AronowAudit.P013.schoolCSupport := rfl

theorem schoolStudentJoint_eq {Ξ : Type*} [Fintype Ξ] {N : ℕ} {α : Type*}
    (S : Finset α) (hosts : α → School → Bool) (Q : Ξ → ℝ)
    (school : Fin N → School) (code : Ξ → Fin N → Fin 4)
    (i j : Fin N) (d e : Fin 5) :
    schoolStudentJoint S hosts Q school code i j d e =
      AronowAudit.P013.schoolStudentJoint S hosts Q school code i j d e := rfl

end
end SAP.P013b.Bridge
