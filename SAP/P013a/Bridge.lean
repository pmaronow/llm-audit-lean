import SAP.P013a.Defs
import AronowAudit.P013.P013_Audit
import AronowAudit.P013.P013_Reporting
import AronowAudit.P013.P013_ConfidenceCompletion
import AronowAudit.P013.Wave1.Gap.GLP013P012B1
import AronowAudit.P013.Wave1.Gap.GLP013P012B2
import AronowAudit.P013.Wave1.Gap.GLP013P012B3
import AronowAudit.P013.Wave1.Gap.GP013P012B1
import AronowAudit.P013.Wave1.Gap.FidP013

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a.Bridge

open scoped BigOperators Topology
open Filter
noncomputable section

variable {Ω : Type*} [Fintype Ω] {N K : ℕ}

/-- Preserve the assignment weights and their certificates. -/
def toDesign (P : Design Ω) : AronowAudit.P013.Design Ω where
  weight := P.weight
  positive := P.positive
  total := P.total

def fromDesign (P : AronowAudit.P013.Design Ω) : Design Ω where
  weight := P.weight
  positive := P.positive
  total := P.total

/-- Preserve the exposure map and fixed outcome table. -/
def toPopulation {P : Design Ω} (F : Population P N K) :
    AronowAudit.P013.Population (toDesign P) N K where
  exposure := F.exposure
  outcome := F.outcome

def fromPopulation {P : AronowAudit.P013.Design Ω}
    (F : AronowAudit.P013.Population P N K) : Population (fromDesign P) N K where
  exposure := F.exposure
  outcome := F.outcome

def toExperiment (E : Experiment N) : AronowAudit.P013.Experiment N where
  supportSize := E.supportSize
  exposureSize := E.exposureSize
  design := toDesign E.design
  population := toPopulation E.population

def fromExperiment (E : AronowAudit.P013.Experiment N) : Experiment N where
  supportSize := E.supportSize
  exposureSize := E.exposureSize
  design := fromDesign E.design
  population := fromPopulation E.population

def toSequence (S : ExperimentSequence) : AronowAudit.P013.ExperimentSequence where
  experiment n := toExperiment (S.experiment n)
  treated := S.treated
  control := S.control
  distinct := S.distinct
  positiveTreated := S.positiveTreated
  positiveControl := S.positiveControl

def fromSequence (S : AronowAudit.P013.ExperimentSequence) : ExperimentSequence where
  experiment n := fromExperiment (S.experiment n)
  treated := S.treated
  control := S.control
  distinct := S.distinct
  positiveTreated := S.positiveTreated
  positiveControl := S.positiveControl

theorem design_roundtrip (P : Design Ω) : fromDesign (toDesign P) = P := by
  cases P
  rfl

theorem expectation_eq (P : Design Ω) (X : Ω → ℝ) :
    expectation P X = AronowAudit.P013.expectation (toDesign P) X := rfl

theorem probability_eq (P : Design Ω) (A : Ω → Prop) :
    probability P A = AronowAudit.P013.probability (toDesign P) A := rfl

theorem variance_eq (P : Design Ω) (X : Ω → ℝ) :
    variance P X = AronowAudit.P013.variance (toDesign P) X := rfl

theorem pi_eq {P : Design Ω} (F : Population P N K) (i : Fin N) (d : Fin K) :
    pi F i d = AronowAudit.P013.pi (toPopulation F) i d := rfl

theorem joint_eq {P : Design Ω} (F : Population P N K)
    (i j : Fin N) (d e : Fin K) :
    jointPi F i j d e = AronowAudit.P013.jointPi (toPopulation F) i j d e := rfl

theorem total_eq {P : Design Ω} (F : Population P N K) (d : Fin K) (z : Ω) :
    htTotal F d z = AronowAudit.P013.htTotal (toPopulation F) d z := rfl

theorem effect_eq {P : Design Ω} (F : Population P N K) (d e : Fin K) (z : Ω) :
    htEffect F d e z = AronowAudit.P013.htEffect (toPopulation F) d e z := rfl

theorem variance_estimate_eq {P : Design Ω} (F : Population P N K)
    (d e : Fin K) (z : Ω) :
    effectVariance F d e z = AronowAudit.P013.effectVariance (toPopulation F) d e z := rfl

theorem positivity_eq {P : Design Ω} (F : Population P N K) (d : Fin K) :
    Positivity F d ↔ AronowAudit.P013.Positivity (toPopulation F) d := Iff.rfl

theorem simulated_eq {P : Design Ω} (F : Population P N K) (d : Fin K) (R : ℕ)
    (z : Ω × (Fin R → Ω)) :
    simulatedHTTotal F d R z =
      AronowAudit.P013.simulatedHTTotal (toPopulation F) d R z := rfl

theorem dependence_eq (P : Design Ω) (D : Ω → Fin N → Fin K)
    (h : Fin N → Fin N → Bool) :
    GenuineDependency P D h ↔ AronowAudit.P013.GenuineDependency (toDesign P) D h := Iff.rfl

theorem nesting_eq (S : ExperimentSequence) :
    NestedPopulationSetup S ↔ AronowAudit.P013.NestedPopulationSetup (toSequence S) := Iff.rfl

theorem bounded_eq (S : ExperimentSequence) :
    ComparisonBounded S ↔ AronowAudit.P013.ComparisonBounded (toSequence S) := Iff.rfl

theorem condition4_eq (S : ExperimentSequence) :
    Condition4 S ↔ AronowAudit.P013.Condition4 (toSequence S) := Iff.rfl

theorem condition5_eq (S : ExperimentSequence) :
    Condition5Genuine S ↔ AronowAudit.P013.Condition5Genuine (toSequence S) := Iff.rfl

theorem condition6_eq (S : ExperimentSequence) :
    Condition6 S ↔ AronowAudit.P013.Condition6 (toSequence S) := Iff.rfl

theorem lower_tail_eq (S : ExperimentSequence) :
    LowerTailCondition S ↔ AronowAudit.P013.LowerTailCondition (toSequence S) := Iff.rfl

theorem coverage_eq (S : ExperimentSequence) (α : ℝ) (n : ℕ) :
    seqCoverage S α n = AronowAudit.P013.seqCoverage (toSequence S) α n := rfl

theorem directed_eq (S : ExperimentSequence) :
    Condition5CorrectedDirected S ↔
      AronowAudit.P013.Wave1.Condition5CorrectedDirected (toSequence S) := Iff.rfl

theorem paired_weight_eq (r : ℕ) (hr : 2 ≤ r) (z : Fin r → Fin 4) :
    (pairedDesign r hr).weight z = (AronowAudit.P013.pairedDesign r hr).weight z := rfl

theorem paired_outcome_eq (r : ℕ) (hr : 2 ≤ r) (i : Fin (2*r)) (d : Fin 2) :
    (pairedPopulation r hr).outcome i d =
      (AronowAudit.P013.pairedPopulation r hr).outcome i d := rfl

theorem block_weight_eq (N : ℕ) (z : Fin N → Fin 2) :
    (blockDesign N).weight z = (AronowAudit.P013.blockDesign N).weight z := rfl

theorem block_outcome_eq (i : ℕ) (d : Fin 2) :
    blockOutcome i d = AronowAudit.P013.blockOutcome i d := rfl

theorem display_eq (x p : ℝ) : Displays3 x p ↔ AronowAudit.P013.Displays3 x p := Iff.rfl

theorem complete_probability_eq (U : Finset ℕ) (n : ℕ) (A : Finset ℕ → Prop) :
    completeProbability U n A = AronowAudit.P013.completeProbability U n A := rfl

end
end SAP.P013a.Bridge
