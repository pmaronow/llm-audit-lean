import SAP.P009a.Defs
import AronowAudit.P009.P009_Audit
import AronowAudit.P009.P009_NormalCompletion
import AronowAudit.P009.P009_LimsupCompletion
import AronowAudit.P009.P009_DiagonalCompletion
import AronowAudit.P009.P009_MixingBasics
import AronowAudit.P009.P009_OverwhelmingCompletion
import AronowAudit.P009.Wave1.Gap.GLP0091B1
import AronowAudit.P009.Wave1.Gap.GLP0091B2
import AronowAudit.P009.Wave1.Gap.GLP0091B3
import AronowAudit.P009.Wave1.Gap.GLP0091B7
import AronowAudit.P009.Wave1.Gap.GP0091B1b
import AronowAudit.P009.Wave1.Gap.GP0092B2
import AronowAudit.P009.Wave1.Gap.GLP0092B5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009a.Bridge

open Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

/-- Preserve the finite masses and their certificates. -/
def toProjectDistribution {Ω : Type*} [Fintype Ω] (P : FiniteDistribution Ω) :
    AronowAudit.P009.Law Ω := ⟨P.mass, P.nonneg, P.total⟩

def fromProjectDistribution {Ω : Type*} [Fintype Ω] (P : AronowAudit.P009.Law Ω) :
    FiniteDistribution Ω := ⟨P.mass, P.nonneg, P.total⟩

/-- Preserve the design and every full-cube potential response. -/
def toProjectExperiment {n : ℕ} (E : FiniteExperiment n) : AronowAudit.P009.Experiment n :=
  ⟨toProjectDistribution E.design, E.outcome⟩

def fromProjectExperiment {n : ℕ} (E : AronowAudit.P009.Experiment n) : FiniteExperiment n :=
  ⟨fromProjectDistribution E.design, E.outcome⟩

/-- Preserve sample sizes, growth certificates, and experiments. -/
def toProjectSequence (S : ExperimentSequence) : AronowAudit.P009.Study where
  N := S.N
  positive := S.positive
  grows := S.grows
  experiment := fun t => toProjectExperiment (S.experiment t)

theorem distribution_roundtrip {Ω : Type*} [Fintype Ω] (P : AronowAudit.P009.Law Ω) :
    toProjectDistribution (fromProjectDistribution P) = P := by cases P; rfl

theorem experiment_roundtrip {n : ℕ} (E : AronowAudit.P009.Experiment n) :
    toProjectExperiment (fromProjectExperiment E) = E := by cases E; rfl

theorem expectation_correspondence {Ω : Type*} [Fintype Ω]
    (P : FiniteDistribution Ω) (X : Ω → ℝ) :
    expectation P X = AronowAudit.P009.mean (toProjectDistribution P) X := rfl

theorem probability_correspondence {Ω : Type*} [Fintype Ω]
    (P : FiniteDistribution Ω) (A : Ω → Prop) :
    probability P A = AronowAudit.P009.prob (toProjectDistribution P) A := rfl

theorem covariance_correspondence {Ω : Type*} [Fintype Ω]
    (P : FiniteDistribution Ω) (X Y : Ω → ℝ) :
    covariance P X Y = AronowAudit.P009.cov (toProjectDistribution P) X Y := rfl

theorem estimator_correspondence {n : ℕ} (E : FiniteExperiment n) :
    htEstimate E = AronowAudit.P009.ht (toProjectExperiment E) := rfl

theorem interference_correspondence {n : ℕ} (E : FiniteExperiment n) (i j : Fin n) :
    Affects E i j ↔ AronowAudit.P009.Interferes (toProjectExperiment E) i j := Iff.rfl

theorem mixing_correspondence {Ω A B : Type*} [Fintype Ω]
    (P : FiniteDistribution Ω) (X : Ω → A) (Y : Ω → B) :
    mixingCoefficient P X Y = AronowAudit.P009.alpha (toProjectDistribution P) X Y := rfl

theorem regularity_correspondence {n : ℕ} (E : FiniteExperiment n) (k q s : ℝ) :
    Regularity E k q s ↔ AronowAudit.P009.Regular (toProjectExperiment E) k q s := Iff.rfl

theorem sequence_regularity_correspondence (S : ExperimentSequence) (k q s : ℝ) :
    SequenceRegularity S k q s ↔
      AronowAudit.P009.RegularSequence (toProjectSequence S) k q s := Iff.rfl

theorem conservative_correspondence (S : ExperimentSequence)
    (V : (t : ℕ) → TreatmentVector (S.N t) → ℝ) :
    VarianceConservative S V ↔ AronowAudit.P009.Conservative (toProjectSequence S) V := Iff.rfl

theorem sparse_sequence_correspondence :
    toProjectSequence sparseSequence = AronowAudit.P009.sparseStudy := rfl

theorem cluster_sequence_correspondence :
    toProjectSequence clusterSequence = AronowAudit.P009.limsupStudy := rfl

theorem identity_sequence_correspondence :
    toProjectSequence identitySequence = AronowAudit.P009.identityStudy := rfl

end
end SAP.P009a.Bridge
