import SAP.P004c.Defs
import AronowAudit.P004.P004_RegressionCompletion
import AronowAudit.P004.P004_VarianceComponentsCompletion
import AronowAudit.P004.P004_VarianceOrderCompletion
import AronowAudit.P004.P004_KernelCompletion
import AronowAudit.P004.Wave1.Gap.GP0042B1
import AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004c.Bridge
open SAP.P004c MeasureTheory Filter
open scoped BigOperators Classical
noncomputable section

/-- Preserve every field; no spatial or statistical assumption is manufactured. -/
def toPopulation {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) : AronowAudit.P004.SpatialPopulation N X :=
  ⟨P.node, P.node_nonempty, P.zeta, P.outcome, P.bands⟩

def toSequence {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : PopulationSequence Space) :
    AronowAudit.P004.PopulationSequence Space := fun N => toPopulation (P N)

theorem expect_correspondence {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) :
    AronowAudit.P004.expect p X = expect p X := rfl

theorem ht_correspondence {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) :
    AronowAudit.P004.ht p R = ht p R := rfl

theorem linear_correspondence {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) :
    AronowAudit.P004.linearHajek p R = linearHajek p R := rfl

theorem variance_correspondence {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) :
    AronowAudit.P004.variance p X = variance p X := rfl

theorem moments_correspondence {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) :
    AronowAudit.P004.secondMomentBound p R B g = secondMomentBound p R B g := rfl

theorem circle_correspondence {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) :
    AronowAudit.P004.circleAverage (toPopulation P) d = circleAverage P d := rfl

theorem wellDefined_correspondence {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) :
    AronowAudit.P004.WellDefined (toPopulation P) d ↔ WellDefined P d := Iff.rfl

theorem local_correspondence {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : PopulationSequence Space) :
    AronowAudit.P004.SpatialLocalConditions (toSequence P) ↔ SpatialLocalConditions P := Iff.rfl

theorem ned_correspondence {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : PopulationSequence Space) (p d : ℝ) :
    AronowAudit.P004.NEDConditions (toSequence P) p d ↔ NEDConditions P p d := Iff.rfl

theorem spacing_correspondence {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : PopulationSequence Space) :
    AronowAudit.P004.QuadraticSpacing (toSequence P) ↔ QuadraticSpacing P := Iff.rfl

/-- Change only the notation for positive semidefiniteness. -/
theorem psd_correspondence {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℝ) :
    AronowAudit.P004.PSD Q ↔ Q.PosSemidef :=
  AronowAudit.P004.MatrixCompletion.PSD_iff_posSemidef Q

end
end SAP.P004c.Bridge
