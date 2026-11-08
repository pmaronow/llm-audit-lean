import SAP.P004a.Defs
import AronowAudit.P004.P004_Spatial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.Bridge

open MeasureTheory Filter
open SAP.P004a
noncomputable section

/-- Preserve the spatial data, including the nonempty-node certificates. -/
def toPopulation {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) : AronowAudit.P004.SpatialPopulation N X where
  node := P.node
  node_nonempty := P.node_nonempty
  zeta := P.zeta
  outcome := P.outcome
  bands := P.bands

def fromPopulation {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : AronowAudit.P004.SpatialPopulation N X) : SpatialPopulation N X where
  node := P.node
  node_nonempty := P.node_nonempty
  zeta := P.zeta
  outcome := P.outcome
  bands := P.bands

theorem from_to {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) : fromPopulation (toPopulation P) = P := rfl

theorem to_from {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : AronowAudit.P004.SpatialPopulation N X) : toPopulation (fromPopulation P) = P := rfl

def toSequence {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : PopulationSequence Space) :
    AronowAudit.P004.PopulationSequence Space := fun N => toPopulation (P N)

theorem circleAverage_eq {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) :
    AronowAudit.P004.circleAverage (toPopulation P) d = circleAverage P d := rfl

theorem region_eq {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i : Fin N) (d : ℝ) :
    AronowAudit.P004.region (toPopulation P) i d = region P i d := rfl

theorem separation_eq {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) :
    AronowAudit.P004.nodeSeparation (toPopulation P) = nodeSeparation P := rfl

theorem wellDefined_eq {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) :
    AronowAudit.P004.WellDefined (toPopulation P) d ↔ WellDefined P d := Iff.rfl

theorem spatialConditions_eq {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : PopulationSequence Space) :
    AronowAudit.P004.SpatialLocalConditions (toSequence P) ↔ SpatialLocalConditions P := Iff.rfl

theorem pointEffect_eq {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (p : Fin N → ℝ) :
    AronowAudit.P004.pointEffect (toPopulation P) p = pointEffect P p := rfl

theorem threeTypePopulation_eq (N : ℕ) :
    toPopulation (threeTypePopulation N) = AronowAudit.P004.threeTypePopulation N := rfl

theorem activePopulation_eq (N : ℕ) :
    toPopulation (activePopulation N) = AronowAudit.P004.activePopulation N := rfl

theorem starPopulation_eq (N : ℕ) :
    toPopulation (starPopulation N) = AronowAudit.P004.starPopulation N := rfl

theorem areaPopulation_eq :
    toPopulation areaBinaryPopulation = AronowAudit.P004.areaBinaryPopulation := rfl

theorem shellPopulation_eq (D : Set ℝ) :
    toPopulation (shellSpatialPopulation D) = AronowAudit.P004.shellSpatialPopulation D := rfl

theorem nullPopulation_eq :
    toPopulation eightNodeNullPopulation = AronowAudit.P004.eightNodeNullPopulation := rfl

end
end SAP.P004a.Bridge
