import SAP.P004b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

structure SpatialPopulation (N : ℕ) (X : Type*) [MetricSpace X] [MeasurableSpace X] where
  node : Fin N → Set X
  node_nonempty : ∀ i, (node i).Nonempty
  zeta : Measure X
  outcome : X → Assignment N → ℝ
  bands : ℝ → Set ℝ

def nodeDistance {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i : Fin N) (x : X) : ℝ := Metric.infDist x (P.node i)

def nodeSeparation {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i j : Fin N) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ P.node i, ∃ y ∈ P.node j, dist x y = r}

def region {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i : Fin N) (d : ℝ) : Set X :=
  {x | nodeDistance P i x ∈ P.bands d}

def circleAverage {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) : CircleTable N :=
  fun i z => (∫ x in region P i d, P.outcome x z ∂P.zeta) /
    (P.zeta (region P i d)).toReal

def WellDefined {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) : Prop :=
  ∀ i, MeasurableSet (region P i d) ∧ 0 < P.zeta (region P i d) ∧
    P.zeta (region P i d) < ⊤ ∧ ∀ z, IntegrableOn (fun x => P.outcome x z) (region P i d) P.zeta

def FiniteSourceRange {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (dbar : ℝ) : Prop :=
  ∀ l x z z', (∀ k, k ≠ l → z k = z' k) → dbar < nodeDistance P l x →
    P.outcome x z = P.outcome x z'

def Polygonal (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ m : ℕ, ∃ v : Fin m → Fin 3 → EuclideanSpace ℝ (Fin 2),
    A = ⋃ i, convexHull ℝ (Set.range (v i))

def rectangle (a b c d : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ d}

def rectangleWitness : SpatialPopulation 3 (EuclideanSpace ℝ (Fin 2)) where
  node := ![rectangle 0 1 0 1, rectangle 10 11 0 1, rectangle 0 11 2 3]
  node_nonempty := by
    intro i
    fin_cases i
    · exact ⟨WithLp.toLp 2 ![0,0], by norm_num [rectangle]⟩
    · exact ⟨WithLp.toLp 2 ![10,0], by norm_num [rectangle]⟩
    · exact ⟨WithLp.toLp 2 ![0,2], by norm_num [rectangle]⟩
  zeta := volume
  outcome := fun x z => if x ∈ rectangle 0 1 0 1 ∪ rectangle 10 11 0 1 then bit (z 2) else 0
  bands := fun d => {d}

def thinPolygon (n : ℕ) (i : Fin (n+1)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  if i = 0 then rectangle 0 1 0 1
  else rectangle 2 (2+n) (2*((i : ℝ)-1)/n) ((2*((i : ℝ)-1)+1)/n)

def planePoint (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a,b]

def polygonRangeFamily (L : ℝ) (hL : 2 ≤ L) :
    SpatialPopulation 3 (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => if i = 0 then rectangle 0 1 0 1
    else if i = 1 then rectangle L (L+1) 0 1 else rectangle 0 (L+1) 2 3
  node_nonempty := by
    intro i
    fin_cases i
    · exact ⟨planePoint 0 0, by norm_num [rectangle, planePoint]⟩
    · exact ⟨planePoint (L+1) 0, by norm_num [rectangle, planePoint] <;> linarith⟩
    · exact ⟨planePoint 0 2, by norm_num [rectangle, planePoint] <;> linarith⟩
  zeta := volume
  outcome := fun x z => if x ∈ rectangle 0 1 0 1 ∪ rectangle L (L+1) 0 1 then bit (z 2) else 0
  bands := fun d => Set.Icc 0 d

end
end SAP.P004b
