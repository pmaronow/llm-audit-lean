import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P004a
universe u v
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]

abbrev Assignment (N : ℕ) := Fin N → Bool

def dot {k : ℕ} (u v : Fin k → ℝ) : ℝ := ∑ j, u j * v j

def bit (a : Bool) : ℝ := if a then 1 else 0

def LogisticConditions {k : ℕ} (O : ∀ N, Fin N → Fin k → ℝ)
    (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
    (θhat : ∀ N, Assignment N → Fin k → ℝ) : Prop :=
  IsCompact Θ ∧ θ₀ ∈ Θ ∧
  (∃ U : ℝ, ∀ N i j, |O N i j| ≤ U) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ᶠ N in atTop, ∀ v : Fin k → ℝ,
    c * (∑ j, (v j)^2) ≤ (∑ i, (dot (O N i) v)^2) / N) ∧
  (∀ N z, θhat N z ∈ Θ ∧ ∀ θ ∈ Θ,
    (∑ i, (bit (z i) * dot (O N i) θ - Real.log (1 + Real.exp (dot (O N i) θ)))) ≤
    (∑ i, (bit (z i) * dot (O N i) (θhat N z) -
      Real.log (1 + Real.exp (dot (O N i) (θhat N z))))))

def threeTypeONat (N : ℕ) (i : Fin N) : Fin 2 → ℝ :=
  ![1, (((i.val % 3 : ℕ) : ℝ) - 1)]

def threeTypeTheta : Fin 2 → ℝ := ![0, Real.log 2]

def threeTypeParameterSet : Set (Fin 2 → ℝ) := {θ | ∀ j, -2 ≤ θ j ∧ θ j ≤ 2}

structure SpatialPopulation (N : ℕ) (X : Type*) [MetricSpace X] [MeasurableSpace X] where
  node : Fin N → Set X
  node_nonempty : ∀ i, (node i).Nonempty
  zeta : Measure X
  outcome : X → Assignment N → ℝ
  bands : ℝ → Set ℝ

abbrev PopulationSequence (Space : ℕ → Type*) [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] := ∀ N, SpatialPopulation N (Space N)

abbrev CircleTable (N : ℕ) := Fin N → Assignment N → ℝ

def interferes {N : ℕ} (R : CircleTable N) (i j : Fin N) : Prop :=
  i = j ∨ ∃ z z' : Assignment N,
    (∀ k, k ≠ j → z k = z' k) ∧ R i z ≠ R i z'

def sharesSource {N : ℕ} (R : CircleTable N) (i j : Fin N) : Prop :=
  ∃ l, interferes R i l ∧ interferes R j l

def LocalAt {N : ℕ} (R : CircleTable N) (dist : Fin N → Fin N → ℝ) (h : ℝ) : Prop :=
  ∀ i j, h < dist i j → ¬ sharesSource R i j

def nodeDistance {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i : Fin N) (x : X) : ℝ := Metric.infDist x (P.node i)

def region {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i : Fin N) (d : ℝ) : Set X :=
  {x | nodeDistance P i x ∈ P.bands d}

def circleAverage {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) : CircleTable N :=
  fun i z => (∫ x in region P i d, P.outcome x z ∂P.zeta) /
    (P.zeta (region P i d)).toReal

def nodeSeparation {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i j : Fin N) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ P.node i, ∃ y ∈ P.node j, dist x y = r}

def ball {N : ℕ} (dist : Fin N → Fin N → ℝ) (i : Fin N) (r : ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun j => dist i j ≤ r)

def SpatialLocalConditions (P : PopulationSequence Space) : Prop :=
  (∃ b : ℝ, 0 < b ∧ ∀ᶠ N in atTop, ∀ x z, |(P N).outcome x z| < b) ∧
  (∃ h : ℝ → ℝ, (∀ d, 0 ≤ d → 0 ≤ h d) ∧
    ∀ d, 0 ≤ d → ∀ᶠ N in atTop,
      LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) (h d)) ∧
  (∃ c : ℝ → ℝ, ∀ r, 0 ≤ r → ∀ᶠ N in atTop, ∀ i,
    ((ball (nodeSeparation (P N)) i r).card : ℝ) ≤ c r)

def planePoint (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a,b]

def linePopulation {N : ℕ} (R : CircleTable N) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => {planePoint (10*(i : ℝ)) 0}
  node_nonempty := fun _ => Set.singleton_nonempty _
  zeta := ∑ i : Fin N, Measure.dirac (planePoint (10*(i : ℝ)) 0)
  outcome := fun x z => ∑ i : Fin N, if x = planePoint (10*(i : ℝ)) 0 then R i z else 0
  bands := fun d => Set.Icc 0 d

def threeTypeTable (N : ℕ) : CircleTable N := fun i _ => if i.val % 3 = 1 then 21/20 else 1

def threeTypePopulation (N : ℕ) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) := linePopulation (threeTypeTable N)

def Overlap (p : ∀ N, Fin N → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1/2 ∧ ∀ N i, ε < p N i ∧ p N i < 1-ε

def logistic (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)

def propensities {N k : ℕ} (O : Fin N → Fin k → ℝ) (θ : Fin k → ℝ) : Fin N → ℝ :=
  fun i => logistic (dot (O i) θ)

def WellDefined {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d : ℝ) : Prop :=
  ∀ i, MeasurableSet (region P i d) ∧ 0 < P.zeta (region P i d) ∧
    P.zeta (region P i d) < ⊤ ∧ ∀ z, IntegrableOn (fun x => P.outcome x z) (region P i d) P.zeta

def coin (p : ℝ) (a : Bool) : ℝ := if a then p else 1 - p

def designWeight {N : ℕ} (p : Fin N → ℝ) (z : Assignment N) : ℝ :=
  ∏ i, coin (p i) (z i)

def expect {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) : ℝ :=
  ∑ z, designWeight p z * X z

def marginal {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (i : Fin N)
    (a : Bool) : ℝ :=
  expect p (fun z => if z i = a then R i z else 0) / coin (p i) a

def nodeEffect {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (i : Fin N) : ℝ :=
  marginal p R i true - marginal p R i false

def residualEffect {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) : ℝ :=
  nodeEffect p R i - (g i true - g i false)

def homophilyQ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ B i, residualEffect p R g i * residualEffect p R g j) / N

def information {N k : ℕ} (p : Fin N → ℝ) (O : Fin N → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b => (∑ i, p i * (1-p i) * O i a * O i b) / N

def beta {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (a : Bool) : Fin k → ℝ :=
  (information p O)⁻¹ *ᵥ (fun j =>
    (∑ i, marginal p R i a * p i * (1-p i) * O i j) / N)

def printedFits {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (i : Fin N) (a : Bool) : ℝ := dot (O i) (beta p R O a)

def Nondegenerate (V : ℕ → ℝ) : Prop :=
  ∃ v : ℝ, 0 < v ∧ ∀ᶠ N : ℕ in atTop, v ≤ (N : ℝ) * V N

def cov {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) : ℝ :=
  expect p (fun z => X z * Y z) - expect p X * expect p Y

def variance {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) : ℝ := cov p X X

def augmented {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, (g i true - g i false + bit (z i) * (R i z - g i true) / p i -
    (1 - bit (z i)) * (R i z - g i false) / (1 - p i))) / N

def prob {N : ℕ} (p : Fin N → ℝ) (A : Assignment N → Prop) : ℝ :=
  expect p (fun z => if A z then 1 else 0)

def InProb (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N => prob (p N) (fun z => ε < |U N z|)) atTop (nhds 0)

def LittleOp (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) (r : ℕ → ℝ) : Prop :=
  InProb p (fun N z => U N z / r N)

def ht {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (z : Assignment N) : ℝ :=
  (∑ i, (bit (z i) * R i z / p i - (1 - bit (z i)) * R i z / (1 - p i))) / N

def fittedIPW {N k : ℕ} (R : CircleTable N) (O : Fin N → Fin k → ℝ)
    (θhat : Assignment N → Fin k → ℝ) (z : Assignment N) : ℝ :=
  ht (propensities O (θhat z)) R z

def circleSequence (P : PopulationSequence Space) (d : ℝ) (N : ℕ) : CircleTable N :=
  circleAverage (P N) d

def spatialNeighborhoods (P : PopulationSequence Space) (h : ℝ) (N : ℕ) : Fin N → Finset (Fin N) :=
  fun i => ball (nodeSeparation (P N)) i h

def scoreGamma {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) : Fin k → ℝ :=
  (information p O)⁻¹ *ᵥ (fun j =>
    (∑ i, ((1-p i)*marginal p R i true + p i*marginal p R i false)*O i j) / N)

def scoreFits {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (i : Fin N) (a : Bool) : ℝ :=
  let δ := printedFits p R O i true - printedFits p R O i false
  let L := dot (O i) (scoreGamma p R O)
  if a then p i * δ + p i * (1-p i) * L
  else -(1-p i) * δ + p i * (1-p i) * L

def BigOp (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N in atTop, prob (p N) (fun z => C * |r N| < |U N z|) < ε

def normalCDF (x : ℝ) : ℝ := (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal

def NormalLimit (p : ∀ N, Fin N → ℝ) (U : ∀ N, Assignment N → ℝ) : Prop :=
  ∀ x : ℝ, Tendsto (fun N => prob (p N) (fun z => U N z ≤ x)) atTop (nhds (normalCDF x))

def ame {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) : ℝ :=
  (∑ i, nodeEffect p R i) / N

def LiminfAtLeast (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, a-ε ≤ u N

def Conservative (coverage : ℕ → ℝ) (α : ℝ) : Prop :=
  LiminfAtLeast coverage (1-α)

def normalQuantile (a : ℝ) : ℝ := sInf {x : ℝ | a ≤ normalCDF x}

def rawSAH {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, (B i).card * (bit (z i) * (R i z-g i true)^2 / (p i)^2 +
    (1-bit (z i)) * (R i z-g i false)^2 / (1-p i)^2)) / (N : ℝ)^2

def fittedBeta {N k : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (a : Bool) (z : Assignment N) : Fin k → ℝ :=
  (information phat O)⁻¹ *ᵥ (fun j =>
    (∑ i, (if z i = a then R i z * coin (phat i) (!a) * O i j else 0)) / N)

def fittedGamma {N k : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (z : Assignment N) : Fin k → ℝ :=
  (information phat O)⁻¹ *ᵥ (fun j =>
    (∑ i, (bit (z i)*R i z*(1-phat i)/phat i +
      (1-bit (z i))*R i z*phat i/(1-phat i))*O i j) / N)

def fittedScoreFits {N k : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) (z : Assignment N) (i : Fin N) (a : Bool) : ℝ :=
  let δ := dot (O i) (fittedBeta phat R O true z) - dot (O i) (fittedBeta phat R O false z)
  let L := dot (O i) (fittedGamma phat R O z)
  if a then phat i*δ + phat i*(1-phat i)*L
    else -(1-phat i)*δ + phat i*(1-phat i)*L

def residualContrast {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) (z : Assignment N) : ℝ :=
  bit (z i) * (R i z - g i true) / p i -
  (1-bit (z i)) * (R i z - g i false) / (1-p i)

def oracleHAC {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, ∑ j ∈ B i, residualContrast p R g i z * residualContrast p R g j z) / (N : ℝ)^2

def armSign (a : Bool) : ℝ := if a then 1 else -1

def pairMarginal {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ)
    (i j : Fin N) (a b : Bool) : ℝ :=
  expect p (fun z => if z i = a ∧ z j = b then X z else 0) /
    (coin (p i) a * coin (p j) b)

def secondMomentBound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  ((∑ i, (marginal p (fun i z => (R i z - g i true)^2) i true / p i +
    marginal p (fun i z => (R i z - g i false)^2) i false / (1-p i))) +
    ∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
      armSign a * armSign b * pairMarginal p
        (fun z => (R i z - g i a)*(R j z - g j b)) i j a b) / (N : ℝ)^2

def activeGroup (N : ℕ) (i : Fin N) : Prop := i.val % 8 < 2
end
end SAP.P004a
