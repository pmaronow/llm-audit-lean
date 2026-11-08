import SAP.P004a.Defs.Part1

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

def activeO (N : ℕ) (i : Fin N) : Fin 2 → ℝ :=
  if activeGroup N i then ![1,0] else ![0,1]

def activeTheta : Fin 2 → ℝ := ![0, -Real.log 9]

def activeParameterSet : Set (Fin 2 → ℝ) := {θ | ∀ j, -Real.log 19 ≤ θ j ∧ θ j ≤ Real.log 19}

def activeTable (N : ℕ) : CircleTable N :=
  fun i z => (if i.val % 8 = 0 then 1 else if i.val % 8 = 1 then -1 else 0) * bit (z i)

def activePopulation (N : ℕ) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) := linePopulation (activeTable N)

def armCount {N : ℕ} (z : Assignment N) (a : Bool) : ℝ :=
  ∑ i, if z i = a then (1 : ℝ) else 0

def weightedEpsilon {N : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (z : Assignment N) (i : Fin N) : ℝ :=
  armCount z true / N * bit (z i) / phat i * (R i z-g i true) +
  armCount z false / N * (1-bit (z i)) / (1-phat i) * (R i z-g i false)

def printedSAH {N : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, (B i).card * (bit (z i) * (weightedEpsilon phat R g z i)^2 / (phat i)^2 +
    (1-bit (z i)) * (weightedEpsilon phat R g z i)^2 / (1-phat i)^2)) / (N : ℝ)^2

def sahLimit {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, (B i).card * (marginal p (fun i z => (R i z-g i true)^2) i true / p i +
    marginal p (fun i z => (R i z-g i false)^2) i false / (1-p i))) / (N : ℝ)^2

def areaWitnessAssignment : Assignment 2 := ![true, false]

def areaBinaryCenter (i : Fin 2) : EuclideanSpace ℝ (Fin 2) := planePoint (100*(i : ℝ)) 0

def angularFraction (c x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  let θ := Complex.arg ((x 0-c 0 : ℝ) + (x 1-c 1 : ℝ)*Complex.I)
  (if θ < 0 then θ+2*Real.pi else θ)/(2*Real.pi)

def areaBinaryShare (c x : EuclideanSpace ℝ (Fin 2)) (a : Bool) : ℝ :=
  if a then (if dist x c ≤ 1 then 1/50 else 273/2500) else 1/10

def areaBinaryPopulation : SpatialPopulation 2 (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => Metric.closedBall (areaBinaryCenter i) 1
  node_nonempty := fun i => ⟨areaBinaryCenter i, Metric.mem_closedBall_self (by norm_num)⟩
  zeta := volume
  outcome := fun x z =>
    if dist x (areaBinaryCenter 0) ≤ 6 then
      (if angularFraction (areaBinaryCenter 0) x < areaBinaryShare (areaBinaryCenter 0) x (z 0) then 1 else 0)
    else if dist x (areaBinaryCenter 1) ≤ 6 then
      (if angularFraction (areaBinaryCenter 1) x < areaBinaryShare (areaBinaryCenter 1) x (z 1) then 1 else 0)
    else 0
  bands := fun d => if d = 0 then {0} else if d = 6 then Set.Icc 0 5 else Set.Ioc (d-1) d

def finiteAverage {A : Type*} [Fintype A] (mass : A → ℝ) (Y : A → ℝ) : ℝ :=
  (∑ x, mass x * Y x) / (∑ x, mass x)

def areaWitnessMass (j : Fin 6) (x : Fin 3) : ℝ :=
  (2*(j : ℝ)+1) * (if j = 0 then (![1/50, 2/25, 9/10] : Fin 3 → ℝ) x
    else (![1/10, 23/2500, 2227/2500] : Fin 3 → ℝ) x)

def areaWitnessOutcome (j : Fin 6) (a : Bool) (x : Fin 3) : ℝ :=
  if j = 0 then if a then (if x = 0 then 1 else 0)
    else (if x = 0 ∨ x = 1 then 1 else 0)
  else if a then (if x = 0 ∨ x = 1 then 1 else 0)
    else (if x = 0 then 1 else 0)

def areaWitnessTable (j : Fin 6) : CircleTable 2 :=
  fun i z => finiteAverage (areaWitnessMass j) (areaWitnessOutcome j (z i))

def armMean {N : ℕ} (R : CircleTable N) (z : Assignment N) (a : Bool) : ℝ :=
  (∑ i, if z i = a then R i z else 0) / armCount z a

def hajek {N : ℕ} (R : CircleTable N) (z : Assignment N) : ℝ :=
  armMean R z true - armMean R z false

def starAssignment20 : Assignment 20 :=
  ![true,true,false,true,false, false,true,false,true,false,
    true,true,false,true,false, false,true,false,true,false]

def starY : Fin 5 → ℝ := ![0,1,1,-1,-1]

def starBlockTable (m : ℕ) : CircleTable (5*m) :=
  fun i _ => starY ⟨i.val%5, Nat.mod_lt _ (by omega)⟩

def lambda {N : ℕ} (z : Assignment N) (i : Fin N) : ℝ :=
  bit (z i) / armCount z true - (1-bit (z i)) / armCount z false

def kernelVariance {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, lambda z i * lambda z j * e i * e j * Q i j

def residual {N : ℕ} (R : CircleTable N) (z : Assignment N) (i : Fin N) : ℝ :=
  R i z - armMean R z (z i)

def starKernel : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of (fun i j => if i = j ∨ i = 0 ∨ j = 0 then 1 else 0)

def starNegativeVector : Fin 5 → ℝ := ![2,-1,-1,-1,-1]

def starPD : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of (fun i j => starKernel i j+starNegativeVector i*starNegativeVector j/8)

def starBlockKernel (m : ℕ) (pd : Bool) : Matrix (Fin (5*m)) (Fin (5*m)) ℝ :=
  Matrix.of (fun i j => if i.val/5 = j.val/5 then
    (if pd then starPD else starKernel) ⟨i.val%5, Nat.mod_lt _ (by omega)⟩
      ⟨j.val%5, Nat.mod_lt _ (by omega)⟩ else 0)

def designMatrix {N : ℕ} (z : Assignment N) : Matrix (Fin N) (Fin 2) ℝ :=
  fun i a => if a = 0 then 1 else bit (z i)

def residualMaker {N : ℕ} (z : Assignment N) : Matrix (Fin N) (Fin N) ℝ :=
  let X := designMatrix z
  1 - X * (X.transpose * X)⁻¹ * X.transpose

def adjustmentMatrix {N : ℕ} (z : Assignment N)
    (Q : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (armCount z true * armCount z false / N) •
    (residualMaker z * Matrix.of (fun i j => lambda z i * lambda z j * Q i j) * residualMaker z)

def adjustmentMu {N : ℕ} (z : Assignment N) (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  Matrix.trace (adjustmentMatrix z Q)

def starPoint {N : ℕ} (i : Fin N) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (![10*((i.val/5 : ℕ) : ℝ) +
    (if i.val%5 = 1 then 1 else if i.val%5 = 3 then -1 else 0),
    if i.val%5 = 2 then 1 else if i.val%5 = 4 then -1 else 0] : Fin 2 → ℝ)

def starPopulation (N : ℕ) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => {starPoint i}
  node_nonempty := fun _ => Set.singleton_nonempty _
  zeta := ∑ i : Fin N, Measure.dirac (starPoint i)
  outcome := fun x _ => ∑ i : Fin N, if x = starPoint i then
    starY ⟨i.val%5, Nat.mod_lt _ (by omega)⟩ else 0
  bands := fun d => Set.Icc 0 d

def barMu {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (a : Bool) : ℝ :=
  (∑ i, marginal p R i a) / N

def linearHajek {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) : Assignment N → ℝ :=
  augmented p R (fun _ a => barMu p R a)

def uniformDistanceKernel {N : ℕ} (D : Fin N → Fin N → ℝ) (h : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => if D i j ≤ h then 1 else 0)

def adjustmentNu {N : ℕ} (z : Assignment N) (Q : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  2 * Matrix.trace (adjustmentMatrix z Q * adjustmentMatrix z Q)

def studentDensity (ν x : ℝ) : ℝ :=
  Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2)) *
    (1+x^2/ν)^(-(ν+1)/2)

def studentCDF (ν x : ℝ) : ℝ := ∫ t in Set.Iic x, studentDensity ν t

def studentQuantile (ν α : ℝ) : ℝ := sInf {x : ℝ | α ≤ studentCDF ν x}

def spectralKernel {N : ℕ} (values : Fin N → ℝ)
    (vectors : Matrix (Fin N) (Fin N) ℝ) (trim : Bool) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ k, (if trim then max (values k) 0 else values k) * vectors i k * vectors j k

def cappedVariance (V μ : ℝ) : ℝ := if 0 < μ then V / min μ 1 else V

def boundaryMLE {N : ℕ} (z : Assignment N) : ℝ :=
  let q := armCount z true / N
  if q ≤ 1/2 then 0 else if logistic 1 ≤ q then 1 else Real.log (q/(1-q))

def logisticScore {N k : ℕ} (p : Fin N → ℝ) (O : Fin N → Fin k → ℝ)
    (z : Assignment N) : Fin k → ℝ := fun j => (∑ i, (bit (z i)-p i)*O i j) / N

def printedObsHT {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (z : Assignment N) : ℝ :=
  (∑ i, (bit (z i) * R i z / p i - (1 - bit (z i)) * R i z / p i)) / N

def SharpNull {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) : Prop :=
  ∀ x z, P.outcome x z = P.outcome x (fun _ => false)

def eightNodeNullPoint (i : Fin 8) : EuclideanSpace ℝ (Fin 2) := planePoint (3*((i : ℝ)+1)) 0

def eightNodeNullTable : CircleTable 8 := fun i _ => (2 : ℝ)^i.val/128

def eightNodeNullPopulation : SpatialPopulation 8 (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => {eightNodeNullPoint i}
  node_nonempty := fun _ => Set.singleton_nonempty _
  zeta := ∑ i : Fin 8, Measure.dirac (eightNodeNullPoint i)
  outcome := fun x z => ∑ i : Fin 8, if x = eightNodeNullPoint i then eightNodeNullTable i z else 0
  bands := fun d => Set.Icc 0 d

def eightNodeObserved : Assignment 8 := fun _ => false

def eightNodeResampled : Assignment 8 := fun i => decide (i.val < 7)

def mcDrawWeight {N : ℕ} (p : Fin N → ℝ) {P : ℕ}
    (draws : Fin (P+1) → Assignment N) : ℝ := ∏ r, designWeight p (draws r)

def eightNodeMCDraws : Fin 101 → Assignment 8 :=
  fun r => if r = 0 then eightNodeObserved else eightNodeResampled

def mcExceedances {N P : ℕ} (T : Assignment N → ℝ)
    (draws : Fin (P+1) → Assignment N) : ℕ :=
  (Finset.univ.filter (fun r : Fin (P+1) => r ≠ 0 ∧ |T (draws 0)| ≤ |T (draws r)|)).card

def mcPlusPvalue {N P : ℕ} (T : Assignment N → ℝ)
    (draws : Fin (P+1) → Assignment N) : ℝ := (1 + mcExceedances T draws : ℝ) / (P+1)

def eightNodeMCNumerator : ℕ :=
  ∑ m ∈ Finset.range 128, ∑ b ∈ Finset.range 6,
    Nat.choose 100 b * (m+1)^b * (128-(m+1))^(100-b)

def eightNodeMCSize : ℝ :=
  (eightNodeMCNumerator : ℝ) / (128 : ℝ)^101

def shellNodePoint (i : Fin 2) : EuclideanSpace ℝ (Fin 2) :=
  planePoint (3*(i : ℝ)) 0

def shellAtomPoint (x : Fin 3) : EuclideanSpace ℝ (Fin 2) :=
  if x = 0 then planePoint 0 4 else if x = 1 then planePoint 3 4 else planePoint 3 (-4)

def shellWitnessEffect (i : Fin 2) (x : Fin 3) : ℝ :=
  if i = 0 then (if x = 0 then 0 else 1) else (if x = 0 then -1 else 0)

def shellWitnessOutcome (x : Fin 3) (z : Assignment 2) : ℝ :=
  1 + ∑ i, bit (z i) * shellWitnessEffect i x

def shellSpatialPopulation (D : Set ℝ) : SpatialPopulation 2 (EuclideanSpace ℝ (Fin 2)) where
  node := fun i => {shellNodePoint i}
  node_nonempty := fun _ => Set.singleton_nonempty _
  zeta := ∑ x : Fin 3, Measure.dirac (shellAtomPoint x)
  outcome := fun y z => 1 + ∑ x : Fin 3,
    if y = shellAtomPoint x then shellWitnessOutcome x z-1 else 0
  bands := fun _ => D

def pointEffect {N : ℕ} {A : Type*} [MetricSpace A] [MeasurableSpace A]
    (P : SpatialPopulation N A) (p : Fin N → ℝ) (i : Fin N) (x : A) : ℝ :=
  marginal p (fun _ z => P.outcome x z) i true -
    marginal p (fun _ z => P.outcome x z) i false

def supportedShellMass {A : Type*} [Fintype A] {m N : ℕ}
    (mass : A → ℝ) (shell : Fin N → A → Fin m) (i : Fin N) (k : Fin m) : ℝ :=
  ∑ x, if shell i x = k then mass x else 0
end
end SAP.P004a
