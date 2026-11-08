import SAP.P045a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a
noncomputable section

def allTreated {n : ℕ} (A : Fin n → Fin n → Bool) (z : Assignment n) (i : Fin n) : Prop :=
  neighborhoodCount A z i = (neighborhood A i).card

def allControl {n : ℕ} (A : Fin n → Fin n → Bool) (z : Assignment n) (i : Fin n) : Prop :=
  neighborhoodCount A z i = 0

def badAllControl {n : ℕ} (A : Fin n → Fin n → Bool) (z : Assignment n) (i : Fin n) : Prop :=
  neighborhoodCount A z i < (neighborhood A i).card

def fullHT {n : ℕ} (p : Assignment n → ℝ) (A : Fin n → Fin n → Bool)
    (Y : Fin n → Assignment n → ℝ) (correct : Bool) (z : Assignment n) : ℝ :=
  by classical exact mean (fun i =>
    (if allTreated A z i then Y i z / prob p (fun v => allTreated A v i) else 0) -
    (if (if correct then allControl A z i else badAllControl A z i) then
      Y i z / prob p (fun v => if correct then allControl A v i else badAllControl A v i) else 0))

def allVsNone {n : ℕ} (Y : Fin n → Assignment n → ℝ) : ℝ :=
  mean (fun i => Y i (fun _ => true) - Y i (fun _ => false))

def edge2 (i j : Fin 2) : Bool := decide (i ≠ j)

def linear2 (_i : Fin 2) (z : Assignment 2) : ℝ := 1 + bit (z 0) + bit (z 1)

def threshold2 (_i : Fin 2) (z : Assignment 2) : ℝ :=
  1 + 2 * (if z 0 = true ∧ z 1 = true then 1 else 0)

def upperCells (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (fun j => (List.range n).filterMap
    (fun i => if i < j then some (i,j) else none))

def lowerCells (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (fun j => (List.range n).filterMap
    (fun i => if j < i then some (i,j) else none))

def faultyCopy (n : ℕ) (M : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if j < i then
    let cell := (upperCells n)[(lowerCells n).idxOf (i,j)]?.getD (0,0)
    M cell.1 cell.2
  else M i j

def correctedCopy (M : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if j < i then M j i else M i j

def singleEdge4 (i j : ℕ) : ℝ :=
  if (i=0 ∧ j=3) ∨ (i=3 ∧ j=0) then 1 else 0

def matrixExposure {n : ℕ} (M : ℕ → ℕ → ℝ) (z : Assignment n) (i : Fin n) : Exposure :=
  if z i then
    if 0 < ∑ j, bit (z j) * M j.val i.val then .d11 else .d10
  else if 0 < ∑ j, bit (z j) * M j.val i.val then .d01 else .d00

def upperInput4 (u : Fin 6 → Bool) (i j : ℕ) : ℝ :=
  if i < j then bit (u ⟨(upperCells 4).idxOf (i,j) % 6, Nat.mod_lt _ (by decide)⟩)
  else if j < i then bit (u ⟨(upperCells 4).idxOf (j,i) % 6, Nat.mod_lt _ (by decide)⟩)
  else 0

def htObserved {n : ℕ} (p : Assignment n → ℝ)
    (D : Assignment n → Fin n → Exposure) (Y : Fin n → Assignment n → ℝ)
    (d : Exposure) (z : Assignment n) : ℝ :=
  ∑ i, if D z i = d then Y i z / exposureProb p D i d else 0

def printedAdj : Fin 10 → Fin 10 → Bool :=
  ![![false,true,true,false,true,false,false,false,false,false],
    ![true,false,true,true,false,false,false,false,false,true],
    ![true,true,false,true,true,true,false,false,true,false],
    ![false,true,true,false,true,true,true,false,false,false],
    ![true,false,true,true,false,true,false,true,false,false],
    ![false,false,true,true,true,false,false,false,false,false],
    ![false,false,false,true,false,false,false,true,true,false],
    ![false,false,false,false,true,false,true,false,true,true],
    ![false,false,true,false,false,false,true,true,false,true],
    ![false,true,false,false,false,false,false,true,true,false]]

def printedEdges : Finset (Fin 10 × Fin 10) :=
  univ.filter (fun e => e.1 < e.2 ∧ printedAdj e.1 e.2 = true)

def deletionMasks (d : ℕ) : Finset (Finset (Fin 10 × Fin 10)) := printedEdges.powersetCard d

def deletedAdj (R : Finset (Fin 10 × Fin 10)) (i j : Fin 10) : Bool :=
  printedAdj i j && decide ((i,j) ∉ R ∧ (j,i) ∉ R)

def measuredDegree (R : Finset (Fin 10 × Fin 10)) (i : Fin 10) : ℕ :=
  (univ.filter (fun j => deletedAdj R i j = true)).card

def biasBaseline (i : Fin 10) : ℝ := if i=1 then 5/2 else 1

def deletionHajek (R : Finset (Fin 10 × Fin 10)) (t : Fin 10) : ℝ :=
  let S := univ.filter (fun i => deletedAdj R t i = true)
  let C := univ \ insert t S
  ((∑ i ∈ S, ((5/4)*biasBaseline i)/(measuredDegree R i)) /
    (∑ i ∈ S, 1/(measuredDegree R i : ℝ))) -
  ((∑ i ∈ C, biasBaseline i*(1+(if printedAdj t i then (1/4 : ℝ) else 0))/
      (9-(measuredDegree R i : ℝ))) /
    (∑ i ∈ C, 1/(9-(measuredDegree R i : ℝ))))

def deletionBias (d : ℕ) : ℝ := average (deletionMasks d) (fun R => mean (deletionHajek R)) - 23/80

def separated {V : Type*} (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (ε : ℕ∞) ≤ d s t

def covers {V : Type*} (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) : Prop :=
  ∀ v, v ∉ S → ∃ s ∈ S, d s v ≤ ((ε-1 : ℕ) : ℕ∞)

def epsilonNet {V : Type*} (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) : Prop :=
  separated d ε S ∧ covers d ε S

def marked {V : Type*} [Fintype V] (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) : Finset V :=
  univ.filter (fun v => ∃ s ∈ S, d s v ≤ ((ε-1 : ℕ) : ℕ∞))

def greedyRun {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → V → ℕ∞) (ε : ℕ) (cs : List V) : Prop :=
  ∀ k : Fin cs.length, cs.get k ∉ marked d ε (cs.take k.val).toFinset

def pathDistance {n : ℕ} (i j : Fin n) : ℕ∞ := (Nat.dist i.val j.val : ℕ)

def centreDraw {n : ℕ} (d : Fin n → Fin n → ℕ∞) (ε : ℕ) (coded : Bool)
    (S : Finset (Fin n)) (v : Fin n) : ℝ :=
  let R := univ \ marked d ε S
  if coded = true ∧ R.card = 1 then
    let u := R.toList.head?.getD v
    if v.val ≤ u.val then 1/(u.val+1 : ℕ) else 0
  else if v ∈ R then 1/R.card else 0

def traceMass {n : ℕ} (d : Fin n → Fin n → ℕ∞) (ε : ℕ) (coded : Bool)
    (cs : List (Fin n)) : ℝ :=
  if (∀ k : Fin cs.length, marked d ε (cs.take k.val).toFinset ≠ univ) ∧
      marked d ε cs.toFinset = univ then
    ∏ k : Fin cs.length, centreDraw d ε coded (cs.take k.val).toFinset (cs.get k)
  else 0

def terminalCentres {n : ℕ} (d : Fin n → Fin n → ℕ∞) (ε : ℕ)
    (coded : Bool) (S : Finset (Fin n)) : ℝ :=
  ∑' t : ℕ, ∑ z : Fin t → Fin n,
    if (List.ofFn z).toFinset = S then traceMass d ε coded (List.ofFn z) else 0

def nearestCentre {n : ℕ} (d : Fin n → Fin n → ℕ∞)
    (S : Finset (Fin n)) (v : Fin n) : Option (Fin n) :=
  (S.toList.mergeSort (fun a b => decide (d a v < d b v ∨ (d a v = d b v ∧ a ≤ b)))).head?

def clusterProb {n : ℕ} (d : Fin n → Fin n → ℕ∞) (S : Finset (Fin n))
    (p : ℝ) (z : Assignment n) : ℝ :=
  prob (bernoulli p) (fun c => ∀ v, ∃ s, nearestCentre d S v = some s ∧ z v = c s)

def clusteredTreatment {n : ℕ} (d : Fin n → Fin n → ℕ∞) (coded : Bool)
    (p : ℝ) (z : Assignment n) : ℝ :=
  ∑ S : Finset (Fin n), terminalCentres d 3 coded S * clusterProb d S p z

def treatmentPairs : Finset (Fin 10 × Fin 10) := univ.filter (fun e => e.1 < e.2)

def pairAssignment (e : Fin 10 × Fin 10) : Assignment 10 := fun i => decide (i=e.1 ∨ i=e.2)

def pairExposureProb (A : Fin 10 → Fin 10 → Bool) (i : Fin 10) (d : Exposure) : ℝ :=
  average treatmentPairs (fun e => if exposure A (pairAssignment e) i = d then 1 else 0)

def cycle10 (i j : Fin 10) : Bool :=
  decide ((i.val+1)%10 = j.val ∨ (j.val+1)%10 = i.val)

def cycleOut (_i : Fin 10) (d : Exposure) : ℝ :=
  match d with | .d11 => 2 | .d10 => 1 | .d01 => 1 | .d00 => 0

def cycleL (e : Fin 10 × Fin 10) : ℝ :=
  mean (fun i => if pairAssignment e i then cycleOut i (exposure cycle10 (pairAssignment e) i)/(1/5) else 0)

def cycleR (e : Fin 10 × Fin 10) : ℝ :=
  mean (fun i =>
    (if exposure cycle10 (pairAssignment e) i = .d11 then 2/pairExposureProb cycle10 i .d11 else 0) +
    (if exposure cycle10 (pairAssignment e) i = .d10 then 1/pairExposureProb cycle10 i .d10 else 0))

def ownProb {n : ℕ} (p : Assignment n → ℝ) (i : Fin n) : ℝ := prob p (fun z => z i = true)

def naiveTreated {n : ℕ} (p : Assignment n → ℝ) (A : Fin n → Fin n → Bool)
    (y : Fin n → Exposure → ℝ) (z : Assignment n) : ℝ :=
  mean (fun i => if z i then y i (exposure A z i)/ownProb p i else 0)

end
end SAP.P045a
