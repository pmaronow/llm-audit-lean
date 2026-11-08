import SAP.P045b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P045b
open Finset
open scoped BigOperators
noncomputable section

structure Network (n : ℕ) where
  adj : Fin n → Fin n → Bool
  symmetric : ∀ i j, adj i j = adj j i
  loopless : ∀ i, adj i i = false

def firstStageSets (G C : ℕ) : Finset (Finset (Fin G)) := univ.powersetCard C

abbrev GroupAssignments {G : ℕ} (n : Fin G → ℕ) := (g : Fin G) → Assignment (n g)

def selectedLaw {G : ℕ} (n : Fin G → ℕ) (C : ℕ)
    (q : (g : Fin G) → Assignment (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : ℝ :=
  if w.1 ∈ firstStageSets G C then
    (1 / (firstStageSets G C).card) * ∏ g, q g (w.2 g) else 0

def selectedMean {G : ℕ} {n : Fin G → ℕ} (C : ℕ)
    (X : (g : Fin G) → Assignment (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : ℝ :=
  (∑ g ∈ w.1, X g (w.2 g)) / C

def crMass (n k : ℕ) (z : Assignment n) : ℝ :=
  if z ∈ fixedAssignments n k then 1 / (fixedAssignments n k).card else 0

def rawSampleVar {I : Type*} (S : Finset I) (x : I → ℝ) : ℝ :=
  (∑ i ∈ S, (x i - average S x)^2) / ((S.card : ℝ)-1)

def treatedSet {n : ℕ} (z : Assignment n) : Finset (Fin n) := univ.filter (fun i => z i = true)

def directGroup {n : ℕ} (a b : Fin n → ℝ) (z : Assignment n) : ℝ :=
  average (treatedSet z) a - average (univ \ treatedSet z) b

def droppedWithin {n : ℕ} (a b : Fin n → ℝ) (z : Assignment n) : ℝ :=
  (if 2 ≤ (treatedSet z).card then rawSampleVar (treatedSet z) a / (treatedSet z).card else 0) +
  (if 2 ≤ (univ \ treatedSet z).card then
    rawSampleVar (univ \ treatedSet z) b / (univ \ treatedSet z).card else 0)

def directVarianceEstimate {G : ℕ} {n : Fin G → ℕ} (C : ℕ)
    (a b : (g : Fin G) → Fin (n g) → ℝ)
    (w : Finset (Fin G) × GroupAssignments n) : ℝ :=
  ((1 - (C : ℝ)/G)/C) * rawSampleVar w.1 (fun g => directGroup (a g) (b g) (w.2 g)) +
    (∑ g ∈ w.1, droppedWithin (a g) (b g) (w.2 g)) / ((C : ℝ)*G)

def neighborhood {n : ℕ} (A : Fin n → Fin n → Bool) (i : Fin n) : Finset (Fin n) :=
  insert i (univ.filter (fun j => A i j = true))

def neighborhoodCount {n : ℕ} (A : Fin n → Fin n → Bool)
    (z : Assignment n) (i : Fin n) : ℕ :=
  ((neighborhood A i).filter (fun j => z j = true)).card

def badAllControl {n : ℕ} (A : Fin n → Fin n → Bool) (z : Assignment n) (i : Fin n) : Prop :=
  neighborhoodCount A z i < (neighborhood A i).card

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

def withinThree (S : Finset (Fin 9)) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, pathDistance s t ≤ 3

def hierarchyLaw {G : ℕ} (n : Fin G → ℕ) (S : Design (Assignment G)) (ψ φ : ℝ)
    (w : Assignment G × GroupAssignments n) : ℝ :=
  S.mass w.1 * ∏ g, bernoulli (if w.1 g then ψ else φ) (w.2 g)

def regimeGroups {G : ℕ} (s : Assignment G) (high : Bool) : Finset (Fin G) :=
  univ.filter (fun g => s g=high)

def hierarchyArm {G : ℕ} {n : Fin G → ℕ}
    (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ)
    (high b : Bool) (w : Assignment G × GroupAssignments n) : ℝ :=
  average (regimeGroups w.1 high) (fun g => armMean (y g) b (w.2 g))

def hierarchyDomain {G : ℕ} {n : Fin G → ℕ}
    (high b : Bool) (w : Assignment G × GroupAssignments n) : Prop :=
  (regimeGroups w.1 high).Nonempty ∧ ∀ g ∈ regimeGroups w.1 high, armExists b (w.2 g)

def hierarchyTarget {G : ℕ} {n : Fin G → ℕ}
    (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ) (p : ℝ) (b : Bool) : ℝ :=
  mean (fun g => mean (fun i => marginal (bernoulli p) (y g) i b))

def hierarchyOverall {G : ℕ} {n : Fin G → ℕ}
    (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ)
    (high : Bool) (w : Assignment G × GroupAssignments n) : ℝ :=
  average (regimeGroups w.1 high) (fun g => groupOverall (y g) (w.2 g))

instance {V : Type*} [Fintype V] [DecidableEq V] (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) :
    Decidable (separated d ε S) :=
  inferInstanceAs (Decidable (∀ s ∈ S, ∀ t ∈ S, s ≠ t → (ε : ℕ∞) ≤ d s t))
instance {V : Type*} [Fintype V] [DecidableEq V] (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) :
    Decidable (covers d ε S) :=
  inferInstanceAs (Decidable (∀ v, v ∉ S → ∃ s ∈ S, d s v ≤ ((ε-1 : ℕ) : ℕ∞)))
instance {V : Type*} [Fintype V] [DecidableEq V] (d : V → V → ℕ∞) (ε : ℕ) (S : Finset V) :
    Decidable (epsilonNet d ε S) :=
  inferInstanceAs (Decidable (separated d ε S ∧ covers d ε S))

end
end SAP.P045b
