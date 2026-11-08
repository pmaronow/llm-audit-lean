import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

abbrev Vec (k : ℕ) := Fin k → ℝ

abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℝ

def outer {k : ℕ} (x y : Vec k) : Mat k := fun a b => x a * y b

def dot {k : ℕ} (x y : Vec k) : ℝ := ∑ a, x a * y a

def dyads (N : ℕ) : Finset (Finset (Fin N)) := univ.powersetCard 2

abbrev Dyad (N : ℕ) := ↥(dyads N)

def members {N : ℕ} (d : Dyad N) : Finset (Fin N) := d.val

theorem members_card {N : ℕ} (d : Dyad N) : (members d).card = 2 := by
  exact (mem_powersetCard.mp d.property).2

def neighbors {N : ℕ} (d : Dyad N) : Finset (Dyad N) :=
  univ.filter (fun q => q ≠ d ∧ (members d ∩ members q).Nonempty)

def overlap {N : ℕ} (d q : Dyad N) : Prop := (members d ∩ members q).Nonempty

instance {N : ℕ} (d q : Dyad N) : Decidable (overlap d q) :=
  inferInstanceAs (Decidable ((members d ∩ members q).Nonempty))

def sandwich {k : ℕ} (P M : Mat k) : Mat k := P * M * P

def score {k : ℕ} (x : Vec k) (r : ℝ) : Vec k := r • x

def meat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) : Mat k :=
  ∑ d, ∑ f, if (s d ∩ s f).Nonempty then outer (q d) (q f) else 0

def unitScore {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) (i : V) : Vec k :=
  ∑ d, if i ∈ s d then q d else 0

def dyadMeat {E : Type*} [Fintype E] {k : ℕ} (q : E → Vec k) : Mat k :=
  ∑ d, outer (q d) (q d)

def individualMeat {E : Type*} [Fintype E] {k : ℕ}
    (T : E → ℕ) (q : (d : E) → Fin (T d) → Vec k) : Mat k :=
  ∑ d, ∑ t, outer (q d t) (q d t)

def nonincidentMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (T : E → ℕ)
    (q : (d : E) → Fin (T d) → Vec k) (i : V) : Mat k :=
  ∑ d, if i ∉ s d then ∑ t, outer (q d t) (q d t) else 0

def clusterMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (T : E → ℕ)
    (q : (d : E) → Fin (T d) → Vec k) (i : V) : Mat k :=
  outer (unitScore s (fun d => ∑ t, q d t) i)
    (unitScore s (fun d => ∑ t, q d t) i) + nonincidentMeat s T q i

def orderedNonincidentMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (T : E → ℕ)
    (q : (d : E) → Fin (T d) → Vec k) (i : V) : Mat k :=
  ∑ _orientation : Fin 2, nonincidentMeat s T q i

def orderedClusterMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (T : E → ℕ)
    (q : (d : E) → Fin (T d) → Vec k) (i : V) : Mat k :=
  outer (unitScore s (fun d => ∑ t,q d t) i) (unitScore s (fun d => ∑ t,q d t) i) +
    orderedNonincidentMeat s T q i

def crossUnitMeat {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) (i : V) : Mat k :=
  ∑ d, ∑ f, if d ≠ f ∧ i ∈ s d ∧ i ∈ s f then outer (q d) (q f) else 0

def incidentDiagonalMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) (i : V) : Mat k :=
  ∑ d, if i ∈ s d then outer (q d) (q d) else 0

/-- Paper units 1,...,4 are represented by 0,...,3, in the printed six-dyad order. -/
def sixMembers : Fin 6 → Finset (Fin 4) := ![{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}]

def orderedWitness : Fin 6 → Vec 1 := fun d => ![(![1,2,3,4,5,6] : Fin 6 → ℝ) d]

def sampleGram {E : Type*} [Fintype E] {k : ℕ} (X : E → Vec k) : Mat k :=
  ∑ d, outer (X d) (X d)

def sampleOLS {E : Type*} [Fintype E] {k : ℕ} (X : E → Vec k) (Y : E → ℝ) : Vec k :=
  (sampleGram X)⁻¹.mulVec (∑ d, score (X d) (Y d))

def fittedResidual {E : Type*} [Fintype E] {k : ℕ}
    (X : E → Vec k) (Y : E → ℝ) (d : E) : ℝ := Y d - dot (X d) (sampleOLS X Y)

def sampleVariance {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (X : E → Vec k) (Y : E → ℝ) : Mat k :=
  sandwich (sampleGram X)⁻¹ (meat s (fun d => score (X d) (fittedResidual X Y d)))

def negativeX : Fin 6 → Vec 2 := fun d => ![1, (![1,2,3,1,2,1] : Fin 6 → ℝ) d]

def negativeY : Fin 6 → ℝ := ![4,3,5,3,3,4]

def negativeE : Fin 6 → ℝ := ![3/5,-4/5,4/5,-2/5,-4/5,3/5]

def standardError (v : ℝ) : Option ℝ := if 0 ≤ v then some (Real.sqrt v) else none

/-- Table 1 columns H,C,D. Rows: Alliances, Power ratio, Lower democracy,
Lower dependence, International organizations, Non-contiguity, Log distance,
Only minor powers, Constant. Entries are exact printed decimals. -/
def tableSE : List (ℚ × ℚ × ℚ) :=
  [(69/1000,175/1000,265/1000),(20/1000,47/1000,70/1000),
   (5/1000,10/1000,15/1000),(10734/1000,17560/1000,24749/1000),
   (2/1000,5/1000,8/1000),(74/1000,181/1000,185/1000),
   (26/1000,68/1000,102/1000),(78/1000,188/1000,344/1000),
   (211/1000,562/1000,840/1000)]

def expit (t : ℝ) : ℝ := 1 / (1 + Real.exp (-t))

def logisticScore {k : ℕ} (x : Vec k) (y : ℝ) (β : Vec k) : Vec k :=
  score x (y - expit (dot x β))

def logisticBread {E : Type*} [Fintype E] {k : ℕ}
    (X : E → Vec k) (β : Vec k) : Mat k :=
  ∑ d, (expit (dot (X d) β) * (1 - expit (dot (X d) β))) • outer (X d) (X d)

def logLikelihood {k : ℕ} (x : Vec k) (y : ℝ) (β : Vec k) : ℝ :=
  y * dot x β - Real.log (1 + Real.exp (dot x β))

def logisticNegativeJacobian {k : ℕ} (x : Vec k) (y : ℝ) (β : Vec k) : Mat k :=
  fun a b => -deriv (fun t => logisticScore x y (Function.update β b t) a) (β b)

end SAP.P018b
