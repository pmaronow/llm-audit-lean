import SAP.P044.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

def insertOwn {N : ℕ} (i : Fin N) (a : Bool) (u : {j : Fin N // j ≠ i} → Bool) :
    Assignment N := fun j => if h : j = i then a else u ⟨j, h⟩

def NoInterference {N : ℕ} (y : Fin N → Assignment N → ℝ) : Prop :=
  ∀ i a u v, y i (insertOwn i a u) = y i (insertOwn i a v)

def Interference {N : ℕ} (y : Fin N → Assignment N → ℝ) : Prop :=
  ∃ i a u v, y i (insertOwn i a u) ≠ y i (insertOwn i a v)

def completeProfiles (N M : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powersetCard M

def completeProbability (N M : ℕ) (A : Adjacency N) (i : Fin N) (a : Exposure) : ℚ :=
  ((completeProfiles N M).filter (fun s => exposure A (fun j => decide (j ∈ s)) i = a)).card /
    ((completeProfiles N M).card : ℚ)

def starAdj : Adjacency 4 := fun i j => decide (i ≠ j ∧ (i = 0 ∨ j = 0))

def starAssignments : Fin 6 → Assignment 4 :=
  ![![false,false,true,true], ![false,true,false,true], ![false,true,true,false],
    ![true,false,false,true], ![true,false,true,false], ![true,true,false,false]]

def starA : Fin 4 → Exposure → ℚ := fun _ _ => 1

def starB : Fin 4 → Exposure → ℚ := fun i a => if i = 0 ∧ a = .d00 then 5 else 1

def cycle8Adj : Adjacency 8 := fun i j => decide
  ((i.val + 1) % 8 = j.val ∨ (j.val + 1) % 8 = i.val)

def cycle8Assignments (r : Fin 8) : Assignment 8 := fun i =>
  decide ((i.val + r.val) % 8 ∈ ({0,1,3} : Finset ℕ))

def exposureCount {R N : ℕ} {D : Type*} [DecidableEq D]
    (f : Fin R → Fin N → D) (i : Fin N) (a : D) : ℕ :=
  (Finset.univ.filter (fun r => f r i = a)).card

def jointCount {R N : ℕ} {D : Type*} [DecidableEq D]
    (f : Fin R → Fin N → D) (i j : Fin N) (a b : D) : ℕ :=
  (Finset.univ.filter (fun r => f r i = a ∧ f r j = b)).card

def smoothedWeight {R N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    (f : Fin R → Fin N → D) (i : Fin N) (a : D) : K :=
  ((exposureCount f i a : K) + 1) / ((R : K) + 1)

def smoothedJoint {R N : ℕ} {D K : Type*} [DecidableEq D] [Field K]
    (f : Fin R → Fin N → D) (i j : Fin N) (a b : D) : K :=
  if a = b then ((jointCount f i j a b : K) + if i = j then 1 else 0) / ((R : K) + 1)
  else (jointCount f i j a b : K) / R

def cycle8Y : Fin 8 → Exposure → ℚ := fun _ a =>
  match a with | .d11 => 2 | .d10 => 3/2 | .d01 => 5/4 | .d00 => 1

def degree {N : ℕ} (A : Adjacency N) (i : Fin N) : ℕ :=
  ∑ j, if A i j then 1 else 0

def twoWalkDegree {N : ℕ} (A : Adjacency N) (i : Fin N) : ℕ :=
  (Finset.univ.filter (fun j => j ≠ i ∧ ∃ k, A i k = true ∧ A k j = true)).card

def degreeScale {N : ℕ} (A : Adjacency N) (i : Fin N) : ℕ :=
  degree A i + twoWalkDegree A i + degree A i * twoWalkDegree A i

def baseline (a g e : ℝ) : ℝ := a * |g| + e

def dilatedOutcomes {N : ℕ} (B : Fin N → ℝ) : Fin N → Exposure → ℝ :=
  fun i d => (match d with | .d11 => 2 | .d10 => 3/2 | .d01 => 5/4 | .d00 => 1) * B i

noncomputable def normalPair : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 1 (1/16))

noncomputable def baselineLaw (a : ℝ) : Measure ℝ :=
  normalPair.map (fun x => baseline a x.1 x.2)

noncomputable def halfNormalLaw : Measure ℝ := (gaussianReal 0 1).map (fun g => |g|)

def blockEdgeProbability {N : ℕ} {C : Type*} [DecidableEq C]
    (s : ℝ) (t : Fin N → ℝ) (c : Fin N → C) (i j : Fin N) : ℝ :=
  s * t i * t j * (if c i = c j then 1 else 0)

noncomputable def withinEdges {N : ℕ} {C : Type*} (G : SimpleGraph (Fin N))
    (c : Fin N → C) : Finset (Sym2 (Fin N)) := by
  classical
  exact G.edgeFinset.filter (fun e => ∃ i j, e = s(i,j) ∧ c i = c j)

noncomputable def normalPopulation (N : ℕ) : Measure (Fin N → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin N => normalPair)

def generatedBaselines {N : ℕ} (A : Adjacency N) (x : Fin N → ℝ × ℝ) : Fin N → ℝ :=
  fun i => baseline (degreeScale A i) (x i).1 (x i).2

def standardNormalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

end
end SAP.P044
