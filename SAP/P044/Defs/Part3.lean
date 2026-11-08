import SAP.P044.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

def cliquePairs : Fin 66 → Fin 12 × Fin 12 :=
  ![(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (0,9), (0,10), (0,11), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (1,10), (1,11), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10), (2,11), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (4,5), (4,6), (4,7), (4,8), (4,9), (4,10), (4,11), (5,6), (5,7), (5,8), (5,9), (5,10), (5,11), (6,7), (6,8), (6,9), (6,10), (6,11), (7,8), (7,9), (7,10), (7,11), (8,9), (8,10), (8,11), (9,10), (9,11), (10,11)]

def cliqueAssignments (r : Fin 66) : Assignment 12 := fun i =>
  decide (i = (cliquePairs r).1 ∨ i = (cliquePairs r).2)

def cliqueAdj : Adjacency 12 := fun i j => decide (i ≠ j ∧ i.val / 4 = j.val / 4)

def cliqueF (r : Fin 66) (i : Fin 12) : Exposure :=
  let u := (cliquePairs r).1
  let v := (cliquePairs r).2
  if i = u ∨ i = v then
    (if u.val / 4 = v.val / 4 then .d11 else .d10)
  else (if i.val / 4 = u.val / 4 ∨ i.val / 4 = v.val / 4 then .d01 else .d00)

def cliqueY : Fin 12 → Exposure → ℚ := fun _ _ => 1

def retainedAssignments (t : Fin 66) (r : Fin 65) : Assignment 12 :=
  cliqueAssignments (t.succAbove r)

def retainedF (t : Fin 66) : Fin 65 → Fin 12 → Exposure :=
  fun r => cliqueF (t.succAbove r)

def cliqueFullCount (a : Exposure) : ℕ :=
  match a with | .d11 => 3 | .d10 => 8 | .d01 => 27 | .d00 => 28

def cliqueFullJoint (i j : Fin 12) (a b : Exposure) : ℕ :=
  if i = j then (if a = b then cliqueFullCount a else 0)
  else match a,b with
    | .d01,.d01 => if i.val / 4 = j.val / 4 then 17 else 9
    | .d00,.d00 => if i.val / 4 = j.val / 4 then 28 else 6
    | .d01,.d00 | .d00,.d01 => if i.val / 4 = j.val / 4 then 0 else 15
    | _,_ => jointCount cliqueF i j a b

def cliqueWeights (t : Fin 66) (i : Fin 12) (a : Exposure) : ℚ :=
  ((cliqueFullCount a - if cliqueF t i = a then 1 else 0 : ℕ) + 1 : ℕ) / (66 : ℚ)

def cliqueJoints (t : Fin 66) (i j : Fin 12) (a b : Exposure) : ℚ :=
  let c := cliqueFullJoint i j a b - if cliqueF t i = a ∧ cliqueF t j = b then 1 else 0
  if a = b then ((c + if i = j then 1 else 0 : ℕ) : ℚ) / 66 else (c : ℚ) / 65

def cliqueT (t z : Fin 66) : ℚ :=
  htContrast cliqueF cliqueY (cliqueWeights t) .d01 .d00 z

def cliqueV (t z : Fin 66) : ℚ :=
  varianceEstimate cliqueF cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00 z

def cliqueJointMass (included : Bool) (x : Fin 66 × Fin 66) : ℚ :=
  if included then (if x.1 = x.2 then 0 else 1/4290) else 1/4356

def cliqueObservationMass (t : Fin 66) (included : Bool) (z : Fin 66) : ℚ :=
  if included then (if z = t then 0 else 1/65) else 1/66

def cliqueObservationMarginal (t : Fin 66) (included : Bool) (i : Fin 12) (a : Exposure) : ℚ :=
  if included then ((cliqueFullCount a - if cliqueF t i = a then 1 else 0 : ℕ) : ℚ) / 65
  else (cliqueFullCount a : ℚ) / 66

end
end SAP.P044
