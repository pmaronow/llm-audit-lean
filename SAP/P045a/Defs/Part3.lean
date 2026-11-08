import SAP.P045a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a
noncomputable section

def repairedExpansion {n : ℕ} (p : Assignment n → ℝ) (A : Fin n → Fin n → Bool)
    (y : Fin n → Exposure → ℝ) (z : Assignment n) : ℝ :=
  mean (fun i =>
    (if exposure A z i = .d11 then y i .d11/ownProb p i else 0) +
    (if exposure A z i = .d10 then y i .d10/ownProb p i else 0))

def cancellingOut2 (i : Fin 2) (d : Exposure) : ℝ :=
  match d with
  | .d11 => if i=0 then 2 else 1
  | .d10 => if i=0 then 1 else 2
  | .d01 | .d00 => 0

def pooledMean (a b : ℕ) (A B : ℝ) : Option ℝ :=
  if a+b=0 then none else some ((A+B)/(a+b : ℕ))

def printedPool (a b : ℕ) (A B : ℝ) : Option ℝ :=
  if a=0 ∨ b=0 then none else some (A/a+B/b)

def tractPartner (g : Fin 6) : Fin 6 :=
  ![1,0,3,2,5,4] g

def sameRegimeCount (H : Finset (Fin 6)) : ℕ := (H.filter (fun g => tractPartner g ∈ H)).card

def tractWitnessAssignment (g : Fin 6) : Assignment 75 :=
  fun i => decide (i.val < if g.val < 3 then 50 else 25)

def tractOutcome (w : Fin 6 → Assignment 75) (g : Fin 6) (i : Fin 75) : ℝ :=
  let k := treatedCount (w g)+treatedCount (w (tractPartner g))
  if w g i then (if k=100 then 9/4 else if k=75 then 2 else 3/2)
  else (if k=100 then 11/8 else if k=75 then 5/4 else 1)

def tractObservedArm (w : Fin 6 → Assignment 75) (g : Fin 6) (b : Bool) : ℝ :=
  armMean (fun i _ => tractOutcome w g i) b (w g)

def dilated (b : ℝ) (d : Exposure) : ℝ :=
  match d with | .d11 => 2*b | .d10 => (3/2)*b | .d01 => (5/4)*b | .d00 => b

def pairHT (A : Fin 10 → Fin 10 → Bool) (y : Fin 10 → Exposure → ℝ)
    (d : Exposure) (e : Fin 10 × Fin 10) : ℝ :=
  ∑ i, if exposure A (pairAssignment e) i = d then y i d/pairExposureProb A i d else 0

def printedContrast (e : Fin 10 × Fin 10) : ℝ :=
  (pairHT printedAdj (fun _ => dilated 1) .d11 e - pairHT printedAdj (fun _ => dilated 1) .d00 e)/10

def pairCellNonempty (d : Exposure) (e : Fin 10 × Fin 10) : Prop :=
  ∃ i, exposure printedAdj (pairAssignment e) i = d

abbrev TractAssignment := Fin 6 → Assignment 75

def tractRegimeCount (H : Finset (Fin 6)) (g : Fin 6) : ℕ :=
  if g ∈ H then 50 else 25

def tractSecondStageMass (H : Finset (Fin 6)) (w : TractAssignment) : ℝ :=
  ∏ g : Fin 6, crMass 75 (tractRegimeCount H g) (w g)

def tractTwoStageMass (ω : Finset (Fin 6) × TractAssignment) : ℝ :=
  if ω.1 ∈ firstStageSets 6 3 then
    (1 / ((firstStageSets 6 3).card : ℝ)) * tractSecondStageMass ω.1 ω.2
  else 0

def tractDirectEstimator (H : Finset (Fin 6)) (w : TractAssignment) : ℝ :=
  (∑ g ∈ H, tractObservedArm w g true) / (H.card : ℝ) -
    (∑ g ∈ H, tractObservedArm w g false) / (H.card : ℝ)

def tractAllPsiMass (w : TractAssignment) : ℝ :=
  tractSecondStageMass Finset.univ w

def tractPsiPsiPotential (g : Fin 6) (i : Fin 75) (b : Bool) : ℝ :=
  condMean tractAllPsiMass (fun w => w g i = b)
    (fun w => tractOutcome w g i)

def tractGroupAt (t : Fin 3) (s : Fin 2) : Fin 6 :=
  (![![0, 1], ![2, 3], ![4, 5]] : Fin 3 → Fin 2 → Fin 6) t s

def tractPsiPsiTarget : ℝ :=
  mean (fun t : Fin 3 =>
    mean (fun u : Fin 2 × Fin 75 =>
      tractPsiPsiPotential (tractGroupAt t u.1) u.2 true) -
    mean (fun u : Fin 2 × Fin 75 =>
      tractPsiPsiPotential (tractGroupAt t u.1) u.2 false))

end
end SAP.P045a
