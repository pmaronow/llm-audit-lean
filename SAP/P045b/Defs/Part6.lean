import SAP.P045b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P045b
open Finset
open scoped BigOperators
noncomputable section

def cliquePairs : Fin 66 → Fin 12 × Fin 12 :=
  ![(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (0,8), (0,9), (0,10), (0,11), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (1,9), (1,10), (1,11), (2,3), (2,4), (2,5), (2,6), (2,7), (2,8), (2,9), (2,10), (2,11), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,10), (3,11), (4,5), (4,6), (4,7), (4,8), (4,9), (4,10), (4,11), (5,6), (5,7), (5,8), (5,9), (5,10), (5,11), (6,7), (6,8), (6,9), (6,10), (6,11), (7,8), (7,9), (7,10), (7,11), (8,9), (8,10), (8,11), (9,10), (9,11), (10,11)]

def cliqueAssignments (r : Fin 66) : Assignment 12 := fun i =>
  decide (i = (cliquePairs r).1 ∨ i = (cliquePairs r).2)

def cliqueAdj : Fin 12 → Fin 12 → Bool := fun i j => decide (i ≠ j ∧ i.val / 4 = j.val / 4)

def retainedAssignments (t : Fin 66) (r : Fin 65) : Assignment 12 :=
  cliqueAssignments (t.succAbove r)

def cliqueJointMass (included : Bool) (x : Fin 66 × Fin 66) : ℚ :=
  if included then (if x.1 = x.2 then 0 else 1/4290) else 1/4356

def cliqueObservationMass (t : Fin 66) (included : Bool) (z : Fin 66) : ℚ :=
  if included then (if z = t then 0 else 1/65) else 1/66

/-- Four-condition exposure, with the label representation supplied by a bijection. -/
def fourExposure {E : Type*} (labels : Fin 4 ≃ E)
    (A : Fin 12 → Fin 12 → Bool) (z : Assignment 12) (i : Fin 12) : E :=
  let peers := ∑ j, if A i j && z j then (1 : ℕ) else 0
  if z i then (if 0 < peers then labels 0 else labels 1)
  else (if 0 < peers then labels 2 else labels 3)

/-- Exact finite-clique witness: the exposure representation is immaterial. -/
def T32Facts (E : Type) [DecidableEq E] (labels : Fin 4 ≃ E)
    (f : Fin 66 → Fin 12 → E)
    (w : Fin 66 → Fin 12 → E → ℚ)
    (q : Fin 66 → Fin 12 → Fin 12 → E → E → ℚ) : Prop :=
  let k := labels 2
  let l := labels 3
  let y : Fin 12 → E → ℚ := fun _ _ => 1
  let p := fun _ : Fin 66 => (1/66 : ℚ)
  let T := fun t z => weightedContrast f y (w t) k l z
  let V := fun t z => varianceEstimate f y (w t) (q t) k l z
  f = (fun r => fourExposure labels cliqueAdj (cliqueAssignments r)) ∧
  (∀ z : Assignment 12, (univ.filter (fun i => z i)).card = 2 ↔ ∃ r, cliqueAssignments r = z) ∧
  Function.Injective cliqueAssignments ∧
  (∀ i j, cliqueAdj i j = cliqueAdj j i) ∧
  (∀ i, cliqueAdj i i = false ∧ ∃ j, cliqueAdj i j = true) ∧
  (∀ t, Function.Injective (retainedAssignments t) ∧
    ∀ r, retainedAssignments t r ≠ cliqueAssignments t) ∧
  (∀ t i a, w t i a = smoothedWeight (fun r : Fin 65 => f (t.succAbove r)) i a) ∧
  (∀ t i j a b, (a = k ∨ a = l) → (b = k ∨ b = l) →
    q t i j a b = smoothedJoint (fun r : Fin 65 => f (t.succAbove r)) i j a b) ∧
  (∀ t i, 0 < w t i k ∧ 0 < w t i l) ∧
  exposureEffect y k l = 0 ∧
  (∀ i, exposureCount f i k = 27 ∧ exposureCount f i l = 28 ∧
    exposureMarginal p f i k = 9/22 ∧ exposureMarginal p f i l = 14/33 ∧
    0 < exposureMarginal p f i k ∧ 0 < exposureMarginal p f i l) ∧
  (∀ i j, i ≠ j →
    jointCount f i j k k = (if i.val/4 = j.val/4 then 17 else 9) ∧
    jointCount f i j l l = (if i.val/4 = j.val/4 then 28 else 6) ∧
    jointCount f i j k l = (if i.val/4 = j.val/4 then 0 else 15)) ∧
  (∀ r, (univ.filter (fun i => f r i = k)).card =
      (if (cliquePairs r).1.val/4 = (cliquePairs r).2.val/4 then 2 else 6) ∧
    (univ.filter (fun i => f r i = l)).card =
      (if (cliquePairs r).1.val/4 = (cliquePairs r).2.val/4 then 8 else 4)) ∧
  (univ.filter (fun r => (cliquePairs r).1.val/4 = (cliquePairs r).2.val/4)).card = 18 ∧
  (univ.filter (fun r => (cliquePairs r).1.val/4 ≠ (cliquePairs r).2.val/4)).card = 48 ∧
  (let m := exposureMarginal p f
   let J := exposureJoint p f
   let exactT := weightedContrast f y m k l
   (∀ r, exactT r =
     if (cliquePairs r).1.val/4 = (cliquePairs r).2.val/4 then -220/189 else 55/126) ∧
   expect p exactT = 0 ∧ momentVariance p exactT = 6050/11907 ∧
   expect p (varianceEstimate f y m J k l) = 6050/11907) ∧
  (∀ included x, 0 ≤ cliqueJointMass included x) ∧
  (∀ included, ∑ x, cliqueJointMass included x = (1 : ℚ)) ∧
  expect (cliqueJointMass false) (fun x => T x.1 x.2) = -67/53592 ∧
  momentVariance (cliqueJointMass false) (fun x => T x.1 x.2) = 113448938731/232640299584 ∧
  expect (cliqueJointMass false) (fun x => V x.1 x.2) = 1040129476423/2326402995840 ∧
  expect (cliqueJointMass false) (fun x => V x.1 x.2) -
    momentVariance (cliqueJointMass false) (fun x => T x.1 x.2) = -953130413/23499020160 ∧
  expect (cliqueJointMass true) (fun x => T x.1 x.2) = -67/52780 ∧
  momentVariance (cliqueJointMass true) (fun x => T x.1 x.2) = 11375808887/23342482800 ∧
  expect (cliqueJointMass true) (fun x => V x.1 x.2) = 4673362763/10414338480 ∧
  expect (cliqueJointMass true) (fun x => V x.1 x.2) -
    momentVariance (cliqueJointMass true) (fun x => T x.1 x.2) = -20161943/522324075 ∧
  (∀ included,
    expect (cliqueJointMass included) (fun x => V x.1 x.2) <
      momentVariance (cliqueJointMass included) (fun x => T x.1 x.2) ∧
    expect (cliqueJointMass included) (fun x => V x.1 x.2) < 6050/11907) ∧
  (∀ t : Fin 66,
    let same := (cliquePairs t).1.val/4 = (cliquePairs t).2.val/4
    momentVariance p (T t) = (if same then 2810528137/5767941312 else 937589375/1922647104) ∧
    expect p (V t) = (if same then 267260522663/634473544320 else 4830430961/10574559072) ∧
    expect p (V t) - momentVariance p (T t) =
      (if same then -1551761941/23499020160 else -72513467/2349902016) ∧
    expect p (V t) < momentVariance p (T t)) ∧
  (∀ t, ∃ e : Equiv.Perm (Fin 12),
    (∀ i j, cliqueAdj (e i) (e j) = cliqueAdj i j) ∧
    (∀ i, cliqueAssignments t (e i) =
      cliqueAssignments (if (cliquePairs t).1.val/4 = (cliquePairs t).2.val/4 then 0 else 3) i)) ∧
  (∀ included : Bool,
    let pr := fun x => (cliqueJointMass included x : ℝ)
    let Tr := fun x : Fin 66 × Fin 66 =>
      weightedContrast f (fun _ _ => (1 : ℝ))
        (fun i a => (w x.1 i a : ℝ)) k l x.2
    let Vr := fun x : Fin 66 × Fin 66 =>
      varianceEstimate f (fun _ _ => (1 : ℝ))
        (fun i a => (w x.1 i a : ℝ)) (fun i j a b => (q x.1 i j a b : ℝ)) k l x.2
    (∀ x, 0 ≤ pr x) ∧ (∑ x, pr x) = 1 ∧
    expect pr Vr < momentVariance pr Tr ∧ expect pr Vr < 6050/11907)

/-- Rational certificates use the canonical embedding into the real-valued estimator. -/
def T32Statement : Prop :=
  ∃ (E : Type) (decE : DecidableEq E) (labels : Fin 4 ≃ E),
    ∃ f w q, @T32Facts E decE labels f w q

def T33Statement : Prop :=
  ∀ {Ω D : Type*} {N : ℕ} [Fintype Ω] [DecidableEq D],
    0 < N → ∀ (P : Design Ω) (f : Ω → Fin N → D)
    (y : Fin N → D → ℝ) (a b : D), a ≠ b →
    (∀ i, 0 < exposureMarginal P.mass f i a) →
    (∀ i, 0 < exposureMarginal P.mass f i b) →
    expect P.mass (varianceEstimate f y (exposureMarginal P.mass f) (exposureJoint P.mass f) a b) -
      momentVariance P.mass (weightedContrast f y (exposureMarginal P.mass f) a b) =
        zeroSurplus y (exposureJoint P.mass f) a b ∧
    momentVariance P.mass (weightedContrast f y (exposureMarginal P.mass f) a b) ≤
      expect P.mass (varianceEstimate f y (exposureMarginal P.mass f) (exposureJoint P.mass f) a b) ∧
    expect P.mass (weightedContrast f y (exposureMarginal P.mass f) a b) = exposureEffect y a b

end
end SAP.P045b
