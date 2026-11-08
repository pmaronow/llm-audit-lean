import SAP.P037a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037a

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

noncomputable def eligibleFraction (i : Fin 4) : ℝ :=
  if i.val < 2 then 1/10 else 3/10

noncomputable def stratumMass (r : ℕ) (k : Fin 4) : ℝ :=
  (r.choose k.val : ℝ) * ((10-r).choose (5-k.val) : ℝ) / (10:ℕ).choose 5

noncomputable def countMass (r : ℕ) (k : Fin 13) : ℝ :=
  ∑ c : Fin 4 → Fin 4,
    if (∑ s, (c s).val) = k.val then ∏ s, stratumMass r (c s) else 0

def stratumReferents (i : Fin 4) : ℕ := if i.val < 2 then 1 else 3

abbrev CompositionAssignment := Fin 6 × Fin 13 × Fin 13

noncomputable def assignmentMass (w : CompositionAssignment) : ℝ :=
  (1/6) * countMass (stratumReferents (treatmentPair w.1).1) w.2.1 *
    countMass (stratumReferents (treatmentPair w.1).2) w.2.2

noncomputable def compositionColumn (w : CompositionAssignment) (i : Fin 4) : ℝ :=
  if i = (treatmentPair w.1).1 then (w.2.1.val:ℝ)/20 else
  if i = (treatmentPair w.1).2 then (w.2.2.val:ℝ)/20 else 0

noncomputable def potentialOutcome (i : Fin 4) (treated : Bool) (_c : ℝ) : ℝ :=
  if treated then 3/10-eligibleFraction i else 3/10

noncomputable def observedOutcome (w : CompositionAssignment) (i : Fin 4) : ℝ :=
  3/10 - treatment w.1 i*eligibleFraction i

noncomputable def centeredCross (x y : Fin 4 → ℝ) : ℝ :=
  (∑ i, x i*y i) - (∑ i, x i)*(∑ i, y i)/4

noncomputable def regressionColumns (w : CompositionAssignment) (k : Fin 3) : Fin 4 → ℝ :=
  ![treatment w.1, eligibleFraction, compositionColumn w] k

noncomputable def compositionMean (X : CompositionAssignment → ℝ) : ℝ :=
  ∑ w, assignmentMass w * X w

noncomputable def populationGram : Matrix (Fin 3) (Fin 3) ℝ :=
  fun k l => compositionMean (fun w => centeredCross (regressionColumns w k) (regressionColumns w l))

noncomputable def populationRhs : Fin 3 → ℝ :=
  fun k => compositionMean (fun w => centeredCross (regressionColumns w k) (observedOutcome w))

noncomputable def mixturePotential (a tau b1 b2 g : ℝ)
    (i : Fin 4) (treated : Bool) (c : ℝ) : ℝ :=
  a+g*eligibleFraction i +
    if treated then tau+b1*(c-eligibleFraction i)+b2*(eligibleFraction i-1/5) else 0

noncomputable def mixtureObserved (a tau b1 b2 g : ℝ)
    (w : CompositionAssignment) (i : Fin 4) : ℝ :=
  a+tau*treatment w.1 i+
    b1*(compositionColumn w i-treatment w.1 i*eligibleFraction i)+
    b2*treatment w.1 i*(eligibleFraction i-1/5)+g*eligibleFraction i

noncomputable def centeredBlockCross {B : ℕ}
    (x y : (Fin B × Fin 4) → ℝ) : ℝ :=
  ∑ b, ∑ i, ∑ j, (if i=j then (3/4:ℝ) else -1/4) * x (b,i) * y (b,j)

def CompositionRandomized {Ω : Type*} [Fintype Ω] {B : ℕ}
    (d : Design Ω) (D : Ω → (Fin B × Fin 4) → Bool)
    (R : Ω → (Fin B × Fin 4) → ℝ) : Prop :=
  ∀ (f : ((Fin B × Fin 4) → Bool) → ℝ) i,
    mean d (fun w => f (D w)*R w i) = 0

def NormalEquations {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ}
    (d : Design Ω) (X : K → Ω → (Fin B × Fin 4) → ℝ)
    (Y : Ω → (Fin B × Fin 4) → ℝ) (theta : K → ℝ) : Prop :=
  ∀ k, mean d (fun w => centeredBlockCross (X k w) (Y w)) =
    ∑ l, theta l * mean d (fun w => centeredBlockCross (X k w) (X l w))

def ExtendedNormalEquations {Ω K : Type*} [Fintype Ω] [Fintype K] {B : ℕ}
    (d : Design Ω) (W : K → Ω → (Fin B × Fin 4) → ℝ)
    (R Y : Ω → (Fin B × Fin 4) → ℝ) (delta : K → ℝ) (beta : ℝ) : Prop :=
  (∀ k, mean d (fun w => centeredBlockCross (W k w) (Y w)) =
    (∑ l, delta l*mean d (fun w => centeredBlockCross (W k w) (W l w))) +
      beta*mean d (fun w => centeredBlockCross (W k w) (R w))) ∧
  mean d (fun w => centeredBlockCross (R w) (Y w)) =
    (∑ l, delta l*mean d (fun w => centeredBlockCross (R w) (W l w))) +
      beta*mean d (fun w => centeredBlockCross (R w) (R w))

noncomputable def innovation (w : CompositionAssignment) (i : Fin 4) : ℝ :=
  compositionColumn w i - treatment w.1 i*eligibleFraction i

noncomputable def expandedColumns (w : CompositionAssignment) (k : Fin 4) : Fin 4 → ℝ :=
  ![treatment w.1, eligibleFraction, compositionColumn w,
    (fun i => treatment w.1 i*eligibleFraction i)] k

noncomputable def centeredColumns (w : CompositionAssignment) (k : Fin 3) : Fin 4 → ℝ :=
  ![treatment w.1, eligibleFraction, innovation w] k

def CompositionEquations {n : ℕ} (X : CompositionAssignment → Fin n → Fin 4 → ℝ)
    (Y : CompositionAssignment → Fin 4 → ℝ) (theta : Fin n → ℝ) : Prop :=
  ∀ k, (∑ l, theta l*compositionMean (fun w => centeredCross (X w k) (X w l))) =
    compositionMean (fun w => centeredCross (X w k) (Y w))

noncomputable def seedCompositionMean {H : ℕ} (N K n : Fin H → ℕ) : ℝ :=
  (∑ h, (n h:ℝ)*((K h:ℝ)/N h))/(∑ h, (n h:ℝ))

noncomputable def eligibleShare {H : ℕ} (N K : Fin H → ℕ) : ℝ :=
  (∑ h, (K h:ℝ))/(∑ h, (N h:ℝ))

abbrev SeedAssignment {H : ℕ} (N n : Fin H → ℕ) :=
  (h : Fin H) → {s : Finset (Fin (N h)) // s.card=n h}

noncomputable def seedComposition {H : ℕ} (N n : Fin H → ℕ)
    (refs : (h : Fin H) → Finset (Fin (N h))) (z : SeedAssignment N n) : ℝ :=
  (∑ h, ((refs h∩(z h).val).card:ℝ))/(∑ h, (n h:ℝ))

end SAP.P037a
