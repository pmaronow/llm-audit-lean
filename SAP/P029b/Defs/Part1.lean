import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b

universe u v

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

def bit (b : Bool) : ℝ := if b then 1 else 0

structure PotentialUnit (X : Type*) where
  x : X
  d0 : Bool
  d1 : Bool
  y0 : ℝ
  y1 : ℝ

def PotentialUnit.tau {X : Type*} (u : PotentialUnit X) : ℝ := u.y1 - u.y0

def PotentialUnit.complier {X : Type*} (u : PotentialUnit X) : Prop :=
  u.d0 = false ∧ u.d1 = true

def PotentialUnit.defier {X : Type*} (u : PotentialUnit X) : Prop :=
  u.d0 = true ∧ u.d1 = false

def PotentialUnit.receipt {X : Type*} (u : PotentialUnit X) (z : Bool) : Bool :=
  if z then u.d1 else u.d0

def PotentialUnit.outcome {X : Type*} (u : PotentialUnit X) (z : Bool) : ℝ :=
  if u.receipt z then u.y1 else u.y0

def ValidLaw {L : Type*} [Fintype L] (p : L → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1

def fE {L : Type*} [Fintype L] (p v : L → ℝ) : ℝ := ∑ i, p i * v i

def fP {L : Type*} [Fintype L] (p : L → ℝ) (A : L → Prop) : ℝ :=
  ∑ i, if A i then p i else 0

def fCE {L : Type*} [Fintype L] (p v : L → ℝ) (A : L → Prop) : ℝ :=
  fE p (fun i => if A i then v i else 0) / fP p A

def FIndep {L A B : Type*} [Fintype L] (p : L → ℝ) (U : L → A) (V : L → B) : Prop :=
  ∀ a b, fP p (fun i => U i = a ∧ V i = b) =
    fP p (fun i => U i = a) * fP p (fun i => V i = b)

def randomized {L : Type*} (p : L → ℝ) (e : ℝ) : L × Bool → ℝ :=
  fun i => p i.1 * if i.2 then e else 1 - e

def fWald {L X : Type*} [Fintype L] (p : L → ℝ) (U : L → PotentialUnit X)
    (Z : L → Bool) (w : L → ℝ) : ℝ :=
  ((fCE p (fun i => w i * (U i).outcome (Z i)) (fun i => Z i = true) /
      fCE p w (fun i => Z i = true)) -
    (fCE p (fun i => w i * (U i).outcome (Z i)) (fun i => Z i = false) /
      fCE p w (fun i => Z i = false))) /
  ((fCE p (fun i => w i * bit ((U i).receipt (Z i))) (fun i => Z i = true) /
      fCE p w (fun i => Z i = true)) -
    (fCE p (fun i => w i * bit ((U i).receipt (Z i))) (fun i => Z i = false) /
      fCE p w (fun i => Z i = false)))

def fScore {L X : Type*} [Fintype L] (p : L → ℝ) (U : L → PotentialUnit X)
    (x : X) : ℝ := fP p (fun i => (U i).complier ∧ (U i).x = x) /
      fP p (fun i => (U i).x = x)

def fLatentIgnorability {L X : Type*} [Fintype L] (p : L → ℝ)
    (U : L → PotentialUnit X) : Prop :=
  ∀ x, 0 < fP p (fun i => (U i).x = x) →
    fCE p (fun i => (U i).tau) (fun i => (U i).x = x) =
    fCE p (fun i => (U i).tau) (fun i => (U i).complier ∧ (U i).x = x)

def fTypicalIgnorability {L X : Type*} [Fintype L] (p : L → ℝ)
    (U : L → PotentialUnit X) (Z : L → Bool) (x : X) : Prop :=
  fCE p (fun i => (U i).y0) (fun i => (U i).receipt (Z i) = true ∧ (U i).x = x) =
    fCE p (fun i => (U i).y0) (fun i => (U i).receipt (Z i) = false ∧ (U i).x = x) ∧
  fCE p (fun i => (U i).y1) (fun i => (U i).receipt (Z i) = true ∧ (U i).x = x) =
    fCE p (fun i => (U i).y1) (fun i => (U i).receipt (Z i) = false ∧ (U i).x = x)

def FIV {L X : Type*} [Fintype L] (p : L → ℝ) (U : L → PotentialUnit X)
    (Z : L → Bool) : Prop :=
  ValidLaw p ∧ 0 < fP p (fun i => Z i = true) ∧ fP p (fun i => Z i = true) < 1 ∧
  FIndep p (fun i => ((U i).x, (U i).d0, (U i).d1, (U i).y0, (U i).y1)) Z ∧
  fP p (fun i => (U i).defier) = 0 ∧
  fCE p (fun i => bit ((U i).receipt (Z i))) (fun i => Z i = true) -
    fCE p (fun i => bit ((U i).receipt (Z i))) (fun i => Z i = false) ≠ 0

def typeMass (i : Fin 3) : ℝ := if i.val = 0 then 1/2 else 1/4

def case2Unit (i : Fin 3) : PotentialUnit Unit :=
  ⟨(), decide (i.val = 1), decide (i.val ≠ 2),
    if i.val = 1 then 1 else 0, (if i.val = 1 then 1 else 0) + 1⟩

def constantUnit (i : Fin 3) : PotentialUnit Unit :=
  ⟨(), decide (i.val = 1), decide (i.val ≠ 2), 0, 1⟩

def sixMass : Fin 3 × Bool → ℝ := randomized typeMass (1/2)

def liftUnit {L X : Type*} (u : L → PotentialUnit X) : L × Bool → PotentialUnit X :=
  fun i => u i.1

def mP {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) : ℝ :=
  (μ A).toReal

def mCE {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → ℝ)
    (A : Set Ω) : ℝ := (∫ ω in A, v ω ∂μ) / mP μ A

def IVAssumptions {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (U : Ω → PotentialUnit X) (Z : Ω → Bool) : Prop :=
  Measurable (fun ω => (U ω).x) ∧ Measurable (fun ω => (U ω).d0) ∧
  Measurable (fun ω => (U ω).d1) ∧ Measurable (fun ω => (U ω).y0) ∧
  Measurable (fun ω => (U ω).y1) ∧ Measurable Z ∧
  Integrable (fun ω => (U ω).y0) μ ∧ Integrable (fun ω => (U ω).y1) μ ∧
  IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1)) μ ∧
  0 < mP μ {ω | Z ω = true} ∧ mP μ {ω | Z ω = true} < 1 ∧
  μ {ω | (U ω).defier} = 0 ∧
  mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = true} -
    mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = false} ≠ 0

def latentAt {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (x : X) : Prop :=
  mCE μ (fun ω => (U ω).tau) {ω | (U ω).x = x} =
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier ∧ (U ω).x = x}

def typicalAt {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (Z : Ω → Bool) (x : X) : Prop :=
  mCE μ (fun ω => (U ω).y0) {ω | (U ω).receipt (Z ω) = true ∧ (U ω).x = x} =
    mCE μ (fun ω => (U ω).y0) {ω | (U ω).receipt (Z ω) = false ∧ (U ω).x = x} ∧
  mCE μ (fun ω => (U ω).y1) {ω | (U ω).receipt (Z ω) = true ∧ (U ω).x = x} =
    mCE μ (fun ω => (U ω).y1) {ω | (U ω).receipt (Z ω) = false ∧ (U ω).x = x}

def scoreAt {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (x : X) : ℝ :=
  mP μ {ω | (U ω).complier ∧ (U ω).x = x} / mP μ {ω | (U ω).x = x}

def complierAt {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (x : X) : ℝ :=
  mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier ∧ (U ω).x = x}

def mArm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → Bool)
    (w v : Ω → ℝ) (z : Bool) : ℝ :=
  mCE μ (fun ω => w ω * v ω) {ω | Z ω = z} / mCE μ w {ω | Z ω = z}

def mWald {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → PotentialUnit X) (Z : Ω → Bool) (w : Ω → ℝ) : ℝ :=
  (mArm μ Z w (fun ω => (U ω).outcome (Z ω)) true -
    mArm μ Z w (fun ω => (U ω).outcome (Z ω)) false) /
  (mArm μ Z w (fun ω => bit ((U ω).receipt (Z ω))) true -
    mArm μ Z w (fun ω => bit ((U ω).receipt (Z ω))) false)

def bernoulliFactor (p : ℝ) (d : Bool) : ℝ :=
  p ^ (if d then 1 else 0 : ℕ) * (1 - p) ^ (if d then 0 else 1 : ℕ)

def nestedReceipt (a b : ℝ) (z : Bool) : ℝ := a * (1 - b) * bit z + a * b

def packageObjective {I : Type*} [Fintype I] (L w : I → ℝ) : ℝ :=
  -(∑ i, Real.log (L i * w i))

def weightedObjective {I : Type*} [Fintype I] (L w : I → ℝ) : ℝ :=
  -(∑ i, w i * Real.log (L i))

def IsMinimizer {Θ : Type*} (Q : Θ → ℝ) (θ : Θ) : Prop := ∀ t, Q θ ≤ Q t

def twoSidedSuccesses (i : Bool × Bool) : ℕ := if i.2 then (if i.1 then 3 else 2) else 1

def packageCells (i : Bool × Bool) : ℝ := if i.2 then (if i.1 then 3/4 else 1/2) else 1/4

def positiveScore (r1 r0 : ℝ) : ℝ := max (r1 - r0) 0

def binomialMass (n : ℕ) (p : ℝ) (k : Fin (n+1)) : ℝ :=
  (n.choose k.val : ℝ) * p^k.val * (1-p)^(n-k.val)

def binomialArmLaw (n1 n0 : ℕ) (p1 p0 : ℝ) : Fin (n1+1) × Fin (n0+1) → ℝ :=
  fun k => binomialMass n1 p1 k.1 * binomialMass n0 p0 k.2

def armRateScore (n1 n0 : ℕ) (k : Fin (n1+1) × Fin (n0+1)) : ℝ :=
  positiveScore ((k.1.val : ℝ)/n1) ((k.2.val : ℝ)/n0)

def nextOrderIndex {n : ℕ} (j : Fin (n+1)) : Fin (n+1) :=
  ⟨min (j.val+1) n, Nat.lt_succ_of_le (min_le_right _ _)⟩

def Type7Quantile {n : ℕ} (s : Fin (n+1) → ℝ) (level c : ℝ) : Prop :=
  ∃ π : Equiv.Perm (Fin (n+1)), Monotone (fun i => s (π i)) ∧
    ∃ j : Fin (n+1), (j.val : ℝ) ≤ (n : ℝ)*level ∧ (n : ℝ)*level < (j.val : ℝ)+1 ∧
      c = (1 - ((n : ℝ)*level - j.val)) * s (π j) +
        ((n : ℝ)*level - j.val) * s (π (nextOrderIndex j))

def belowCount {n : ℕ} (s : Fin (n+1) → ℝ) (c : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => s i < c)).card

def weightChange (s c : ℝ) : ℝ := 1/s - 1/max s c

def positiveIndicator (index : ℝ) : ℝ := if 0 < index then 1 else 0

def latentAC (indexAC : ℝ) : ℝ := positiveIndicator indexAC

def latentA (indexAC indexA : ℝ) : ℝ := positiveIndicator indexA * latentAC indexAC

def latentC (indexAC indexA : ℝ) : ℝ := latentAC indexAC - latentA indexAC indexA

def latentD (indexAC indexA : ℝ) (z : Bool) : ℝ :=
  latentC indexAC indexA * bit z + latentA indexAC indexA
end
end SAP.P029b
