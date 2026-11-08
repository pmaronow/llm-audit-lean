import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004c
open scoped BigOperators Classical
open MeasureTheory Filter
noncomputable section

abbrev Assignment (N : ℕ) := Fin N → Bool
abbrev CircleTable (N : ℕ) := Fin N → Assignment N → ℝ

def bit (a : Bool) : ℝ := if a then 1 else 0
def coin (p : ℝ) (a : Bool) : ℝ := if a then p else 1 - p

/-- The independent Bernoulli assignment law, allowing unequal probabilities. -/
def designWeight {N : ℕ} (p : Fin N → ℝ) (z : Assignment N) : ℝ :=
  ∏ i, coin (p i) (z i)

/-- Expectation over the finite assignment space. -/
def expect {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) : ℝ :=
  ∑ z, designWeight p z * X z

def prob {N : ℕ} (p : Fin N → ℝ) (A : Assignment N → Prop) : ℝ :=
  expect p (fun z => if A z then 1 else 0)

def cov {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) : ℝ :=
  expect p (fun z => X z * Y z) - expect p X * expect p Y

def variance {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) : ℝ := cov p X X

/-- The arm-conditional circle mean; all uses require strictly interior coins. -/
def marginal {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (i : Fin N) (a : Bool) : ℝ :=
  expect p (fun z => if z i = a then R i z else 0) / coin (p i) a

def pairMarginal {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ)
    (i j : Fin N) (a b : Bool) : ℝ :=
  expect p (fun z => if z i = a ∧ z j = b then X z else 0) /
    (coin (p i) a * coin (p j) b)

def nodeEffect {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (i : Fin N) : ℝ :=
  marginal p R i true - marginal p R i false

def ame {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) : ℝ :=
  (∑ i, nodeEffect p R i) / N

def barMu {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (a : Bool) : ℝ :=
  (∑ i, marginal p R i a) / N

def ht {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (z : Assignment N) : ℝ :=
  (∑ i, (bit (z i) * R i z / p i - (1 - bit (z i)) * R i z / (1 - p i))) / N

def armCount {N : ℕ} (z : Assignment N) (a : Bool) : ℝ :=
  ∑ i, if z i = a then (1 : ℝ) else 0

/-- Empty arms have mean zero, the convention used in the supplement. -/
def armMean {N : ℕ} (R : CircleTable N) (z : Assignment N) (a : Bool) : ℝ :=
  (∑ i, if z i = a then R i z else 0) / armCount z a

def hajek {N : ℕ} (R : CircleTable N) (z : Assignment N) : ℝ :=
  armMean R z true - armMean R z false

def augmented {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, (g i true - g i false + bit (z i) * (R i z - g i true) / p i -
    (1 - bit (z i)) * (R i z - g i false) / (1 - p i))) / N

/-- The corrected linearization, with control denominator N(1-p). -/
def linearHajek {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) : Assignment N → ℝ :=
  augmented p R (fun _ a => barMu p R a)

def interferes {N : ℕ} (R : CircleTable N) (i j : Fin N) : Prop :=
  i = j ∨ ∃ z z' : Assignment N,
    (∀ k, k ≠ j → z k = z' k) ∧ R i z ≠ R i z'

def sharesSource {N : ℕ} (R : CircleTable N) (i j : Fin N) : Prop :=
  ∃ l, interferes R i l ∧ interferes R j l

def ball {N : ℕ} (D : Fin N → Fin N → ℝ) (i : Fin N) (r : ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun j => D i j ≤ r)

def maxDegree {N : ℕ} (B : Fin N → Finset (Fin N)) : ℕ :=
  Finset.univ.sup (fun i => (B i).card)

def LocalAt {N : ℕ} (R : CircleTable N) (D : Fin N → Fin N → ℝ) (h : ℝ) : Prop :=
  ∀ i j, h < D i j → ¬ sharesSource R i j

def residualContrast {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) (z : Assignment N) : ℝ :=
  bit (z i) * (R i z - g i true) / p i -
    (1 - bit (z i)) * (R i z - g i false) / (1 - p i)

def residualEffect {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (i : Fin N) : ℝ :=
  nodeEffect p R i - (g i true - g i false)

def armSign (a : Bool) : ℝ := if a then 1 else -1

/-- The corrected second-moment terms (2) and (4) of Lemma A.4. -/
def secondMomentBound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  ((∑ i, (marginal p (fun i z => (R i z - g i true)^2) i true / p i +
    marginal p (fun i z => (R i z - g i false)^2) i false / (1-p i))) +
    ∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
      armSign a * armSign b * pairMarginal p
        (fun z => (R i z - g i a)*(R j z - g j b)) i j a b) / (N : ℝ)^2

/-- C5 for constant arm fits; the neighborhood includes its centre. -/
def homophilyQ {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ B i, residualEffect p R g i * residualEffect p R g j) / N

/-- Lines (2)-(5) of Lemma A.4, including both subtracted mean products. -/
def varianceExpansion {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) : ℝ :=
  ((∑ i, (marginal p (fun i z => (R i z - g i true)^2) i true / p i +
    marginal p (fun i z => (R i z - g i false)^2) i false / (1-p i) -
    (residualEffect p R g i)^2)) +
    ∑ i, ∑ j ∈ (B i).erase i, ∑ a : Bool, ∑ b : Bool,
      armSign a * armSign b *
        (pairMarginal p (fun z => (R i z - g i a)*(R j z - g j b)) i j a b -
          (marginal p R i a - g i a)*(marginal p R j b - g j b))) / (N : ℝ)^2

def htDiagonal {N : ℕ} (p : ℝ) (R : CircleTable N) : ℝ :=
  (∑ i, (marginal (fun _ => p) (fun i z => (R i z)^2) i true/p +
    marginal (fun _ => p) (fun i z => (R i z)^2) i false/(1-p) -
    (nodeEffect (fun _ => p) R i)^2)) / (N : ℝ)^2

def htPairCov {N : ℕ} (p : ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (a b : Bool) : ℝ :=
  (∑ i, ∑ j ∈ (B i).erase i,
    (pairMarginal (fun _ => p) (fun z => R i z * R j z) i j a b -
      marginal (fun _ => p) R i a * marginal (fun _ => p) R j b)) / (N : ℝ)^2

end
end SAP.P004c
