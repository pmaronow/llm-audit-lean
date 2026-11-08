import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

abbrev Assignment (N : ℕ) := Fin N → Bool

def bit (a : Bool) : ℝ := if a then 1 else 0

def coin (p : ℝ) (a : Bool) : ℝ := if a then p else 1 - p

def designWeight {N : ℕ} (p : Fin N → ℝ) (z : Assignment N) : ℝ :=
  ∏ i, coin (p i) (z i)

def expect {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) : ℝ :=
  ∑ z, designWeight p z * X z

def prob {N : ℕ} (p : Fin N → ℝ) (A : Assignment N → Prop) : ℝ :=
  expect p (fun z => if A z then 1 else 0)

def cov {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) : ℝ :=
  expect p (fun z => X z * Y z) - expect p X * expect p Y

def variance {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) : ℝ := cov p X X

abbrev CircleTable (N : ℕ) := Fin N → Assignment N → ℝ

def marginal {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) (i : Fin N)
    (a : Bool) : ℝ :=
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

def armMean {N : ℕ} (R : CircleTable N) (z : Assignment N) (a : Bool) : ℝ :=
  (∑ i, if z i = a then R i z else 0) / armCount z a

def hajek {N : ℕ} (R : CircleTable N) (z : Assignment N) : ℝ :=
  armMean R z true - armMean R z false

def augmented {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, (g i true - g i false + bit (z i) * (R i z - g i true) / p i -
    (1 - bit (z i)) * (R i z - g i false) / (1 - p i))) / N

def linearHajek {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N) : Assignment N → ℝ :=
  augmented p R (fun _ a => barMu p R a)

def residual {N : ℕ} (R : CircleTable N) (z : Assignment N) (i : Fin N) : ℝ :=
  R i z - armMean R z (z i)

def interferes {N : ℕ} (R : CircleTable N) (i j : Fin N) : Prop :=
  i = j ∨ ∃ z z' : Assignment N,
    (∀ k, k ≠ j → z k = z' k) ∧ R i z ≠ R i z'

def sharesSource {N : ℕ} (R : CircleTable N) (i j : Fin N) : Prop :=
  ∃ l, interferes R i l ∧ interferes R j l

def ball {N : ℕ} (dist : Fin N → Fin N → ℝ) (i : Fin N) (r : ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun j => dist i j ≤ r)

def maxDegree {N : ℕ} (B : Fin N → Finset (Fin N)) : ℕ :=
  Finset.univ.sup (fun i => (B i).card)

def LocalAt {N : ℕ} (R : CircleTable N) (dist : Fin N → Fin N → ℝ) (h : ℝ) : Prop :=
  ∀ i j, h < dist i j → ¬ sharesSource R i j

end
end SAP.P004b
