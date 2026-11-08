import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009c
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Assignment (n : ℕ) := Fin n → Bool

def bit (b : Bool) : ℝ := if b then 1 else 0

/-- A probability law on a finite assignment space; expectation is a finite sum. -/
structure Law (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

def mean {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.mass ω * X ω

def prob {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) : ℝ :=
  mean P (fun ω => if A ω then 1 else 0)

/-- Conditional mean; claims using it ensure the conditioning event has positive mass. -/
def cmean {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) (X : Ω → ℝ) : ℝ :=
  mean P (fun ω => if A ω then X ω else 0) / prob P A

def cov {Ω : Type*} [Fintype Ω] (P : Law Ω) (X Y : Ω → ℝ) : ℝ :=
  mean P (fun ω => (X ω - mean P X) * (Y ω - mean P Y))

def var {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) : ℝ := cov P X X

def ccov {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) (X Y : Ω → ℝ) : ℝ :=
  cmean P A (fun ω => (X ω - cmean P A X) * (Y ω - cmean P A Y))

/-- The design and potential outcomes on the entire binary cube, including null assignments. -/
structure Experiment (n : ℕ) where
  design : Law (Assignment n)
  outcome : Fin n → Assignment n → ℝ

def marginal {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool) : ℝ :=
  prob E.design (fun z => z i = b)

def potential {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool)
    (z : Assignment n) : ℝ := E.outcome i (Function.update z i b)

def effect {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n) : ℝ :=
  potential E i true z - potential E i false z

def ateAt {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ :=
  (∑ i, effect E i z) / n

def NoInterference {n : ℕ} (E : Experiment n) : Prop :=
  ∀ i z z', z i = z' i → E.outcome i z = E.outcome i z'

def ate {n : ℕ} (E : Experiment n) : ℝ := ateAt E (fun _ => false)

def eate {n : ℕ} (E : Experiment n) : ℝ := mean E.design (ateAt E)

def adse {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, (cmean E.design (fun z => z i = true) (E.outcome i) -
    cmean E.design (fun z => z i = false) (E.outcome i))) / n

def muHat {n : ℕ} (E : Experiment n) (b : Bool) (z : Assignment n) : ℝ :=
  (∑ i, (if z i = b then E.outcome i z else 0) / marginal E i b) / n

def nHat {n : ℕ} (E : Experiment n) (b : Bool) (z : Assignment n) : ℝ :=
  ∑ i, (if z i = b then (1 : ℝ) else 0) / marginal E i b

def ht {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ :=
  muHat E true z - muHat E false z

def ArmsNonempty {n : ℕ} (E : Experiment n) (z : Assignment n) : Prop :=
  nHat E true z ≠ 0 ∧ nHat E false z ≠ 0

/-- The printed contrast on nonempty weighted arms, extended by zero elsewhere.
For positive populations, complete and paired randomization give nonempty weighted
arms on their design support. Statements using `HajekExtension` allow arbitrary
values off the nonzero-denominator domain. -/
def hajek {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ :=
  if ArmsNonempty E z then
    (n : ℝ) * muHat E true z / nHat E true z -
    (n : ℝ) * muHat E false z / nHat E false z
  else 0

/-- Full-cube structural interference, including the paper's mandatory diagonal. -/
def Interferes {n : ℕ} (E : Experiment n) (i j : Fin n) : Prop :=
  i = j ∨ ∃ z z', (∀ ℓ, ℓ ≠ i → z ℓ = z' ℓ) ∧ E.outcome j z ≠ E.outcome j z'

def I {n : ℕ} (E : Experiment n) (i j : Fin n) : ℝ :=
  if Interferes E i j then 1 else 0

def Dependent {n : ℕ} (E : Experiment n) (i j : Fin n) : Prop :=
  ∃ ℓ, Interferes E ℓ i ∧ Interferes E ℓ j

def d {n : ℕ} (E : Experiment n) (i j : Fin n) : ℝ :=
  if Dependent E i j then 1 else 0

def degree {n : ℕ} (E : Experiment n) (i : Fin n) : ℝ := ∑ j, d E i j

def dAvg {n : ℕ} (E : Experiment n) : ℝ := (∑ i, degree E i) / n

def outgoing {n : ℕ} (E : Experiment n) (i : Fin n) : ℝ := ∑ j, I E i j

def C1 {n : ℕ} (E : Experiment n) : ℝ := (∑ i, outgoing E i) / n

def C2 {n : ℕ} (E : Experiment n) : ℝ :=
  Real.sqrt ((∑ i, outgoing E i ^ 2) / n)

def Cp {n : ℕ} (E : Experiment n) (p : ℝ) : ℝ :=
  Real.rpow ((∑ i, Real.rpow (outgoing E i) p) / n) (1 / p)

/-- The maximum outgoing count; the claims always have a positive population size. -/
def Cinf {n : ℕ} (E : Experiment n) : ℝ := sSup (Set.range (outgoing E))

def dMax {n : ℕ} (E : Experiment n) : ℝ := sSup (Set.range (degree E))

def dRMS {n : ℕ} (E : Experiment n) : ℝ := Real.sqrt ((∑ i, degree E i ^ 2) / n)

structure Pairing (n : ℕ) where
  partner : Fin n ≃ Fin n
  involution : ∀ i, partner (partner i) = i
  no_fixed : ∀ i, partner i ≠ i

def e {n : ℕ} (E : Experiment n) (ρ : Pairing n) (i j : Fin n) : ℝ :=
  if ¬ Dependent E i j ∧ ∃ ℓ, Interferes E ℓ i ∧ Interferes E (ρ.partner ℓ) j
  then 1 else 0

def eAvg {n : ℕ} (E : Experiment n) (ρ : Pairing n) : ℝ :=
  (∑ i, ∑ j, e E ρ i j) / n

def rSum {n : ℕ} (E : Experiment n) (ρ : Pairing n) : ℝ :=
  ∑ i, I E (ρ.partner i) i

def Bernoulli {n : ℕ} (E : Experiment n) : Prop :=
  (∀ i, 0 < marginal E i true ∧ marginal E i true < 1) ∧
  ∀ z, E.design.mass z = ∏ i, (if z i then marginal E i true else 1 - marginal E i true)

def Complete {n : ℕ} (E : Experiment n) (m : ℕ) : Prop :=
  0 < m ∧ m < n ∧ ∀ z, E.design.mass z =
    if (∑ i, if z i then (1 : ℕ) else 0) = m then 1 / (n.choose m : ℝ) else 0

def Paired {n : ℕ} (E : Experiment n) (ρ : Pairing n) : Prop :=
  Even n ∧ ∀ z, E.design.mass z =
    if ∀ i, z i ≠ z (ρ.partner i) then 1 / (2 : ℝ) ^ (n / 2) else 0

/-- Assumption 1: uniform interior assignment probabilities and observed/potential moments. -/
def Regular {n : ℕ} (E : Experiment n) (k q s : ℝ) : Prop :=
  0 < k ∧ 2 ≤ q ∧ 1 ≤ s ∧
  (∀ i, k⁻¹ ≤ marginal E i true ∧ marginal E i true ≤ 1 - k⁻¹) ∧
  (∀ i, mean E.design (fun z => Real.rpow |E.outcome i z| q) ≤ Real.rpow k q) ∧
  (∀ i b, mean E.design (fun z => Real.rpow |potential E i b z| s) ≤ Real.rpow k s)

def masked {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n) : Assignment n :=
  fun j => if Interferes E j i then z j else false

def maskedOthers {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n) : Assignment n :=
  Function.update (masked E i z) i false

def alpha {Ω A B : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → A) (Y : Ω → B) : ℝ :=
  sSup {r | ∃ (S : Set A) (T : Set B),
    r = |prob P (fun ω => X ω ∈ S ∧ Y ω ∈ T) -
      prob P (fun ω => X ω ∈ S) * prob P (fun ω => Y ω ∈ T)|}

def mixPower (a θ : ℝ) : ℝ := if a = 0 then 0 else Real.rpow a θ

def alphaExt {n : ℕ} (E : Experiment n) (θ : ℝ) : ℝ :=
  (∑ i, ∑ j, (1 - d E i j) * mixPower
    (alpha E.design (masked E i) (masked E j)) θ) / n

def alphaInt {n : ℕ} (E : Experiment n) (θ : ℝ) : ℝ :=
  ∑ i, mixPower (alpha E.design (fun z => z i) (maskedOthers E i)) θ

def vBER {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ :=
  (∑ i, ((if z i then E.outcome i z ^ 2 else 0) / marginal E i true ^ 2 +
    (if z i then 0 else E.outcome i z ^ 2) / marginal E i false ^ 2)) / (n : ℝ) ^ 2

def msq {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, mean E.design (effect E i) ^ 2) / n
end
end SAP.P009c
