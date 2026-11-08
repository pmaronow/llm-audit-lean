import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Assignment (n : ℕ) := Fin n → Bool

def bit (b : Bool) : ℝ := if b then 1 else 0

structure Law (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

def mean {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.mass ω * X ω

def prob {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) : ℝ :=
  mean P (fun ω => if A ω then 1 else 0)

def cmean {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) (X : Ω → ℝ) : ℝ :=
  mean P (fun ω => if A ω then X ω else 0) / prob P A

def cov {Ω : Type*} [Fintype Ω] (P : Law Ω) (X Y : Ω → ℝ) : ℝ :=
  mean P (fun ω => (X ω - mean P X) * (Y ω - mean P Y))

def var {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) : ℝ := cov P X X

def ccov {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) (X Y : Ω → ℝ) : ℝ :=
  cmean P A (fun ω => (X ω - cmean P A X) * (Y ω - cmean P A Y))

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

def eate {n : ℕ} (E : Experiment n) : ℝ := mean E.design (ateAt E)

def adse {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, (cmean E.design (fun z => z i = true) (E.outcome i) -
    cmean E.design (fun z => z i = false) (E.outcome i))) / n

def muHat {n : ℕ} (E : Experiment n) (b : Bool) (z : Assignment n) : ℝ :=
  (∑ i, (if z i = b then E.outcome i z else 0) / marginal E i b) / n

def nHat {n : ℕ} (E : Experiment n) (b : Bool) (z : Assignment n) : ℝ :=
  ∑ i, (if z i = b then (1 : ℝ) else 0) / marginal E i b

def mu {n : ℕ} (E : Experiment n) (b : Bool) : ℝ :=
  (∑ i, mean E.design (potential E i b)) / n

def muBreve {n : ℕ} (E : Experiment n) (b : Bool) : ℝ :=
  (∑ i, cmean E.design (fun z => z i = b) (potential E i b)) / n

def ht {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ :=
  muHat E true z - muHat E false z

def ArmsNonempty {n : ℕ} (E : Experiment n) (z : Assignment n) : Prop :=
  nHat E true z ≠ 0 ∧ nHat E false z ≠ 0

def hajek {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ :=
  if ArmsNonempty E z then
    (n : ℝ) * muHat E true z / nHat E true z -
    (n : ℝ) * muHat E false z / nHat E false z
  else 0

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

def incoming {n : ℕ} (E : Experiment n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => Interferes E j i)).card

def C2 {n : ℕ} (E : Experiment n) : ℝ :=
  Real.sqrt ((∑ i, outgoing E i ^ 2) / n)

def dMax {n : ℕ} (E : Experiment n) : ℝ := sSup (Set.range (degree E))

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

def vBER {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ :=
  (∑ i, ((if z i then E.outcome i z ^ 2 else 0) / marginal E i true ^ 2 +
    (if z i then 0 else E.outcome i z ^ 2) / marginal E i false ^ 2)) / (n : ℝ) ^ 2

def msq {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, mean E.design (effect E i) ^ 2) / n

def xi {n : ℕ} (E : Experiment n) (i j : Fin n) (a : Bool) : ℝ :=
  mean E.design (fun z =>
    E.outcome i (Function.update (Function.update z i a) j true) -
    E.outcome i (Function.update (Function.update z i a) j false))

def xiBreve {n : ℕ} (E : Experiment n) (i j : Fin n) : ℝ :=
  (1 - marginal E i true) * xi E i j true + marginal E i true * xi E i j false

def yBreve {n : ℕ} (E : Experiment n) (i : Fin n) : ℝ :=
  (1 - marginal E i true) * cmean E.design (fun z => z i = true) (E.outcome i) +
  marginal E i true * cmean E.design (fun z => z i = false) (E.outcome i)

def B1 {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, ∑ j, if j = i then 0 else
    xiBreve E i j * xiBreve E j i +
    2 * yBreve E j * (xi E i j true - xi E i j false)) / ((n : ℝ) * dAvg E)

def B2 {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, ∑ j, if j = i then 0 else
    ∑ a : Bool, ∑ b : Bool,
      (1 - 2 * bit a) * (1 - 2 * bit b) *
        ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)) /
      ((n : ℝ) * dAvg E)

def quadD {n : ℕ} (E : Experiment n) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * d E i j * v j

def lambdaMax {n : ℕ} (E : Experiment n) : ℝ :=
  sSup {r | ∃ v : Fin n → ℝ, (∑ i, v i ^ 2) = 1 ∧ r = quadD E v}

def vAVG {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ := dAvg E * vBER E z

def vMAX {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ := dMax E * vBER E z

end
end SAP.P009b
