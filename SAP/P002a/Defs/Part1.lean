import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
attribute [local instance] Classical.propDecidable

structure Population (n : ℕ) where
  y : Fin n → Bool → ℝ
  d : Fin n → Bool → Bool
  n1 : ℕ

structure CovPopulation (n k : ℕ) where
  pop : Population n
  x : Fin n → Fin k → ℝ

def binary (b : Bool) : ℝ := if b then 1 else 0

def compliers {n : ℕ} (P : Population n) : Finset (Fin n) :=
  Finset.univ.filter fun i => P.d i false = false ∧ P.d i true = true

def MonotoneReceipt {n : ℕ} (P : Population n) : Prop :=
  ∀ i, P.d i false = true → P.d i true = true

def mean {n : ℕ} (q : Fin n → ℝ) : ℝ := (∑ i, q i) / (n : ℝ)

def groupMean {n : ℕ} (S : Finset (Fin n)) (q : Fin n → ℝ) : ℝ :=
  (∑ i ∈ S, q i) / (S.card : ℝ)

def late {n : ℕ} (P : Population n) : ℝ :=
  groupMean (compliers P) fun i => P.y i true - P.y i false

def popVar {n : ℕ} (q : Fin n → ℝ) : ℝ :=
  (∑ i, (q i - mean q) ^ 2) / ((n : ℝ) - 1)

def popCov {n : ℕ} (q t : Fin n → ℝ) : ℝ :=
  (∑ i, (q i - mean q) * (t i - mean t)) / ((n : ℝ) - 1)

def groupCov {n : ℕ} (S : Finset (Fin n)) (q t : Fin n → ℝ) : ℝ :=
  if 2 ≤ S.card then
    (∑ i ∈ S, (q i - groupMean S q) * (t i - groupMean S t)) / ((S.card : ℝ) - 1)
  else 0

def groupVar {n : ℕ} (S : Finset (Fin n)) (q : Fin n → ℝ) : ℝ := groupCov S q q

def w {n : ℕ} (P : Population n) (a : Bool) (β : ℝ) (i : Fin n) : ℝ :=
  P.y i (P.d i a) - β * binary (P.d i a)

def v {n : ℕ} (P : Population n) (a : Bool) (β : ℝ) (i : Fin n) : ℝ :=
  w P a β i - mean (w P a β)

def fraction {n : ℕ} (P : Population n) : ℝ := (P.n1 : ℝ) / (n : ℝ)

def controlSize {n : ℕ} (P : Population n) : ℝ := (n : ℝ) - (P.n1 : ℝ)

def ValidDesign {n : ℕ} (P : Population n) : Prop := 2 ≤ n ∧ 0 < P.n1 ∧ P.n1 < n

def assignments {n : ℕ} (P : Population n) : Finset (Finset (Fin n)) :=
  Finset.univ.powersetCard P.n1

def expectation {n : ℕ} (P : Population n) (f : Finset (Fin n) → ℝ) : ℝ :=
  (∑ S ∈ assignments P, f S) / ((assignments P).card : ℝ)

def designVariance {n : ℕ} (P : Population n) (f : Finset (Fin n) → ℝ) : ℝ :=
  expectation P fun S => (f S - expectation P f) ^ 2

def probability {n : ℕ} (P : Population n) (E : Finset (Fin n) → Prop) : ℝ :=
  (((assignments P).filter E).card : ℝ) / ((assignments P).card : ℝ)

def observedD {n : ℕ} (P : Population n) (S : Finset (Fin n)) (i : Fin n) : Bool :=
  P.d i (decide (i ∈ S))

def observedY {n : ℕ} (P : Population n) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  P.y i (observedD P S i)

def observedW {n : ℕ} (P : Population n) (β : ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  observedY P S i - β * binary (observedD P S i)

def rawTau {n : ℕ} (P : Population n) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ i, q i * ((if i ∈ S then 1 else 0) - fraction P)) / (n : ℝ)

def tau {n : ℕ} (P : Population n) (β : ℝ) (S : Finset (Fin n)) : ℝ :=
  rawTau P (observedW P β S) S

def armMean {n : ℕ} (q : Fin n → ℝ) (S : Finset (Fin n)) (a : Bool) : ℝ :=
  groupMean (if a then S else Sᶜ) q

def rawSigma2 {n : ℕ} (P : Population n) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (fraction P) ^ 2 * (1 - fraction P) ^ 2 *
    ((∑ i ∈ S, (q i - armMean q S true) ^ 2) / (P.n1 : ℝ) ^ 2 +
     (∑ i ∈ Sᶜ, (q i - armMean q S false) ^ 2) / (controlSize P) ^ 2)

def absStudent (t s2 : ℝ) : ℝ≥0∞ :=
  if s2 = 0 then (if t = 0 then 0 else ⊤) else ENNReal.ofReal (|t| / Real.sqrt s2)

def rawAR {n : ℕ} (P : Population n) (q : Fin n → ℝ) (S : Finset (Fin n)) : ℝ≥0∞ :=
  absStudent (rawTau P q S) (rawSigma2 P q S)

def quantile {n : ℕ} (P : Population n) (g : Finset (Fin n) → ℝ≥0∞) (α : ℝ) : ℝ≥0∞ :=
  let C := ((assignments P).image g).filter fun t => 1 - α ≤ probability P (fun S => g S ≤ t)
  if h : C.Nonempty then C.min' h else ⊤

def accepted {n : ℕ} (P : Population n) (β α : ℝ) (S : Finset (Fin n)) : Prop :=
  rawAR P (observedW P β S) S ≤ quantile P (rawAR P (observedW P β S)) α

def coverage {n : ℕ} (P : Population n) (β α : ℝ) : ℝ :=
  probability P (accepted P β α)

def S2 {n : ℕ} (P : Population n) (β : ℝ) (a : Bool) : ℝ :=
  (fraction P)^2 * (1-fraction P)^2 * popVar (w P a β)

def Sdiff2 {n : ℕ} (P : Population n) (β : ℝ) : ℝ :=
  (fraction P)^2 * (1-fraction P)^2 *
    (∑ i, (v P true β i - v P false β i)^2) / ((n : ℝ)-1)

def fourthNorm {n : ℕ} (q : Fin n → ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (mean fun i => q i ^ 4))

def Theta {n : ℕ} (P : Population n) (δ r A : ℝ) : Prop :=
  ValidDesign P ∧ MonotoneReceipt P ∧ (compliers P).Nonempty ∧
  r * (n : ℝ) ≤ (P.n1 : ℝ) ∧ (P.n1 : ℝ) ≤ (1-r) * (n : ℝ) ∧
  groupCov (compliers P) (w P true (late P)) (w P false (late P)) ≥
    -δ * Real.sqrt (groupVar (compliers P) (w P true (late P))) *
      Real.sqrt (groupVar (compliers P) (w P false (late P))) ∧
  ∀ a, fourthNorm (v P a (late P)) ≤ A * Real.sqrt (popVar (w P a (late P)))

end
end SAP.P002a
