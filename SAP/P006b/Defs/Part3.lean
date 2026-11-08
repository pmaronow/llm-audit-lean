import Mathlib
import SAP.P006b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def untreatedProbability {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (κ : Kernel X U) (π : (X × U) → ℝ) (x : X) : ℝ :=
  ∫ u, 1-π (x,u) ∂κ x

def untreatedConditionalLaw {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (κ : Kernel X U) (π : (X × U) → ℝ) (x : X) : Measure U :=
  (κ x).withDensity (fun u => ENNReal.ofReal
    ((1-π (x,u))/untreatedProbability κ π x))

def selectedBaseline {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (κ : Kernel X U) (μ0 : (X × U) → ℝ) (π : (X × U) → ℝ) (x : X) : ℝ :=
  (∫ u, μ0 (x,u)*(1-π (x,u)) ∂κ x) / untreatedProbability κ π x

def maximumDeviation {X U : Type*} (μ0 : (X × U) → ℝ) (c : X × U) : ℝ :=
  sSup (Set.range (fun u => |μ0 c-μ0 (c.1,u)|))

def finiteSelectedBaseline {K : ℕ} (p m π : Fin K → ℝ) : ℝ :=
  finiteA p m (fun i => 1-π i) / finiteMass p (fun i => 1-π i)

def leaveOnlyType {K : ℕ} (j : Fin K) : Fin K → ℝ :=
  fun i => if i = j then 0 else 1

def treatOnlyType {K : ℕ} (j : Fin K) : Fin K → ℝ :=
  fun i => if i = j then 1 else 0

def twoTTConstant (π : BinaryPolicy) : ℝ :=
  ∑ x0 : Bool, ∑ x1 : Bool, ∑ t0 : Bool, ∑ t1 : Bool,
    (1/4 : ℝ) * coinMass (binaryRule π x0) t0 *
      coinMass (binaryRule π x1) t1 *
      wTT (fun _ : Bool => 0) ![x0,x1] ![t0,t1] ![1,1]

def logistic (z : ℝ) : ℝ := 1/(1+Real.exp (-z))

structure LogisticFit (d : ℕ) where
  β0 : ℝ
  β1 : Fin d → ℝ
  β2 : ℝ
  β3 : Fin d → ℝ

def linearPredictor {d : ℕ} (β : LogisticFit d) (x : Fin d → ℝ) (t : Bool) : ℝ :=
  β.β0 + (∑ j, β.β1 j*x j) + β.β2*bit t + (∑ j, β.β3 j*x j*bit t)

def signedOutcome (alive : Bool) : ℝ := if alive then 1 else -1

def signedBernoulliMean (p : ℝ) : ℝ :=
  ∑ y : Bool, coinMass p y * signedOutcome y

def logisticWitnessMass (y0 y1 : Bool) : ℝ :=
  (1/2 : ℝ) * coinMass (1/4) y1

def empiricalGroup {C : Type*} [DecidableEq C] {n : ℕ}
    (X : Fin n → C) (x : C) : Finset (Fin n) := Finset.univ.filter (fun i => X i = x)

def empiricalMean {C : Type*} [DecidableEq C] {n : ℕ}
    (X : Fin n → C) (m : Fin n → ℝ) (x : C) : ℝ :=
  (∑ i ∈ empiricalGroup X x, m i) / (empiricalGroup X x).card

def empiricalGamma {C : Type*} [DecidableEq C] {n : ℕ}
    (X : Fin n → C) (m : Fin n → ℝ) : ℝ :=
  (∑ i, |empiricalMean X m (X i)-m i|) / n

end
end SAP.P006b
