import Mathlib
import SAP.P006a.Defs.Part1
import SAP.P006a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

universe u v
namespace SAP.P006a
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/- Exact finite experiments use Boolean covariates, false = 0 and true = 1. -/
abbrev BinaryPolicy := ℝ × ℝ

def binaryRule (p : BinaryPolicy) : Bool → ℝ := fun x => if x then p.2 else p.1

def binaryFeasible (p : BinaryPolicy) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

def binaryPolicies : Set BinaryPolicy := {p | binaryFeasible p}

def coinMass (q : ℝ) (t : Bool) : ℝ := if t then q else 1 - q

def twoATO (p : ℝ) (m : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ x0 : Bool, ∑ x1 : Bool, ∑ t0 : Bool, ∑ t1 : Bool,
    coinMass p x0 * coinMass p x1 *
      coinMass (binaryRule π x0) t0 * coinMass (binaryRule π x1) t1 *
      wATO ![t0, t1] ![m x0, m x1]

def oneTT (y1 : Bool → ℝ) (est : Bool → Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ x : Bool, ∑ t : Bool,
    (1 / 2 : ℝ) * coinMass (binaryRule π x) t *
      wTT (est x) ![x] ![t] ![y1 x]

def binaryWelfare (p : ℝ) (τ : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  (1 - p) * π.1 * τ false + p * π.2 * τ true

def effectE001 (x : Bool) : ℝ := if x then 1 else 9/10

def rewardE001 (π : BinaryPolicy) : ℝ := twoATO (1/2) effectE001 π

def estA (s x : Bool) : ℝ := if x = s then 1 else -1

def estB (s x : Bool) : ℝ := -estA s x

def fixedEstimatorMean (est : Bool → Bool → ℝ) (x : Bool) : ℝ :=
  ∑ s : Bool, (1/2 : ℝ) * est s x

def welfareA (π : BinaryPolicy) : ℝ :=
  binaryWelfare (1/2) (fun _ => 1/2) π

def welfareB (π : BinaryPolicy) : ℝ :=
  binaryWelfare (1/2) (fun _ => -1/2) π

def rewardA (π : BinaryPolicy) : ℝ := oneTT (fun _ => 1/2) estA π

def rewardB (π : BinaryPolicy) : ℝ := oneTT (fun _ => -1/2) estB π

def sharedEst (xj xk x : Bool) : ℝ := (if x = xj then 1 else 0) -
  (if x = xk then 1 else 0)

def scoreJ (π : BinaryPolicy) : ℝ :=
  ∑ xj : Bool, ∑ xk : Bool, ∑ t : Bool,
    (1/4 : ℝ) * coinMass (binaryRule π xj) t *
      wTT (sharedEst xj xk) ![xj] ![t] ![1/4]

def scoreK (π : BinaryPolicy) : ℝ :=
  ∑ xj : Bool, ∑ xk : Bool, ∑ t : Bool,
    (1/4 : ℝ) * coinMass (binaryRule π xk) t *
      wTT (sharedEst xj xk) ![xk] ![t] ![1/8]

def eventMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) (f : Ω → ℝ) : ℝ :=
  (∫ ω in s, f ω ∂μ) / (μ s).toReal

def finitePolicies {K : ℕ} : Set (Fin K → ℝ) :=
  {π | ∀ i, 0 ≤ π i ∧ π i ≤ 1}

def finiteMass {K : ℕ} (p π : Fin K → ℝ) : ℝ := ∑ i, p i * π i

def finiteA {K : ℕ} (p m π : Fin K → ℝ) : ℝ := ∑ i, p i * m i * π i

def prefixMass {K : ℕ} (p : Fin K → ℝ) (j : Fin K) : ℝ :=
  ∑ i, if i < j then p i else 0

def prefixA {K : ℕ} (p m : Fin K → ℝ) (j : Fin K) : ℝ :=
  ∑ i, if i < j then p i * m i else 0

def thresholdRule {K : ℕ} (p : Fin K → ℝ) (j : Fin K) (q : ℝ) : Fin K → ℝ :=
  fun i => if i < j then 1 else if i = j then (q-prefixMass p j)/p j else 0

def finiteConditionalAverage {K : ℕ} (p m π : Fin K → ℝ) : ℝ :=
  if 0 < finiteMass p π then finiteA p m π / finiteMass p π else 0

def binaryMarginalHeterogeneity (b0 μ0 : Bool → ℝ) : ℝ :=
  ∑ x : Bool, (1/2 : ℝ)*|b0 x-μ0 x|

def binaryObservedWelfare (p : ℝ) (y0 y1 : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ x : Bool, ∑ t : Bool, coinMass p x*coinMass (binaryRule π x) t*
    ((if t then y1 x else y0 x)-y0 x)

/-- One-unit ATT expectation in the same fair-covariate experiment as oneTT. -/
def oneATT (y1 : Bool → ℝ) (est : Bool → Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ x : Bool, ∑ t : Bool, (1/2 : ℝ) * coinMass (binaryRule π x) t *
    wATT (est x) ![x] ![t] ![y1 x]

/-- Treated estimator mean, used only at the all-treated policy (denominator one). -/
def treatedEstimatorMean (est : Bool → Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  (∑ x : Bool, (1/2 : ℝ) * binaryRule π x * est x x) /
    (∑ x : Bool, (1/2 : ℝ) * binaryRule π x)

/-- Actual two-unit ATO expectation, retaining the SUTVA observed outcomes. -/
def witnessReward (π : BinaryPolicy) : ℝ :=
  ∑ x0 : Bool, ∑ x1 : Bool, ∑ t0 : Bool, ∑ t1 : Bool,
    coinMass (1/2) x0 * coinMass (1/2) x1 *
      coinMass (binaryRule π x0) t0 * coinMass (binaryRule π x1) t1 *
      wATO ![t0,t1] (fun i => if ![t0,t1] i then
        ![effectE001 x0,effectE001 x1] i else 0)

/-- Actual welfare E[Y(T) - Y(0)] in the zero-baseline two-point witness. -/
def witnessWelfare (π : BinaryPolicy) : ℝ :=
  binaryObservedWelfare (1/2) (fun _ => 0) effectE001 π

/-- ATT objective with the nonrandom zero baseline in the two-unit witness. -/
def rewardE001ATT (π : BinaryPolicy) : ℝ :=
  ∑ x0 : Bool, ∑ x1 : Bool, ∑ t0 : Bool, ∑ t1 : Bool,
    coinMass (1/2) x0 * coinMass (1/2) x1 *
      coinMass (binaryRule π x0) t0 * coinMass (binaryRule π x1) t1 *
      wATT (fun _ => 0) ![x0,x1] ![t0,t1] ![effectE001 x0,effectE001 x1]

end
end SAP.P006a
