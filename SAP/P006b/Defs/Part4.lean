import Mathlib
import SAP.P006b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def missingWorldPrevalence (world : Bool) : ℝ := if world then 3/4 else 1/2

def missingObservationProbability (world y0 : Bool) : ℝ :=
  if world then 1/2 else if y0 then 3/4 else 1/4

def missingWorldMass (world y0 t r : Bool) : ℝ :=
  coinMass (missingWorldPrevalence world) y0 * (1/2 : ℝ) *
    (if t then (if r then 1 else 0)
      else coinMass (missingObservationProbability world y0) r)

def missingRecord (y0 t r : Bool) : Bool × Bool × Option Bool :=
  (t,r,if r then some (if t then true else y0) else none)

def missingObservedMass (world : Bool) (record : Bool × Bool × Option Bool) : ℝ :=
  ∑ y0 : Bool, ∑ t : Bool, ∑ r : Bool, missingWorldMass world y0 t r *
    (if missingRecord y0 t r = record then 1 else 0)

def missingWorldMean (world : Bool) : ℝ :=
  ∑ y0 : Bool, ∑ t : Bool, ∑ r : Bool, missingWorldMass world y0 t r * bit y0

def missingUntreatedObservedMean (world : Bool) : ℝ :=
  (∑ y0 : Bool, missingWorldMass world y0 false true * bit y0) /
    (∑ y0 : Bool, missingWorldMass world y0 false true)

def lowerBoundY0 (α : ℝ) (u : Bool) : ℝ := if u then -α else α

def lowerBoundY1 (β η : ℝ) (u : Bool) : ℝ := if u then -η else β

def lowerBoundReward (β η : ℝ) (π : BinaryPolicy) : ℝ :=
  oneTT (lowerBoundY1 β η) (fun _ _ => 0) π

def lowerBoundWelfare (α β η : ℝ) (π : BinaryPolicy) : ℝ :=
  binaryWelfare (1/2) (fun u => lowerBoundY1 β η u-lowerBoundY0 α u) π

def lowerBoundGamma (α : ℝ) : ℝ :=
  (∑ u : Bool, (1/2 : ℝ)*|0-lowerBoundY0 α u|)

def finiteIIDAverage (n : ℕ) (p : ℝ) (m : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ X : Fin n → Bool, ∑ T : Fin n → Bool,
    (∏ i, coinMass p (X i)) * (∏ i, coinMass (binaryRule π (X i)) (T i)) *
      wATO T (fun i => m (X i))

def finiteIIDTT (n : ℕ) (y1 : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ z : Fin n → (Bool × Bool),
    (∏ i, (1/2 : ℝ)*coinMass (binaryRule π (z i).1) (z i).2) *
      wTT (fun _ => 0) (fun i => (z i).1) (fun i => (z i).2)
        (fun i => y1 (z i).1)

end
end SAP.P006b
