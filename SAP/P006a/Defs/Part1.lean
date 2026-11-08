import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

universe u v
namespace SAP.P006a
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/- Shared measurable treatment experiments, rewards, and attained optimization. -/
def Admissible {C : Type*} [MeasurableSpace C] (π : C → ℝ) : Prop :=
  Measurable π ∧ ∀ x, 0 ≤ π x ∧ π x ≤ 1

def bit (t : Bool) : ℝ := if t then 1 else 0

def treatedCount {n : ℕ} (T : Fin n → Bool) : ℝ := ∑ i, bit (T i)

def wATO {n : ℕ} (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  if 0 < treatedCount T then (∑ i, Y i * bit (T i)) / treatedCount T else 0

def wATT {C : Type*} {n : ℕ} (μhat : C → ℝ) (X : Fin n → C)
    (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  wATO T (fun i => Y i - μhat (X i))

def wWeightedTT {C : Type*} {n : ℕ} (μhat g : C → ℝ) (X : Fin n → C)
    (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  ∑ i, (Y i - μhat (X i)) * bit (T i) * g (X i)

def wTT {C : Type*} {n : ℕ} (μhat : C → ℝ) (X : Fin n → C)
    (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  wWeightedTT μhat (fun _ => 1) X T Y

def IsBest {P : Type*} (PiSet : Set P) (f : P → ℝ) (π : P) : Prop :=
  π ∈ PiSet ∧ ∀ π' ∈ PiSet, f π' ≤ f π

def bestValue {P : Type*} (PiSet : Set P) (f : P → ℝ) : ℝ := sSup (f '' PiSet)

def regret {P : Type*} (PiSet : Set P) (V : P → ℝ) (π : P) : ℝ :=
  bestValue PiSet V - V π

def positiveRule {C : Type*} (m : C → ℝ) : C → ℝ :=
  fun x => if 0 < m x then 1 else 0

def printedAverageRule {C : Type*} (m : C → ℝ) : C → ℝ :=
  fun x => if (∀ z, m z ≤ m x) ∧ 0 < m x then 1 else 0

def emptyFactor (n : ℕ) (q : ℝ) : ℝ := ∑ j ∈ Finset.range n, (1 - q) ^ j

structure Experiment (Ω C : Type*) [MeasurableSpace Ω] [MeasurableSpace C]
    (n : ℕ) where
  
  hn : 0 < n
  

  PX : Measure C
  
  μ0 : C → ℝ
  
  μ1 : C → ℝ
  

  law : (C → ℝ) → Measure Ω
  
  X : Fin n → Ω → C
  
  Y0 : Fin n → Ω → ℝ
  
  Y1 : Fin n → Ω → ℝ
  
  T : (C → ℝ) → Fin n → Ω → Bool
  


  μhat : (C → ℝ) → Ω → C → ℝ

namespace Experiment
variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}

def τ (E : Experiment Ω C n) : C → ℝ := fun x => E.μ1 x - E.μ0 x

def observed (E : Experiment Ω C n) (π : C → ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => if E.T π i ω then E.Y1 i ω else E.Y0 i ω

def V (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ ω, E.observed π ω ⟨0, E.hn⟩ - E.Y0 ⟨0, E.hn⟩ ω ∂E.law π

def meanWelfare (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ x, π x * E.τ x ∂E.PX

def expectedATO (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ ω, wATO (fun i => E.T π i ω) (E.observed π ω) ∂E.law π

def expectedATT (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ ω, wATT (E.μhat π ω) (fun i => E.X i ω)
    (fun i => E.T π i ω) (E.observed π ω) ∂E.law π

def expectedWeightedTT (E : Experiment Ω C n) (g π : C → ℝ) : ℝ :=
  ∫ ω, wWeightedTT (E.μhat π ω) g (fun i => E.X i ω)
    (fun i => E.T π i ω) (E.observed π ω) ∂E.law π

def expectedTT (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  E.expectedWeightedTT (fun _ => 1) π

def q (E : Experiment Ω C n) (π : C → ℝ) : ℝ := ∫ x, π x ∂E.PX

def A (E : Experiment Ω C n) (m π : C → ℝ) : ℝ := ∫ x, m x * π x ∂E.PX

def averageObjective (E : Experiment Ω C n) (m π : C → ℝ) : ℝ :=
  emptyFactor n (E.q π) * E.A m π

def covariateSigma (E : Experiment Ω C n) (i : Fin n) : MeasurableSpace Ω :=
  MeasurableSpace.comap (E.X i) inferInstance

def vectorSigma (E : Experiment Ω C n) (π : C → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => ((fun i => E.X i ω), (fun i => E.T π i ω)))
    inferInstance

end Experiment

end
end SAP.P006a
