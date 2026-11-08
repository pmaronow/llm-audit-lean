import Mathlib
import SAP.P006a.Defs.Part1
import SAP.P006a.Defs.Part2
import SAP.P006a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

universe u v
namespace SAP.P006a
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/- Ranking, fitted-sample summaries, and observed-law identification witnesses. -/
def UniformRankPreservation {K : Type*} {C : Type*}
    (PiSet : K → Set (C → ℝ)) (score : K → (C → ℝ) → ℝ) (τ : K → C → ℝ) : Prop :=
  ∀ j k, (∀ x, τ k x ≤ τ j x) →
    bestValue (PiSet k) (score k) ≤ bestValue (PiSet j) (score j)

def RelativeRankPreservation {K C : Type*} [MeasurableSpace C]
    (P0 : Measure C) (PiSet : K → Set (C → ℝ)) (score : K → (C → ℝ) → ℝ)
    (τ : K → C → ℝ) : Prop :=
  ∀ j k, (∫ x, τ k x ∂P0) ≤ (∫ x, τ j x ∂P0) →
    bestValue (PiSet k) (score k) ≤ bestValue (PiSet j) (score j)

def positivePart (t : ℝ) : ℝ := t * (if 0 < t then 1 else 0)

def referenceWeight {C : Type*} [MeasurableSpace C]
    (n : ℕ) (P0 Pk : Measure C) : C → ℝ :=
  fun x => (n : ℝ)⁻¹ * (P0.rnDeriv Pk x).toReal

def beneficiaries {n : ℕ} (τhat : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 < τhat i)

def positiveEffectSum {n : ℕ} (τhat : Fin n → ℝ) : ℝ :=
  ∑ i ∈ beneficiaries τhat, τhat i

def fittedOptimalUtility {n : ℕ} (τhat : Fin n → ℝ) : ℝ :=
  positiveEffectSum τhat / n

def beneficiaryMean {n : ℕ} (τhat : Fin n → ℝ) : ℝ :=
  positiveEffectSum τhat / (beneficiaries τhat).card

abbrev OutcomeLaw (C : Type*) [MeasurableSpace C] := Measure (C × (ℝ × ℝ))

def FiniteOutcomeLaw {C : Type*} [MeasurableSpace C] (D : OutcomeLaw C) : Prop :=
  IsProbabilityMeasure D ∧ Integrable (fun z => z.2.1) D ∧
    Integrable (fun z => z.2.2) D

def treatedProjection {C : Type*} : C × (ℝ × ℝ) → C × ℝ :=
  fun z => (z.1,z.2.2)

def oneATOExpectation {C : Type*} [MeasurableSpace C]
    (D : OutcomeLaw C) (π : C → ℝ) : ℝ :=
  ∫ z, (∑ t : Bool, coinMass (π z.1) t *
    wATO ![t] ![if t then z.2.2 else z.2.1]) ∂D

def outcomeWelfare {C : Type*} [MeasurableSpace C]
    (D : OutcomeLaw C) (π : C → ℝ) : ℝ :=
  ∫ z, π z.1 * (z.2.2-z.2.1) ∂D

def NondegenerateReward {C : Type*} [MeasurableSpace C]
    (PiSet : Set (C → ℝ)) (reward : OutcomeLaw C → (C → ℝ) → ℝ) : Prop :=
  ∃ D π, FiniteOutcomeLaw D ∧ IsBest PiSet (reward D) π ∧
    0 < (∫ z, π z.1 ∂D)

def TreatedDataInvariant {C : Type*} [MeasurableSpace C]
    (PiSet : Set (C → ℝ)) (reward : OutcomeLaw C → (C → ℝ) → ℝ) : Prop :=
  ∀ D D', FiniteOutcomeLaw D → FiniteOutcomeLaw D' →
    Measure.map treatedProjection D = Measure.map treatedProjection D' →
    ∀ π ∈ PiSet, reward D π = reward D' π

def shiftedOutcomeLaw {C : Type*} [MeasurableSpace C]
    (D : OutcomeLaw C) (B : ℝ) : OutcomeLaw C :=
  Measure.map (fun z => (z.1,(z.2.2+B,z.2.2))) D

def intervalLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

def referenceWithAtom : Measure ℝ :=
  (1/2 : ℝ≥0∞) • intervalLaw + (1/2 : ℝ≥0∞) • Measure.dirac (1/2)

def deterministicObserved (y0 y1 : Bool → ℝ) (x t : Bool) : ℝ :=
  if t then y1 x else y0 x

def binaryObservedMass (y0 y1 : Bool → ℝ) (π : BinaryPolicy)
    (record : Bool × Bool × ℝ) : ℝ :=
  ∑ x : Bool, ∑ t : Bool, (1/2 : ℝ)*coinMass (binaryRule π x) t *
    (if record = (x,t,deterministicObserved y0 y1 x t) then 1 else 0)

def singletonObservedMass (y0 y1 : ℝ) (record : Bool × ℝ) : ℝ :=
  ∑ t : Bool, coinMass 1 t * (if record = (t,if t then y1 else y0) then 1 else 0)

def maximumDeviation {X U : Type*} (μ0 : (X × U) → ℝ) (c : X × U) : ℝ :=
  sSup (Set.range (fun u => |μ0 c-μ0 (c.1,u)|))

end
end SAP.P006a
