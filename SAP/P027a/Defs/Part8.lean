import Mathlib
import SAP.P027a.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

def InvalidPPSWitness : Prop :=
  (∑ k, invalidSize8 k) = 37 ∧ printedPPS 2 invalidSize8 0 = 60/37 ∧
    (∑ k, printedPPS 2 invalidSize8 k) = 2 ∧
    printedPPS 2 invalidSize8 0 - 1 = 23/37 ∧
    ∀ (Ω' : Type) [Fintype Ω'] (D : Design (Fin 8) Ω'), Valid D →
      ¬ (∀ k, pi D k = printedPPS 2 invalidSize8 k)

def InvalidPPSValues : Prop :=
  
  (∀ k, printedPPS 2 invalidSize8 k = if k = 0 then 60/37 else 2/37) ∧
  (∀ (Ω : Type) [Fintype Ω] (D : Design (Fin 8) Ω), Valid D → ∀ k, pi D k ≤ 1) ∧
  (∀ k, 1+(nbWitness k : ℝ) = invalidSize8 k)

def NegativeBinomialWitness : Prop :=
  IsProbabilityMeasure nbProductLaw ∧
    (∀ (k : Fin 8) (j : ℕ), (nbProductLaw {v | v k = j}).toReal = nbMass j) ∧
    (∀ k : Fin 8, outcomeE nbProductLaw (fun v => (v k:ℝ)) = 6 ∧
      outcomeE nbProductLaw (fun v => ((v k:ℝ)-6)^2) = 16) ∧
    (nbProductLaw {nbWitness}).toReal = nbMass 29*nbMass 0^7 ∧
    0 < (nbProductLaw {nbWitness}).toReal

def NBFiniteMoments : Prop :=
  ∀ k : Fin 8,
  Integrable (fun v : Fin 8 → ℕ => (v k : ℝ)) nbProductLaw ∧
  Integrable (fun v : Fin 8 → ℕ => ((v k : ℝ)-6)^2) nbProductLaw

def AllPPSConfigurations : Prop :=
  ∀ row : Fin 6,
let N := ppsConfigurationN row
    let m := ppsConfigurationM row
    let L := ppsConfigurationL row
    let v : Fin N → ℕ := fun k => if k.val = 0 then L-1 else 0
    let x : Fin N → ℝ := fun k => 1 + (v k : ℝ)
    2 ≤ N ∧ 0 < m ∧ m < N ∧ L = (N-1)/(m-1)+1 ∧
    (∑ k, x k) = (L:ℝ)+N-1 ∧
    (∀ k, x k = if k.val = 0 then L else 1) ∧
    (∃ k : Fin N, k.val = 0 ∧ printedPPS m x k = ppsConfigurationPi row ∧
      1 < printedPPS m x k) ∧
    IsProbabilityMeasure (nbProductLawN N) ∧
    0 < ((nbProductLawN N) {v}).toReal ∧
    ∀ (Ω' : Type) [Fintype Ω'] (D : Design (Fin N) Ω'), Valid D →
      ¬ (∀ k, pi D k = printedPPS m x k)

def T12Statement : Prop :=
  InvalidPPSWitness ∧ InvalidPPSValues ∧ NegativeBinomialWitness ∧ NBFiniteMoments ∧ AllPPSConfigurations

def PPSFeasibility : Prop :=
  ∀ {N : ℕ}, 2 ≤ N → ∀ m : ℕ, 0 < m → m < N →
  ∀ x : Fin N → ℝ, (∀ k, 0 < x k) →
  (∀ (Ω : Type) [Fintype Ω] (D : Design (Fin N) Ω),
    Valid D → (∀ k, pi D k = printedPPS m x k) → ∀ k, (m:ℝ)*x k ≤ ∑ a, x a) ∧
  ((∃ c : ℝ, 0 < c ∧ (∑ k, min 1 (c*x k)) = m) ∧
    ((∀ k, (m:ℝ)*x k ≤ ∑ a, x a) →
      (∑ k, min 1 ((m:ℝ)/(∑ a, x a)*x k)) = m ∧
      ∀ k, min 1 ((m:ℝ)/(∑ a, x a)*x k) = printedPPS m x k))

def SystematicConstruction : Prop :=
  ∀ {N : ℕ}, 2 ≤ N → ∀ m : ℕ, 0 < m → m < N →
  ∀ π : Fin N → ℝ, (∀ k, 0 < π k ∧ π k ≤ 1) → (∑ k, π k) = m → (∀ k, Integrable (fun u : ℝ =>
    if systematicSelected π m u k then (1:ℝ) else 0) (volume.restrict (Set.Ico 0 1))) →
(∀ u : ℝ, 0 ≤ u → u < 1 →
      (Finset.univ.filter (fun k => systematicSelected π m u k)).card = m) ∧
    (∀ k, (∫ u : ℝ, (if systematicSelected π m u k then (1:ℝ) else 0)
      ∂(MeasureTheory.volume.restrict (Set.Ico 0 1))) = π k)

def T13Statement : Prop :=
  PPSFeasibility ∧ SystematicConstruction ∧ ((∑ k, min 1 ((1/7 : ℝ)*invalidSize8 k)) = 2 ∧
    (∑ k, min 1 (printedPPS 2 invalidSize8 k)) = 51/37 ∧
    (∀ k, min 1 ((1/7 : ℝ)*invalidSize8 k) = if k = 0 then 1 else 1/7)) ∧ (Positive certainty8 ∧
    (∀ k, pi certainty8 k = min 1 ((1/7:ℝ)*invalidSize8 k)) ∧
    (∀ k l, joint certainty8 k l = if k = l then pi certainty8 k else
      if k = 0 ∨ l = 0 then 1/7 else 0))
end
end SAP.P027a
