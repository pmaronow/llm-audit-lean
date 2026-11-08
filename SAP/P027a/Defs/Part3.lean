import Mathlib
import SAP.P027a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

variable {Ω : Type} [Fintype Ω]

def outcomeE {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) (f : Ξ → ℝ) : ℝ :=
  ∫ ξ, f ξ ∂μ

def NoiseMoments {Ξ K : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (ε : K → Ξ → ℝ) (σ2 : ℝ) : Prop :=
  (∀ k, Integrable (ε k) μ ∧ outcomeE μ (ε k) = 0) ∧
  ∀ k l, Integrable (fun ξ => ε k ξ * ε l ξ) μ ∧
    outcomeE μ (fun ξ => ε k ξ * ε l ξ) = if k = l then σ2 else 0

def UncorrelatedNoise {Ξ K : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (ε : K → Ξ → ℝ) : Prop :=
  (∀ k, Integrable (ε k) μ ∧ outcomeE μ (ε k) = 0) ∧
  ∀ k l, Integrable (fun ξ => ε k ξ * ε l ξ) μ ∧
    (k ≠ l → outcomeE μ (fun ξ => ε k ξ * ε l ξ) = 0)

def rawOutcomes {Ξ K : Type} (x : K → ℝ) (β : ℝ) (ε : K → Ξ → ℝ)
    (ξ : Ξ) (k : K) : ℝ := β*x k+ε k ξ

def centeredOutcomes {Ξ K : Type} [Fintype K] (x : K → ℝ) (β : ℝ)
    (ε : K → Ξ → ℝ) (ξ : Ξ) (k : K) : ℝ :=
  rawOutcomes x β ε ξ k - (∑ l, rawOutcomes x β ε ξ l)/(Fintype.card K : ℝ)

def calibratedMeanBias (q : ℝ) (ρ : ℝ) (N : ℝ) : ℝ :=
  -900*ρ^2*(N-1)/(q*N)-900*(1-ρ^2)*(q-1)/(q*N)

def a3LowTrue : Fin 4 → ℝ := ![42.55,56.35,23.14,28.58]

def a3LowC2 : Fin 4 → ℝ := ![653.92,891.43,622.28,861.11]

def a3LowQ : Fin 4 → ℝ := ![4,20,4,20]

def row21Fibre (k : Σ _ : Fin 2 × Fin 2, Fin 30) : ℝ :=
  (if k.1.2 = 0 then -4 else 4) + 2*(k.2 : ℝ) - 29

def printedPPS {N : ℕ} (m : ℕ) (x : Fin N → ℝ) (k : Fin N) : ℝ :=
  m*x k/(∑ a, x a)

def invalidSize8 (k : Fin 8) : ℝ := if k = 0 then 30 else 1

def nbMass (j : ℕ) : ℝ :=
  (∏ i ∈ Finset.range j, ((18/5 : ℝ)+(i:ℝ))) / (j.factorial : ℝ) *
    (3/8 : ℝ) ^ (18/5 : ℝ) * (5/8 : ℝ)^j

def nbWitness (k : Fin 8) : ℕ := if k = 0 then 29 else 0

def nbProductLaw : Measure (Fin 8 → ℕ) :=
  Measure.sum (fun v : Fin 8 → ℕ =>
    ENNReal.ofReal (∏ k, nbMass (v k)) • Measure.dirac v)

def nbProductLawN (N : ℕ) : Measure (Fin N → ℕ) :=
  Measure.sum (fun v : Fin N → ℕ =>
    ENNReal.ofReal (∏ k, nbMass (v k)) • Measure.dirac v)

def ppsConfigurationN : Fin 6 → ℕ := ![8,40,120,600,240,1200]

def ppsConfigurationM : Fin 6 → ℕ := ![2,2,30,30,60,60]

def ppsConfigurationL : Fin 6 → ℕ := ![8,40,5,21,5,21]

def ppsConfigurationPi : Fin 6 → ℝ := ![16/15,80/79,150/124,630/620,300/244,1260/1220]

def zeroNeighborCount {G : Type} [Fintype G] (D : Design G Ω) (g : G) : ℕ :=
  (Finset.univ.filter (fun h => g ≠ h ∧ joint D g h = 0)).card

def zeroNeighborSize {G : Type} [Fintype G] (D : Design G Ω) (n : G → ℕ) (g : G) : ℝ :=
  ∑ h, if g ≠ h ∧ joint D g h = 0 then (n h:ℝ) else 0

def groupedPeriodic4 : Design (Fin 4) (Fin 4) := oneDraw periodic8.weight

def ratioExampleTotals : Fin 4 → ℝ := ![1,0,-1,0]

def certainty8 : Design (Fin 8) (Fin 7) where
  weight _ := 1/7
  selected ω k := decide (k = 0 ∨ k.val = ω.val+1)

end
end SAP.P027a
