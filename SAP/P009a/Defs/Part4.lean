import SAP.P009a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P009a

open Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

def fairDistribution (n : ℕ) : FiniteDistribution (TreatmentVector n) where
  mass := fun _ => 1 / (2 : ℝ) ^ n
  nonneg := fun _ => by positivity
  total := by simp [Fintype.card_fin, Fintype.card_bool]

def fairPopulation (n : ℕ) (y : Fin n → TreatmentVector n → ℝ) : FiniteExperiment n :=
  ⟨fairDistribution n, y⟩

def sparsePopulation (n : ℕ) : FiniteExperiment n :=
  fairPopulation n (fun i z => if i.val = 0 then treatmentValue (z i) else 0)

def sparseSequence : ExperimentSequence where
  N := fun t => t+1
  positive := by intro t; omega
  grows := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop b] with t htEstimate
    omega
  experiment := fun t => sparsePopulation (t+1)

def clusterSize (n : ℕ) : ℕ := max 1 (n/2-1)

def clusterDensity (n : ℕ) : ℝ :=
  ((clusterSize n : ℝ)^2 + n - clusterSize n) / (n:ℝ)^2

def FiniteLimsup (a : ℕ → ℝ) (L : ℝ) : Prop :=
  (∀ ε > 0, ∀ᶠ t in atTop, a t < L+ε) ∧
  (∀ ε > 0, ∃ᶠ t in atTop, L-ε < a t)

def firstHalf (r : ℕ) : Finset (Fin (4*r+2)) :=
  Finset.univ.filter (fun i => i.val = 0 ∨ (2 ≤ i.val ∧ i.val ≤ 2*r+1))

def halfPopulationResponse (r : ℕ) (i : Fin (4*r+2)) (z : TreatmentVector (4*r+2)) : ℝ :=
  if i.val = 0 then (∑ j ∈ firstHalf r, treatmentValue (z j)) / (2*r+1:ℕ)
  else if i.val = 1 then (∑ j ∈ Finset.univ \ firstHalf r, treatmentValue (z j)) / (2*r+1:ℕ)
  else treatmentValue (z i)

def starPopulationResponse (m : ℕ) (hm : 2 ≤ m) (i : Fin (m*m)) (z : TreatmentVector (m*m)) : ℝ :=
  let hub : Fin (m*m) := ⟨((i.val / m)*m) % (m*m), Nat.mod_lt _ (by nlinarith)⟩
  let leaf : Fin (m*m) := ⟨((i.val / m)*m+1) % (m*m), Nat.mod_lt _ (by nlinarith)⟩
  treatmentValue (z i) + if i.val % m = 0 then treatmentValue (z leaf) else treatmentValue (z hub)

def cancellingPopulation : FiniteExperiment 3 := fairPopulation 3
  (fun i z => if i = 1 then treatmentValue (z 0)*(2*treatmentValue (z 2)-1) else 0)

def treatedIncomingCount {n : ℕ} (E : FiniteExperiment n) (i : Fin n) (z : TreatmentVector n) : ℕ :=
  ∑ j, if j ≠ i ∧ Affects E j i ∧ z j = true then 1 else 0

def printedHypergeomMass (n m draws t : ℕ) : ℝ :=
  (m.choose t : ℝ) * ((n-m).choose (draws-t) : ℝ) / (n.choose draws : ℝ)

def subsequenceResponse {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n) (M : ℕ)
    (i : Fin n) (z : TreatmentVector n) : ℝ :=
  if i.val < M then (n:ℝ)/(M:ℝ)*treatmentValue (z ⟨0,hn⟩)*
    (treatmentValue (z i)*armProbability E i true - (1-treatmentValue (z i))*armProbability E i false) else 0

def clusterPopulation (n : ℕ) (hn : 0 < n) : FiniteExperiment n :=
  fairPopulation n (fun i z => if i.val < clusterSize n then treatmentValue (z ⟨0,hn⟩) else 0)

def clusterSequence : ExperimentSequence :=
  { sparseSequence with
    experiment := fun t => clusterPopulation (t+1) (by omega) }


def identityPopulation (n : ℕ) : FiniteExperiment n := fairPopulation n (fun i z => treatmentValue (z i))

def identitySequence : ExperimentSequence := {sparseSequence with experiment := fun t => identityPopulation (t+1)}


end
end SAP.P009a
