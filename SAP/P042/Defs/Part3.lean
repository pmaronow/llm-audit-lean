import SAP.P042.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042

noncomputable section
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

def roboEffects : Fin 2 → ℝ := ![58247/25000, 21649/25000]

def roboSE : Fin 2 → ℝ := ![1741/3125, 40891/50000]

def roboVariances (j : Fin 2) : ℝ := (roboSE j)^2

def roboFixedMean : ℝ := ∑ j, normalizedWeight roboVariances j * roboEffects j

def roboFixedVariance : ℝ := (totalWeight roboVariances)⁻¹

def roboQ : ℝ := ∑ j, precisionWeight roboVariances j * (roboEffects j - roboFixedMean)^2

def roboC : ℝ := totalWeight roboVariances -
  (∑ j, (precisionWeight roboVariances j)^2) / totalWeight roboVariances

def roboTauSq : ℝ := max 0 ((roboQ - 1) / roboC)

def roboRandomVariances (j : Fin 2) : ℝ := roboVariances j + roboTauSq

def roboRandomMean : ℝ := ∑ j, normalizedWeight roboRandomVariances j * roboEffects j

def roboRandomVariance : ℝ := (totalWeight roboRandomVariances)⁻¹

def completeAssignments (N m : ℕ) : Finset (Finset (Fin N)) := Finset.univ.powersetCard m

def assignedTreatmentMean {N : ℕ} (m : ℕ) (S : Finset (Fin N)) (U : Fin N → ℝ) : ℝ :=
  (∑ i, if i ∈ S then U i else 0)/(m:ℝ)

def assignedControlMean {N : ℕ} (m : ℕ) (S : Finset (Fin N)) (U : Fin N → ℝ) : ℝ :=
  (∑ i, if i ∉ S then U i else 0)/((N-m:ℕ):ℝ)

def assignedOutcome {N : ℕ} (S : Finset (Fin N)) (Y : Fin N → Bool → ℝ) (i : Fin N) : ℝ :=
  if i ∈ S then Y i true else Y i false

def complierCount {N : ℕ} (c : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i => c i = true)).card

def complierShare {N : ℕ} (c : Fin N → Bool) : ℝ := (complierCount c:ℝ)/(N:ℝ)

def complierEffect {N : ℕ} (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) : ℝ :=
  (∑ i, if c i = true then Y i true - Y i false else 0)/(complierCount c:ℝ)

def assignmentEffect {N : ℕ} (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) : ℝ :=
  populationMean (fun i => Y i (c i) - Y i false)

def contactedOutcome {N : ℕ} (S : Finset (Fin N))
    (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) (i : Fin N) : ℝ :=
  Y i (if i ∈ S then c i else false)

def assignedContactRate {N : ℕ} (m : ℕ) (S : Finset (Fin N)) (c : Fin N → Bool) : ℝ :=
  assignedTreatmentMean m S (fun i => if c i = true then 1 else 0)

end
end SAP.P042
