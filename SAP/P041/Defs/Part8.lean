import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- Mathematical content packaged for P041-T6. -/
def T6Statement : Prop :=
  (∀ (m : ℕ) (hm : 1 ≤ m)
    (g : Fin (2*m) → Bool → ℝ),
    balancedExpectation m (fun z => citationContrast m z
      (fun r => g r (decide (r ∈ z)))) =
    (∑ r : Fin (2*m), (g r true - g r false)) / (2*m)) ∧
  (∀ (m : ℕ), 1 ≤ m → ∀ c : Fin (2*m) → ℝ,
      balancedExpectation m (fun z => citationContrast m z c) = 0) ∧
  (∀ (g : Fin 4 → Bool → ℝ),
    balancedExpectation 2 (fun z => citationContrast 2 z
      (fun r => g r (decide (r ∈ z)))) =
    (∑ r : Fin 4, (g r true - g r false)) / 4) ∧
  (∀ (m : ℕ) (hm : 1 ≤ m),
    (∀ z z' : Finset (Fin (2*m)), ∀ r : Fin (2*m),
      (∀ s, s ≠ r → (s ∈ z ↔ s ∈ z')) → scrutinyOutcome z r - scrutinyOutcome z' r = 0) ∧
    balancedExpectation m (fun z => citationContrast m z (fun _ => 0)) = 0 ∧
    balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) = 1/((m:ℝ)*(m+1)) ∧
    0 < balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z))) ∧
  (balancedExpectation 2 (fun z => citationContrast 2 z (scrutinyOutcome z)) = 1/6 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (fun _ => 0)) = 0 ∧
    (∀ z z' : Finset (Fin 4), ∀ r : Fin 4,
      (∀ s, s ≠ r → (s ∈ z ↔ s ∈ z')) → scrutinyOutcome z r - scrutinyOutcome z' r = 0)) ∧
  (balancedExpectation 2 (fun z => citationContrast 2 z ![0,0,1,1]) = 0 ∧
    balancedExpectation 50 (fun z => citationContrast 50 z (scrutinyOutcome z)) = 1/2550)

end SAP.P041
