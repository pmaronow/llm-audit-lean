import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- One row of T5's six-order table; cited ranks are zero based. -/
def scrutinyBlockCase (z : Finset (Fin 4)) (y : Fin 4 → ℝ) (c u d : ℝ) : Prop :=
  scrutinyOutcome z = y ∧
  (∑ r ∈ z, scrutinyOutcome z r) / 2 = c ∧
  (∑ r ∈ Finset.univ \ z, scrutinyOutcome z r) / 2 = u ∧
  citationContrast 2 z (scrutinyOutcome z) = d

/-- Mathematical content packaged for P041-T5. -/
def T5Statement : Prop :=
  (∀ {n : ℕ} (z z' : Finset (Fin n)) (r : Fin n),
      (∀ s, s < r → (s ∈ z ↔ s ∈ z')) → scrutinyOutcome z r = scrutinyOutcome z' r) ∧
  (∀ (m : ℕ), 1 ≤ m → ∀ z : Finset (Fin (2*m)),
      citationContrast m z (fun _ => 0) = 0) ∧
  (∀ (m : ℕ), 1 ≤ m →
      balancedExpectation m (fun z => citationContrast m z (fun _ => 0)) = 0) ∧
  (balancedSequences 2 = {{2,3},{1,3},{1,2},{0,3},{0,2},{0,1}} ∧
    scrutinyBlockCase {2,3} ![0,1,1,1] 1 (1/2) (1/2) ∧
    scrutinyBlockCase {1,3} ![0,1,1,1] 1 (1/2) (1/2) ∧
    scrutinyBlockCase {1,2} ![0,1,1,1] 1 (1/2) (1/2) ∧
    scrutinyBlockCase {0,3} ![0,0,1,1] (1/2) (1/2) 0 ∧
    scrutinyBlockCase {0,2} ![0,0,1,1] (1/2) (1/2) 0 ∧
    scrutinyBlockCase {0,1} ![0,0,0,1] 0 (1/2) (-1/2)) ∧
  (citationContrast 2 {2,3} (scrutinyOutcome {2,3}) = 1/2 ∧
    citationContrast 2 {1,3} (scrutinyOutcome {1,3}) = 1/2 ∧
    citationContrast 2 {1,2} (scrutinyOutcome {1,2}) = 1/2 ∧
    citationContrast 2 {0,3} (scrutinyOutcome {0,3}) = 0 ∧
    citationContrast 2 {0,2} (scrutinyOutcome {0,2}) = 0 ∧
    citationContrast 2 {0,1} (scrutinyOutcome {0,1}) = -1/2 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (scrutinyOutcome z)) = 1/6 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (scrutinyOutcome z)) ≠ 0 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (fun _ => 0)) = 0) ∧
  (∀ (m : ℕ) (hm : 1 ≤ m),
    (∀ k ≤ m, leadingCitedProbability m k =
      (((2*m-k-1).choose (m-1) : ℝ) / ((2*m).choose m : ℝ))) ∧
    balancedExpectation m (fun z => (leadingCited z : ℝ)) = (m:ℝ)/(m+1) ∧
    (∀ z ∈ balancedSequences m,
      (∑ r ∈ z, scrutinyOutcome z r) = (m:ℝ) - leadingCited z ∧
      (∑ r ∈ Finset.univ \ z, scrutinyOutcome z r) = (m:ℝ)-1) ∧
    balancedExpectation m (fun z => (∑ r ∈ z, scrutinyOutcome z r) / m) =
      (m:ℝ)/(m+1) ∧
    balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) =
      1/((m:ℝ)*(m+1)) ∧
    0 < balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z))) ∧
  (∀ (m : ℕ), 1 ≤ m → ∀ z ∈ balancedSequences m,
      (∑ r ∈ Finset.univ \ z, scrutinyOutcome z r) / m = ((m:ℝ)-1)/m) ∧
  (balancedExpectation 50 (fun z => (leadingCited z : ℝ)) = 50/51 ∧
    balancedExpectation 50 (fun z => (∑ r ∈ z, scrutinyOutcome z r) / 50) = 50/51 ∧
    (∀ z ∈ balancedSequences 50,
      (∑ r ∈ Finset.univ \ z, scrutinyOutcome z r) / 50 = 49/50) ∧
    balancedExpectation 50 (fun z => citationContrast 50 z (scrutinyOutcome z)) = 1/2550 ∧
    balancedExpectation 50 (fun z => citationContrast 50 z (scrutinyOutcome z)) ≠ 0) ∧
  (∀ (m : ℕ), 1 ≤ m → ∀ Y : Fin (2*m) → ℝ,
      balancedExpectation m (fun z => citationContrast m z Y) = 0) ∧
  (balancedExpectation 2 (fun z => citationContrast 2 z ![0,0,1,1]) = 0) ∧
  (independentCitationExpectation = 0)

end SAP.P041
