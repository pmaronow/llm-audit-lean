import SAP.P041.Defs
import AronowAudit.P041.P041_Hazards
import AronowAudit.P041.P041_OLS
import AronowAudit.P041.P041_Order
import AronowAudit.P041.P041_PrintedRefutations
import AronowAudit.P041.P041_Risks
import AronowAudit.P041.P041_Tenure
import AronowAudit.P041.P041_Wald
import AronowAudit.P041.Wave1.Gap.GLP041P042P045B1
import AronowAudit.P041.Wave1.Gap.GP041P042P045B1

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.Bridge
open Matrix
open scoped BigOperators

theorem balanced_scrutiny_general_proof :
  ∀ (m : ℕ) (hm : 1 ≤ m),
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
    0 < balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) := by
  exact @AronowAudit.P041.Wave1.balanced_scrutiny_general_proof

theorem study_one_size_scrutiny_proof :
  balancedExpectation 50 (fun z => (leadingCited z : ℝ)) = 50/51 ∧
    balancedExpectation 50 (fun z => (∑ r ∈ z, scrutinyOutcome z r) / 50) = 50/51 ∧
    (∀ z ∈ balancedSequences 50,
      (∑ r ∈ Finset.univ \ z, scrutinyOutcome z r) / 50 = 49/50) ∧
    balancedExpectation 50 (fun z => citationContrast 50 z (scrutinyOutcome z)) = 1/2550 ∧
    balancedExpectation 50 (fun z => citationContrast 50 z (scrutinyOutcome z)) ≠ 0 := by
  exact @AronowAudit.P041.Wave1.study_one_size_scrutiny_proof

theorem fixed_calendar_block_unbiased :
  balancedExpectation 2 (fun z => citationContrast 2 z ![0,0,1,1]) = 0 := by
  exact @AronowAudit.P041.fixed_calendar_block_unbiased

theorem independent_citation_boundary :
  independentCitationExpectation = 0 := by
  exact @AronowAudit.P041.independent_citation_boundary

theorem random_order_block_counterexample :
  citationContrast 2 {2,3} (scrutinyOutcome {2,3}) = 1/2 ∧
    citationContrast 2 {1,3} (scrutinyOutcome {1,3}) = 1/2 ∧
    citationContrast 2 {1,2} (scrutinyOutcome {1,2}) = 1/2 ∧
    citationContrast 2 {0,3} (scrutinyOutcome {0,3}) = 0 ∧
    citationContrast 2 {0,2} (scrutinyOutcome {0,2}) = 0 ∧
    citationContrast 2 {0,1} (scrutinyOutcome {0,1}) = -1/2 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (scrutinyOutcome z)) = 1/6 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (scrutinyOutcome z)) ≠ 0 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (fun _ => 0)) = 0 := by
  exact @AronowAudit.P041.random_order_block_counterexample

theorem scrutiny_no_direct_effect :
  ∀ {n : ℕ} (z z' : Finset (Fin n)) (r : Fin n)
    (hp : ∀ s, s < r → (s ∈ z ↔ s ∈ z')),
    scrutinyOutcome z r = scrutinyOutcome z' r := by
  exact @AronowAudit.P041.scrutiny_no_direct_effect

theorem adaptive_protocol_estimands_general_proof :
  ∀ (m : ℕ) (hm : 1 ≤ m),
    (∀ z z' : Finset (Fin (2*m)), ∀ r : Fin (2*m),
      (∀ s, s ≠ r → (s ∈ z ↔ s ∈ z')) → scrutinyOutcome z r - scrutinyOutcome z' r = 0) ∧
    balancedExpectation m (fun z => citationContrast m z (fun _ => 0)) = 0 ∧
    balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) = 1/((m:ℝ)*(m+1)) ∧
    0 < balancedExpectation m (fun z => citationContrast m z (scrutinyOutcome z)) := by
  exact @AronowAudit.P041.Wave1.adaptive_protocol_estimands_general_proof

theorem adaptive_protocol_estimands_differ :
  balancedExpectation 2 (fun z => citationContrast 2 z (scrutinyOutcome z)) = 1/6 ∧
    balancedExpectation 2 (fun z => citationContrast 2 z (fun _ => 0)) = 0 ∧
    (∀ z z' : Finset (Fin 4), ∀ r : Fin 4,
      (∀ s, s ≠ r → (s ∈ z ↔ s ∈ z')) → scrutinyOutcome z r - scrutinyOutcome z' r = 0) := by
  exact @AronowAudit.P041.adaptive_protocol_estimands_differ

theorem block_without_interference :
  ∀ (g : Fin 4 → Bool → ℝ),
    balancedExpectation 2 (fun z => citationContrast 2 z
      (fun r => g r (decide (r ∈ z)))) =
    (∑ r : Fin 4, (g r true - g r false)) / 4 := by
  exact @AronowAudit.P041.block_without_interference

theorem random_order_without_interference :
  ∀ (m : ℕ) (hm : 1 ≤ m)
    (g : Fin (2*m) → Bool → ℝ),
    balancedExpectation m (fun z => citationContrast m z
      (fun r => g r (decide (r ∈ z)))) =
    (∑ r : Fin (2*m), (g r true - g r false)) / (2*m) := by
  exact @AronowAudit.P041.random_order_without_interference

theorem block_two_sequences :
  balancedSequences 2 =
      {{2,3},{1,3},{1,2},{0,3},{0,2},{0,1}} := by
  exact @AronowAudit.P041.block_two_sequences

theorem block_two_outcomes :
  scrutinyOutcome ({2,3} : Finset (Fin 4)) = ![0,1,1,1] ∧
    scrutinyOutcome ({1,3} : Finset (Fin 4)) = ![0,1,1,1] ∧
    scrutinyOutcome ({1,2} : Finset (Fin 4)) = ![0,1,1,1] ∧
    scrutinyOutcome ({0,3} : Finset (Fin 4)) = ![0,0,1,1] ∧
    scrutinyOutcome ({0,2} : Finset (Fin 4)) = ![0,0,1,1] ∧
    scrutinyOutcome ({0,1} : Finset (Fin 4)) = ![0,0,0,1] := by
  exact @AronowAudit.P041.block_two_outcomes

end SAP.P041.Bridge
