import Mathlib
import SAP.P025a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a
noncomputable section
open scoped BigOperators

/-- The disjoint prefix/tail numerator in the upper class formula. -/
def wholeUpperNumerator {J : ℕ} (y mass : Fin J → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  (∑ j with j.val < k, mass j * y j) + γ * ∑ j with k ≤ j.val, mass j * y j

/-- The denominator in the upper class formula. -/
def wholeUpperDenominator {J : ℕ} (mass : Fin J → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  (∑ j with j.val < k, mass j) + γ * ∑ j with k ≤ j.val, mass j

/-- Original-scale lower threshold weights: first k entries 1/α, then 1/β. -/
def wholeLowerWeights_W2 {J : ℕ} (α β : ℝ) (k : ℕ) (j : Fin J) : ℝ :=
  if j.val < k then 1 / α else 1 / β

/-- Original-scale upper threshold weights: first k entries 1/β, then 1/α. -/
def wholeUpperWeights_W2 {J : ℕ} (α β : ℝ) (k : ℕ) (j : Fin J) : ℝ :=
  if j.val < k then 1 / β else 1 / α

/-- P025-T4; pp. 237-238 (PDF pp. 3-4); proof in the Supplement, pp. 1-2.
Both corrected first class cuts exist. Their prescribed original-scale threshold vectors are feasible,
have the displayed disjoint prefix/tail values, and attain the global minimum and maximum. Both last-cut
inequalities and both class-weight increment identities hold, including equal probability bounds.
Every displayed denominator is positive; optimality does not assert uniqueness. -/
def T4WholeStatement : Prop :=
  ∀ {J : ℕ} (hJ : 0 < J) (y mass : Fin J → ℝ), StrictMono y →
    (∀ j, 0 < mass j) → ∀ α β : ℝ, 0 < α → α ≤ β → β ≤ 1 →
    (∀ k : ℕ, k ≤ J →
      lowerValue y mass (β / α) k =
        lowerNumerator y mass (β / α) k / lowerDenominator mass (β / α) k ∧
      upperValue y mass (β / α) k =
        wholeUpperNumerator y mass (β / α) k / wholeUpperDenominator mass (β / α) k ∧
      0 < lowerDenominator mass (β / α) k ∧
      0 < wholeUpperDenominator mass (β / α) k) ∧
    lowerValue y mass (β / α) (J - 1) ≤ y ⟨J - 1, by omega⟩ ∧
    upperValue y mass (β / α) (J - 1) ≤ y ⟨J - 1, by omega⟩ ∧
    (∀ k : Fin J,
      lowerValue y mass (β / α) (k.val + 1) - lowerValue y mass (β / α) k.val =
        ((β / α) - 1) * mass k * (y k - lowerValue y mass (β / α) k.val) /
          lowerDenominator mass (β / α) (k.val + 1) ∧
      upperValue y mass (β / α) (k.val + 1) - upperValue y mass (β / α) k.val =
        (1 - (β / α)) * mass k * (y k - upperValue y mass (β / α) k.val) /
          wholeUpperDenominator mass (β / α) (k.val + 1)) ∧
    ∃ kL kH : Fin J,
      lowerCut y mass (β / α) kL ∧ upperCut y mass (β / α) kH ∧
      weightBox α β (wholeLowerWeights_W2 (J := J) α β kL.val) ∧
      weightBox α β (wholeUpperWeights_W2 (J := J) α β kH.val) ∧
      ratio y mass (wholeLowerWeights_W2 α β kL.val) = lowerValue y mass (β / α) kL.val ∧
      ratio y mass (wholeUpperWeights_W2 α β kH.val) = upperValue y mass (β / α) kH.val ∧
      (∀ W : Fin J → ℝ, weightBox α β W →
        lowerValue y mass (β / α) kL.val ≤ ratio y mass W ∧
        ratio y mass W ≤ upperValue y mass (β / α) kH.val) ∧
      IsLeast (attainable y mass α β) (lowerValue y mass (β / α) kL.val) ∧
      IsGreatest (attainable y mass α β) (upperValue y mass (β / α) kH.val) ∧
      lowerEndpoint y mass α β =
        lowerNumerator y mass (β / α) kL.val / lowerDenominator mass (β / α) kL.val ∧
      upperEndpoint y mass α β =
        wholeUpperNumerator y mass (β / α) kH.val / wholeUpperDenominator mass (β / α) kH.val

/-- A labeled fixed-quota draw, with membership in the existing quota family retained. -/
abbrev WholeQuotaSpace (N s : ℕ) := ↥(quotaDraws N s)

/-- The uniform mass on a quota family. Its nonempty uses are certified below. -/
def wholeQuotaProbability (N s : ℕ) (_ : WholeQuotaSpace N s) : ℝ :=
  1 / ((quotaDraws N s).card : ℝ)

/-- Probability of an event under a finite mass function. -/
def wholeEventProbability {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (A : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, p ω * (if A ω then 1 else 0)

/-- The finite independent product mass, including dependent coordinate spaces. -/
def wholeProductProbability {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    (p : ∀ j, Ω j → ℝ) (ω : ∀ j, Ω j) : ℝ := ∏ j, p j (ω j)

/-- Factorization of every rectangular event is mutual independence of all coordinates. -/
def wholeIndependentCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ j, Fintype (Ω j)] (p : ∀ j, Ω j → ℝ) : Prop := by
  classical
  exact ∀ A : ∀ j, Ω j → Prop,
    wholeEventProbability (wholeProductProbability p) (fun ω => ∀ j, A j (ω j)) =
      ∏ j, wholeEventProbability (p j) (A j)

/-- The gallery infected, gallery uninfected, exchange infected, exchange uninfected quotas. -/
def wholeApplicationQuotas : Fin 4 → ℕ := ![44, 4, 291, 288]

def wholeApplicationSizesA : Fin 4 → ℕ := ![48, 16, 864, 288]

def wholeApplicationSizesB : Fin 4 → ℕ := ![48, 12, 1156, 289]

/-- A single joint draw of all four infection strata. -/
abbrev WholeApplicationSpace (N : Fin 4 → ℕ) :=
  ∀ j, WholeQuotaSpace (N j) (wholeApplicationQuotas j)

def wholeApplicationProbability (N : Fin 4 → ℕ) : WholeApplicationSpace N → ℝ :=
  wholeProductProbability (fun j => wholeQuotaProbability (N j) (wholeApplicationQuotas j))

/-- A population is the disjoint union of its infected and uninfected labeled units. -/
def wholeBinaryOutcome {N₁ N₀ : ℕ} : Fin N₁ ⊕ Fin N₀ → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

def wholeBinarySample {N₁ N₀ : ℕ} (t₁ : Finset (Fin N₁)) (t₀ : Finset (Fin N₀)) :
    Finset (Fin N₁ ⊕ Fin N₀) := t₁.disjSum t₀

def wholeGallerySample (N : Fin 4 → ℕ) (ω : WholeApplicationSpace N) :
    Finset (Fin (N 0) ⊕ Fin (N 1)) := wholeBinarySample (ω 0).val (ω 1).val

def wholeExchangeSample (N : Fin 4 → ℕ) (ω : WholeApplicationSpace N) :
    Finset (Fin (N 2) ⊕ Fin (N 3)) := wholeBinarySample (ω 2).val (ω 3).val

/-- These are actual marginals of the joint law, not supplied selection probabilities. -/
def wholeGalleryInclusion (N : Fin 4 → ℕ) : Fin (N 0) ⊕ Fin (N 1) → ℝ :=
  designInclusion (wholeGallerySample N) (wholeApplicationProbability N)

def wholeExchangeInclusion (N : Fin 4 → ℕ) : Fin (N 2) ⊕ Fin (N 3) → ℝ :=
  designInclusion (wholeExchangeSample N) (wholeApplicationProbability N)

/-- Unit-level mean of the full binary population. -/
def wholeBinaryPopulationMean (N₁ N₀ : ℕ) : ℝ :=
  (∑ i : Fin N₁ ⊕ Fin N₀, wholeBinaryOutcome i) / Fintype.card (Fin N₁ ⊕ Fin N₀)

def wholeSampleFraction {N₁ N₀ : ℕ} (s : Finset (Fin N₁ ⊕ Fin N₀)) : ℝ :=
  (∑ i ∈ s, wholeBinaryOutcome i) / (s.card : ℝ)

def wholeHajekDenominator {ι : Type*} (π : ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, 1 / π i

/-- Equation (1), evaluated using the actual unit inclusion probabilities. -/
def wholeBinaryHajek {N₁ N₀ : ℕ} (π : Fin N₁ ⊕ Fin N₀ → ℝ)
    (s : Finset (Fin N₁ ⊕ Fin N₀)) : ℝ :=
  (∑ i ∈ s, wholeBinaryOutcome i / π i) / wholeHajekDenominator π s

/-- Counts, raw sample fraction, and the unit-level Hajek estimator on one draw. -/
def wholeBinaryDrawFacts {N₁ N₀ : ℕ} (π : Fin N₁ ⊕ Fin N₀ → ℝ)
    (s : Finset (Fin N₁ ⊕ Fin N₀)) (q : ℝ) (s₁ s₀ : ℕ) : Prop :=
  (s.filter (fun i => wholeBinaryOutcome i = 1)).card = s₁ ∧
  (s.filter (fun i => wholeBinaryOutcome i = 0)).card = s₀ ∧
  s.card = s₁ + s₀ ∧
  wholeSampleFraction s = (s₁ : ℝ) / (s₁ + s₀) ∧
  0 < wholeHajekDenominator π s ∧ wholeBinaryHajek π s = q

/-- Full design certificate for a concrete pair of populations. The four strata are independent
uniform quota draws. Tagged population samples have actual bounded inclusion probabilities and, on
every possible draw, the reported counts, rounded proportions, and equal Hajek estimates. -/
def wholeApplicationCertificate (N : Fin 4 → ℕ) (q : ℝ) : Prop :=
  Nonempty (WholeApplicationSpace N) ∧
  (∀ ω, 0 ≤ wholeApplicationProbability N ω) ∧
  (∑ ω, wholeApplicationProbability N ω) = 1 ∧
  wholeIndependentCoordinates (fun j => wholeQuotaProbability (N j) (wholeApplicationQuotas j)) ∧
  (∀ j (i : Fin (N j)),
    wholeEventProbability (wholeApplicationProbability N) (fun ω => i ∈ (ω j).val) =
      (wholeApplicationQuotas j : ℝ) / N j) ∧
  (∀ i, wholeGalleryInclusion N i =
    Sum.elim (fun _ => (44 : ℝ) / N 0) (fun _ => (4 : ℝ) / N 1) i) ∧
  (∀ i, wholeExchangeInclusion N i =
    Sum.elim (fun _ => (291 : ℝ) / N 2) (fun _ => (288 : ℝ) / N 3) i) ∧
  (∀ i, wholeGalleryInclusion N i ∈ Set.Icc (1 / 4 : ℝ) 1) ∧
  (∀ i, wholeExchangeInclusion N i ∈ Set.Icc (1 / 4 : ℝ) 1) ∧
  wholeBinaryPopulationMean (N 0) (N 1) = q ∧
  wholeBinaryPopulationMean (N 2) (N 3) = q ∧
  (∀ ω : WholeApplicationSpace N,
    wholeBinaryDrawFacts (wholeGalleryInclusion N) (wholeGallerySample N ω) q 44 4 ∧
    wholeBinaryDrawFacts (wholeExchangeInclusion N) (wholeExchangeSample N ω) q 291 288 ∧
    (917 / 10 : ℝ) - 1 / 20 ≤ 100 * wholeSampleFraction (wholeGallerySample N ω) ∧
    100 * wholeSampleFraction (wholeGallerySample N ω) < 917 / 10 + 1 / 20 ∧
    (503 / 10 : ℝ) - 1 / 20 ≤ 100 * wholeSampleFraction (wholeExchangeSample N ω) ∧
    100 * wholeSampleFraction (wholeExchangeSample N ω) < 503 / 10 + 1 / 20)

/-- P025-T5; pp. 238-239 (PDF pp. 4-5); Table 1 on p. 238 (PDF p. 4).
These two finite population pairs refute the reading of the application sentence that equal gallery
and exchange population prevalences require both actual directional selection ratios to exceed three:
the pairs have equal prevalences and the reported samples, while respectively the exchange and gallery
selection ratio is below three.
Their joint independent uniform fixed-quota sampling designs are normalized, have the stated actual
unit marginals in [1/4,1], and on every draw yield the reported counts and equal Hajek estimates.
The interval memberships, rounding bounds, ratio identities, and both exact rounded-input variants hold. -/
def T5WholeStatement : Prop :=
  T5Statement ∧
  wholeApplicationCertificate wholeApplicationSizesA (3 / 4) ∧
  wholeApplicationCertificate wholeApplicationSizesB (4 / 5) ∧
  binaryLower (44 / 48) 4 = 11 / 15 ∧
  binaryUpper (291 / 579) 4 = 388 / 484 ∧
  (388 / 484 : ℝ) = 97 / 121 ∧
  (1 : ℝ) / (503 / 1491) = 1491 / 503 ∧
  (1 : ℝ) / (332 / 917) = 917 / 332

end
end SAP.P025a
