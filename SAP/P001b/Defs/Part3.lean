import Mathlib
import SAP.P001b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Classical Topology
noncomputable section

/-- Discrete overlap, its uniform-bound consequence, and its finite-support converse. -/
def T20Statement : Prop :=
  (∀ {E : Type*} (t c : E → ℝ), (∀ x, 0 ≤ t x) → (∀ x, 0 ≤ c x) →
    ({x | 0 < t x} = {x | 0 < c x} ↔
      ∀ x, 0 < t x + c x → 0 < t x / (t x + c x) ∧ t x / (t x + c x) < 1) ∧
    ((∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < t x + c x →
      ε < t x / (t x + c x) ∧ t x / (t x + c x) < 1 - ε) →
      {x | 0 < t x} = {x | 0 < c x})) ∧
  (∀ {E : Type*} (t c : E → ℝ),
    (∀ x, 0 ≤ t x) → (∀ x, 0 ≤ c x) → {x | 0 < t x + c x}.Finite →
    {x | 0 < t x} = {x | 0 < c x} →
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < t x + c x →
      ε < t x / (t x + c x) ∧ t x / (t x + c x) < 1 - ε)

/-- A fully specified four-atom referendum model refutes the information implication. -/
def T21Statement : Prop :=
  (∀ i, 0 ≤ voterMass i) ∧ (∑ i, voterMass i) = 1 ∧
  (∀ d : Bool, (displayedLeaflet d).1 = 0 ∧ (displayedLeaflet d).2.1 = d ∧
    (displayedLeaflet d).2.2 = false) ∧
  (∀ i d, countedVoteShare i d = potentialVoteShare (if d then 1 else 0) i) ∧
  (∀ i, observedVoteShare i = potentialVoteShare 1 i * displayedGender i +
    potentialVoteShare 0 i * (1 - displayedGender i)) ∧
  (∀ i, potentialVoteShare 0 i ∈ Set.Icc (0 : ℝ) 100 ∧
    potentialVoteShare 1 i ∈ Set.Icc (0 : ℝ) 100) ∧
  (∀ i, observedVoteShare i ∈ Set.Icc (0 : ℝ) 100) ∧
  (∀ i, potentialVoteShare 1 i - potentialVoteShare 0 i = 5) ∧
  finiteProbability voterMass (fun i => displayedGender i = 1) = 1/2 ∧
  finiteProbability voterMass (fun i => displayedGender i = 0) = 1/2 ∧
  finiteConditionalMean voterMass displayedGender (fun _ => 0) 0 = 1/2 ∧
  finiteProbability voterMass (fun i =>
    (potentialVoteShare 0 i, potentialVoteShare 1 i) = (60, 65) ∧ displayedGender i = 1) = 3/8 ∧
  finiteProbability voterMass (fun i =>
    (potentialVoteShare 0 i, potentialVoteShare 1 i) = (60, 65)) = 1/2 ∧
  finiteProbability voterMass (fun i =>
    (potentialVoteShare 0 i, potentialVoteShare 1 i) = (60, 65)) *
    finiteProbability voterMass (fun i => displayedGender i = 1) = 1/4 ∧
  ¬ FiniteConditionalIndependence voterMass
    (fun i => (potentialVoteShare 0 i, potentialVoteShare 1 i)) displayedGender (fun _ => (0 : ℝ)) ∧
  finiteConditionalMean voterMass observedVoteShare displayedGender 1 = 55 ∧
  finiteConditionalMean voterMass observedVoteShare displayedGender 0 = 30 ∧
  finiteConditionalMean voterMass observedVoteShare displayedGender 1 -
    finiteConditionalMean voterMass observedVoteShare displayedGender 0 = 25 ∧
  finiteMean voterMass (fun i => potentialVoteShare 1 i - potentialVoteShare 0 i) = 5 ∧
  (25 : ℝ) ≠ 5

/-- Only the counterexample component of the corrected ignorability discussion. -/
def T22Statement : Prop := T21Statement

def T23Statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω), MeasurableSet A → MeasurableSet B →
    (A ⊆ B ↔ ∀ ω, ω ∈ A → ω ∈ B) ∧
    (A ⊆ B → probability μ A ≤ probability μ B) ∧
    (A ⊆ B → probability μ (B \ A) = probability μ B - probability μ A) ∧
    probability μ ∅ = 0 ∧ (0 ≤ probability μ A ∧ probability μ A ≤ 1) ∧
    probability μ Aᶜ = 1 - probability μ A ∧
    probability μ (A ∪ B) = probability μ A + probability μ B - probability μ (A ∩ B) ∧
    (A ⊆ B → A ≠ B → ¬ ∀ ω, ω ∈ B → ω ∈ A)

def T24Statement : Prop :=
  (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] (A : ι → Set Ω),
    (∀ i, MeasurableSet (A i)) → (∀ i, (A i).Nonempty) →
    Pairwise (fun i j => Disjoint (A i) (A j)) → (⋃ i, A i) = Set.univ →
    ∀ B : Set Ω, MeasurableSet B →
    probability μ B = ∑' i, probability μ (B ∩ A i) ∧
    ((∀ i, 0 < probability μ (A i)) →
      probability μ B = ∑' i,
        (probability μ (B ∩ A i) / probability μ (A i)) * probability μ (A i)) ∧
    (∀ C : Set Ω, MeasurableSet C →
      0 ≤ probability μ C ∧
      ((C.Nonempty ∧ Cᶜ.Nonempty) ↔ C ≠ ∅ ∧ C ≠ Set.univ) ∧
      probability μ B = probability μ (B ∩ C) + probability μ (B ∩ Cᶜ)) ∧
    (0 ≤ probability μ (∅ : Set Ω) ∧ ¬ 0 < probability μ (∅ : Set Ω))) ∧
  (∀ {Ω : Type*} (A : Set Ω),
    (∀ C ∈ complementFamily A, C.Nonempty) ∧
    (∀ C ∈ complementFamily A, ∀ D ∈ complementFamily A, C ≠ D → Disjoint C D) ∧
    ⋃₀ complementFamily A = Set.univ) ∧
  ((1/8 + 1/12 : ℝ) = 5/24)

def T25Statement : Prop :=
  finiteProbability zeroMass (fun _ => (0 : ℝ) < 4) = 1 ∧
  (∑ k ∈ Finset.Icc (1 : ℤ) 3, finiteProbability zeroMass (fun _ => (0 : ℤ) = k)) = 0 ∧
  finiteProbability zeroMass (fun _ => (0 : ℝ) < 4) ≠
    ∑ k ∈ Finset.Icc (1 : ℤ) 3, finiteProbability zeroMass (fun _ => (0 : ℤ) = k)

def T26Statement : Prop :=
  ∀ q : ℤ → ℝ, (∀ k, 0 ≤ q k) → Summable q → (∑' k, q k) = 1 →
  (∑' k : ℤ, if (k : ℝ) < 4 then q k else 0) = integerCDF q 3 ∧
  integerCDF q 3 - (∑ k ∈ Finset.Icc (1 : ℤ) 3, q k) = integerCDF q 0 ∧
  (integerCDF q 3 = (∑ k ∈ Finset.Icc (1 : ℤ) 3, q k) ↔ integerCDF q 0 = 0)

def T27Statement : Prop :=
  Summable dyadicWeight ∧ (∑' i, dyadicWeight i) = 1 ∧
  (∀ i, 0 < dyadicWeight i) ∧ (Set.range dyadicLocation).Countable ∧
  (∀ a b : ℝ, 0 < a → a < b → b < 1 →
    dyadicDistributionFunction a < dyadicDistributionFunction b) ∧
  ContinuousAt dyadicDistributionFunction (1/3) ∧
  ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x - 1/3| < ε →
    dyadicDistributionFunction x = dyadicDistributionFunction (1/3)

def T28Statement : Prop :=
  (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ), Measurable X → ∀ [Countable (Set.range X)] (x : ℝ),
    distributionFunction μ X x = ∑' t : Set.range X,
      if t.val ≤ x then probability μ {ω | X ω = t.val} else 0) ∧
  (∀ {m : ℕ} (w : Fin (m+1) → ℝ), (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
    ∀ X : Fin (m+1) → ℝ, StrictMono X → ∀ x : ℝ,
    (x < X 0 → finiteProbability w (fun i => X i ≤ x) = 0) ∧
    (∀ l : Fin m, X l.castSucc ≤ x → x < X l.succ →
      finiteProbability w (fun i => X i ≤ x) =
        ∑ i : Fin (m+1), if i ≤ l.castSucc then w i else 0) ∧
    (X (Fin.last m) ≤ x → finiteProbability w (fun i => X i ≤ x) = 1)) ∧
  (∀ {n : ℕ} (w : Fin n → ℝ), (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
    ∀ (X : Fin n → ℝ) (a b : ℝ), a ≤ b →
    (∀ i, ¬ (a < X i ∧ X i ≤ b)) →
    finiteProbability w (fun i => X i ≤ a) = finiteProbability w (fun i => X i ≤ b)) ∧
  (finiteProbability dieMass (fun i => dieValue i ≤ -1) = 0 ∧
    finiteProbability dieMass (fun i => dieValue i ≤ 1) = 1/6 ∧
    finiteProbability dieMass (fun i => dieValue i ≤ 3/2) = 1/6 ∧
    finiteProbability dieMass (fun i => dieValue i ≤ 2) = 1/3 ∧
    finiteProbability dieMass (fun i => dieValue i ≤ 6) = 1 ∧
    finiteProbability dieMass (fun i => dieValue i ≤ 7) = 1)

def T29Statement : Prop :=
  (∀ x : ℝ, 0 ≤ closedUniformDensity x ∧ 0 ≤ openUniformDensity x ∧
    0 ≤ modifiedUniformDensity x) ∧
  (∀ x : ℝ, (∫ u in Set.Iic x, closedUniformDensity u) = uniformDistributionFunction x ∧
    (∫ u in Set.Iic x, openUniformDensity u) = uniformDistributionFunction x ∧
    (∫ u in Set.Iic x, modifiedUniformDensity u) = uniformDistributionFunction x) ∧
  closedUniformDensity ≠ openUniformDensity ∧ closedUniformDensity ≠ modifiedUniformDensity ∧
  openUniformDensity ≠ modifiedUniformDensity ∧
  ¬ DifferentiableAt ℝ uniformDistributionFunction 0 ∧
  ¬ DifferentiableAt ℝ uniformDistributionFunction 1 ∧
  (∀ h : ℝ, 0 < h → h ≤ 1 →
    (uniformDistributionFunction (-h) - uniformDistributionFunction 0) / (-h) = 0 ∧
    (uniformDistributionFunction h - uniformDistributionFunction 0) / h = 1 ∧
    (uniformDistributionFunction (1-h) - uniformDistributionFunction 1) / (-h) = 1 ∧
    (uniformDistributionFunction (1+h) - uniformDistributionFunction 1) / h = 0) ∧
  closedUniformDensity 0 = 1 ∧ closedUniformDensity 1 = 1

end
end SAP.P001b
