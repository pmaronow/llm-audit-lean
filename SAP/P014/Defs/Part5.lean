import SAP.P014.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014
open scoped BigOperators
noncomputable section
universe u

def LocalConsequences {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) (X : Ω → Fin N → ℝ) (b : ℝ)
    (S : Finset (Fin N)) (v : S → ℝ) (m : ℕ) : Prop :=
  (∀ᵐ ω ∂μ, armSize S (thresholdAssignment (X ω)) true = m ∧
    0 < armSize S (thresholdAssignment (X ω)) true ∧
    armSize S (thresholdAssignment (X ω)) true < S.card ∧
    windowSubjects b (X ω) = S ∧ (windowSubjects b (X ω)).card = S.card ∧
    ∀ t, windowCDF S (X ω) t =
      (∑ i : S, if v i ≤ t then (1 : ℝ) else 0) / S.card) ∧
  (∀ i : S, eventProbability μ (fun ω => thresholdAssignment (X ω) i = true) =
    (m : ℝ) * (S.card - 1).factorial / S.card.factorial ∧
    eventProbability μ (fun ω => thresholdAssignment (X ω) i = true) = (m : ℝ) / S.card ∧
    eventProbability μ (fun ω => thresholdAssignment (X ω) i = false) =
      ((S.card : ℝ) - m) / S.card) ∧
  (∀ i j : S, i ≠ j → eventProbability μ (fun ω => X ω i = X ω j) = 0)

def T6GeneralPart : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ) (m : ℕ),
  0 < b → 2 ≤ S.card → Function.Injective v → (∀ i, insideWindow b (v i)) →
  0 < m → m < S.card →
  (Finset.univ.filter (fun i : S => 0 ≤ v i)).card = m →
  CorrectedLocalConditions μ X b S v →
  LocalConsequences μ X b S v m ∧
  (∀ g : (S → ℝ) → Fin N → ℝ,
    (∀ᵐ ω ∂μ, ∀ j ∉ S, X ω j = g (fun i : S => X ω i) j) →
    ∃ A : FiniteDistribution (Fin N → ℝ), IsDistribution A ∧
      A.atoms.card = S.card.factorial ∧
      (∀ x ∈ A.atoms, A.weight x = 1 / (S.card.factorial : ℝ)) ∧
      (∀ x, eventProbability μ (fun ω => X ω = x) =
        if x ∈ A.atoms then A.weight x else 0))

def T6OutsideExample : Prop :=
  IsDistribution extendedDistribution ∧
  (∀ ω : Fin 6 × Bool, windowSubjects 2 (extendedScores ω) = localThree) ∧
  (∀ a : Fin 6, probability extendedDistribution (fun ω =>
    (fun i : Fin 3 => extendedScores ω (Fin.castSucc i)) = localCoordinates scores1 a) = 1/6) ∧
  (∀ σ : Equiv.Perm (Fin 3), probability extendedDistribution (fun ω => ∀ i : Fin 3,
    extendedScores ω (Fin.castSucc i) = (![-2,-1,1] : Fin 3 → ℝ) (σ i)) = 1/6) ∧
  (∀ ω : Fin 6 × Bool, armSize localThree (thresholdAssignment (extendedScores ω)) true = 1) ∧
  localThree.card = 3 ∧
  (pushforward extendedDistribution extendedScores).atoms.card = 12 ∧
  (∀ ω : Fin 6 × Bool, probability extendedDistribution (fun η =>
    extendedScores η = extendedScores ω) = if ω.2 then 1/9 else 1/18) ∧
  (∀ ω : Fin 6 × Bool, probability extendedDistribution (fun η =>
    extendedScores η = extendedScores ω) ≠ 1/6) ∧
  probability extendedDistribution (fun ω => extendedScores ω 3 = -3) = 1/3 ∧
  probability extendedDistribution (fun ω => extendedScores ω 3 = 3) = 2/3 ∧
  (∀ a : Fin 6, ∀ t : Bool, probability extendedDistribution (fun ω =>
    (fun i : Fin 3 => extendedScores ω (Fin.castSucc i)) = localCoordinates scores1 a ∧
    extendedScores ω 3 = (if t then 3 else -3)) =
    probability extendedDistribution (fun ω =>
      (fun i : Fin 3 => extendedScores ω (Fin.castSucc i)) = localCoordinates scores1 a) *
    probability extendedDistribution (fun ω => extendedScores ω 3 = (if t then 3 else -3)))

def T6Statement : Prop := T6GeneralPart.{u} ∧ T6OutsideExample

def T7GeneralPart : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ) (S : Finset (Fin N)),
  ((∀ i ∈ S, ∀ j ∈ S, eventProbability μ (fun ω => X ω i = X ω j) = 0) ↔ S = ∅) ∧
  (∀ i ∈ S, eventProbability μ (fun ω => X ω i = X ω i) = 1) ∧
  ((∀ i ∈ S, ∀ j ∈ S, eventProbability μ (fun ω => X ω i = X ω j) = 0) ↔
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → eventProbability μ (fun ω => X ω i = X ω j) = 0) ∧
    (∀ i ∈ S, eventProbability μ (fun ω => X ω i = X ω i) = 0)) ∧
  (∀ m : ℕ, 0 < m → m < S.card → 2 ≤ S.card ∧ S.Nonempty ∧
    ¬ (∀ i ∈ S, ∀ j ∈ S, eventProbability μ (fun ω => X ω i = X ω j) = 0))

def T7LocalPart : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : ℕ}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin N → ℝ) (b : ℝ) (S : Finset (Fin N)) (v : S → ℝ) (m : ℕ),
  0 < b → 2 ≤ S.card → Function.Injective v → (∀ i, insideWindow b (v i)) →
  0 < m → m < S.card →
  (Finset.univ.filter (fun i : S => 0 ≤ v i)).card = m →
  CorrectedLocalConditions μ X b S v →
  ∀ i j : S, i ≠ j → eventProbability μ (fun ω => X ω i = X ω j) = 0

def T7Statement : Prop :=
  T7GeneralPart.{u} ∧ T7LocalPart.{u} ∧ localThree.card = 3 ∧
    DistinctNoTies uniformSix scores1 localThree ∧
    DistinctNoTies uniformSix scores5 localThree ∧
    DistinctNoTies uniformSix scores9 localThree

def T8Statement : Prop :=
  ∀ {N : ℕ} (S : Finset (Fin N)) (f : Fin N → Bool → ℝ), S.Nonempty →
  windowContrast S f = ((∑ i ∈ S, f i true) - ∑ i ∈ S, f i false) / S.card

end
end SAP.P014
