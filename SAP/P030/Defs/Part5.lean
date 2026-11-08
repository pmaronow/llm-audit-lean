import SAP.P030.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P030
open scoped BigOperators
noncomputable section

def T6Statement : Prop :=
  (∀ {N : ℕ} (Ω : AssignmentSet N) (S : FixedIndicator N) (obs : Assignment N), obs ∈ Ω →
    ∀ (Y : PotentialOutcomes N) (g : ({i // S i = true} → ℝ) → Assignment N → ℝ),
    (NoInterference Ω Y → FixedOutcomeNull (conditionalAssignments Ω S obs) S Y) ∧
    (FixedOutcomeNull (conditionalAssignments Ω S obs) S Y →
      (∀ z ∈ conditionalAssignments Ω S obs, fixedOutcomes S Y z = fixedOutcomes S Y obs) ∧
      (∀ z ∈ conditionalAssignments Ω S obs,
        referenceStatistic S Y g obs z = statistic S Y g z) ∧
      (∀ x : ℝ, uniformProbability (conditionalAssignments Ω S obs)
        (fun z => referenceStatistic S Y g obs z ≤ x) =
        uniformProbability (conditionalAssignments Ω S obs) (fun z => statistic S Y g z ≤ x)))) ∧
  OutcomeNullNonconstant

def T7Statement : Prop :=
  ∀ {N : ℕ} (Ω : AssignmentSet N) (S : FixedIndicator N) (obs : Assignment N), obs ∈ Ω →
  (∀ z ∈ conditionalAssignments Ω S obs, ∀ z' ∈ conditionalAssignments Ω S obs,
    ∀ i, S i = true → z i = z' i) ∧
  (∀ Y : PotentialOutcomes N, NoInterference Ω Y →
    FixedOutcomeNull (conditionalAssignments Ω S obs) S Y) ∧
  (∀ Y : PotentialOutcomes N,
    (∃ i, S i = true ∧ ∃ z ∈ conditionalAssignments Ω S obs,
      ∃ z' ∈ conditionalAssignments Ω S obs, Y i z ≠ Y i z') → ¬ NoInterference Ω Y) ∧
  (∀ c τ : Fin N → ℝ,
    NoInterference Ω (fun i z => c i + τ i * treatment z i) ∧
    FixedOutcomeNull (conditionalAssignments Ω S obs) S (fun i z => c i + τ i * treatment z i)) ∧
  (∀ Y : PotentialOutcomes N, NoEffects Ω Y → NoInterference Ω Y)

def T8Statement : Prop :=
  TableNumerics ∧
  (∀ r : Fin 6, printedRho 4 (tableDistances r) tableY =
    (![-4/45,-4/45,-4/45,-20/27,-4/5,-4/5] : Fin 6 → ℝ) r) ∧
  (∀ r : Fin 6, printedRho 3 (tableDistances r) tableY =
    (![-1/15,-1/15,-1/15,-5/9,-3/5,-3/5] : Fin 6 → ℝ) r) ∧
  (-4/5 : ℝ) ≠ -3 / Real.sqrt 10 ∧ (-3/5 : ℝ) ≠ -3 / Real.sqrt 10 ∧
  (-4/5 : ℝ) ≠ -3/5 ∧
  (0 < rankSquares (![1,2,1,1] : Fin 4 → ℝ) ∧
    0 < rankSquares (![0,2,1,1] : Fin 4 → ℝ)) ∧
  spearman (![1,2,1,1] : Fin 4 → ℝ) tableY = Real.sqrt 6 / 3 ∧
  spearman (![0,2,1,1] : Fin 4 → ℝ) tableY = 5/6 ∧
  printedRho 4 (![1,2,1,1] : Fin 4 → ℝ) tableY = 8/9 ∧
  printedRho 4 (![0,2,1,1] : Fin 4 → ℝ) tableY = 20/27 ∧
  Real.sqrt 6 / 3 < (5/6 : ℝ) ∧ (20/27 : ℝ) < 8/9 ∧ WeakMonotoneExample

def T9Statement : Prop :=
  (∀ {n : ℕ}, 2 ≤ n → ∀ a b : Fin n → ℝ, Nonconstant a → Nonconstant b →
    (∑ k, averageRank a k) = (n : ℝ) * ((n : ℝ)+1)/2 ∧
    (∑ k, averageRank b k) = (n : ℝ) * ((n : ℝ)+1)/2 ∧
    0 < rankSquares a ∧ 0 < rankSquares b ∧
    (∀ m : ℝ, 0 < m → spearman a b =
      rankCov m a b / Real.sqrt ((rankSquares a / m)*(rankSquares b / m))) ∧
    (-1 ≤ spearman a b ∧ spearman a b ≤ 1) ∧
    (|spearman a b| = 1 ↔ ∃ c : ℝ, c ≠ 0 ∧ centeredRanks a = fun k => c * centeredRanks b k) ∧
    (∀ c : ℝ, c ≠ 0 → centeredRanks a = (fun k => c * centeredRanks b k) →
      (0 < c → spearman a b = 1) ∧ (c < 0 → spearman a b = -1)) ∧
    ((∀ k l, a k < a l ↔ b k < b l) → averageRank a = averageRank b ∧ spearman a b = 1) ∧
    ((∀ k l, a k < a l ↔ b l < b k) →
      (∀ k, averageRank a k = (n : ℝ)+1-averageRank b k) ∧ spearman a b = -1)) ∧
  WeakMonotoneExample ∧ TableNumerics

def T10Statement : Prop :=
  (∀ {N : ℕ} (d : Fin N → Fin N → ℝ) (z : Assignment N) (i : Fin N), d i i = 0 →
    (1 - (if i = i then (1 : ℝ) else 0)) * treatment z i = 0 ∧
    ((3/2 : ℝ) * d i i)^2 = 0 ∧
    partialRealQuotient ((1 - (if i = i then (1 : ℝ) else 0)) * treatment z i)
      (((3/2 : ℝ) * d i i)^2) = none) ∧
  (∀ {N : ℕ} (d : Fin N → Fin N → ℝ), (∀ i j, i ≠ j → 0 < d i j) →
    (∀ i j, j ∈ Finset.univ.erase i → ((3/2 : ℝ)*d i j)^2 ≠ 0) ∧
    (∀ (z : Assignment N) i, inverseSquareIndirect d z i =
      ∑ j ∈ Finset.univ.erase i, treatment z j * inverseSquare (d i j)) ∧
    (∀ i, inverseSquareSpatial d i = ∑ j ∈ Finset.univ.erase i, inverseSquare (d i j))) ∧
  (∀ d : ℝ, 0 < d →
    inverseSquare d = 4/(9*d^2) ∧ inverseSquare (2*d) / inverseSquare d = 1/4 ∧
    inverseSquare (2/3) = 1 ∧ inverseSquare 1 = 4/9 ∧ inverseSquare 2 = 1/9) ∧
  (¬ ∃ A c : ℝ, ∀ d : ℝ, 0 < d → inverseSquare d = A * Real.exp (-c*d)) ∧
  (∀ B d : ℝ, 0 < B → 0 < d → d < 2/(3*Real.sqrt B) → B < inverseSquare d) ∧
  (∀ A c : ℝ, Filter.Tendsto (fun d : ℝ => A*Real.exp (-c*d))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds A))

end
end SAP.P030
