import SAP.P030.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P030
open scoped BigOperators
noncomputable section

def T11Statement : Prop :=
  (∀ {A : Type*} [DecidableEq A] (U F C T : Finset A),
    U = (F ∪ C) ∪ T → Disjoint F C → Disjoint F T → Disjoint C T →
    U.card = F.card + C.card + T.card ∧
    ¬ (U.card = 344056 ∧ F.card = 114629 ∧ C.card = 191228 ∧ T.card = 38198)) ∧
  (114629 + 191228 + 38198 = (344055 : ℕ) ∧ (344055 : ℕ) ≠ 344056 ∧
    (344056 : ℕ) - 191228 - 38198 = 114630) ∧
  (∀ N F C T : ℕ,
    (N = F+C+T ∧
      ((N ≠ 344056 ∧ F = 114629 ∧ C = 191228 ∧ T = 38198) ∨
       (N = 344056 ∧ F ≠ 114629 ∧ C = 191228 ∧ T = 38198) ∨
       (N = 344056 ∧ F = 114629 ∧ C ≠ 191228 ∧ T = 38198) ∨
       (N = 344056 ∧ F = 114629 ∧ C = 191228 ∧ T ≠ 38198))) ↔
      (N = 344055 ∧ F = 114629 ∧ C = 191228 ∧ T = 38198) ∨
      (N = 344056 ∧ F = 114630 ∧ C = 191228 ∧ T = 38198) ∨
      (N = 344056 ∧ F = 114629 ∧ C = 191229 ∧ T = 38198) ∨
      (N = 344056 ∧ F = 114629 ∧ C = 191228 ∧ T = 38199))

def T12Statement : Prop :=
  ∀ {N : ℕ} (Ω : AssignmentSet N) (S : FixedIndicator N) (a : Assignment N)
    (hΩ' : (conditionalAssignments Ω S a).Nonempty) (Y : PotentialOutcomes N)
    (g : ({i // S i = true} → ℝ) → Assignment N → ℝ),
    NoInterference Ω Y ∨ FixedOutcomeNull (conditionalAssignments Ω S a) S Y →
    let Ω' := conditionalAssignments Ω S a
    let μ := uniformLaw Ω' hΩ'
    let t := statistic S Y g
    (∀ z ∈ Ω', ∀ w ∈ Ω', referenceStatistic S Y g z w = t w) ∧
    (∀ z ∈ Ω', lowerTail μ t (t z) = uniformProbability Ω' (fun w => t w ≤ t z)) ∧
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 → probability μ (fun z => lowerTail μ t (t z) ≤ u) ≤ u) ∧
    (∀ z ∈ Ω', probability μ (fun w => lowerTail μ t (t w) ≤ lowerTail μ t (t z)) =
      lowerTail μ t (t z)) ∧
    (∀ u : ℝ, IsGreatest ({0} ∪ {p | ∃ z ∈ Ω', p = lowerTail μ t (t z) ∧ p ≤ u})
      (probability μ (fun z => lowerTail μ t (t z) ≤ u)))

def T13Statement : Prop := by
  classical
  exact ∀ N M : ℕ, 2 ≤ N → M ≤ N →
    ∀ (i : Fin N) (neighbors : Finset (Fin N)), i ∉ neighbors →
    let Ω := completeAssignments N M
    let Ω1 := Ω.filter (fun z => z i = true)
    let Ω0 := Ω.filter (fun z => z i = false)
    let E := uniformMean Ω (proximalExposure neighbors)
    let E1 := uniformMean Ω1 (proximalExposure neighbors)
    let E0 := uniformMean Ω0 (proximalExposure neighbors)
    Ω.Nonempty ∧ (1 ≤ M → Ω1.Nonempty) ∧ (M ≤ N-1 → Ω0.Nonempty) ∧
    E = (neighbors.card : ℝ)*(M : ℝ)/(N : ℝ) ∧
    (1 ≤ M → E1 = (neighbors.card : ℝ)*((M : ℝ)-1)/((N : ℝ)-1)) ∧
    (M ≤ N-1 → E0 = (neighbors.card : ℝ)*(M : ℝ)/((N : ℝ)-1)) ∧
    (∀ j : Fin N, ∀ neighbors' : Finset (Fin N), j ∉ neighbors' → 1 ≤ M →
      neighbors.card < neighbors'.card → E < uniformMean Ω (proximalExposure neighbors')) ∧
    (1 ≤ M → M ≤ N-1 → 1 ≤ neighbors.card → E1 < E ∧ E < E0) ∧
    (1 ≤ M → M ≤ N-1 → (M : ℝ)/(N : ℝ)*E1 + ((N : ℝ)-(M : ℝ))/(N : ℝ)*E0 = E)

def T14Statement : Prop :=
  tenPsi = ![1,2,2,2,2,2,2,2,2,1] ∧
  (fun i => tenTheta i (tenAssignment 6)) = ![0,0,0,0,0,1,0,1,0,0] ∧
  (fun i => tenYexample i (tenAssignment 6)) = ![1,2,2,2,2,3,2,3,2,1] ∧
  (fun i : Fin 4 => tenYexample (tenFixed i) (tenAssignment 6)) = ![1,3,2,1] ∧
  tableDistances 5 = ![6,1,2,3] ∧ TableDesign ∧ TableNumerics ∧
  (∀ r : Fin 6, referenceStatistic tenS tenYexample tenG (tenAssignment 6)
    (tenAssignment (tableTreatment r)) = tableRho r) ∧
  statistic tenS tenYexample tenG (tenAssignment 6) = -3 / Real.sqrt 10 ∧
  (Finset.univ.filter (fun r : Fin 6 => tableRho r ≤ tableRho 5)).card = 2 ∧
  uniformProbability tableΩ (fun w => referenceStatistic tenS tenYexample tenG
    (tenAssignment 6) w ≤ statistic tenS tenYexample tenG (tenAssignment 6)) = 1/3 ∧
  |(1/3 : ℝ) - 0.333| < 0.0005

def T15Statement : Prop :=
  (∀ C f : ℝ, f*(C-f) = C^2/4-(f-C/2)^2) ∧
  (∀ C M : ℤ, 1 ≤ C → 1 ≤ M →
    (∀ k : ℤ, C = 2*k → ∀ f : ℤ, 0 ≤ f → f ≤ C →
      ((∀ g : ℤ, 0 ≤ g → g ≤ C → fixedSizeObjective C M g ≤ fixedSizeObjective C M f) ↔ f = k)) ∧
    (∀ k : ℤ, C = 2*k+1 → ∀ f : ℤ, 0 ≤ f → f ≤ C →
      ((∀ g : ℤ, 0 ≤ g → g ≤ C → fixedSizeObjective C M g ≤ fixedSizeObjective C M f) ↔
        f = k ∨ f = k+1)))

end
end SAP.P030
