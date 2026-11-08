import Mathlib
import SAP.P008a.Defs.Part1
import SAP.P008a.Defs.Part2
import SAP.P008a.Defs.Part3
import SAP.P008a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P008a

open MeasureTheory Filter
open scoped BigOperators Classical

noncomputable section

/-- The mathematical statement of P008-T1. -/
def T1Statement : Prop :=
  (unrestricted121.card = Nat.choose 121 60 ∧
    blocked121.card = Nat.choose 10 5 * Nat.choose 111 55 ∧
    blocked121 ⊂ unrestricted121 ∧
    observed121 ∈ unrestricted121 ∧ observed121 ∈ blocked121 ∧
    alternative121 ∈ unrestricted121 ∧ alternative121 ∉ blocked121 ∧
    0 < supportMass unrestricted121 observed121 ∧
    0 < supportMass blocked121 observed121 ∧
    0 < supportMass unrestricted121 alternative121 ∧
    supportMass blocked121 alternative121 = 0 ∧
    (∑ z ∈ unrestricted121, supportMass unrestricted121 z) = 1 ∧
    (∑ z ∈ blocked121, supportMass blocked121 z) = 1) ∧
  (supportMass unrestricted121 ≠ supportMass blocked121) ∧
  (Function.Injective sixAssignment ∧
    (∀ z : Assignment 4, treatedCount z = 2 ↔ ∃ k, sixAssignment k = z) ∧
    sixAssignment 1 = ![true, false, true, false]) ∧
  (Function.Injective blockedAssignment ∧
    (∀ z : Assignment 4, (z 0 ≠ z 1 ∧ z 2 ≠ z 3) ↔
      ∃ k, blockedAssignment k = z)) ∧
  (∀ k : Fin 6,
    contrast4 ![0, 1, 0, 1] (sixAssignment k) = (![0, -1, 0, 0, 1, 0] : Fin 6 → ℝ) k ∧
    contrast4 ![0, 1 / 3, 2 / 3, 1] (sixAssignment k) =
      (![-2 / 3, -1 / 3, 0, 0, 1 / 3, 2 / 3] : Fin 6 → ℝ) k) ∧
  (tailP (uniformLaw (Fin 6))
      (fun k => contrast4 ![0, 1, 0, 1] (sixAssignment k)) 1 = 1 / 3 ∧
    tailP (uniformLaw (Fin 4))
      (fun k => contrast4 ![0, 1, 0, 1] (blockedAssignment k)) 0 = 1 / 2 ∧
    tailP (uniformLaw (Fin 6))
      (fun k => contrast4 ![0, 1 / 3, 2 / 3, 1] (sixAssignment k)) 1 = 2 / 3 ∧
    tailP (uniformLaw (Fin 4))
      (fun k => contrast4 ![0, 1 / 3, 2 / 3, 1] (blockedAssignment k)) 0 = 1 / 2 ∧
    (1 / 3 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 2 / 3)

/-- The mathematical statement of P008-T2. -/
def T2Statement : Prop :=
  (∀ {Ω : Type} [Fintype Ω] (Q : FiniteLaw Ω)
    (T : Ω → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1),
    Q.prob (fun z => tailP Q T z ≤ δ) ≤ δ) ∧
  (∀ {Ω : Type} [Fintype Ω] (Q : FiniteLaw Ω)
    (A : Ω → Prop) (hA : 0 < Q.prob A) (T : Ω → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1),
    (conditionalLaw Q A hA).prob
      (fun z => tailP (conditionalLaw Q A hA) T z ≤ δ) ≤ δ) ∧
  (∀ {N : ℕ} (Q : FiniteLaw (Assignment N))
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hQ : commonBernoulli Q p)
    (M : ℕ) (hM : M ≤ N),
    0 < Q.prob (fun z => treatedCount z = M) ∧
    (∀ z, treatedCount z = M →
      Q.mass z / Q.prob (fun w => treatedCount w = M) =
        (Nat.choose N M : ℝ)⁻¹)) ∧
  (∀ {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (A : Assignment N → Prop) (hA : 0 < Q.prob A)
    (D : Finset ℝ) (hfield : MeasurableSet P.field) (hsharp : P.sharpNull)
    (hN : 0 < N) (hmass : ∀ i d, d ∈ D → 0 < P.circleMass i d)
    (hfinite : ∀ i d, d ∈ D → P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : ∀ i d, d ∈ D → ∀ z, Integrable (fun x => P.Y x z) (P.circleMeasure i d))
    (harms : ∀ z, A z → 0 < Q.mass z → nTreated z ≠ 0 ∧ nControl z ≠ 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1),
    let S := fun z => ∑ d ∈ D, hajek (fun i w => P.M i d w) z
    (conditionalLaw Q A hA).prob (fun z => tailP (conditionalLaw Q A hA) S z ≤ δ) ≤ δ ∧
    (∀ z, A z → 0 < Q.mass z →
      S z = ∑ d ∈ D, hajek (fun i _ => P.M i d (fun _ => false)) z)) ∧
  (tailP (uniformLaw (Fin 6))
      (fun k => contrast4 ![0, 1, 0, 1] (sixAssignment k)) 1 = 1 / 3 ∧
    tailP (uniformLaw (Fin 4))
      (fun k => contrast4 ![0, 1, 0, 1] (blockedAssignment k)) 0 = 1 / 2 ∧
    tailP (uniformLaw (Fin 6))
      (fun k => contrast4 ![0, 1 / 3, 2 / 3, 1] (sixAssignment k)) 1 = 2 / 3 ∧
    tailP (uniformLaw (Fin 4))
      (fun k => contrast4 ![0, 1 / 3, 2 / 3, 1] (blockedAssignment k)) 0 = 1 / 2 ∧
    (1 / 3 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 2 / 3)

/-- The mathematical statement of P008-T3. -/
def T3Statement : Prop :=
  (Function.Injective sixAssignment ∧
    (∀ z : Assignment 4, treatedCount z = 2 ↔ ∃ k, sixAssignment k = z) ∧
    sixAssignment 1 = ![true, false, true, false]) ∧
  ((∀ i : Fin 4, {x : Plane | dist x (validatorRectangleModel.node i) ≤ 1} ⊆
      validatorRectangleModel.field) ∧
    (∀ i k : Fin 4, i ≠ k → Disjoint
      {x : Plane | dist x (validatorRectangleModel.node i) ≤ 1}
      {x : Plane | dist x (validatorRectangleModel.node k) ≤ 1}) ∧
    (∀ i : Fin 4, ∀ j : Fin 5,
      0 < validatorRectangleModel.circleMass i (validatorRadius j) ∧
      validatorRectangleModel.circleMeasure i (validatorRadius j) Set.univ ≠ ⊤ ∧
      ∀ z, Integrable (fun x => validatorRectangleModel.Y x z)
        (validatorRectangleModel.circleMeasure i (validatorRadius j))) ∧
    (∀ x z, validatorRectangleModel.Y x z =
      validatorRectangleModel.Y x (fun _ => false)) ∧
    (∀ i : Fin 4, ∀ j : Fin 5, ∀ z,
      validatorRectangleModel.M i (validatorRadius j) z = i.val) ∧
    (∀ j k, validatorRectangleStatistic j k = percentileExample k) ∧
    (∀ j, quantile7 (validatorRectangleStatistic j) (1 / 40) = -15 / 8 ∧
      quantile7 (validatorRectangleStatistic j) (39 / 40) = 15 / 8 ∧
      (uniformLaw (Fin 6)).prob (fun k => outside (-15 / 8) (15 / 8)
        (validatorRectangleStatistic j k)) = 1 / 3) ∧
    quantile7 (fun k => ∑ j, validatorRectangleStatistic j k) (1 / 40) = -75 / 8 ∧
    quantile7 (fun k => ∑ j, validatorRectangleStatistic j k) (39 / 40) = 75 / 8 ∧
    (uniformLaw (Fin 6)).prob (fun k => outside (-75 / 8) (75 / 8)
      (∑ j, validatorRectangleStatistic j k)) = 1 / 3 ∧ (1 / 20 : ℝ) < 1 / 3) ∧
  (∀ (Q : FiniteLaw (Assignment 4)), commonBernoulli Q (1 / 2) →
    0 < Q.prob (fun z => treatedCount z = 2) ∧
    (∀ z, treatedCount z = 2 → Q.mass z / Q.prob (fun w => treatedCount w = 2) = (6 : ℝ)⁻¹)) ∧
  (∀ j : Fin 5, ∀ k : Fin 6,
    (outside (-15 / 8) (15 / 8) (validatorRectangleStatistic j k) ↔ k = 0 ∨ k = 5) ∧
    (∑ r : Fin 5, validatorRectangleStatistic r k) =
      (![-10, -5, 0, 0, 5, 10] : Fin 6 → ℝ) k ∧
    (outside (-75 / 8) (75 / 8) (∑ r : Fin 5, validatorRectangleStatistic r k) ↔
      k = 0 ∨ k = 5))

/-- The mathematical statement of P008-T4. -/
def T4Statement : Prop :=
  (∀ (y : Fin 4 → ℝ) (k : Fin 6),
    sixComplement k ≠ k ∧ sixAssignment (sixComplement k) = (fun i => !(sixAssignment k i)) ∧
    nTreated (sixAssignment k) = 2 ∧ nControl (sixAssignment k) = 2 ∧
    hajek (fun i _ => y i) (sixAssignment k) = contrast4 y (sixAssignment k)) ∧
  (∀ {J : ℕ} (a : Fin J → ℝ) (m : Fin J → Fin 4 → ℝ),
    let S := fun k => ∑ j, a j * contrast4 (m j) (sixAssignment k)
    (∀ k, S (sixComplement k) = -S k) ∧
    (∀ k, 1 / 3 ≤ tailP (uniformLaw (Fin 6)) S k ∧
      ¬ tailP (uniformLaw (Fin 6)) S k ≤ 1 / 20)) ∧
  (∀ R : Finset (Fin 6), R.Nonempty →
    (uniformLaw (Fin 6)).prob (fun k => k ∈ R) = R.card / 6 ∧
    (1 / 6 : ℝ) ≤ (uniformLaw (Fin 6)).prob (fun k => k ∈ R) ∧
    (1 / 20 : ℝ) < (uniformLaw (Fin 6)).prob (fun k => k ∈ R)) ∧
  (∀ {Ω : Type} [Fintype Ω] (Q : FiniteLaw Ω)
    (T : Ω → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1),
    Q.prob (fun z => tailP Q T z ≤ δ) ≤ δ) ∧
  (∀ {Ω : Type} [Fintype Ω]
    (Q : FiniteLaw Ω) (B : ℕ) (R : FiniteLaw (Fin (B + 1) → Ω))
    (hIID : ∀ z, R.mass z = ∏ k, Q.mass (z k)) (S : Ω → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1),
    R.prob (fun z =>
      (1 + ((Finset.univ.filter (fun b : Fin B =>
        |S (z 0)| ≤ |S (z b.succ)|)).card : ℝ)) / (B + 1) ≤ δ) ≤ δ) ∧
  ((1491 / 1000 : ℝ) + 1550 / 1000 + 1550 / 1000 + 1691 / 1000 + 1714 / 1000 = 1999 / 250)

end
end SAP.P008a
