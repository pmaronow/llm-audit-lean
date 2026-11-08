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

/-- The mathematical statement of P008-T7. -/
def T7Statement : Prop :=
  ((∀ i j k z, riskOutcome i j k z = 0 ∨ riskOutcome i j k z = 1) ∧
    (∀ i j z, riskM i j z = ((riskBaseline i : ℝ) - 321 * bit (z i)) / 40000)) ∧
  ((∀ i j b, marginal (uniformLaw (Assignment 4)) (riskM i j) i b =
      ((riskBaseline i : ℝ) - 321 * bit b) / 40000) ∧
    (∀ j, (1 / 4 : ℝ) * ∑ i,
      (marginal (uniformLaw (Assignment 4)) (riskM i j) i true - marginal (uniformLaw (Assignment 4)) (riskM i j) i false) = -321 / 40000) ∧
    (∀ j, hajek (fun i z => riskM i j z) ![true, true, false, false] = -321 / 40000) ∧
    (∑ _j : Fin 4, (-321 / 40000 : ℝ)) = -321 / 10000 ∧
    (379 / 40000 - 7 / 400 : ℝ) = -321 / 40000 ∧
    (7 / 400 - 321 / 10000 : ℝ) = -73 / 5000 ∧
    (-73 / 5000 : ℝ) < 0 ∧
    (∑ _j : Fin 4, (-1 : ℝ)) = -4 ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → a - b ≠ -4)) ∧
  (riskSamplingProbability (uniformLaw (Assignment 4)) false = 7 / 400 ∧
    riskSamplingProbability (uniformLaw (Assignment 4)) true = 379 / 40000 ∧
    riskSamplingProbability (uniformLaw (Assignment 4)) true - riskSamplingProbability (uniformLaw (Assignment 4)) false = -321 / 40000) ∧
  ((∀ i j k z, companionRiskOutcome i j k z = 0 ∨ companionRiskOutcome i j k z = 1) ∧
    (∀ i j z, companionRiskM i j z = 1 - bit (z i)) ∧
    (∀ j, finiteAMR (uniformLaw (Assignment 4)) (fun i z => companionRiskM i j z) = -1) ∧
    (∑ j : Fin 4, finiteAMR (uniformLaw (Assignment 4)) (fun i z => companionRiskM i j z)) = -4 ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      a - b ≠ ∑ j : Fin 4, finiteAMR (uniformLaw (Assignment 4)) (fun i z => companionRiskM i j z))) ∧
  (commonBernoulli (uniformLaw (Assignment 4)) (1 / 2) ∧
    (uniformLaw (Assignment 4)).mass ![true, true, false, false] = 1 / 16 ∧
    (∀ j : Fin 4, hajek (fun i z => companionRiskM i j z)
      ![true, true, false, false] = -1) ∧
    (∑ j : Fin 4, hajek (fun i z => companionRiskM i j z)
      ![true, true, false, false]) = -4) ∧
  (∀ (w : Fin 4 → ℝ), (∀ j, 0 ≤ w j) → (∑ j, w j = 1) →
    (∑ j, w j * finiteAMR (uniformLaw (Assignment 4)) (fun i z => riskM i j z)) = -321 / 40000)

/-- The mathematical statement of P008-T8. -/
def T8Statement : Prop :=
  (∀ {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (d : ℝ) (hN : 0 < N)
    (hfield : MeasurableSet P.field)
    (hmass : ∀ i, 0 < P.circleMass i d)
    (hfinite : ∀ i, P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : ∀ i b z, Q.mass z ≠ 0 → Integrable (fun x => P.Y x (Function.update z i b))
      (P.circleMeasure i d))
    (hbinary : ∀ x ∈ P.field, ∀ z, P.Y x z = 0 ∨ P.Y x z = 1),
    (∀ b, 0 ≤ P.risk Q b d ∧ P.risk Q b d ≤ 1) ∧
    P.amr Q d = P.risk Q true d - P.risk Q false d) ∧
  (∀ {J : ℕ} (w q₀ q₁ : Fin J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1)
    (h₀ : ∀ j, 0 ≤ q₀ j ∧ q₀ j ≤ 1) (h₁ : ∀ j, 0 ≤ q₁ j ∧ q₁ j ≤ 1)
    (L U : ℝ) (hL : ∀ j, L ≤ q₁ j - q₀ j) (hU : ∀ j, q₁ j - q₀ j ≤ U),
    (0 ≤ ∑ j, w j * q₀ j ∧ ∑ j, w j * q₀ j ≤ 1) ∧
    (0 ≤ ∑ j, w j * q₁ j ∧ ∑ j, w j * q₁ j ≤ 1) ∧
    (∑ j, w j * q₁ j) - (∑ j, w j * q₀ j) = ∑ j, w j * (q₁ j - q₀ j) ∧
    L ≤ ∑ j, w j * (q₁ j - q₀ j) ∧ ∑ j, w j * (q₁ j - q₀ j) ≤ U ∧
    |(∑ j, w j * q₁ j) - (∑ j, w j * q₀ j)| ≤ 1) ∧
  (∀ {J : ℕ} (hJ : 0 < J) (q₀ q₁ : Fin J → ℝ),
    (∑ j, q₁ j) / J - (∑ j, q₀ j) / J = (∑ j, (q₁ j - q₀ j)) / J ∧
    (∑ j, (q₁ j - q₀ j)) = (J : ℝ) * ((∑ j, (q₁ j - q₀ j)) / J)) ∧
  (∀ {J : ℕ}
    (w : Fin J → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1) (t : ℝ),
    (∑ _j : Fin J, t) = (J : ℝ) * t ∧ (∑ j, w j * t) = t) ∧
  (∀ {n : ℕ} (s : Fin (n + 1) → ℝ)
    (hs : Monotone s) (q m x y : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1) (hm : 0 < m),
    (x ≤ y ↔ x / m ≤ y / m) ∧ (|x| ≤ |y| ↔ |x / m| ≤ |y / m|) ∧
    quantile7 (fun j => s j / m) q = quantile7 s q / m) ∧
  ((-19 / 625 : ℝ) / 4 = -19 / 2500 ∧
    (-321 / 10000 : ℝ) / 4 = -321 / 40000 ∧
    (21 / 625 : ℝ) / 4 = 21 / 2500 ∧
    (-321 / 40000 : ℝ) < -19 / 2500 ∧
    (-321 / 10000 : ℝ) < -19 / 625) ∧
  ((∑ j : Fin 4, finiteAMR (uniformLaw (Assignment 4)) (fun i z => companionRiskM i j z)) = -4 ∧
  (∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
    a - b ≠ ∑ j : Fin 4, finiteAMR (uniformLaw (Assignment 4)) (fun i z => companionRiskM i j z)))

/-- The mathematical statement of P008-T9. -/
def T9Statement : Prop :=
  ((∀ i j, dist (bandwidthSpatialModel.node i) (bandwidthSpatialModel.node j) =
      |2 * (i : ℝ) - 2 * (j : ℝ)|) ∧
    (∀ i : Fin 4, ∀ j : Fin 3,
      bandwidthSpatialModel.circleMass i (bandwidthSpatialRadius j) = 1 ∧
      bandwidthSpatialModel.circleMeasure i (bandwidthSpatialRadius j) Set.univ ≠ ⊤ ∧
      ∀ z, Integrable (fun x => bandwidthSpatialModel.Y x z)
        (bandwidthSpatialModel.circleMeasure i (bandwidthSpatialRadius j))) ∧
    (∀ i : Fin 4, ∀ j : Fin 3, ∀ z,
      bandwidthSpatialModel.M i (bandwidthSpatialRadius j) z = 2 * (i : ℝ))) ∧
  (bandwidthShortGrid 0 = bandwidthLongGrid 1 ∧
    bandwidthShortGrid 0 = (1 / 5 : ℝ) ∧
    nTreated (![false, false, true, true] : Assignment 4) = 2 ∧
    nControl (![false, false, true, true] : Assignment 4) = 2 ∧
    (∀ i j z, bandwidthSpatialModel.M i (bandwidthSpatialRadius j) z = 2 * (i : ℝ)) ∧
    (∀ i j, dist (bandwidthSpatialModel.node i) (bandwidthSpatialModel.node j) =
      bandwidthExampleDistance i j) ∧
    hajek (fun i z => bandwidthSpatialModel.M i (1 / 5) z)
      ![false, false, true, true] = 4 ∧
    archivedVariance
      (regressionScore ![false, false, true, true]
        (fun i => bandwidthSpatialModel.M i (1 / 5) ![false, false, true, true]))
      (fun i j => dist (bandwidthSpatialModel.node i) (bandwidthSpatialModel.node j))
      (2 / 5) 1 = 1 ∧
    archivedVariance
      (regressionScore ![false, false, true, true]
        (fun i => bandwidthSpatialModel.M i (1 / 5) ![false, false, true, true]))
      (fun i j => dist (bandwidthSpatialModel.node i) (bandwidthSpatialModel.node j))
      (2 / 5) 2 = 1 / 2) ∧
  (∀ i, regressionScore ![false, false, true, true] ![0, 2, 4, 6] i =
    (![1 / 2, -1 / 2, -1 / 2, 1 / 2] : Fin 4 → ℝ) i) ∧
  (∀ (z : Assignment 4) (M : Fin 4 → ℝ)
    (h₁ : nTreated z ≠ 0) (h₀ : nControl z ≠ 0),
    (∀ i j, dist (toyNode i) (toyNode j) ^ 2 ≤ 32) ∧
    archivedVariance (regressionScore z M)
      (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) 6 = 0 ∧
    (∀ a : ℝ, 2 * a * Real.sqrt (archivedVariance (regressionScore z M)
      (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) 6) ≠ 869 / 250))

end
end SAP.P008a
