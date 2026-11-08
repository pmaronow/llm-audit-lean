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

/-- The mathematical statement of P008-T5. -/
def T5Statement : Prop :=
  (Function.Bijective pairAssignment) ∧
  ((∀ i, pairNode i ∈ pairField) ∧
    lineCircle pairField pairNode 0 1 = {-1, 1} ∧
    lineCircle pairField pairNode 1 1 = {1, 3} ∧
    (∀ z, pairM 0 z = bit (z 0) + bit (z 1) / 2 ∧
      pairM 1 z = bit (z 1) + bit (z 0) / 2)) ∧
  ((∀ i : Fin 2,
      (uniformLaw (Fin 4)).expect (fun k => pairM i
        (Function.update (pairAssignment k) i true)) = 5 / 4 ∧
      (uniformLaw (Fin 4)).expect (fun k => pairM i
        (Function.update (pairAssignment k) i false)) = 1 / 4) ∧
    (∀ i k, linearizationScore pairM (5 / 4) (1 / 4) i (pairAssignment k) =
      (1 / 2 : ℝ) * (2 * bit (pairAssignment k 0) - 1) *
        (2 * bit (pairAssignment k 1) - 1)) ∧
    (uniformLaw (Fin 4)).var (fun k => linearizationScore pairM (5 / 4) (1 / 4) 0
      (pairAssignment k)) = 1 / 4 ∧
    (uniformLaw (Fin 4)).cov
      (fun k => linearizationScore pairM (5 / 4) (1 / 4) 0 (pairAssignment k))
      (fun k => linearizationScore pairM (5 / 4) (1 / 4) 1 (pairAssignment k)) = 1 / 4 ∧
    (uniformLaw (Fin 4)).var (fun k =>
      (linearizationScore pairM (5 / 4) (1 / 4) 0 (pairAssignment k) +
        linearizationScore pairM (5 / 4) (1 / 4) 1 (pairAssignment k)) / 2) = 1 / 4 ∧
    ((1 / 4 + 1 / 4) / 4 : ℝ) = 1 / 8 ∧ (1 / 8 : ℝ) < 1 / 4) ∧
  (((1 / 2 : ℝ) ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2,
      if dist (lineEmbedding (pairNode i)) (lineEmbedding (pairNode j)) ≤ 1 then
        (uniformLaw (Fin 4)).cov
          (fun k => linearizationScore pairM (5 / 4) (1 / 4) i (pairAssignment k))
          (fun k => linearizationScore pairM (5 / 4) (1 / 4) j (pairAssignment k))
      else 0) = 1 / 8 ∧
    (uniformLaw (Fin 4)).var (fun k => (1 / 2 : ℝ) * ∑ i : Fin 2,
      linearizationScore pairM (5 / 4) (1 / 4) i (pairAssignment k)) = 1 / 4 ∧
    (1 / 8 : ℝ) < 1 / 4) ∧
  ((∀ i : Fin 2,
    (uniformLaw (Fin 4)).expect
      (fun k => linearizationScore pairM (5 / 4) (1 / 4) i (pairAssignment k)) = 0 ∧
    (uniformLaw (Fin 4)).var
      (fun k => linearizationScore pairM (5 / 4) (1 / 4) i (pairAssignment k)) = 1 / 4) ∧
  (1 / 2 : ℝ) * ∑ i : Fin 2,
    ((uniformLaw (Fin 4)).expect (fun k => pairM i (Function.update (pairAssignment k) i true)) -
     (uniformLaw (Fin 4)).expect (fun k => pairM i (Function.update (pairAssignment k) i false))) = 1) ∧
  (∀ (M : ℕ) (hM : 0 < M),
    (∀ i : Fin M × Fin 2, replicatedNode i ∈ replicatedField M) ∧
    (∀ x ∈ replicatedField M, ∀ z : (Fin M × Fin 2) → Bool, 0 ≤ replicatedOutcome x z ∧ replicatedOutcome x z ≤ 2) ∧
    (∀ i : Fin M × Fin 2, replicatedCircle i = {replicatedNode i - 1, replicatedNode i + 1}) ∧
    (∀ g : Fin M, ∀ z,
      replicatedCircleM (g, 0) z = bit (z (g, 0)) + bit (z (g, 1)) / 2 ∧
      replicatedCircleM (g, 1) z = bit (z (g, 1)) + bit (z (g, 0)) / 2) ∧
    (∀ i : Fin M × Fin 2, ∀ z, replicatedSpatialScore i z = replicatedPairScore i z) ∧
    (uniformLaw ((Fin M × Fin 2) → Bool)).var
      (fun z => (2 * M : ℝ)⁻¹ * ∑ i, replicatedSpatialScore i z) = 1 / (2 * (2 * M)) ∧
    (2 * M : ℝ)⁻¹ ^ 2 * ∑ i,
      (uniformLaw ((Fin M × Fin 2) → Bool)).var (replicatedSpatialScore i) = 1 / (4 * (2 * M))) ∧
  (∀ (M : ℕ) (hM : 0 < M)
    (i : Fin M × Fin 2) (b : Bool),
    (uniformLaw ((Fin M × Fin 2) → Bool)).expect
      (fun z => replicatedCircleM i (Function.update z i b)) = bit b + 1 / 4) ∧
  (∀ {M : ℕ} (i : Fin M × Fin 2) (x : ℚ),
    x ∈ replicatedCircle i ↔ x ∈ replicatedField M ∧
      dist (lineEmbedding (replicatedNode i)) (lineEmbedding x) = 1) ∧
  (∀ {M : ℕ} (i j : Fin M × Fin 2) (hij : i ≠ j),
    2 ≤ dist (lineEmbedding (replicatedNode i)) (lineEmbedding (replicatedNode j))) ∧
  (∀ (M : ℕ) (hM : 0 < M)
    (i : Fin M × Fin 2) (z z' : (Fin M × Fin 2) → Bool)
    (h₀ : z (i.1, 0) = z' (i.1, 0)) (h₁ : z (i.1, 1) = z' (i.1, 1)),
    replicatedCircleM i z = replicatedCircleM i z') ∧
  (∀ (M : ℕ) (hM : 0 < M),
    (2 * M : ℝ)⁻¹ ^ 2 * ∑ i : Fin M × Fin 2, ∑ j : Fin M × Fin 2,
      (if dist (lineEmbedding (replicatedNode i)) (lineEmbedding (replicatedNode j)) ≤ 1 then
        (uniformLaw ((Fin M × Fin 2) → Bool)).cov
          (replicatedSpatialScore i) (replicatedSpatialScore j) else 0) =
      1 / (4 * (2 * M)))

/-- The mathematical statement of P008-T6. -/
def T6Statement : Prop :=
  (∀ {N : ℕ} (z : Assignment N) (M : Fin N → ℝ) (D : Fin N → Fin N → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (h₁ : 1 ≤ nTreated z) (h₀ : 1 ≤ nControl z),
    let X := binaryDesign z
    let H := (X.transpose * X)⁻¹
    hajek (fun i _ => M i) z = ∑ i, contrastWeight z i * M i ∧
    (∀ i, (H * X.transpose) 1 i = contrastWeight z i) ∧
    (∀ i, olsResidual z M i = groupResidual z M i) ∧
    (H * olsMeat z M D c * H) 1 1 = hac (regressionScore z M) D c ∧
    (∀ (hdiag : ∀ i, D i i = 0) (hsep : ∀ i j, i ≠ j → c < D i j),
      hac (regressionScore z M) D c = ∑ i, (regressionScore z M i)^2 ∧
      hac (regressionScore z M) D c =
        (∑ i ∈ Finset.univ.filter (fun i => z i = true), (groupResidual z M i)^2) / (nTreated z)^2 +
        (∑ i ∈ Finset.univ.filter (fun i => z i = false), (groupResidual z M i)^2) / (nControl z)^2 ∧
      hac (regressionScore z M) D c = hac (regressionScore z M) D 0)) ∧
  (∀ (g : Fin 4 → ℝ),
    (∀ i j : Fin 4, i ≠ j → (2 / 5 : ℝ) < dist (toyNode i) (toyNode j)) ∧
    hac g (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) = ∑ i, (g i) ^ 2 ∧
    hac g (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) =
      hac g (fun i j => dist (toyNode i) (toyNode j)) 0 ∧
    (∀ t critical : ℝ,
      t - critical * Real.sqrt (hac g (fun i j => dist (toyNode i) (toyNode j)) (2 / 5)) =
        t - critical * Real.sqrt (hac g (fun i j => dist (toyNode i) (toyNode j)) 0) ∧
      t + critical * Real.sqrt (hac g (fun i j => dist (toyNode i) (toyNode j)) (2 / 5)) =
        t + critical * Real.sqrt (hac g (fun i j => dist (toyNode i) (toyNode j)) 0))) ∧
  (∀ {N : ℕ} (base : Fin N → ℝ)
    (a : Fin N → Fin N → ℝ) (m₁ m₀ : ℝ) (i j : Fin N) (hne : i ≠ j),
    (uniformLaw (Assignment N)).cov
      (fun z => linearizationScore (fun i z => base i + ∑ k, a i k * bit (z k)) m₁ m₀ i z)
      (fun z => linearizationScore (fun i z => base i + ∑ k, a i k * bit (z k)) m₁ m₀ j z) =
    a i j * a j i) ∧
  (∀ {N : ℕ} (hN : 0 < N) (base : Fin N → ℝ) (a : Fin N → Fin N → ℝ) (m₁ m₀ : ℝ),
    let Q := uniformLaw (Assignment N)
    let φ := fun i z => linearizationScore
      (fun i z => base i + ∑ k, a i k * bit (z k)) m₁ m₀ i z
    Q.var (fun z => (N : ℝ)⁻¹ * ∑ i, φ i z) =
      (N : ℝ)⁻¹^2 * ((∑ i, Q.var (φ i)) +
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), a i j * a j i) ∧
    (∀ (D : Fin N → Fin N → ℝ) (c : ℝ) (hc : 0 ≤ c) (hdiag : ∀ i, D i i = 0)
      (hzero : ∀ i j, c < D i j → a i j * a j i = 0),
      (N : ℝ)⁻¹^2 * (∑ i, ∑ j, Q.cov (φ i) (φ j) * (if D i j ≤ c then 1 else 0)) =
        Q.var (fun z => (N : ℝ)⁻¹ * ∑ i, φ i z))) ∧
  (∀ {N : ℕ} (P : SpatialModel N) (d r c : ℝ) (g : Fin N → Fin N → Plane → ℝ)
    (hfield : MeasurableSet P.field) (hmass : ∀ i, 0 < P.circleMass i d)
    (hfinite : ∀ i, P.circleMeasure i d Set.univ ≠ ⊤)
    (heffect : ∀ i k x, r < dist (P.node k) x → g i k x = 0) (hcut : d + r ≤ c),
    ∀ i k, c < dist (P.node i) (P.node k) → P.average i d (g i k) = 0)

end
end SAP.P008a
