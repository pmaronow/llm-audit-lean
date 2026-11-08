import SAP.P032.Defs.Part8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- Unconditional spectral clipping, its fixed points and the exact ten-dyad example. -/
def T7Statement (P : Type*) [Fintype P] [DecidableEq P] : Prop :=
  (∀ (Q : Matrix P P ℝ) (eigs : P → ℝ), Q.transpose*Q = 1 → Q*Q.transpose = 1 →
    (clipEigenvalues Q eigs).transpose = clipEigenvalues Q eigs ∧
    (clipEigenvalues Q eigs).PosSemidef ∧
    (∀ c : P → ℝ, quadForm (clipEigenvalues Q eigs) c =
      ∑ j, max (eigs j) 0 * (∑ i, Q i j*c i)^2) ∧
    (∀ c : P → ℝ, 0 ≤ quadForm (clipEigenvalues Q eigs) c) ∧
    (clipEigenvalues Q eigs = Q*Matrix.diagonal eigs*Q.transpose ↔
      (Q*Matrix.diagonal eigs*Q.transpose).PosSemidef)) ∧
  (∀ (V : Matrix P P ℝ) (hV : V.IsHermitian),
    (psdPart V hV).PosSemidef ∧ (psdPart V hV = V ↔ V.PosSemidef) ∧
    ((diagonalGate V hV).PosSemidef ↔ (∃ i, V i i < 0) ∨ V.PosSemidef)) ∧
  (∀ a b d : ℝ, 0 ≤ a → 0 ≤ d →
    ((!![a,b;b,d] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef ↔ b^2 ≤ a*d)) ∧
  (∀ i : Fin 2, 0 < tenCovariance i i) ∧ ¬tenCovariance.PosSemidef ∧
  tenCovariance.trace = 467922/3655808 ∧ tenCovariance.det = -70529/308915776 ∧
  (∃ hV : tenCovariance.IsHermitian,
    ((hV.eigenvalues 0 = tenPositiveRoot ∧ hV.eigenvalues 1 = tenNegativeRoot) ∨
      (hV.eigenvalues 1 = tenPositiveRoot ∧ hV.eigenvalues 0 = tenNegativeRoot)) ∧
    tenNegativeRoot < 0 ∧ 0 < tenPositiveRoot ∧
    (∃ q : Fin 2 → ℝ, q ⬝ᵥ q = 1 ∧ tenCovariance *ᵥ q = tenPositiveRoot • q ∧
      psdPart tenCovariance hV = tenPositiveRoot • Matrix.vecMulVec q q) ∧
    (psdPart tenCovariance hV).rank = 1 ∧
    (psdPart tenCovariance hV).PosSemidef ∧ psdPart tenCovariance hV ≠ tenCovariance)

/-- Fixed-factor Rubin gap and repair; count denominators are nonzero. -/
def T9Statement (P J : Type*) [Fintype P] [DecidableEq P] [Fintype J] : Prop :=
  (∀ (m : ℕ), 2 ≤ m → ∀ s a : J → ℝ, (∀ j, a j ≠ 0) →
    ∀ U : J → Fin m → Matrix P P ℝ, (∀ j t, (U j t).transpose = U j t) →
    ∀ b : Fin m → P → ℝ,
      poolBeforeCombining s a U b =
        (∑ j, s j • componentAverage U j)+(∑ j, s j*a j) • rubinContribution b ∧
      combineBeforePooling s U b = (∑ j, s j • componentAverage U j)+rubinContribution b ∧
      poolBeforeCombining s a U b-combineBeforePooling s U b =
        ((∑ j, s j*a j)-1) • rubinContribution b ∧
      poolBeforeCombining s a U b+(1-(∑ j, s j*a j)) • rubinContribution b =
        combineBeforePooling s U b) ∧
  (∀ k : ℕ, ∑ j, decompositionWeight k j = 1) ∧
  (∀ (k m : ℕ), 2 ≤ m →
    ∀ U : (Fin k ⊕ Fin 2) → Fin m → Matrix P P ℝ,
      (∀ j t, (U j t).transpose = U j t) → ∀ b : Fin m → P → ℝ,
      poolBeforeCombining (decompositionWeight k) (fun _ => 1) U b =
        combineBeforePooling (decompositionWeight k) U b) ∧
  (∀ (k : ℕ) (Gi : Fin k → ℝ) (GD n : ℝ),
    (∀ i, Gi i ≠ 0) → GD ≠ 0 → n ≠ 0 →
    (∑ j, decompositionWeight k j*undoFactors k Gi GD n j)-1 =
      -(∑ i, 1/Gi i)+1/GD+((k : ℝ)-2)/n) ∧
  (4*(12/13 : ℝ)-5/6-2*(23/24))-1 = -3/52

end
end SAP.P032
