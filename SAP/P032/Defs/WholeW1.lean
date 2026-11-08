import Mathlib
import SAP.P032.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032

open scoped BigOperators

universe u v

/-- P032-T9; code/1_reanalysis_stata.do lines 1373–1385; dcr.ado lines 125–238;
p. 191 (PDF p. 6), decomposition display.
For at least two imputations, common coefficient estimates, fixed nonzero component
factors and symmetric completed-data matrices, with no active PSD adjustment, the
pooled-first total is the weighted within-imputation mean plus c times Rubin's full
between-imputation term Q = (1 + 1/M)B. Combining within each imputation and then
pooling gives the same within mean plus Q, so the gap is (c - 1)Q and adding
(1 - c)Q repairs it. The DCR weights sum to one and, when all factors are one,
decomposition commutes with Rubin pooling. For the asylike factors,
c - 1 = -sum_i 1/G_i + 1/G_D + (K - 2)/n; at K = 4, G_i = 13, G_D = 6, n = 24
it is -3/52 and is nonzero. The standalone scalar identity also holds for zero
denominators under Lean's total division. -/
def T9WholeStatement : Prop :=
  (∀ (P : Type u) (J : Type v) [Fintype P] [Fintype J]
    (m : ℕ), 2 ≤ m → ∀ s a : J → ℝ, (∀ j, a j ≠ 0) →
    ∀ U : J → Fin m → Matrix P P ℝ, (∀ j t, (U j t).transpose = U j t) →
    ∀ b : Fin m → P → ℝ,
      poolBeforeCombining s a U b =
        (∑ j, s j • componentAverage U j) + (∑ j, s j * a j) • rubinContribution b ∧
      combineBeforePooling s U b =
        (∑ j, s j • componentAverage U j) + rubinContribution b ∧
      poolBeforeCombining s a U b - combineBeforePooling s U b =
        ((∑ j, s j * a j) - 1) • rubinContribution b ∧
      poolBeforeCombining s a U b + (1 - (∑ j, s j * a j)) • rubinContribution b =
        combineBeforePooling s U b) ∧
  (∀ k : ℕ, ∑ j, decompositionWeight k j = 1) ∧
  (∀ (P : Type u) [Fintype P] (k m : ℕ), 2 ≤ m →
    ∀ U : (Fin k ⊕ Fin 2) → Fin m → Matrix P P ℝ,
      (∀ j t, (U j t).transpose = U j t) → ∀ b : Fin m → P → ℝ,
      poolBeforeCombining (decompositionWeight k) (fun _ => 1) U b =
        combineBeforePooling (decompositionWeight k) U b) ∧
  (∀ (k : ℕ) (Gi : Fin k → ℝ) (GD n : ℝ),
    (∑ j, decompositionWeight k j * undoFactors k Gi GD n j) - 1 =
      -(∑ i, 1 / Gi i) + 1 / GD + ((k : ℝ) - 2) / n) ∧
  ((∑ j, decompositionWeight 4 j * undoFactors 4 (fun _ => 13) 6 24 j) - 1 =
    (-3 / 52 : ℝ)) ∧
  ((∑ j, decompositionWeight 4 j * undoFactors 4 (fun _ => 13) 6 24 j) - 1 ≠ 0)

end SAP.P032
