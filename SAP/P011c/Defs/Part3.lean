import Mathlib
import SAP.P011c.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011c

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-- OLS linear representation and unbiasedness, together with the general variance identity. -/
def T29Statement : Prop :=
  (∀ (n p : ℕ), 0 < n → ∀ (m : Model n)
      (D : Matrix (Fin n) (Fin p) ℝ) (b : Fin p → ℝ),
    (Dᵀ*D).det ≠ 0 → MeanModel m D b →
      (∀ j y, ols D y j = (∑ i, olsTheta D j i*y i)/(n : ℝ)) ∧
      (∀ j, expectation m (fun y => ols D y j) = b j)) ∧
  (∀ (n : ℕ), 0 < n → ∀ (m : Model n),
    (∀ i, MemLp (fun y => y i) 2 m.law) →
      var m (betaHat m) = (∑ i, ∑ j, m.theta i*m.theta j*
        covOf m (fun y => y i) (fun y => y j))/(n : ℝ)^2)

/-- Negation of the universal printed oracle-consistency assertion. -/
def T31Statement : Prop :=
  ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
    InProbability F (scaledOracle F) (scaledTrue F)

/-- Negation of the combined printed Corollary 1 contract, including its specialization. -/
def T32Statement : Prop :=
  ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 → Valid F →
    ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
      Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) ∧
        ((∀ k, Homoskedastic (F.model k)) →
          Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)))

/-- Negative estimates count as undefined, uncovered printed intervals. -/
def T33Statement : Prop :=
  ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 → Valid F →
    ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
      PrintedConservativeCoverage F
        (fun k y => V1 (A k y) (weighted (F.model k) y))

/-- Only the explicit degree-factor bounds from the printed proof. -/
def T34Statement : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
    ∀ k, 1 ≤ gFactor (F.model k) ∧ gFactor (F.model k) ≤ 1+c2

/-- Negation of the package's combined variance and coverage guarantee for OLS. -/
def T35Statement : Prop :=
  ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 → Valid F →
    ∀ (p : ℕ) (j : Fin p) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ)
      (b : Fin p → ℝ),
      (∀ k, ((D k)ᵀ * D k).det ≠ 0) → (∀ k, MeanModel (F.model k) (D k) b) →
      (∀ k i, (F.model k).theta i = olsTheta (D k) j i) →
      ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
        (∀ k y, Maximizes (F.model k).R (F.model k).d
          (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
        Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) ∧
          PrintedConservativeCoverage F
            (fun k y => V1 (A k y) (weighted (F.model k) y))

/-- The displayed conservativeness conclusion of Proposition 2. -/
def T36Statement : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
    (∀ k, Homoskedastic (F.model k)) →
    Conservative F (fun k y => V2 (F.model k).G (weighted (F.model k) y))

/-- Both conclusions of Corollary 2, with no bound on supplied degree caps. -/
def T37Statement : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
    (∀ k, Homoskedastic (F.model k)) → Valid F →
    ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
      (∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => V2 B (weighted (F.model k) y)) (A k y)) →
      Conservative F (fun k y => V2 (A k y) (weighted (F.model k) y)) ∧
      Conservative F (fun k y => V2prime (F.model k).d (weighted (F.model k) y))

end
end SAP.P011c
