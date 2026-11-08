import SAP.P002b.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002b
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory

/-- The standard-normal (1-alpha/2)-quantile. The interior significance-level
hypothesis in T21 excludes the empty or unbounded-below quantile branches. -/
def standardNormalCritical (α : ℝ) : ℝ :=
  sInf {z : ℝ | ENNReal.ofReal (1-α/2) ≤ ProbabilityTheory.gaussianReal 0 1 (Set.Iic z)}

/-- The adjusted tail supremum over LATE and the adjusted parameter space.
Empty model suprema are zero. The negative-cutoff disjunct preserves the tail
event when conversion to extended nonnegative reals truncates a negative cutoff.
The adjusted statistic retains zero for zero-over-zero, infinity for nonzero-over-zero,
and the fixed least-squares-minimizer convention on singular regression arms. -/
def adjustedTailSupremum (n k : ℕ) (δ e A B r α κ : ℝ) : ℝ≥0∞ :=
  ⨆ β : ℝ, ⨆ P : {P : CovPopulation n k // Xi P δ e A B r ∧ late P.pop = β},
    ENNReal.ofReal (probability P.val.pop (fun S =>
      standardNormalCritical α - κ < 0 ∨
      adjustedAR P.val (observedW P.val.pop β S) S >
        ENNReal.ofReal (standardNormalCritical α - κ)))

/-- The adjusted uniform tail bound with an inner limit superior and an
ordinary outer right-hand limit; ordinary inner-limit existence is not asserted. -/
def T21Statement : Prop :=
  ∀ (k : ℕ) (δ e A B r α : ℝ),
    0 < k → δ < 1 → 0 < e → 0 < A → 0 < B →
    (0 < r ∧ r ≤ 1/2) → (0 < α ∧ α < 1) →
    ∃ u : ℝ≥0∞,
      Tendsto (fun κ : ℝ => Filter.limsup
        (fun n : ℕ => adjustedTailSupremum n k δ e A B r α κ) atTop)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds u) ∧
      u ≤ ENNReal.ofReal α

end
end SAP.P002b
