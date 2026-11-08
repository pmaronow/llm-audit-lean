import SAP.P009c.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009c
open Filter
open scoped Topology

/-- A finite real limsup, expressed by eventual upper and frequent lower bounds. -/
def HasLimsup (a : ℕ → ℝ) (L : ℝ) : Prop :=
  (∀ ε > 0, ∀ᶠ t in atTop, a t < L + ε) ∧
  (∀ ε > 0, ∃ᶠ t in atTop, L - ε < a t)

/-- The HT component of Proposition 1, preserving designs, sizes and the positive limsup. -/
def T40Statement : Prop :=
  ∀ (S : Study) (k : ℝ), 0 < k →
    (∀ t i, k⁻¹ ≤ marginal (S.experiment t) i true ∧
      marginal (S.experiment t) i true ≤ 1 - k⁻¹) →
    ¬ Restricted S →
    ∃ y : (t : ℕ) → Fin (S.N t) → Assignment (S.N t) → ℝ,
      let S' : Study := {S with experiment := fun t => {S.experiment t with outcome := y t}}
      (∃ K q s, RegularSequence S' K q s) ∧
      (∃ L > 0,
        HasLimsup (fun t => dAvg (S.experiment t) / size S t) L ∧
        HasLimsup (fun t => dAvg (S'.experiment t) / size S' t) L) ∧
      ¬ InProbability S' (fun t z => ht (S'.experiment t) z - eate (S'.experiment t))

end SAP.P009c
