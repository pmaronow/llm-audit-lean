import AronowAudit.P002.Wave1.E61EigenvalueBlueprint

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

universe u

/-- Transfer the finite tails through the marginal laws and intersect the entrywise a.e. limits. -/
theorem n10_proof : N10.{u} := by
  intro htail hsum hbc Ω _ μ _ sizes hsizes k P Z δ e A B r hA hr hP hZ sub hsub
  apply MeasureTheory.ae_all_iff.mpr
  intro a
  apply MeasureTheory.ae_all_iff.mpr
  intro s
  apply MeasureTheory.ae_all_iff.mpr
  intro t
  let D : ℕ → Ω → ℝ := fun j ω =>
    gram (P (sub j)).x (if a then Z (sub j) ω else (Z (sub j) ω)ᶜ) s t -
      gram (P (sub j)).x Finset.univ s t
  let bound : ℝ → ℕ → ℝ := fun τ j =>
    2 * ((sizes (sub j) : ℝ) + 1) *
      Real.exp (-2 * r ^ 2 * sizes (sub j) * τ ^ 2 / max 1 A)
  have hC : 0 < max (1 : ℝ) A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hsummable : ∀ τ : ℝ, 0 < τ → Summable (bound τ) := by
    intro τ hτ
    have hc : 0 < 2 * r ^ 2 * τ ^ 2 / max 1 A := by positivity
    refine (hsum sizes sub hsizes hsub (2 * r ^ 2 * τ ^ 2 / max 1 A) hc).congr ?_
    intro j
    dsimp only [bound]
    congr 1
    congr 1
    ring
  have hμ : ∀ τ : ℝ, 0 < τ → ∀ j,
      μ {ω | τ ≤ |D j ω|} ≤ ENNReal.ofReal (bound τ j) := by
    intro τ hτ j
    have hmarginal := (hZ (sub j) (fun S =>
      τ ≤ |gram (P (sub j)).x (if a then S else Sᶜ) s t -
        gram (P (sub j)).x Finset.univ s t|)).2
    calc
      μ {ω | τ ≤ |D j ω|} = ENNReal.ofReal
          (probability (P (sub j)).pop (fun S =>
            τ ≤ |gram (P (sub j)).x (if a then S else Sᶜ) s t -
              gram (P (sub j)).x Finset.univ s t|)) := hmarginal
      _ ≤ ENNReal.ofReal (bound τ j) :=
        ENNReal.ofReal_le_ofReal
          (htail (sizes (sub j)) k (P (sub j)) δ e A B r hA hr (hP (sub j)) a s t τ hτ)
  exact hbc μ D bound hsummable hμ

end
end AronowAudit.P002.Wave1.E61Eigenvalue
