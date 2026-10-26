import AronowAudit.P002.Wave1.E61EigenvalueBlueprint
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Basic

namespace AronowAudit.P002.Wave1.E61Eigenvalue
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- One maximum over both arms yields a common vanishing quadratic-form error. -/
theorem n12_proof : N12 := by
  intro hquadratic k H G c hentry hG
  let ι := Bool × Option (Fin k) × Option (Fin k)
  let entry : ℕ → ι → ℝ := fun j i =>
    |H j i.1 i.2.1 i.2.2 - G j i.2.1 i.2.2|
  have hnonempty : (Finset.univ : Finset ι).Nonempty :=
    ⟨(false, none, none), Finset.mem_univ _⟩
  let D : ℕ → ℝ := fun j => Finset.univ.sup' hnonempty (entry j)
  have hbound : ∀ j a s t, |H j a s t - G j s t| ≤ D j := by
    intro j a s t
    exact Finset.le_sup' (entry j) (Finset.mem_univ (a, s, t))
  have hDnonneg : ∀ j, 0 ≤ D j := by
    intro j
    exact (abs_nonneg _).trans (hbound j false none none)
  have hentries : ∀ i : ι, Tendsto (fun j => entry j i) atTop (nhds 0) := by
    intro i
    simpa only [entry, abs_zero] using (hentry i.1 i.2.1 i.2.2).abs
  -- Bound the finite maximum by the finite sum to prove convergence by squeezing.
  let E : ℕ → ℝ := fun j => ∑ i : ι, entry j i
  have hE : Tendsto E atTop (nhds 0) := by
    simpa only [E, Finset.sum_const_zero] using
      (tendsto_finsetSum (Finset.univ : Finset ι) (fun i _hi => hentries i))
  have hDle : ∀ j, D j ≤ E j := by
    intro j
    apply Finset.sup'_le hnonempty (entry j)
    intro i hi
    exact Finset.single_le_sum (fun p _hp => abs_nonneg _) hi
  have hD : Tendsto D atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hE hDnonneg hDle
  refine ⟨fun j => -(((k : ℝ) + 1) * D j), ?_, ?_⟩
  · simpa only [mul_zero, neg_zero] using (hD.const_mul ((k : ℝ) + 1)).neg
  · intro j a b
    have herror := hquadratic k (H j a) (G j) (D j) (hbound j a) b
    have hlower := (abs_le.mp herror).1
    have hpopulation := hG j b
    nlinarith only [hlower, hpopulation]

end
end AronowAudit.P002.Wave1.E61Eigenvalue
