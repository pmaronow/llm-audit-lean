import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Direct finite order-statistic continuity. Maximizing the new values over
the old weak lower set gives the perturbation bound, including all ties. -/
theorem n2_proof : N2 := by
  intro M g α hM hα hg
  let a : Fin M → ℝ → ℝ := fun s β => Real.sqrt (g s β)
  let c : ℝ := (1 - α) * (M : ℝ)
  let V : ℝ → Finset ℝ := fun β => Finset.univ.image (fun s => a s β)
  let C : ℝ → Finset ℝ := fun β => (V β).filter fun q =>
    c ≤ ((Finset.univ.filter (fun s : Fin M => a s β ≤ q)).card : ℝ)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hc0 : 0 < c := mul_pos (sub_pos.mpr hα.2) hMr
  have hcM : c ≤ (M : ℝ) := by
    dsimp [c]
    nlinarith [mul_nonneg hα.1.le hMr.le]
  let m₀ : Fin M := ⟨0, hM⟩
  have haV (s : Fin M) (β : ℝ) : a s β ∈ V β :=
    Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
  have hC (β : ℝ) : (C β).Nonempty := by
    have hV : (V β).Nonempty := ⟨a m₀ β, haV m₀ β⟩
    have hmax (s : Fin M) : a s β ≤ (V β).max' hV :=
      Finset.le_max' (V β) (a s β) (haV s β)
    have hfilter :
        Finset.univ.filter (fun s : Fin M => a s β ≤ (V β).max' hV) =
          Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro s _
      exact hmax s
    refine ⟨(V β).max' hV,
      Finset.mem_filter.mpr ⟨Finset.max'_mem (V β) hV, ?_⟩⟩
    rw [hfilter]
    simpa only [Finset.card_univ, Fintype.card_fin] using hcM
  have hcrit (β : ℝ) : mcCritical g α β = (C β).min' (hC β) := by
    change (if h : (C β).Nonempty then (C β).min' h else 0) =
      (C β).min' (hC β)
    rw [dif_pos (hC β)]
  have hqual (β : ℝ) :
      c ≤ ((Finset.univ.filter
        (fun s : Fin M => a s β ≤ mcCritical g α β)).card : ℝ) := by
    rw [hcrit β]
    exact (Finset.mem_filter.mp (Finset.min'_mem (C β) (hC β))).2
  -- A one-sided uniform perturbation gives a one-sided strict quantile bound.
  have hupper (x y ε : ℝ) (hxy : ∀ s, a s x < a s y + ε) :
      mcCritical g α x < mcCritical g α y + ε := by
    let S : Finset (Fin M) :=
      Finset.univ.filter fun s => a s y ≤ mcCritical g α y
    have hS : S.Nonempty := by
      have hcard : 0 < S.card := by
        have hcardR : (0 : ℝ) < S.card := lt_of_lt_of_le hc0 (hqual y)
        exact_mod_cast hcardR
      exact Finset.card_pos.mp hcard
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S (fun s => a s x) hS
    have hsub : S ⊆ Finset.univ.filter (fun s : Fin M => a s x ≤ a j x) := by
      intro s hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmax s hs⟩
    have hcardle : (S.card : ℝ) ≤
        ((Finset.univ.filter (fun s : Fin M => a s x ≤ a j x)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hjC : a j x ∈ C x := by
      apply Finset.mem_filter.mpr
      exact ⟨haV j x, (hqual y).trans hcardle⟩
    have hminle : mcCritical g α x ≤ a j x := by
      rw [hcrit x]
      exact Finset.min'_le (C x) (a j x) hjC
    have hjy : a j y ≤ mcCritical g α y := (Finset.mem_filter.mp hj).2
    linarith [hxy j]
  have haContinuous (s : Fin M) : Continuous (a s) :=
    Real.continuous_sqrt.comp (hg s)
  -- Finitely many coordinate neighborhoods have a common neighborhood.
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hall : ∀ᶠ y in 𝓝 x, ∀ s : Fin M, dist (a s y) (a s x) < ε := by
    apply Filter.eventually_all.mpr
    intro s
    exact Metric.continuousAt_iff'.mp (haContinuous s).continuousAt ε hε
  filter_upwards [hall] with y hy
  have habs (s : Fin M) : |a s y - a s x| < ε := by
    simpa only [Real.dist_eq] using hy s
  have hforward : ∀ s, a s y < a s x + ε := by
    intro s
    rcases abs_sub_lt_iff.mp (habs s) with ⟨h₁, h₂⟩
    linarith
  have hbackward : ∀ s, a s x < a s y + ε := by
    intro s
    rcases abs_sub_lt_iff.mp (habs s) with ⟨h₁, h₂⟩
    linarith
  have h₁ := hupper y x ε hforward
  have h₂ := hupper x y ε hbackward
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

end
end AronowAudit.P002.Wave1.AlgorithmSupport
