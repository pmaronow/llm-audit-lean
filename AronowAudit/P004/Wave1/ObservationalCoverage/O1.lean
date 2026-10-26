import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

/-- Every source affecting an entry is that entry's own coordinate.  This includes
the diagonal which is part of the definition of `interferes`. -/
private theorem activeTable_source {N : ℕ} (i j : Fin N)
    (h : interferes (activeTable N) i j) : i = j := by
  rcases h with hij | ⟨z, z', heq, hne⟩
  · exact hij
  · by_contra hij
    apply hne
    unfold activeTable
    rw [heq i hij]

/-- Only the self-separation identity is needed here, rather than the full N1 formula. -/
private theorem activePopulation_separation_self {N : ℕ} (i : Fin N) :
    nodeSeparation (activePopulation N) i i = 0 := by
  let P := activePopulation N
  have hz : (0 : ℝ) ∈ {r : ℝ | ∃ x ∈ P.node i, ∃ y ∈ P.node i, dist x y = r} := by
    obtain ⟨x, hx⟩ := P.node_nonempty i
    exact ⟨x, hx, x, hx, dist_self x⟩
  have hn : ∀ r ∈ {r : ℝ | ∃ x ∈ P.node i, ∃ y ∈ P.node i, dist x y = r},
      0 ≤ r := by
    rintro r ⟨x, hx, y, hy, hr⟩
    rw [← hr]
    exact dist_nonneg
  change sInf {r : ℝ | ∃ x ∈ P.node i, ∃ y ∈ P.node i, dist x y = r} = 0
  exact le_antisymm (csInf_le ⟨0, hn⟩ hz) (le_csInf ⟨0, hz⟩ hn)

theorem o1_proof : O1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro N i z
    unfold activeTable
    split_ifs <;> cases hzi : z i <;> norm_num [bit, hzi]
  · intro N j k z b hdist
    have hjk : j ≠ k := by
      intro hjk
      subst k
      simpa only [sub_self, abs_zero, mul_zero, lt_self_iff_false] using hdist
    simp only [activeTable, Function.update_of_ne hjk]
  · intro N i j hdist hshared
    obtain ⟨l, hil, hjl⟩ := hshared
    have hij : i = j := (activeTable_source i l hil).trans (activeTable_source j l hjl).symm
    subst j
    rw [activePopulation_separation_self] at hdist
    exact (lt_irrefl (0 : ℝ)) hdist

end
end AronowAudit.P004.Wave1.ObservationalCoverage
