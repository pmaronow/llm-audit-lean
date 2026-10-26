import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The largest attained square root qualifies, so the minimum qualifying value
is itself attained. No sign assumption is needed until interpreting the curves. -/
theorem n1_proof : N1 := by
  intro M g α β hM hα _hn
  let a : Fin M → ℝ := fun s => Real.sqrt (g s β)
  let c : ℝ := (1 - α) * (M : ℝ)
  let V : Finset ℝ := Finset.univ.image a
  let C : Finset ℝ := V.filter fun q =>
    c ≤ ((Finset.univ.filter (fun s : Fin M => a s ≤ q)).card : ℝ)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hcM : c ≤ (M : ℝ) := by
    dsimp [c]
    nlinarith [mul_nonneg hα.1.le hMr.le]
  let m₀ : Fin M := ⟨0, hM⟩
  have haV (s : Fin M) : a s ∈ V :=
    Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
  have hV : V.Nonempty := ⟨a m₀, haV m₀⟩
  have hmax (s : Fin M) : a s ≤ V.max' hV :=
    Finset.le_max' V (a s) (haV s)
  have hfilter :
      Finset.univ.filter (fun s : Fin M => a s ≤ V.max' hV) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro s _
    exact hmax s
  have hC : C.Nonempty := by
    refine ⟨V.max' hV, Finset.mem_filter.mpr ⟨Finset.max'_mem V hV, ?_⟩⟩
    rw [hfilter]
    simpa only [Finset.card_univ, Fintype.card_fin] using hcM
  have hcrit : mcCritical g α β = C.min' hC := by
    change (if h : C.Nonempty then C.min' h else 0) = C.min' hC
    rw [dif_pos hC]
  have hminV : C.min' hC ∈ V :=
    (Finset.mem_filter.mp (Finset.min'_mem C hC)).1
  obtain ⟨m, _hm, ham⟩ := Finset.mem_image.mp hminV
  have hm : m ∈ mcIndices g α β := by
    simp only [mcIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    change a m = mcCritical g α β
    exact ham.trans hcrit.symm
  refine ⟨⟨m, hm⟩, ?_⟩
  rw [hcrit, ← ham]
  exact Real.sqrt_nonneg (g m β)

end
end AronowAudit.P002.Wave1.AlgorithmSupport
