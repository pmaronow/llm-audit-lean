import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint
import Mathlib.Topology.Order.IntermediateValue

namespace AronowAudit.P002.Wave1.AlgorithmSupport
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Every comparison with the selected curve has constant sign on the open
interval; the strict and weak rank filters therefore stay unchanged. -/
theorem n3_proof : N3 := by
  intro M g α m l u x₀ hM hα hg hn hx₀ hno hm x hx
  -- The segment between two interior points still lies in the open interval.
  have hsegment (a b : ℝ) (ha : a ∈ openInterval l u)
      (hb : b ∈ openInterval l u) : Set.uIcc a b ⊆ openInterval l u := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with ⟨hat, htb⟩ | ⟨hbt, hta⟩
    · exact ⟨lt_of_lt_of_le ha.1 (EReal.coe_le_coe_iff.mpr hat),
        lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr htb) hb.2⟩
    · exact ⟨lt_of_lt_of_le hb.1 (EReal.coe_le_coe_iff.mpr hbt),
        lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hta) ha.2⟩
  have htransport (s : Fin M) (hs : g s ≠ g m) (a b : ℝ)
      (ha : a ∈ openInterval l u) (hb : b ∈ openInterval l u)
      (hsa : g s a < g m a) : g s b < g m b := by
    by_contra hsb
    have hsb' : g m b ≤ g s b := le_of_not_gt hsb
    have hdiff : Continuous (fun t : ℝ => g s t - g m t) := (hg s).sub (hg m)
    have hzero : (0 : ℝ) ∈ Set.uIcc (g s a - g m a) (g s b - g m b) := by
      exact Set.mem_uIcc_of_le (by linarith) (by linarith)
    obtain ⟨t, ht, heq⟩ :=
      intermediate_value_uIcc (a := a) (b := b) hdiff.continuousOn hzero
    have htI : t ∈ openInterval l u := hsegment a b ha hb ht
    apply hno s hs t htI
    linarith
  have hcomparisons (s : Fin M) :
      (g s x ≤ g m x ↔ g s x₀ ≤ g m x₀) ∧
      (g s x < g m x ↔ g s x₀ < g m x₀) := by
    by_cases hs : g s = g m
    · simp [hs]
    · have hstrict : g s x < g m x ↔ g s x₀ < g m x₀ :=
        ⟨htransport s hs x x₀ hx hx₀, htransport s hs x₀ x hx₀ hx⟩
      refine ⟨?_, hstrict⟩
      constructor
      · intro hle
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact (hstrict.mp hlt).le
        · exact (hno s hs x hx heq).elim
      · intro hle
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact (hstrict.mpr hlt).le
        · exact (hno s hs x₀ hx₀ heq).elim
  have hweakFilter :
      Finset.univ.filter (fun s : Fin M => g s x ≤ g m x) =
        Finset.univ.filter (fun s : Fin M => g s x₀ ≤ g m x₀) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hcomparisons s).1
  have hstrictFilter :
      Finset.univ.filter (fun s : Fin M => g s x < g m x) =
        Finset.univ.filter (fun s : Fin M => g s x₀ < g m x₀) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hcomparisons s).2
  have hrank₀ := (quantile_index_rank g hM α x₀ hα (fun s => hn s x₀) m).mp hm
  apply (quantile_index_rank g hM α x hα (fun s => hn s x) m).mpr
  rw [hweakFilter, hstrictFilter]
  exact hrank₀

end
end AronowAudit.P002.Wave1.AlgorithmSupport
