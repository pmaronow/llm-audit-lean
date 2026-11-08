import SAP.P017.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped Classical

noncomputable section

theorem SAP.P017.WH.W1.T3_L1_proof : SAP.P017.WH.W1.T3_L1 := by
  intro Q hQ S hS
  let Z : Set ℝ := {x | x ∈ (S : Set ℝ) ∧ Q.real {x} = 0}
  have hZsub : Z ⊆ (S : Set ℝ) := by
    intro x hx
    exact hx.1
  have hZfinite : Z.Finite := S.finite_toSet.subset hZsub
  have hZzero : Q Z = 0 := by
    rw [measure_null_iff_singleton hZfinite.countable]
    intro x hx
    exact (measureReal_eq_zero_iff).1 hx.2
  have hZae : ∀ᵐ x ∂Q, x ∉ Z := measure_eq_zero_iff_ae_notMem.mp hZzero
  let T : Set ℝ := {x | x ∈ (S : Set ℝ) ∧ 0 < Q.real {x}}
  have hTfinite : T.Finite := S.finite_toSet.subset (by
    intro x hx
    exact hx.1)
  have hTae : ∀ᵐ x ∂Q, x ∈ T := by
    filter_upwards [hS, hZae] with x hxS hxZ
    refine ⟨hxS, ?_⟩
    have hxne : Q.real {x} ≠ 0 := by
      intro hx0
      exact hxZ ⟨hxS, hx0⟩
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hxne)
  have hsub : Q.support ⊆ T :=
    Measure.support_subset_of_isClosed hTfinite.isClosed hTae
  have hfin : Q.support.Finite := hTfinite.subset hsub
  have hnonempty : Q.support.Nonempty := by
    apply Measure.nonempty_support
    intro hzero
    have huniv : Q Set.univ = 0 := by rw [hzero]; simp
    rw [measure_univ] at huniv
    norm_num at huniv
  refine ⟨hfin, hnonempty, ?_⟩
  intro x hx
  exact hsub hx |>.2

