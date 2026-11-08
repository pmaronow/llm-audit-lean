import SAP.P037c.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

/-- A basis of the column space, viewed as the columns of a matrix. -/
theorem SAP.P037c.WH.W1.T34_L2_proof : SAP.P037c.WH.W1.T34_L2 := by
  classical
  intro n p H
  let S : Submodule ℝ (Fin n → ℝ) := wholeColumnSpace H
  let q : ℕ := Module.finrank ℝ S
  let b : Module.Basis (Fin q) ℝ S := Module.finBasis ℝ S
  let B : Matrix (Fin n) (Fin q) ℝ :=
    fun i j => ((b j : S) : Fin n → ℝ) i
  have hcol (j : Fin q) : B.col j = ((b j : S) : Fin n → ℝ) := by
    ext i
    rfl
  have hli : LinearIndependent ℝ B.col := by
    have hb := b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
    have hcols : B.col = S.subtype ∘ b := by
      funext j
      exact hcol j
    rw [hcols]
    exact hb
  have hspan : Submodule.span ℝ (Set.range B.col) = S := by
    rw [show B.col = S.subtype ∘ b from by
      funext j
      exact hcol j]
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq,
      Submodule.map_top, S.range_subtype]
  refine ⟨q, B, ?_, ?_⟩
  · exact Matrix.mulVec_injective_iff.mpr hli
  · change LinearMap.range B.mulVecLin = LinearMap.range H.mulVecLin
    rw [Matrix.range_mulVecLin B, hspan]
    change wholeColumnSpace H = LinearMap.range H.mulVecLin
    rfl
