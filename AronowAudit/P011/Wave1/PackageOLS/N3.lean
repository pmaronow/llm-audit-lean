import AronowAudit.P011.Wave1.PackageOLSBlueprint

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PackageOLS

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne AronowAudit.P011.Wave1.CorollaryOne
  MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Matrix

noncomputable section

/-- The inverse Gram matrix makes every n-scaled intercept weight equal to one. -/
theorem n3_proof : N3 := by
  intro hGram k i
  let n : ℝ := 3 * ((k : ℝ) + 1)
  let s : ℝ := 24 * ((k : ℝ) + 1)
  let B : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![n⁻¹, s⁻¹]
  have hn0 : n ≠ 0 := by dsimp [n]; positivity
  have hs0 : s ≠ 0 := by dsimp [s]; positivity
  have hG : (olsDesign k)ᵀ * olsDesign k = Matrix.diagonal ![n, s] := hGram k
  have hleft : B * ((olsDesign k)ᵀ * olsDesign k) = 1 := by
    rw [hG]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
        Matrix.one_apply, hn0, hs0]
  have hinv : ((olsDesign k)ᵀ * olsDesign k)⁻¹ = B :=
    Matrix.inv_eq_left_inv hleft
  have hn : (PF.size k : ℝ) = n := by
    change ((3 * (k + 1) : ℕ) : ℝ) = 3 * ((k : ℝ) + 1)
    norm_num
  change (1 : ℝ) = olsTheta (olsDesign k) (0 : Fin 2) i
  unfold olsTheta
  rw [hinv]
  simp [B, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
    Matrix.transpose_apply, olsDesign, hn, hn0]

end

end AronowAudit.P011.Wave1.PackageOLS
