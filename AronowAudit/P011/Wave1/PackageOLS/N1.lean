import AronowAudit.P011.Wave1.PackageOLSBlueprint
import AronowAudit.P011.P011_BlockOLSCompletion

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PackageOLS

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne AronowAudit.P011.Wave1.CorollaryOne
  MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Matrix

noncomputable section

/-- Sum the centered design column and its square block by block. -/
theorem n1_proof : N1 := by
  intro k
  let z : Fin (PF.size k) → ℝ := fun i =>
    (![2, -4, 2] : Fin 3 → ℝ) (localIndex (by decide) i)
  have hz : (∑ i, z i) = 0 := by
    change (∑ i : Fin (3 * (k + 1)),
      (![2, -4, 2] : Fin 3 → ℝ) (localIndex (by decide) i)) = 0
    rw [BlockOLSCompletion.local_sum (by decide : 0 < 3)]
    norm_num [Fin.sum_univ_succ]
  have hzz : (∑ i, z i * z i) = 24 * ((k : ℝ) + 1) := by
    change (∑ i : Fin (3 * (k + 1)),
      (![2, -4, 2] : Fin 3 → ℝ) (localIndex (by decide) i) *
        (![2, -4, 2] : Fin 3 → ℝ) (localIndex (by decide) i)) = _
    rw [BlockOLSCompletion.local_sum (by decide : 0 < 3)
      (fun r => (![2, -4, 2] : Fin 3 → ℝ) r * (![2, -4, 2] : Fin 3 → ℝ) r)]
    norm_num [Fin.sum_univ_succ] <;> ring
  have hn : (PF.size k : ℝ) = 3 * ((k : ℝ) + 1) := by
    change ((3 * (k + 1) : ℕ) : ℝ) = 3 * ((k : ℝ) + 1)
    norm_num
  have hD : olsDesign k = fun i j => if j = 0 then 1 else z i := rfl
  simp only [hD]
  ext i j
  set_option backward.isDefEq.respectTransparency false in
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, hz, hzz, hn]

end

end AronowAudit.P011.Wave1.PackageOLS
