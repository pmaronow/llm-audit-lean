import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.RowCol

namespace AronowAudit.P015.SchurCompletion
open Matrix Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

theorem block_ols_coefficient {Q : Type*} [Fintype Q] [DecidableEq Q]
    (A : Matrix Q Q ℝ) (hsym : ∀ i j, A i j=A j i) (hdet : A.det ≠ 0)
    (ω : Q → ℝ) (d : ℝ) (hs : 0 < d-dotProduct ω (A.mulVec ω)) :
    let b := A.mulVec ω
    let s := d-dotProduct ω b
    let B := Matrix.fromBlocks A (Matrix.replicateCol Unit b)
      (Matrix.replicateRow Unit b) (fun (_ _ : Unit) => d)
    B.det ≠ 0 ∧ ∀ (v : Q → ℝ) (t : ℝ),
      B⁻¹.mulVec (Sum.elim v (fun _ => t)) (Sum.inr ()) =
        (t-dotProduct ω v)/s := by
  let b := A.mulVec ω
  let s := d-dotProduct ω b
  let B := Matrix.fromBlocks A (Matrix.replicateCol Unit b)
    (Matrix.replicateRow Unit b) (fun (_ _ : Unit) => d)
  have hAi : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  letI : Invertible A := ((Matrix.isUnit_iff_isUnit_det A).mpr hAi).nonempty_invertible.some
  have hAb : A⁻¹.mulVec b=ω := by
    dsimp [b]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hAi, Matrix.one_mulVec]
  have hBd : B.det=A.det*s := by
    dsimp [B]
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    congr 1
    rw [Matrix.det_unique]
    simp only [Matrix.sub_apply]
    rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec, hAb,
      Matrix.replicateRow_mul_replicateCol_apply, dotProduct_comm b ω]
  have hBdet : B.det ≠ 0 := by rw [hBd];exact mul_ne_zero hdet hs.ne'
  refine ⟨hBdet, ?_⟩
  intro v t
  let u := B⁻¹.mulVec (Sum.elim v (fun _ => t))
  have hBu : B.mulVec u=Sum.elim v (fun _ => t) := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hBdet),
      Matrix.one_mulVec]
  have hleft : A.mulVec (u ∘ Sum.inl) + (u (Sum.inr ())) • b = v := by
    ext i
    have hh := congrFun hBu (Sum.inl i)
    simpa [B,Matrix.fromBlocks_mulVec,Matrix.mulVec,dotProduct,Function.comp_def,
      Matrix.replicateCol,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using hh
  have hright : dotProduct b (u ∘ Sum.inl)+d*u (Sum.inr ())=t := by
    have hh := congrFun hBu (Sum.inr ())
    simpa [B,Matrix.fromBlocks_mulVec,Matrix.mulVec,dotProduct,Function.comp_def,
      Matrix.replicateRow,Pi.add_apply] using hh
  have hsymm : A.IsSymm := Matrix.IsSymm.ext (fun i j => (hsym i j).symm)
  have hm := congrArg (dotProduct ω) hleft
  rw [dotProduct_add, dotProduct_smul] at hm
  have hc : dotProduct ω (A.mulVec (u ∘ Sum.inl)) = dotProduct b (u ∘ Sum.inl) := by
    rw [hsymm.dotProduct_mulVec_comm, dotProduct_comm]
  rw [hc] at hm
  change dotProduct b (u ∘ Sum.inl) + u (Sum.inr ()) * dotProduct ω b =
    dotProduct ω v at hm
  change u (Sum.inr ())=(t-dotProduct ω v)/s
  apply (eq_div_iff hs.ne').2
  change u (Sum.inr ()) * (d-dotProduct ω b)=t-dotProduct ω v
  nlinarith

end
end AronowAudit.P015.SchurCompletion
