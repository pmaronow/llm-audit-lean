import SAP.P015a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a.WH.W1.P.T8_L4

noncomputable section
open Matrix
open scoped BigOperators

private lemma row_hasFDerivAt {n q : ℕ} (Z : Matrix (Fin n) (Fin q) ℝ)
    (i : Fin n) (θ : Fin q → ℝ) :
    HasFDerivAt (fun t => Z.mulVec t i)
      (scoreDifferential (fun a => Z i a)) θ := by
  change HasFDerivAt (fun t => ∑ a, Z i a * t a)
    (scoreDifferential (fun a => Z i a)) θ
  have h : HasFDerivAt (fun t => scoreDifferential (fun a => Z i a) t)
      (scoreDifferential (fun a => Z i a)) θ :=
    ContinuousLinearMap.hasFDerivAt _
  convert h using 1
  ext t
  simp [scoreDifferential]

private lemma weighted_row_sum {n q : ℕ} (Z : Matrix (Fin n) (Fin q) ℝ)
    (s : Finset (Fin n)) (w : Fin n → ℝ) :
    (∑ j ∈ s, w j • scoreDifferential (fun a => Z j a)) =
      scoreDifferential (fun a => ∑ j ∈ s, w j * Z j a) := by
  ext x
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    scoreDifferential, ContinuousLinearMap.proj_apply]
  calc
    (∑ j ∈ s, w j * ∑ a, Z j a * x a) =
        ∑ j ∈ s, ∑ a, w j * (Z j a * x a) := by
          simp only [Finset.mul_sum]
    _ = ∑ a, ∑ j ∈ s, w j * (Z j a * x a) := by
          rw [Finset.sum_comm]
    _ = ∑ a, (∑ j ∈ s, w j * Z j a) * x a := by
          simp [Finset.sum_mul, mul_assoc]

private lemma smul_score {q : ℕ} (c : ℝ) (g : Fin q → ℝ) :
    c • scoreDifferential g = scoreDifferential (fun a => c * g a) := by
  ext x
  simp [scoreDifferential, Finset.mul_sum, mul_assoc]

private lemma sum_score {q e : ℕ} (g : Fin e → Fin q → ℝ) :
    (∑ k, scoreDifferential (g k)) = scoreDifferential (fun a => ∑ k, g k a) := by
  ext x
  simp only [ContinuousLinearMap.sum_apply, scoreDifferential,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply]
  simp_rw [smul_eq_mul]
  rw [Finset.sum_comm]
  simp [Finset.sum_mul]

private lemma score_sub {q : ℕ} (g h : Fin q → ℝ) :
    scoreDifferential g - scoreDifferential h =
      scoreDifferential (fun a => g a - h a) := by
  ext x
  simp [scoreDifferential, Finset.sum_sub_distrib, sub_mul]

private theorem cox_leaf : SAP.P015a.WH.W1.T8_L4 := by
  intro n q e Z event risk hmem θ
  have hpos : ∀ k, 0 < ∑ j ∈ risk k, Real.exp (Z.mulVec θ j) := by
    intro k
    apply Finset.sum_pos'
    · intro j hj
      exact (Real.exp_pos _).le
    · exact ⟨event k, hmem k, Real.exp_pos _⟩
  refine ⟨hpos, ?_⟩
  have hsum : ∀ k,
      HasFDerivAt (fun t => ∑ j ∈ risk k, Real.exp (Z.mulVec t j))
        (∑ j ∈ risk k, Real.exp (Z.mulVec θ j) •
          scoreDifferential (fun a => Z j a)) θ := by
    intro k
    apply HasFDerivAt.fun_sum
    intro j hj
    have hh := (Real.hasDerivAt_exp (Z.mulVec θ j)).hasFDerivAt.comp θ
      (row_hasFDerivAt Z j θ)
    convert hh using 1 <;> ext x <;> simp [mul_comm]
  have hlog : ∀ k,
      HasFDerivAt (fun t => Real.log (∑ j ∈ risk k, Real.exp (Z.mulVec t j)))
        ((∑ j ∈ risk k, Real.exp (Z.mulVec θ j))⁻¹ •
          (∑ j ∈ risk k, Real.exp (Z.mulVec θ j) •
            scoreDifferential (fun a => Z j a))) θ := by
    intro k
    have hh := (Real.hasDerivAt_log (ne_of_gt (hpos k))).hasFDerivAt.comp θ (hsum k)
    convert hh using 1
    · rfl
    · ext x
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.sum_apply]
      simp_rw [smul_eq_mul]
      ring
  have hrow : ∀ k, HasFDerivAt (fun t => Z.mulVec t (event k))
      (scoreDifferential (fun a => Z (event k) a)) θ := by
    intro k
    exact row_hasFDerivAt Z (event k) θ
  have hterms : ∀ k, HasFDerivAt
      (fun t => Z.mulVec t (event k) - Real.log (∑ j ∈ risk k, Real.exp (Z.mulVec t j)))
      (scoreDifferential (fun a => Z (event k) a -
        (∑ j ∈ risk k, Real.exp (Z.mulVec θ j) * Z j a) /
          (∑ j ∈ risk k, Real.exp (Z.mulVec θ j)))) θ := by
    intro k
    have hweighted := weighted_row_sum Z (risk k)
      (fun j => Real.exp (Z.mulVec θ j))
    have hscaled := smul_score
      ((∑ j ∈ risk k, Real.exp (Z.mulVec θ j))⁻¹)
      (fun a => ∑ j ∈ risk k, Real.exp (Z.mulVec θ j) * Z j a)
    have hlog' : (∑ j ∈ risk k, Real.exp (Z.mulVec θ j))⁻¹ •
        (∑ j ∈ risk k, Real.exp (Z.mulVec θ j) •
          scoreDifferential (fun a => Z j a)) =
        scoreDifferential (fun a =>
          (∑ j ∈ risk k, Real.exp (Z.mulVec θ j) * Z j a) /
            (∑ j ∈ risk k, Real.exp (Z.mulVec θ j))) := by
      rw [hweighted, hscaled]
      congr 1
      funext a
      simp [div_eq_mul_inv, mul_comm]
    have hsub := score_sub (fun a => Z (event k) a)
      (fun a => (∑ j ∈ risk k, Real.exp (Z.mulVec θ j) * Z j a) /
        (∑ j ∈ risk k, Real.exp (Z.mulVec θ j)))
    have hh := (hrow k).sub (hlog k)
    convert hh using 1
    rw [hlog']
    exact hsub.symm
  have hder := HasFDerivAt.fun_sum
    (fun k (_ : k ∈ Finset.univ) => hterms k)
  have hscore := sum_score
    (fun k a => Z (event k) a -
      (∑ j ∈ risk k, Real.exp (Z.mulVec θ j) * Z j a) /
        (∑ j ∈ risk k, Real.exp (Z.mulVec θ j)))
  rw [hscore] at hder
  change HasFDerivAt (fun t => ∑ k,
      (Z.mulVec t (event k) - Real.log (∑ j ∈ risk k, Real.exp (Z.mulVec t j))))
    (scoreDifferential (fun a => ∑ k,
      (Z (event k) a -
        (∑ j ∈ risk k, Real.exp (Z.mulVec θ j) * Z j a) /
          (∑ j ∈ risk k, Real.exp (Z.mulVec θ j))))) θ
  exact hder

end

end SAP.P015a.WH.W1.P.T8_L4

theorem SAP.P015a.WH.W1.T8_L4_proof : SAP.P015a.WH.W1.T8_L4 :=
  SAP.P015a.WH.W1.P.T8_L4.cox_leaf
