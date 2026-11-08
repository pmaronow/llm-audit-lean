import SAP.P041.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P041.WH.W2.P.T10_L1

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem memLp_mulVec {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (A : Matrix ι ι ℝ) (X : Ω → ι → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    ∀ i, MemLp (fun ω => (A *ᵥ X ω) i) 2 μ := by
  intro i
  have hsum : MemLp (fun ω => ∑ j : ι, A i j * X ω j) 2 μ := by
    exact memLp_finsetSum Finset.univ (fun j _ => (hX j).const_mul (A i j))
  simpa only [Matrix.mulVec, dotProduct] using hsum

theorem covariance_mulVec {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix ι ι ℝ)
    (X : Ω → ι → ℝ) (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    covarianceMatrixW2 μ (fun ω => A *ᵥ X ω) =
      A * covarianceMatrixW2 μ X * A.transpose := by
  ext i k
  simp only [covarianceMatrixW2, Matrix.mulVec, dotProduct]
  rw [covariance_fun_sum_fun_sum
    (fun j => (hX j).const_mul (A i j))
    (fun l => (hX l).const_mul (A k l))]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  simp only [covarianceMatrixW2]
  ring

end SAP.P041.WH.W2.P.T10_L1

theorem SAP.P041.WH.W2.T10_L1_proof : SAP.P041.WH.W2.T10_L1 := by
  intro Ω ι hΩ hι μ hμ A X hX
  exact ⟨SAP.P041.WH.W2.P.T10_L1.memLp_mulVec μ A X hX,
    SAP.P041.WH.W2.P.T10_L1.covariance_mulVec μ A X hX⟩
