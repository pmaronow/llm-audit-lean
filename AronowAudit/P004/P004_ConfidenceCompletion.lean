import AronowAudit.P004.P004_Spatial
import AronowAudit.P004.P004_RegressionCompletion

open scoped BigOperators
open Filter
noncomputable section
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AronowAudit.P004.ConfidenceFollowup02

/-- The exact unweighted aggregation claim is contradicted by the
finite positive-area binary-outcome construction. -/
theorem printed_area_sum_refuted :
    ¬ (∀ {N m : ℕ} (p : Fin N → ℝ) (R : Fin m → CircleTable N)
      (a : Fin N → Fin m → ℝ), 0 < N → 0 < m →
      (∀ i k, 0 < a i k) → (∀ i, 0 < p i ∧ p i < 1) →
      (∑ k, ame p (R k)) = (∑ i, finiteAverage (a i) (fun k => nodeEffect p (R k) i))/N) := by
  intro h
  have hh := h (fun _ : Fin 2 => (1/2 : ℝ)) areaWitnessTable
    (fun (_ : Fin 2) (k : Fin 6) => 2*(k : ℝ)+1)
    (by omega) (by omega) (by intro i k; positivity) (by intro i; norm_num)
  have hcomm :
      (∑ i : Fin 2, finiteAverage (fun k : Fin 6 => 2*(k : ℝ)+1)
        (fun k => nodeEffect (fun _ => 1/2) (areaWitnessTable k) i))/2 =
      ∑ k : Fin 6, (2*(k : ℝ)+1)/36 * ame (fun _ => 1/2) (areaWitnessTable k) := by
    norm_num [finiteAverage,ame,Fin.sum_univ_succ]
    ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [hcomm] at hh
  have hsum := finite_area_sum_certificate.2.2.2.1
  have hweighted := finite_area_sum_certificate.2.2.2.2.1
  rw [hsum,hweighted] at hh
  norm_num at hh

/-- Residual-maker idempotence expresses the adjustment trace as a double sum. -/
theorem adjustmentMu_trace_reduced {N : ℕ} (z : Assignment N)
    (Q : Matrix (Fin N) (Fin N) ℝ)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) :
    adjustmentMu z Q = (armCount z true*armCount z false/N) *
      Matrix.trace (residualMaker z * Matrix.of (fun i j => lambda z i*lambda z j*Q i j)) := by
  have hm := (MatrixCompletion.residual_algebra z h1 h0).2.1
  unfold adjustmentMu adjustmentMatrix
  rw [Matrix.trace_smul]
  change _ * _ = _ * _
  congr 1
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,hm]

/-- Exact finite N=20 PD-adjustment counterexample.
The residual maker and trace are evaluated explicitly. -/
theorem adjusted_pd_finite_counterexample :
    armCount starAssignment20 true = 10 ∧ armCount starAssignment20 false = 10 ∧
    armMean (starBlockTable 4) starAssignment20 true = 0 ∧
    armMean (starBlockTable 4) starAssignment20 false = 0 ∧
    kernelVariance starAssignment20 (residual (starBlockTable 4) starAssignment20) (starBlockKernel 4 false) = 4/25 ∧
    kernelVariance starAssignment20 (residual (starBlockTable 4) starAssignment20) (starBlockKernel 4 true) = 4/25 ∧
    adjustmentMu starAssignment20 (starBlockKernel 4 false) = 41/50 ∧
    adjustmentMu starAssignment20 (starBlockKernel 4 true) = 101/100 ∧
    (16/101 : ℝ) < 8/41 := by
  have hc1 : armCount starAssignment20 true = 10 := by
    norm_num [armCount,starAssignment20,Fin.sum_univ_succ]
    norm_cast
  have hc0 : armCount starAssignment20 false = 10 := by
    norm_num [armCount,starAssignment20,Fin.sum_univ_succ]
    norm_cast
  have hm1 : armMean (starBlockTable 4) starAssignment20 true = 0 := by
    norm_num [armMean,hc1,starBlockTable,starY,starAssignment20,Fin.sum_univ_succ]
  have hm0 : armMean (starBlockTable 4) starAssignment20 false = 0 := by
    norm_num [armMean,hc0,starBlockTable,starY,starAssignment20,Fin.sum_univ_succ]
  have h1 : 0 < armCount starAssignment20 true := by rw [hc1]; norm_num
  have h0 : 0 < armCount starAssignment20 false := by rw [hc0]; norm_num
  have he (i : Fin 20) : residual (starBlockTable 4) starAssignment20 i =
      starY ⟨i.val%5, Nat.mod_lt _ (by omega)⟩ := by
    unfold residual
    cases hz : starAssignment20 i <;> simp [hz,hm1,hm0,starBlockTable]
  have hM (i j : Fin 20) : residualMaker starAssignment20 i j =
      (if i = j then 1 else 0) -
        (if starAssignment20 i = starAssignment20 j then 1/10 else 0) := by
    unfold residualMaker
    rw [MatrixCompletion.gram_inverse_eq starAssignment20 h1 h0]
    simp only [Matrix.sub_apply,Matrix.one_apply,Matrix.mul_apply,Matrix.transpose_apply,
      Fin.sum_univ_two,MatrixCompletion.gramInverse,hc1,hc0,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.head_cons,Matrix.head_fin_const]
    cases hi : starAssignment20 i <;> cases hj : starAssignment20 j
    all_goals norm_num [designMatrix,bit,hi,hj]
  refine ⟨hc1,hc0,hm1,hm0,?_,?_,?_,?_,by norm_num⟩
  · simp only [kernelVariance,he,lambda,hc1,hc0]
    norm_num [starBlockKernel,starKernel,starAssignment20,starY,bit,Fin.sum_univ_succ]
  · simp only [kernelVariance,he,lambda,hc1,hc0]
    norm_num [starBlockKernel,starPD,starKernel,starNegativeVector,starAssignment20,starY,bit,Fin.sum_univ_succ]
  · rw [adjustmentMu_trace_reduced starAssignment20 _ h1 h0]
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.of_apply,hM,lambda,hc1,hc0]
    norm_num [starBlockKernel,starKernel,starAssignment20,bit,Fin.sum_univ_succ]
  · rw [adjustmentMu_trace_reduced starAssignment20 _ h1 h0]
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.of_apply,hM,lambda,hc1,hc0]
    norm_num [starBlockKernel,starPD,starKernel,starNegativeVector,starAssignment20,bit,Fin.sum_univ_succ]

end AronowAudit.P004.ConfidenceFollowup02

namespace AronowAudit.P004

/-- P004-T7 finite witness: every matrix and residual in the N=20 construction
is explicit. Both arm means vanish and both unadjusted variance estimates are
4/25. Their adjustment factors are 41/50 and 101/100, giving adjusted values
8/41 and 16/101, respectively, with 16/101 < 8/41. -/
theorem adjusted_pd_finite_counterexample :
    armCount starAssignment20 true = 10 ∧ armCount starAssignment20 false = 10 ∧
    armMean (starBlockTable 4) starAssignment20 true = 0 ∧
    armMean (starBlockTable 4) starAssignment20 false = 0 ∧
    kernelVariance starAssignment20 (residual (starBlockTable 4) starAssignment20) (starBlockKernel 4 false) = 4/25 ∧
    kernelVariance starAssignment20 (residual (starBlockTable 4) starAssignment20) (starBlockKernel 4 true) = 4/25 ∧
    adjustmentMu starAssignment20 (starBlockKernel 4 false) = 41/50 ∧
    adjustmentMu starAssignment20 (starBlockKernel 4 true) = 101/100 ∧
    (16/101 : ℝ) < 8/41 := ConfidenceFollowup02.adjusted_pd_finite_counterexample

end AronowAudit.P004

