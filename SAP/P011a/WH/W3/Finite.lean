import SAP.P011a.Defs.WholeW3
import SAP.P011a.Bridge
import AronowAudit.P011.P011_CorrectedAsymptoticCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W3

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000

/-- Split a covariance trace into its diagonal and the two orientations of each
true edge, using the existing off-edge covariance and ordered-pair identities. -/
theorem trace_support : WholeTraceSupport := by
  intro n G C hC N hN
  rcases hC with ⟨m, rfl, hdep, hL2, rfl⟩
  have hsym (i j : Fin n) : covariance m i j = covariance m j i :=
    AronowAudit.P011.QuadraticCompletion.covariance_symm (Bridge.model m) i j
  let f := fun i j => adjacency m.G i j * N i j * covariance m i j
  have hfdiag (i : Fin n) : f i i = 0 := by
    simp [f, adjacency, m.G.property.2]
  have hfsym (i j : Fin n) : f j i = f i j := by
    dsimp [f, adjacency]
    rw [m.G.property.1 j i, hN j i, hsym j i]
  have he (i j : Fin n) : N i j * covariance m i j =
      (if i = j then N i i * covariance m i i else 0) + f i j := by
    by_cases hij : i = j
    · subst j; simp [hfdiag]
    · by_cases hG : m.G.val i j = true
      · simp [hij, f, adjacency, hG]
      · have hg : m.G.val i j = false := by cases h : m.G.val i j <;> simp_all
        have hz : covariance m i j = 0 :=
          AronowAudit.P011.OracleCompletion.covariance_support (Bridge.model m) hdep hL2 i j hij hg
        simp [hij, f, hz]
  have ht : Matrix.trace (N * covariance m) = ∑ i, ∑ j, N i j * covariance m i j :=
    AronowAudit.P011.QuadraticCompletion.trace_prod_symm N (covariance m) hsym
  rw [ht]
  calc
    _ = ∑ i, ∑ j, ((if i = j then N i i * covariance m i i else 0) + f i j) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => he i j
    _ = (∑ i, N i i * covariance m i i) + ∑ i, ∑ j, f i j := by
      simp [Finset.sum_add_distrib]
    _ = (∑ i, N i i * covariance m i i) + upperSum (fun i j => f i j + f j i) := by
      rw [AronowAudit.P011.ordered_pair_sum f hfdiag]
      rfl
    _ = _ := by simp only [hfsym, upperSum, Finset.sum_add_distrib, two_mul]; rfl

/-- The diagonal correction identity, finite maximizer existence, and the Schur
row-norm estimate supplement the already proved finite T5 package. -/
theorem corrected_finite_supplements : WholeCorrectedFinite := by
  classical
  intro n hn R G d hv
  refine ⟨?_, ?_, ?_⟩
  · unfold correctedMatrix
    abel
  · intro x
    refine ⟨?_, ?_, ?_, fun A hm => hm.2 G hv⟩
    · have hI : (1 : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal (fun _ => 1) := by
        ext i j
        simp [Matrix.one_apply, Matrix.diagonal_apply]
      change AronowAudit.P011.VYoung d x =
        AronowAudit.P011.varianceForm (1 + Matrix.diagonal (fun i => (truncatedDegree d i : ℝ))) x
      unfold AronowAudit.P011.VYoung AronowAudit.P011.varianceForm
      rw [AronowAudit.P011.quadratic_add, hI, AronowAudit.P011.quadratic_diagonal,
        AronowAudit.P011.quadratic_diagonal]
      simp only [one_mul, add_mul, Finset.sum_add_distrib]
      rfl
    · unfold VYoung
      apply div_nonneg _ (sq_nonneg _)
      exact Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (sq_nonneg _)
    · let S : Finset (Graph n) := Finset.univ.filter (Compatible R d)
      have hS : S.Nonempty := ⟨G, by simp [S, hv]⟩
      obtain ⟨A, hA, hmax⟩ := S.exists_max_image (fun B => V1plus d B x) hS
      refine ⟨A, ?_, ?_⟩
      · simpa [S] using hA
      · intro B hB
        exact hmax B (by simp [S, hB])
  · intro c2 hc2 hd
    exact AronowAudit.P011.SchurSupport.operatorNorm_le_abs_row_sum _
      (Bridge.CorrectedMatrix_proved hn R G d hv (fun _ => 0)).1.1
      (1+2*c2) (by positivity)
      (AronowAudit.P011.CorrectedAsymptoticCompletion.corrected_row_bound R G d hv c2 hd)

end
end SAP.P011a.WH.W3
