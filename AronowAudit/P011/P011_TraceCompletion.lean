import AronowAudit.P011.P011_QuadraticCompletion
namespace AronowAudit.P011.DenseTraceCompletion
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem trace_covariance_integral {n : ℕ} (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (M*covariance m) = ∫y, quadratic M
      (fun i=>weighted m y i-expectation m (fun z=>weighted m z i)) ∂m.law := by
  letI : IsProbabilityMeasure m.law:=m.probability
  let Z:=fun (i : Fin n) y=>weighted m y i-expectation m (fun z=>weighted m z i)
  have hZ (i : Fin n) : MemLp (Z i) 2 m.law:=(hL2 i).sub (memLp_const _)
  have hp (i j : Fin n) : Integrable (fun y=>M i j*Z i y*Z j y) m.law:=by
    simpa only [Pi.mul_apply,mul_assoc] using ((hZ i).integrable_mul (hZ j)).const_mul (M i j)
  rw [QuadraticCompletion.trace_prod_symm M (covariance m) (QuadraticCompletion.covariance_symm m)]
  change (∑i,∑j,M i j*(∫y,Z i y*Z j y ∂m.law)) = _
  symm
  unfold quadratic
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>hp i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _=>hp i j)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_assoc,integral_const_mul,Z]

theorem trace_psd_covariance {n : ℕ} (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : PSD M) :
    0≤Matrix.trace (M*covariance m) := by
  rw [trace_covariance_integral m hL2 M]
  exact integral_nonneg (fun y=>hM.2 _)

end
end AronowAudit.P011.DenseTraceCompletion
