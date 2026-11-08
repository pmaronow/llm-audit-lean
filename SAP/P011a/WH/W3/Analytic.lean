import SAP.P011a.Defs.WholeW3
import SAP.P011a.Bridge
import AronowAudit.P011.P011_DenseVarianceCompletion
import AronowAudit.P011.P011_TraceCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W3

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- Forget the extra observed-nesting conjunct of the old package. -/
theorem wholeScaling_of_scaling (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) : WholeScaling_W3 F c1 c2 c3 c4 := h.2

/-- The original dense variance estimate is a finite-row theorem. Its constant
does not depend on any relation between different observed graphs. -/
theorem uniform_variance (F : Family) (c1 c2 c3 c4 K : ℝ)
    (h : WholeScaling_W3 F c1 c2 c3 c4)
    (M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ)
    (hM : ∀ k i j, M k i j = M k j i) (hK : ∀ k, operatorNorm (M k) ≤ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k,
      var (F.model k) (fun y => quadratic (M k) (centered (weighted (F.model k) y)))
        ≤ B * (F.size k : ℝ) := by
  rcases h with ⟨hc1, hc2, _, _, hDep, hBound, hDeg, _, _⟩
  let C := 2*(144*(1+c2)^3+2*(1+c2)^2)*(2*c1)^4+8*(1+c2)*c1^4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨C*K^2, by positivity, ?_⟩
  intro k
  have hv := AronowAudit.P011.DenseSampleCompletion.sample_variance_bound
    (F.positive k) (Bridge.model (F.model k)) c1 (1+c2) hc1.le (by positivity)
    (hDep k) (hBound k) (fun i => by
      change (degree (F.model k).G i : ℝ) + 1 ≤ 1+c2
      linarith [hDeg k i]) (M k) (hM k)
  have hk : (operatorNorm (M k))^2 ≤ K^2 :=
    (sq_le_sq₀ (norm_nonneg _) hK0).mpr (hK k)
  exact hv.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk hC) (Nat.cast_nonneg _))

/-- Chebyshev applied to Q/n, followed by the finite O(1) expectation error.
This is the proof of DenseLimitCompletion.limit_clauses_from_variance with only
the row hypotheses it actually uses. In particular there is no nesting premise. -/
theorem expansion_from_variance (F : Family) (c1 c2 c3 c4 K : ℝ)
    (h : WholeScaling_W3 F c1 c2 c3 c4)
    (M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ)
    (hM : ∀ k i j, M k i j = M k j i) (hK : ∀ k, operatorNorm (M k) ≤ K)
    (hVar : ∃ B : ℝ, 0 ≤ B ∧ ∀ k,
      var (F.model k) (fun y => quadratic (M k) (centered (weighted (F.model k) y)))
        ≤ B * (F.size k : ℝ)) :
    InProbability F
      (fun k y => (F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y) - scaledTrue F k)
      (fun k => (Matrix.trace ((M k - oracleMatrix (F.model k).G)*covariance (F.model k)) +
        quadratic (M k) (delta (F.model k))) / (F.size k : ℝ)) := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  rcases h with ⟨hc1, hc2, _, _, hDep, hBound, hDeg, _, _⟩
  let Q := fun k y => quadratic (M k) (centered (weighted (F.model k) y))
  let a := fun k => (Matrix.trace (M k*covariance (F.model k)) +
    quadratic (M k) (delta (F.model k))) / (F.size k : ℝ)
  have hn (k : ℕ) : 0 < (F.size k : ℝ) := by exact_mod_cast F.positive k
  have hN : Tendsto (fun k => (F.size k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.grows
  have hQ (k : ℕ) : MemLp (Q k) 2 (F.model k).law :=
    AronowAudit.P011.DenseLimitCompletion.quadratic_centered_memLp
      (Bridge.model (F.model k)) c1 (hBound k) (M k)
  have hL2 (k : ℕ) : ∀ i, MemLp (fun y => weighted (F.model k) y i) 2 (F.model k).law :=
    AronowAudit.P011.ProbabilityCompletion.weighted_memLp (Bridge.model (F.model k)) c1 (hBound k)
  have hQn (k : ℕ) : MemLp (fun y => Q k y/(F.size k : ℝ)) 2 (F.model k).law := by
    simpa only [div_eq_mul_inv] using (hQ k).mul_const ((F.size k : ℝ)⁻¹)
  have hQV : Tendsto
      (fun k => ProbabilityTheory.variance (fun y => Q k y/(F.size k : ℝ)) (F.model k).law)
      atTop (𝓝 0) := by
    obtain ⟨B, hB, hv⟩ := hVar
    apply squeeze_zero (fun k => ProbabilityTheory.variance_nonneg _ _) (fun k => ?_)
      (hN.const_div_atTop B)
    have he : var (F.model k) (Q k) = ProbabilityTheory.variance (Q k) (F.model k).law :=
      (ProbabilityTheory.variance_eq_integral (hQ k).aemeasurable).symm
    have hv' : ProbabilityTheory.variance (Q k) (F.model k).law ≤ B*(F.size k : ℝ) := by
      rw [← he]; exact hv k
    have hid : (fun y => Q k y/(F.size k : ℝ)) = fun y => (F.size k : ℝ)⁻¹*Q k y := by
      funext y; ring
    rw [hid, ProbabilityTheory.variance_const_mul]
    calc
      _ ≤ ((F.size k : ℝ)⁻¹)^2*(B*(F.size k : ℝ)) :=
        mul_le_mul_of_nonneg_left hv' (sq_nonneg _)
      _ = _ := by field_simp
  have hmean := AronowAudit.P011.OracleCompletion.rowCP_of_variance
    (fun k => (F.model k).law) (fun k y => Q k y/(F.size k : ℝ)) hQn hQV
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  let C := 3*K*(1+c2)*c1^2
  have hE : Tendsto (fun k => expectation (F.model k) (Q k)/(F.size k : ℝ) - a k)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall fun k => ?_) (hN.const_div_atTop C)
    have hb := AronowAudit.P011.DenseCompletion.finite_expectation_error
      (F.positive k) (Bridge.model (F.model k)) c1 (1+c2) hc1.le (by linarith)
      (hDep k) (hBound k) (fun i => by
        change (degree (F.model k).G i : ℝ) + 1 ≤ 1+c2
        linarith [hDeg k i]) (M k) (hM k)
    have hb' : |expectation (F.model k) (Q k) -
        (Matrix.trace (M k*covariance (F.model k)) + quadratic (M k) (delta (F.model k)))| ≤ C :=
      hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hK k) (by norm_num : 0 ≤ (3 : ℝ)))
        (by linarith : 0 ≤ 1+c2)) (sq_nonneg c1))
    rw [Real.norm_eq_abs]
    dsimp only [a]
    rw [← sub_div, abs_div, abs_of_pos (hn k)]
    exact div_le_div_of_nonneg_right hb' (hn k).le
  have hErr : AronowAudit.P011.CoverageCompletion.RowCP (fun k => (F.model k).law)
      (fun k _ => expectation (F.model k) (Q k)/(F.size k : ℝ) - a k) 0 :=
    AronowAudit.P011.CoverageCompletion.rowCP_det _ _ _ hE
  have hQA : ∀ ε > 0, Tendsto
      (fun k => (F.model k).law.real {y | |Q k y/(F.size k : ℝ) - a k| > ε}) atTop (𝓝 0) := by
    suffices hh : ∀ ε > 0, Tendsto
        (fun k => (F.model k).law.real {y | |Q k y/(F.size k : ℝ) - a k - 0| > ε}) atTop (𝓝 0) by
      simpa only [sub_zero] using hh
    apply AronowAudit.P011.OracleCompletion.row_moving_add_error (fun k => (F.model k).law)
      (fun k y => Q k y/(F.size k : ℝ) - expectation (F.model k) (Q k)/(F.size k : ℝ))
      (fun k y => Q k y/(F.size k : ℝ) - a k) (fun _ => 0) ?_ ?_
    · simpa only [expectation, integral_div, sub_zero] using hmean
    · convert hErr using 1
      ext k y
      ring
  let b := fun k => (Matrix.trace ((M k - oracleMatrix (F.model k).G)*covariance (F.model k)) +
    quadratic (M k) (delta (F.model k))) / (F.size k : ℝ)
  have hid (k : ℕ) (y : Fin (F.size k) → ℝ) :
      (F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y) - scaledTrue F k - b k =
        Q k y/(F.size k : ℝ) - a k := by
    have hv : var (F.model k) (betaHat (F.model k)) =
        (∑ i, ∑ j, covariance (F.model k) i j) / (F.size k : ℝ)^2 :=
      AronowAudit.P011.QuadraticCompletion.beta_variance (Bridge.model (F.model k)) (hL2 k)
    have ht : Matrix.trace (oracleMatrix (F.model k).G * covariance (F.model k)) =
        ∑ i, ∑ j, covariance (F.model k) i j :=
      AronowAudit.P011.OracleCompletion.oracle_trace (Bridge.model (F.model k)) (hDep k) (hL2 k)
    dsimp [b, Q, a, varianceForm, scaledTrue]
    rw [hv, Matrix.sub_mul, Matrix.trace_sub, ht]
    field_simp; ring
  change InProbability F
    (fun k y => (F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y) - scaledTrue F k) b
  simpa only [InProbability, probability, hid] using hQA

/-- A nonnegative deterministic F1 centering turns the two-sided expansion
into the required one-sided conservative probability bound. -/
theorem conservative_of_expansion (F : Family)
    (M : ∀ k, Matrix (Fin (F.size k)) (Fin (F.size k)) ℝ)
    (hCP : InProbability F
      (fun k y => (F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y) - scaledTrue F k)
      (fun k => (Matrix.trace ((M k - oracleMatrix (F.model k).G)*covariance (F.model k)) +
        quadratic (M k) (delta (F.model k))) / (F.size k : ℝ)))
    (hp : ∀ k, 0 ≤ quadratic (M k) (delta (F.model k)) ∧
      0 ≤ Matrix.trace ((M k - oracleMatrix (F.model k).G)*covariance (F.model k))) :
    Conservative F (fun k y => varianceForm (M k) (weighted (F.model k) y)) := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  intro ε hε
  apply squeeze_zero (fun k => measureReal_nonneg) (fun k => ?_) (hCP ε hε)
  apply measureReal_mono (μ := (F.model k).law) ?_ (measure_ne_top _ _)
  intro y hy
  change ε < (F.size k : ℝ)*(var (F.model k) (betaHat (F.model k)) -
    varianceForm (M k) (weighted (F.model k) y)) at hy
  change ε < |(F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y) - scaledTrue F k -
    (Matrix.trace ((M k - oracleMatrix (F.model k).G)*covariance (F.model k)) +
      quadratic (M k) (delta (F.model k))) / (F.size k : ℝ)|
  have hb : 0 ≤ (Matrix.trace ((M k - oracleMatrix (F.model k).G)*covariance (F.model k)) +
      quadratic (M k) (delta (F.model k))) / (F.size k : ℝ) :=
    div_nonneg (add_nonneg (hp k).2 (hp k).1) (Nat.cast_nonneg _)
  have ha := neg_le_abs ((F.size k : ℝ)*varianceForm (M k) (weighted (F.model k) y) -
    scaledTrue F k - (Matrix.trace ((M k - oracleMatrix (F.model k).G)*covariance (F.model k)) +
      quadratic (M k) (delta (F.model k))) / (F.size k : ℝ))
  dsimp [scaledTrue] at ha ⊢
  nlinarith

end
end SAP.P011a.WH.W3
