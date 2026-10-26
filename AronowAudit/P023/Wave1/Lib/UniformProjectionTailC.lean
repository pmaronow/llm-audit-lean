import AronowAudit.P023.Wave1.Lib.ProjectionCoreTailC
import AronowAudit.P023.Wave1.Lib.LegendreMomentsTailC

namespace AronowAudit.P023.Wave1
noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter Polynomial AronowAudit.Literature
local instance tc04_uniform_projection_decidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The coefficient on the (2m+1)-th Rodrigues polynomial. -/
def tc04_odd_coefficient (m : ℕ) : ℝ :=
  (-1:ℝ)^m * (4*(m:ℝ)+3) * centralBinomial m / (4*(m:ℝ)+4)

/-- The finite candidate for the exact uniform projection. -/
def tc04_uniform_candidate (J : ℕ) : Polynomial ℝ :=
  C (1/2) + ∑ m ∈ Finset.range ((J+1)/2),
    C (tc04_odd_coefficient m) * legendreRodrigues (2*m+1)

theorem tc04_uniform_candidate_degree (J : ℕ) :
    (tc04_uniform_candidate J).natDegree ≤ J := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro m hm
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    rw [tc04_legendre_degree]
    have hm' := Finset.mem_range.mp hm
    omega

/-- Inner product of the candidate with every Legendre basis polynomial. -/
theorem tc04_uniform_candidate_inner (J k : ℕ) :
    expectation uniformMargins (fun x => (tc04_uniform_candidate J).eval x *
      (legendreRodrigues k).eval x) =
      (1/2:ℝ) * (if 0=k then 1/(2*(k:ℝ)+1) else 0) +
      ∑ m ∈ range ((J+1)/2), tc04_odd_coefficient m *
        (if 2*m+1=k then 1/(2*(k:ℝ)+1) else 0) := by
  have he : (fun x => (tc04_uniform_candidate J).eval x*(legendreRodrigues k).eval x) =
      (fun x => (1/2:ℝ)*((legendreRodrigues 0).eval x*(legendreRodrigues k).eval x) +
        ∑ m ∈ range ((J+1)/2), tc04_odd_coefficient m *
          ((legendreRodrigues (2*m+1)).eval x*(legendreRodrigues k).eval x)) := by
    funext x
    simp [tc04_uniform_candidate, Polynomial.eval_finsetSum, add_mul, Finset.sum_mul, mul_assoc]
  unfold expectation
  rw [he, integral_add]
  · rw [integral_const_mul, integral_finsetSum]
    · simp_rw [integral_const_mul]
      change (1/2:ℝ)*expectation uniformMargins _ +
        ∑ m ∈ range ((J+1)/2), tc04_odd_coefficient m * expectation uniformMargins _ = _
      simp_rw [tc04_legendre_inner]
    · intro m _
      exact (tc04_poly_mul_integrable _ _).const_mul _
  · exact (tc04_poly_mul_integrable _ _).const_mul _
  · apply integrable_finsetSum
    intro m _
    exact (tc04_poly_mul_integrable _ _).const_mul _

/-- The candidate satisfies all the actual monomial normal equations. -/
theorem tc04_uniform_candidate_spec (J : ℕ) :
    IsProjection uniformMargins J (tc04_uniform_candidate J) := by
  refine ⟨tc04_uniform_candidate_degree J, ?_⟩
  have htest : ∀ k ≤ J, expectation uniformMargins
      (fun x => (party x-(tc04_uniform_candidate J).eval x)*(legendreRodrigues k).eval x)=0 := by
    intro k hk
    unfold expectation
    simp_rw [sub_mul]
    rw [integral_sub (by simpa using tc04_residual_mul_integrable 0 (legendreRodrigues k))
      (tc04_poly_mul_integrable _ _)]
    change expectation uniformMargins (fun x => party x*(legendreRodrigues k).eval x) -
      expectation uniformMargins (fun x => (tc04_uniform_candidate J).eval x*
        (legendreRodrigues k).eval x)=0
    rw [tc04_uniform_party_poly, tc04_uniform_candidate_inner]
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨m,hm⟩ := he
      have hk2 : k=2*m := by omega
      clear hm
      subst k
      have hsum : (∑ i ∈ range ((J+1)/2), tc04_odd_coefficient i *
          (if 2*i+1=2*m then 1/(2*((2*m:ℕ):ℝ)+1) else 0))=0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [if_neg (by omega), mul_zero]
      rw [hsum]
      cases m with
      | zero => norm_num
      | succ m =>
        have heq : 2*(m+1)=2*m+2 := by omega
        rw [heq, tc04_legendre_half_even, if_neg (by omega)]
        ring
    · obtain ⟨m,hm⟩ := ho
      have hk2 : k=2*m+1 := by omega
      clear hm
      subst k
      have hmrange : m ∈ range ((J+1)/2) := mem_range.mpr (by omega)
      rw [odd_legendre_half_moment, if_neg (by omega)]
      rw [Finset.sum_eq_single m]
      · split_ifs <;> try omega
        simp only [zero_mul, zero_add, tc04_odd_coefficient, Nat.cast_add, Nat.cast_mul,
          Nat.cast_one, Nat.cast_ofNat]
        field_simp [show 4*(m:ℝ)+3 ≠ 0 by positivity,
          show 4*(m:ℝ)+4 ≠ 0 by positivity, show 2*(m:ℝ)+2 ≠ 0 by positivity]
        <;> ring
      · intro b _ hb
        rw [if_neg (by omega : ¬2*b+1=2*m+1), mul_zero]
      · exact fun hn => (hn hmrange).elim
  intro j hj
  have hs := tc04_legendre_test_span uniformMargins
    (fun x => party x-(tc04_uniform_candidate J).eval x)
    (tc04_residual_mul_integrable _) J htest (X^j) (by simpa using hj)
  simpa only [expectation, Polynomial.eval_pow, Polynomial.eval_X] using hs

/-- The unique chosen polynomial is the finite odd Legendre expansion. -/
theorem tc04_uniform_projection_expansion (J : ℕ) :
    projection uniformMargins J = tc04_uniform_candidate J :=
  tc04_unique J _ _ (tc04_chosen_spec J) (tc04_uniform_candidate_spec J)

theorem tc04_uniform_party_integrable (p : Polynomial ℝ) :
    Integrable (fun x => party x*p.eval x) uniformMargins := by
  simpa using tc04_residual_mul_integrable 0 p

/-- Integral of D times the exact candidate. -/
theorem tc04_uniform_candidate_party (J : ℕ) :
    expectation uniformMargins (fun x => party x*(tc04_uniform_candidate J).eval x) =
      (1/4:ℝ) + ∑ m ∈ range ((J+1)/2),
        (4*(m:ℝ)+3)*centralBinomial m^2/(16*((m:ℝ)+1)^2) := by
  have he : (fun x => party x*(tc04_uniform_candidate J).eval x) =
      (fun x => (1/2:ℝ)*(party x*(legendreRodrigues 0).eval x) +
        ∑ m ∈ range ((J+1)/2), tc04_odd_coefficient m *
          (party x*(legendreRodrigues (2*m+1)).eval x)) := by
    funext x
    simp [tc04_uniform_candidate, Polynomial.eval_finsetSum, mul_add, Finset.mul_sum, mul_assoc, mul_left_comm] <;> ring
  unfold expectation
  rw [he, integral_add]
  · rw [integral_const_mul, integral_finsetSum]
    · simp_rw [integral_const_mul]
      change (1/2:ℝ)*expectation uniformMargins _ + ∑ m ∈ range ((J+1)/2),
        tc04_odd_coefficient m * expectation uniformMargins _ = _
      simp_rw [tc04_uniform_party_poly]
      simp only [tc04_legendre_zero, Polynomial.eval_one, intervalIntegral.integral_const,
        sub_zero, smul_eq_mul, mul_one]
      norm_num only
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      rw [odd_legendre_half_moment]
      have hs : (-1:ℝ)^m * (-1:ℝ)^m=1 := by
        rw [← mul_pow]; norm_num
      dsimp [tc04_odd_coefficient]
      field_simp
      nlinarith [hs]
    · intro m _
      exact (tc04_uniform_party_integrable (legendreRodrigues (2*m+1))).const_mul _
  · exact (tc04_uniform_party_integrable (legendreRodrigues 0)).const_mul _
  · apply integrable_finsetSum
    intro m _
    exact (tc04_uniform_party_integrable (legendreRodrigues (2*m+1))).const_mul _

/-- The exact central-binomial decrement of one projection step. -/
theorem tc04_binomial_drop (m : ℕ) :
    centralBinomial m^2/4-centralBinomial (m+1)^2/4 =
      (4*(m:ℝ)+3)*centralBinomial m^2/(16*((m:ℝ)+1)^2) := by
  have hs := congrArg (fun t : ℝ => t^2) (central_binomial_recurrence m)
  apply (eq_div_iff (show 16*((m:ℝ)+1)^2 ≠ 0 by positivity)).mpr
  nlinarith [hs]

theorem tc04_binomial_telescope (n : ℕ) :
    (1/4:ℝ)-(∑ m ∈ range n, (4*(m:ℝ)+3)*centralBinomial m^2/(16*((m:ℝ)+1)^2)) =
      centralBinomial n^2/4 := by
  induction n with
  | zero => norm_num [centralBinomial]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [tc04_binomial_drop n]

/-- Exact finite-degree projection and residual variance under the uniform law. -/
theorem uniform_projection_variance (J : ℕ) (hJ : 1 ≤ J) :
    let n := (J+1)/2
    let a := fun m : ℕ => (-1:ℝ)^m * (4*(m:ℝ)+3)*centralBinomial m/(4*(m:ℝ)+4)
    IsProjection uniformMargins J (projection uniformMargins J) ∧
    projection uniformMargins J = C (1/2) +
      (∑ m ∈ range n, C (a m)*legendreRodrigues (2*m+1)) ∧
    residualVariance uniformMargins J = centralBinomial n^2/4 ∧
    0 < residualVariance uniformMargins J := by
  have hspec := tc04_chosen_spec J
  have hexp := tc04_uniform_projection_expansion J
  have htest := tc04_test J _ _ hspec hspec.1
  have hres := tc04_residual_mul_integrable (projection uniformMargins J) (projection uniformMargins J)
  have hD : expectation uniformMargins (fun x => party x^2)=(1/2:ℝ) := by
    have he : (fun x => party x^2) = (fun x => party x*(legendreRodrigues 0).eval x) := by
      funext x
      simp [party]
    rw [he, tc04_uniform_party_poly]
    norm_num
  have hDi : Integrable (fun x => party x^2) uniformMargins := by
    convert tc04_piecewise_integrable 1 0 using 1
    funext x
    by_cases hx : 0 ≤ x <;> simp [party,hx]
  have hparty := tc04_uniform_candidate_party J
  unfold expectation at hD htest hparty
  have hv : residualVariance uniformMargins J = centralBinomial ((J+1)/2)^2/4 := by
    have he : (fun x => popResidual uniformMargins J x^2) =
        (fun x => party x^2-party x*(projection uniformMargins J).eval x-
          (party x-(projection uniformMargins J).eval x)*(projection uniformMargins J).eval x) := by
      funext x
      dsimp [popResidual]
      ring
    unfold residualVariance expectation
    rw [he, integral_sub]
    · rw [integral_sub, hD, htest, sub_zero]
      · rw [hexp, hparty]
        linarith [tc04_binomial_telescope ((J+1)/2)]
      · exact hDi
      · simpa using tc04_residual_mul_integrable 0 (projection uniformMargins J)
    · apply Integrable.sub
      · exact hDi
      · simpa using tc04_residual_mul_integrable 0 (projection uniformMargins J)
    · exact hres
  refine ⟨hspec, hexp, hv, ?_⟩
  rw [hv]
  have hn : 1 ≤ (J+1)/2 := by omega
  have hb := central_binomial_lower_bound ((J+1)/2) hn
  have hp : 0 < (1:ℝ)/(4*(((J+1)/2:ℕ):ℝ)) := by positivity
  exact div_pos (lt_of_lt_of_le hp hb) (by norm_num)

end
end AronowAudit.P023.Wave1
