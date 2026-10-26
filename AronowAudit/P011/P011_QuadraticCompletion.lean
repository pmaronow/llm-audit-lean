import AronowAudit.P011.P011_ProbabilityCompletion

namespace AronowAudit.P011.QuadraticCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

def ones (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1
def total {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, M i j

lemma trace_ones_left {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (ones n*M) = total M := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, ones, one_mul, total]
  rw [Finset.sum_comm]

lemma ones_sandwich {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ones n*M*ones n = total M • ones n := by
  ext i j
  simp only [Matrix.mul_apply,ones,one_mul,mul_one,Matrix.smul_apply,smul_eq_mul,total]
  rw [Finset.sum_comm]

lemma total_prod_swap {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j=M j i) (hC : ∀ i j, C i j=C j i) :
    total (C*M) = total (M*C) := by
  unfold total
  simp only [Matrix.mul_apply]
  calc
    (∑ i, ∑ j, ∑ k, C i k*M k j) = ∑ i, ∑ j, ∑ k, M j k*C k i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [hM k j,hC i k,mul_comm]
    _ = _ := Finset.sum_comm

lemma trace_prod_symm {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, C i j=C j i) :
    Matrix.trace (M*C) = ∑ i, ∑ j, M i j*C i j := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hC j i]

lemma trace_centering {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j=M j i) (hC : ∀ i j, C i j=C j i) :
    Matrix.trace (centeringMatrix n*M*centeringMatrix n*C) =
      Matrix.trace (M*C)-2/(n:ℝ)*total (M*C)+total M*(total C/(n:ℝ)^2) := by
  let a : ℝ := 1/(n:ℝ)
  have hP : centeringMatrix n=1-a • ones n := rfl
  have hex : centeringMatrix n*M*centeringMatrix n*C =
      M*C-a • (ones n*M*C)-a • (M*ones n*C)+(a*a) • (ones n*M*ones n*C) := by
    rw [hP]
    simp only [sub_mul,mul_sub,one_mul,mul_one,Matrix.smul_mul,Matrix.mul_smul,
      smul_smul]
    abel
  rw [hex,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_sub]
  simp only [Matrix.trace_smul,smul_eq_mul]
  have h1 : Matrix.trace (ones n*M*C)=total (M*C) := by
    rw [Matrix.mul_assoc,trace_ones_left]
  have h2 : Matrix.trace (M*ones n*C)=total (M*C) := by
    calc
      _ = Matrix.trace (C*M*ones n) := Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace (ones n*(C*M)) := Matrix.trace_mul_comm _ _
      _ = total (C*M) := trace_ones_left _
      _ = _ := total_prod_swap M C hM hC
  have h3 : Matrix.trace (ones n*M*ones n*C)=total M*total C := by
    rw [ones_sandwich,Matrix.smul_mul,Matrix.trace_smul,trace_ones_left]
    rfl
  rw [h1,h2,h3]
  dsimp [a]
  ring

lemma covariance_symm {n : ℕ} (m : Model n) (i j : Fin n) :
    covariance m i j=covariance m j i := by
  unfold covariance
  apply integral_congr_ae
  exact Eventually.of_forall fun y => mul_comm _ _

lemma covariance_eq_mathlib {n : ℕ} (m : Model n) (i j : Fin n) :
    covariance m i j=ProbabilityTheory.covariance (fun y => weighted m y i)
      (fun y => weighted m y j) m.law := rfl

lemma beta_variance {n : ℕ} (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) :
    var m (betaHat m)=total (covariance m)/(n:ℝ)^2 := by
  let : IsProbabilityMeasure m.law := m.probability
  have hb := ProbabilityCompletion.betaHat_memLp m hL2
  unfold var expectation
  rw [← ProbabilityTheory.variance_eq_integral hb.aemeasurable]
  change ProbabilityTheory.variance (fun y => (∑ i, weighted m y i)/(n:ℝ)) m.law = _
  simp only [div_eq_mul_inv]
  rw [ProbabilityTheory.variance_mul_const,ProbabilityTheory.variance_fun_sum hL2]
  simp only [← covariance_eq_mathlib,inv_pow,total]

lemma beta_cross_covariance {n : ℕ} (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) (i : Fin n) :
    cov[fun y => weighted m y i,betaHat m; m.law] =
      (∑ j, covariance m i j)/(n:ℝ) := by
  let : IsProbabilityMeasure m.law := m.probability
  unfold betaHat average
  rw [ProbabilityTheory.covariance_fun_div_right,
    ProbabilityTheory.covariance_fun_sum_right hL2 (hL2 i)]
  simp only [covariance_eq_mathlib]


lemma residual_pair_mean {n : ℕ} (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) (i j : Fin n) :
    expectation m (fun y => centered (weighted m y) i*centered (weighted m y) j) =
      covariance m i j+delta m i*delta m j-
      (∑ k, covariance m i k)/(n:ℝ)-(∑ k, covariance m j k)/(n:ℝ)+var m (betaHat m) := by
  let : IsProbabilityMeasure m.law := m.probability
  have hB := ProbabilityCompletion.betaHat_memLp m hL2
  have hr (i : Fin n) : MemLp (fun y => weighted m y i-betaHat m y) 2 m.law :=
    (memLp_congr_ae (Eventually.of_forall fun y => rfl)).mp ((hL2 i).sub hB)
  have hm (i : Fin n) : expectation m (fun y => weighted m y i-betaHat m y)=delta m i := by
    unfold expectation
    rw [integral_sub ((hL2 i).integrable (by norm_num)) (hB.integrable (by norm_num))]
    rfl
  have hs := ProbabilityTheory.covariance_fun_sub_fun_sub (hL2 i) hB (hL2 j) hB
  have hself : cov[betaHat m,betaHat m; m.law] = var m (betaHat m) := by
    rw [ProbabilityTheory.covariance_self hB.aemeasurable,ProbabilityTheory.variance_eq_integral hB.aemeasurable]
    rfl
  have hcj : cov[betaHat m,fun y => weighted m y j; m.law] =
      (∑ k, covariance m j k)/(n:ℝ) := by
    rw [ProbabilityTheory.covariance_comm,beta_cross_covariance m hL2 j]
  have hp := ProbabilityTheory.covariance_eq_sub (hr i) (hr j)
  change cov[fun y => weighted m y i-betaHat m y,fun y => weighted m y j-betaHat m y; m.law] =
    expectation m (fun y => (weighted m y i-betaHat m y)*(weighted m y j-betaHat m y))-
    expectation m (fun y => weighted m y i-betaHat m y)*
    expectation m (fun y => weighted m y j-betaHat m y) at hp
  rw [hs,←covariance_eq_mathlib,beta_cross_covariance m hL2 i,hcj,hself,hm,hm] at hp
  change expectation m (fun y => (weighted m y i-betaHat m y)*(weighted m y j-betaHat m y)) = _
  linarith

lemma row_total_right {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, M i j*(∑ k, C j k)) = total (M*C) := by
  simp only [Finset.mul_sum,total,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

lemma row_total_left {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j=M j i) :
    (∑ i, ∑ j, M i j*(∑ k, C i k)) = total (M*C) := by
  calc
    _ = ∑ i, ∑ j, M j i*(∑ k, C i k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hM i j]
    _ = ∑ j, ∑ i, M j i*(∑ k, C i k) := Finset.sum_comm
    _ = _ := row_total_right M C

lemma sum_residual_moment {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j=M j i) (hC : ∀ i j, C i j=C j i) (d : Fin n → ℝ) (v : ℝ) :
    (∑ i, ∑ j, M i j*(C i j+d i*d j-(∑ k,C i k)/(n:ℝ)-
      (∑ k,C j k)/(n:ℝ)+v)) =
      Matrix.trace (M*C)+quadratic M d-2/(n:ℝ)*total (M*C)+quadratic M (fun _ => 1)*v := by
  have hpoint (i j : Fin n) : M i j*(C i j+d i*d j-(∑ k,C i k)/(n:ℝ)-
      (∑ k,C j k)/(n:ℝ)+v) = M i j*C i j+M i j*d i*d j-
      (M i j*(∑ k,C i k))/(n:ℝ)-(M i j*(∑ k,C j k))/(n:ℝ)+M i j*v := by ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hl : (∑ i, ∑ j, (M i j*(∑ k,C i k))/(n:ℝ))=total (M*C)/(n:ℝ) := by
    simpa only [Finset.sum_div] using congrArg (fun x : ℝ => x/(n:ℝ)) (row_total_left M C hM)
  have hr : (∑ i, ∑ j, (M i j*(∑ k,C j k))/(n:ℝ))=total (M*C)/(n:ℝ) := by
    simpa only [Finset.sum_div] using congrArg (fun x : ℝ => x/(n:ℝ)) (row_total_right M C)
  have hv : (∑ i, ∑ j, M i j*v)=total M*v := by
    simp only [←Finset.sum_mul,total]
  have hones : quadratic M (fun _ => 1)=total M := by simp [quadratic,total]
  rw [hl,hr,hv,←trace_prod_symm M C hC,hones]
  change Matrix.trace (M*C)+quadratic M d-total (M*C)/(n:ℝ)-total (M*C)/(n:ℝ)+total M*v = _
  ring

lemma expectation_quadratic_centered {n : ℕ} (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j=M j i) :
    expectation m (fun y => quadratic M (centered (weighted m y))) =
      Matrix.trace (M*covariance m)+quadratic M (delta m)-
      2/(n:ℝ)*total (M*covariance m)+quadratic M (fun _ => 1)*var m (betaHat m) := by
  let : IsProbabilityMeasure m.law := m.probability
  have hB := ProbabilityCompletion.betaHat_memLp m hL2
  have hr (i : Fin n) : MemLp (fun y => centered (weighted m y) i) 2 m.law :=
    (memLp_congr_ae (Eventually.of_forall fun y => rfl)).mp ((hL2 i).sub hB)
  have hInt (i j : Fin n) : Integrable
      (fun y => M i j*centered (weighted m y) i*centered (weighted m y) j) m.law := by
    exact ((hr i).integrable_mul (hr j) |>.const_mul (M i j)).congr
      (Eventually.of_forall fun y => by dsimp only [Pi.mul_apply]; ring)
  have hOuter (i : Fin n) : Integrable
      (fun y => ∑ j, M i j*centered (weighted m y) i*centered (weighted m y) j) m.law :=
    integrable_finsetSum Finset.univ (fun j _ => hInt i j)
  calc
    _ = ∑ i, ∑ j, ∫ y, M i j*centered (weighted m y) i*centered (weighted m y) j ∂m.law := by
      unfold expectation quadratic
      rw [integral_finsetSum Finset.univ (fun i _ => hOuter i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hInt i j)]
    _ = ∑ i, ∑ j, M i j*expectation m
        (fun y => centered (weighted m y) i*centered (weighted m y) j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∫ y, M i j*(centered (weighted m y) i*centered (weighted m y) j) ∂m.law :=
          integral_congr_ae (Eventually.of_forall fun y => by ring)
        _ = _ := integral_const_mul _ _
    _ = _ := by
      simp_rw [residual_pair_mean m hL2]
      exact sum_residual_moment M (covariance m) hM (covariance_symm m) (delta m) _

lemma quadratic_expectation_completed {n : ℕ} (_hn : 0 < n) (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j = M j i) :
    expectation m (fun y => quadratic M (centered (weighted m y))) =
      Matrix.trace (centeringMatrix n * M * centeringMatrix n * covariance m) + quadratic M (delta m) ∧
    expectation m (fun y => quadratic M (centered (weighted m y))) =
      Matrix.trace (M * covariance m) + quadratic M (delta m) -
      2/(n : ℝ)*(∑ i, ∑ j, (M * covariance m) i j) +
      quadratic M (fun _ => 1)*var m (betaHat m) := by
  have he := expectation_quadratic_centered m hL2 M hM
  refine ⟨?_,he⟩
  rw [he,trace_centering M (covariance m) hM (covariance_symm m), beta_variance m hL2]
  have hones : quadratic M (fun _ => 1)=total M := by simp [quadratic,total]
  rw [hones]
  ring

end
end AronowAudit.P011.QuadraticCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal
theorem quadratic_expectation {n : ℕ} (hn : 0 < n) (m : Model n)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j = M j i) :
    expectation m (fun y => quadratic M (centered (weighted m y))) =
      Matrix.trace (centeringMatrix n * M * centeringMatrix n * covariance m) + quadratic M (delta m) ∧
    expectation m (fun y => quadratic M (centered (weighted m y))) =
      Matrix.trace (M * covariance m) + quadratic M (delta m) -
      2/(n : ℝ)*(∑ i, ∑ j, (M * covariance m) i j) +
      quadratic M (fun _ => 1)*var m (betaHat m) := by
  exact QuadraticCompletion.quadratic_expectation_completed hn m hL2 M hM
end AronowAudit.P011

