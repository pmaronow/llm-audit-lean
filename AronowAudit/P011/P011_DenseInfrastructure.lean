import AronowAudit.P011.P011_MeanCompletion
import AronowAudit.P011.P011_TraceCompletion

namespace AronowAudit.P011.DenseCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency true

lemma l2_norm {n : ℕ} (x : Fin n→ℝ) : ‖WithLp.toLp 2 x‖=l2 x := by
  simp [EuclideanSpace.norm_eq,l2,Real.norm_eq_abs,sq_abs]

lemma l2_nonneg {n : ℕ} (x : Fin n→ℝ) : 0≤l2 x := Real.sqrt_nonneg _

lemma l2_sq {n : ℕ} (x : Fin n→ℝ) : l2 x^2=∑i,x i^2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _=>sq_nonneg (x i))

lemma mulVec_l2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n→ℝ) :
    l2 (M*ᵥx)≤operatorNorm M*l2 x := by
  have h:=((Matrix.toEuclideanLin M).toContinuousLinearMap).le_opNorm (WithLp.toLp 2 x)
  simpa [operatorNorm,Matrix.toEuclideanLin,Matrix.toLpLin_toLp,l2_norm] using h

lemma bilinear_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n→ℝ) :
    |∑i,∑j,M i j*x i*y j| ≤ operatorNorm M*l2 x*l2 y := by
  have hi : (∑i,∑j,M i j*x i*y j)=
      inner ℝ (WithLp.toLp 2 x) ((Matrix.toEuclideanLin M).toContinuousLinearMap (WithLp.toLp 2 y)) := by
    simp [Matrix.toEuclideanLin,Matrix.toLpLin_toLp,EuclideanSpace.inner_toLp_toLp,
      dotProduct,Matrix.mulVec,Finset.mul_sum,Finset.sum_mul,mul_comm,mul_left_comm,mul_assoc]
  rw [hi,←Real.norm_eq_abs]
  calc
    _ ≤ ‖WithLp.toLp 2 x‖*‖(Matrix.toEuclideanLin M).toContinuousLinearMap (WithLp.toLp 2 y)‖ := norm_inner_le_norm _ _
    _ ≤ ‖WithLp.toLp 2 x‖*(‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖*‖WithLp.toLp 2 y‖) :=
      mul_le_mul_of_nonneg_left (((Matrix.toEuclideanLin M).toContinuousLinearMap).le_opNorm _) (norm_nonneg _)
    _ = _ := by simp only [l2_norm,operatorNorm];ring

lemma l2_abs_bound {n : ℕ} (x : Fin n→ℝ) (B : ℝ) (hB : 0≤B) (hb : ∀i,|x i|≤B) :
    l2 x≤Real.sqrt n*B := by
  apply (sq_le_sq₀ (l2_nonneg x) (mul_nonneg (Real.sqrt_nonneg _) hB)).mp
  rw [l2_sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ∑_i:Fin n,B^2 := Finset.sum_le_sum fun i _=>by nlinarith [sq_nonneg (x i),abs_le.mp (hb i)]
    _ = _ := by simp

lemma centered_sq {n : ℕ} (hn : 0<n) (x : Fin n→ℝ) :
    (∑i,centered x i^2)=(∑i,x i^2)-(n:ℝ)*(average x)^2 := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have he (i:Fin n) : centered x i^2=x i^2-2*average x*x i+(average x)^2 := by unfold centered;ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold average
  field_simp
  <;>ring

lemma centered_l2 {n : ℕ} (hn : 0<n) (x : Fin n→ℝ) : l2 (centered x)≤l2 x := by
  apply (sq_le_sq₀ (l2_nonneg _) (l2_nonneg _)).mp
  rw [l2_sq,l2_sq,centered_sq hn]
  exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))

lemma centering_apply {n : ℕ} (i j:Fin n) :
    centeringMatrix n i j=(if i=j then 1 else 0)-1/(n:ℝ) := by
  erw [centeringMatrix,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply]
  simp only [smul_eq_mul,mul_one]

lemma center_mulVec {n : ℕ} (x : Fin n→ℝ) : centeringMatrix n*ᵥx=centered x := by
  classical
  ext i
  simp only [Matrix.mulVec,dotProduct,centering_apply,sub_mul,Finset.sum_sub_distrib,
    ite_mul,zero_mul,one_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,←Finset.mul_sum]
  simp [centered,average,div_eq_mul_inv,mul_comm]

lemma centering_symm {n : ℕ} (i j:Fin n) : centeringMatrix n i j=centeringMatrix n j i := by
  rw [centering_apply,centering_apply]
  simp [eq_comm]

lemma centering_sandwich_symm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀i j,M i j=M j i) (i j:Fin n) :
    (centeringMatrix n*M*centeringMatrix n) i j=(centeringMatrix n*M*centeringMatrix n) j i := by
  have hp : (centeringMatrix n)ᵀ=centeringMatrix n := by ext i j;exact centering_symm j i
  have hm : Mᵀ=M := by ext i j;exact hM j i
  have he : (centeringMatrix n*M*centeringMatrix n)ᵀ=centeringMatrix n*M*centeringMatrix n := by
    simp [Matrix.transpose_mul,hp,hm,Matrix.mul_assoc]
  exact congr_fun (congr_fun he j) i

lemma centering_sandwich_norm {n : ℕ} (hn : 0<n) (M : Matrix (Fin n) (Fin n) ℝ) :
    operatorNorm (centeringMatrix n*M*centeringMatrix n)≤operatorNorm M := by
  change ‖(Matrix.toEuclideanLin (centeringMatrix n*M*centeringMatrix n)).toContinuousLinearMap‖≤operatorNorm M
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have he : (Matrix.toEuclideanLin (centeringMatrix n*M*centeringMatrix n)).toContinuousLinearMap x=
      WithLp.toLp 2 (centered (M*ᵥcentered (WithLp.ofLp x))) := by
    have hx : x=WithLp.toLp 2 (WithLp.ofLp x) := by simp
    rw [hx]
    simp only [LinearMap.coe_toContinuousLinearMap',Matrix.toEuclideanLin,Matrix.toLpLin_toLp,Matrix.toLin'_apply]
    congr 1
    rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,center_mulVec,center_mulVec]
  rw [he,l2_norm]
  calc
    _ ≤ l2 (M*ᵥcentered (WithLp.ofLp x)) := centered_l2 hn _
    _ ≤ operatorNorm M*l2 (centered (WithLp.ofLp x)) := mulVec_l2 _ _
    _ ≤ operatorNorm M*l2 (WithLp.ofLp x) := mul_le_mul_of_nonneg_left (centered_l2 hn _) (norm_nonneg _)
    _ = _ := by rw [←l2_norm];simp [operatorNorm]

lemma ones_l2 (n : ℕ) : l2 (fun _ : Fin n=>(1:ℝ))=Real.sqrt n := by simp [l2]

lemma total_mul_bound {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℝ) (L : ℝ)
    (hL : 0≤L) (hr : ∀i,|∑j,C i j| ≤L) :
    |QuadraticCompletion.total (M*C)| ≤operatorNorm M*(n:ℝ)*L := by
  rw [←QuadraticCompletion.row_total_right]
  have hb:=bilinear_bound M (fun _=>1) (fun i=>∑j,C i j)
  simp only [mul_one] at hb
  calc
    _ ≤ operatorNorm M*l2 (fun _ : Fin n=>(1:ℝ))*l2 (fun i=>∑j,C i j) := hb
    _ ≤ operatorNorm M*Real.sqrt n*(Real.sqrt n*L) := by
      rw [ones_l2]
      exact mul_le_mul_of_nonneg_left (l2_abs_bound _ L hL hr)
        (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    _ = operatorNorm M*(Real.sqrt n)^2*L := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]

lemma quadratic_ones_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    |quadratic M (fun _=>1)| ≤operatorNorm M*n := by
  have hb:=bilinear_bound M (fun _=>1) (fun _=>1)
  change |quadratic M (fun _=>1)| ≤_ at hb
  calc
    _ ≤ operatorNorm M*Real.sqrt n*Real.sqrt n := by simpa only [ones_l2] using hb
    _ = operatorNorm M*(Real.sqrt n)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]

lemma finite_expectation_error {n : ℕ} (hn:0<n) (m : Model n) (c D:ℝ) (hc:0≤c) (hD0:0≤D)
    (hdep:Dependency m) (hb:∀ᵐ y∂m.law,∀i,|weighted m y i-beta m| ≤c)
    (hD:∀i,(degree m.G i:ℝ)+1≤D) (M:Matrix (Fin n) (Fin n) ℝ)
    (hM:∀i j,M i j=M j i) :
    |expectation m (fun y=>quadratic M (centered (weighted m y)))-
      (Matrix.trace (M*covariance m)+quadratic M (delta m))| ≤3*operatorNorm M*D*c^2 := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hL2:=ProbabilityCompletion.weighted_memLp m c hb
  have he:=(quadratic_expectation hn m hL2 M hM).2
  have ht:=total_mul_bound M (covariance m) (D*c^2) (by positivity)
    (ExpectationCompletion.row_covariance_bound m c D hc hdep hb hD)
  have hq:=quadratic_ones_bound M
  have hv:=ExpectationCompletion.beta_variance_bound hn m c D hc hdep hb hD
  have hv0 : 0≤var m (betaHat m) := integral_nonneg fun _=>sq_nonneg _
  rw [he]
  have hid : Matrix.trace (M*covariance m)+quadratic M (delta m)-
      2/(n:ℝ)*QuadraticCompletion.total (M*covariance m)+quadratic M (fun _=>1)*var m (betaHat m)-
      (Matrix.trace (M*covariance m)+quadratic M (delta m))=
      -(2/(n:ℝ)*QuadraticCompletion.total (M*covariance m))+quadratic M (fun _=>1)*var m (betaHat m) := by ring
  erw [hid]
  calc
    _ ≤ |2/(n:ℝ)*QuadraticCompletion.total (M*covariance m)| +|quadratic M (fun _=>1)*var m (betaHat m)| := by simpa only [abs_neg] using abs_add_le (-(2/(n:ℝ)*QuadraticCompletion.total (M*covariance m))) (quadratic M (fun _=>1)*var m (betaHat m))
    _ = 2/(n:ℝ)*|QuadraticCompletion.total (M*covariance m)| +|quadratic M (fun _=>1)| *var m (betaHat m) := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤2/(n:ℝ)),abs_of_nonneg hv0]
    _ ≤ 2/(n:ℝ)*(operatorNorm M*(n:ℝ)*(D*c^2))+(operatorNorm M*n)*(D*c^2/(n:ℝ)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left ht (by positivity))
        (mul_le_mul hq hv hv0 (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg n)))
    _ = _ := by field_simp;ring

lemma column_l2_le_operatorNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    l2 (fun i=>M i j)≤operatorNorm M := by
  classical
  have h:=mulVec_l2 M (Pi.single j 1)
  have he : l2 (Pi.single j 1 : Fin n→ℝ)=1 := by
    simp [l2,Pi.single_apply]
  rw [he,mul_one,Matrix.mulVec_single_one] at h
  exact h

theorem entry_le_operatorNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    |M i j|≤operatorNorm M := by
  have h:=column_l2_le_operatorNorm M j
  have hc:0≤l2 (fun i=>M i j):=Real.sqrt_nonneg _
  have hn:0≤operatorNorm M:=norm_nonneg _
  have hs:(M i j)^2≤∑k,(M k j)^2:=
    Finset.single_le_sum (fun k _=>sq_nonneg (M k j)) (Finset.mem_univ i)
  have he:=l2_sq (fun i=>M i j)
  apply (sq_le_sq₀ (abs_nonneg _) hn).mp
  rw [sq_abs]
  nlinarith

theorem frobenius_sq_le_size_operatorNorm_sq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑i,∑j,(M i j)^2)≤(n:ℝ)*(operatorNorm M)^2 := by
  have hcol (j : Fin n) : (∑i,(M i j)^2)≤(operatorNorm M)^2:=by
    have h:=column_l2_le_operatorNorm M j
    have hc:0≤l2 (fun i=>M i j):=Real.sqrt_nonneg _
    have hn:0≤operatorNorm M:=norm_nonneg _
    rw [←l2_sq]
    nlinarith
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑_j:Fin n,(operatorNorm M)^2:=Finset.sum_le_sum (fun j _=>hcol j)
    _ = _:=by simp


end
end AronowAudit.P011.DenseCompletion

