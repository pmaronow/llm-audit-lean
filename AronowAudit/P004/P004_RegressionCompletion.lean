import AronowAudit.P004.P004_MatrixCompletion

namespace AronowAudit.P004.MatrixCompletion
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1000000

theorem counts_total {N : ℕ} (z : Assignment N) :
    armCount z true + armCount z false = N := by
  rw [armCount, armCount, ← Finset.sum_add_distrib]
  have he : (∑ i, ((if z i = true then 1 else 0 : ℝ)+(if z i = false then 1 else 0))) = ∑ _i : Fin N, (1:ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    cases z i <;> norm_num
  rw [he]
  simp

theorem sum_bit {N : ℕ} (z : Assignment N) : ∑ i, bit (z i) = armCount z true := by
  unfold armCount
  apply Finset.sum_congr rfl
  intro i _
  cases z i <;> norm_num [bit]

theorem gram_formula {N : ℕ} (z : Assignment N) :
    (designMatrix z).transpose * designMatrix z =
      !![(N:ℝ),armCount z true;armCount z true,armCount z true] := by
  ext a b
  fin_cases a <;> fin_cases b
  all_goals simp only [Matrix.mul_apply, Matrix.transpose_apply, designMatrix]
  all_goals norm_num
  · exact sum_bit z
  · exact sum_bit z
  · rw [← sum_bit]
    apply Finset.sum_congr rfl
    intro i _
    cases z i <;> norm_num [bit]

def gramInverse {N : ℕ} (z : Assignment N) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1/armCount z false, -(1/armCount z false);
     -(1/armCount z false), (N:ℝ)/(armCount z true*armCount z false)]

theorem gramInverse_mul_gram {N : ℕ} (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) :
    gramInverse z * ((designMatrix z).transpose * designMatrix z) = 1 := by
  rw [gram_formula]
  have hc := counts_total z
  ext a b
  fin_cases a <;> fin_cases b
  all_goals norm_num [Matrix.mul_apply,Fin.sum_univ_two,gramInverse]
  all_goals field_simp [h1.ne',h0.ne']
  all_goals nlinarith

theorem gram_inverse_eq {N : ℕ} (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) :
    ((designMatrix z).transpose * designMatrix z)⁻¹ = gramInverse z :=
  Matrix.inv_eq_left_inv (gramInverse_mul_gram z h1 h0)

theorem treatment_row {N : ℕ} (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) (i : Fin N) :
    (((designMatrix z).transpose * designMatrix z)⁻¹ * (designMatrix z).transpose) 1 i = lambda z i := by
  rw [gram_inverse_eq z h1 h0]
  have hc := counts_total z
  simp only [Matrix.mul_apply,Fin.sum_univ_two,gramInverse,Matrix.transpose_apply,designMatrix]
  norm_num
  unfold lambda
  cases z i <;> norm_num [bit]
  all_goals field_simp [h1.ne',h0.ne']
  all_goals nlinarith

theorem residual_algebra {N : ℕ} (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) :
    (residualMaker z).transpose = residualMaker z ∧
    residualMaker z * residualMaker z = residualMaker z ∧
    residualMaker z * designMatrix z = 0 := by
  let X := designMatrix z
  let A := (X.transpose*X)⁻¹
  have hAX : A*(X.transpose*X)=1 := by
    dsimp [A,X]
    rw [gram_inverse_eq z h1 h0]
    exact gramInverse_mul_gram z h1 h0
  have hs : A.transpose=A := (gram_inv_symmetric z).eq
  have hproj : (X*A*X.transpose)*(X*A*X.transpose) = X*A*X.transpose := by
    calc
      _ = X*(A*(X.transpose*X))*A*X.transpose := by simp only [Matrix.mul_assoc]
      _ = X*A*X.transpose := by rw [hAX]; simp
  refine ⟨?_,?_,?_⟩
  · change (1-X*A*X.transpose).transpose=1-X*A*X.transpose
    simp only [Matrix.transpose_sub,Matrix.transpose_one,Matrix.transpose_mul,Matrix.transpose_transpose,hs,Matrix.mul_assoc]
  · change (1-X*A*X.transpose)*(1-X*A*X.transpose)=1-X*A*X.transpose
    rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.one_mul,Matrix.mul_sub,Matrix.mul_one,hproj]
    abel
  · change (1-X*A*X.transpose)*X=0
    rw [Matrix.sub_mul,Matrix.one_mul]
    have he : (X*A*X.transpose)*X=X := by
      calc
        _ = X*(A*(X.transpose*X)) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hAX]; simp
    rw [he,sub_self]

theorem lambda_square_sum {N : ℕ} (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) :
    (∑ i, (lambda z i)^2) = (N:ℝ)/(armCount z true*armCount z false) := by
  have he : ∀ i, (lambda z i)^2 =
      (if z i = true then 1 else 0)/(armCount z true)^2 +
      (if z i = false then 1 else 0)/(armCount z false)^2 := by
    intro i
    cases hzi : z i <;> simp [lambda,bit,hzi,div_pow]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
  change armCount z true/(armCount z true)^2+armCount z false/(armCount z false)^2 = _
  have hc := counts_total z
  field_simp [h1.ne',h0.ne']
  nlinarith

theorem sandwich_treatment {N : ℕ} (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false)
    (e : Fin N → ℝ) (Q : Matrix (Fin N) (Fin N) ℝ) :
    sandwich z e Q 1 1=kernelVariance z e Q := by
  let X := designMatrix z
  let A := (X.transpose*X)⁻¹
  have hs : A.transpose=A := (gram_inv_symmetric z).eq
  have hrow : ∀ i, (A*X.transpose) 1 i=lambda z i := treatment_row z h1 h0
  have he : sandwich z e Q = (A*X.transpose)*Matrix.of (fun i j=>e i*e j*Q i j)*(A*X.transpose).transpose := by
    dsimp only [sandwich,A,X]
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,(gram_inv_symmetric z).eq,Matrix.mul_assoc]
  rw [he]
  unfold kernelVariance
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply,Finset.sum_mul,hrow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem arm_residual_sum {N : ℕ} (R : CircleTable N) (z : Assignment N) (a : Bool)
    (ha : 0 < armCount z a) :
    (∑ i, if z i = a then R i z-armMean R z a else 0) = 0 := by
  have he : ∀ i, (if z i=a then R i z-armMean R z a else 0) =
      (if z i=a then R i z else 0) - (if z i=a then (1:ℝ) else 0)*armMean R z a := by
    intro i
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,←Finset.sum_mul]
  change (∑ i, if z i=a then R i z else 0)-armCount z a*armMean R z a=0
  unfold armMean
  field_simp [ha.ne']
  ring

theorem fitted_normal_equations {N : ℕ} (R : CircleTable N) (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) :
    (∑ i, (R i z-armMean R z false-hajek R z*bit (z i))) = 0 ∧
    (∑ i, (R i z-armMean R z false-hajek R z*bit (z i))*bit (z i)) = 0 := by
  have he : ∀ i, (R i z-armMean R z false-hajek R z*bit (z i)) =
      (if z i = true then R i z-armMean R z true else 0) +
      (if z i = false then R i z-armMean R z false else 0) := by
    intro i
    cases hz : z i <;> simp [bit,hajek,hz] <;> ring
  have het : ∀ i, (R i z-armMean R z false-hajek R z*bit (z i))*bit (z i) =
      if z i = true then R i z-armMean R z true else 0 := by
    intro i
    cases hz : z i <;> simp [bit,hajek,hz] <;> ring
  constructor
  · simp_rw [he]
    rw [Finset.sum_add_distrib,arm_residual_sum R z true h1,arm_residual_sum R z false h0,add_zero]
  · simp_rw [het]
    exact arm_residual_sum R z true h1

theorem ls_square_decomposition {N : ℕ} (R : CircleTable N) (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) (μ τ : ℝ) :
    (∑ i, (R i z-μ-τ*bit (z i))^2) =
      (∑ i, (R i z-armMean R z false-hajek R z*bit (z i))^2) +
      armCount z false*(μ-armMean R z false)^2 +
      armCount z true*(μ+τ-armMean R z true)^2 := by
  let r := fun i => R i z-armMean R z false-hajek R z*bit (z i)
  let a := μ-armMean R z false
  let b := τ-hajek R z
  have hp : ∀ i, (R i z-μ-τ*bit (z i))^2 =
      (r i)^2 + ((a+b*bit (z i))^2 - 2*a*r i - 2*b*(r i*bit (z i))) := by
    intro i
    dsimp only [r,a,b]
    ring
  have hs : ∑ i, (a+b*bit (z i))^2 = armCount z false*a^2+armCount z true*(a+b)^2 := by
    have he : ∀ i, (a+b*bit (z i))^2 =
        (if z i=false then (1:ℝ) else 0)*a^2+(if z i=true then (1:ℝ) else 0)*(a+b)^2 := by
      intro i
      cases hz : z i <;> simp [bit,hz]
    simp_rw [he]
    rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul]
    rfl
  have hr := fitted_normal_equations R z h1 h0
  simp_rw [hp]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    ←Finset.mul_sum,←Finset.mul_sum,hs]
  change _ + (_ - _*(∑ i, r i) - _*(∑ i, r i*bit (z i))) = _
  rw [hr.1,hr.2]
  dsimp only [r,a,b]
  unfold hajek
  ring


end
end AronowAudit.P004.MatrixCompletion

namespace AronowAudit.P004
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1000000

theorem regression_matrix_identities {N : ℕ} (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false)
    (e : Fin N → ℝ) (Q : Matrix (Fin N) (Fin N) ℝ) :
    (residualMaker z).transpose = residualMaker z ∧
    residualMaker z * residualMaker z = residualMaker z ∧
    residualMaker z * designMatrix z = 0 ∧
    (∀ i, (((designMatrix z).transpose * designMatrix z)⁻¹ * (designMatrix z).transpose) 1 i = lambda z i) ∧
    (((designMatrix z).transpose * designMatrix z)⁻¹) 1 1 = N/(armCount z true * armCount z false) ∧
    (∑ i, (lambda z i)^2) = N/(armCount z true * armCount z false) ∧
    sandwich z e Q 1 1 = kernelVariance z e Q := by
  obtain ⟨hs,hm,hx⟩ := MatrixCompletion.residual_algebra z h1 h0
  refine ⟨hs,hm,hx,MatrixCompletion.treatment_row z h1 h0,?_,
    MatrixCompletion.lambda_square_sum z h1 h0,MatrixCompletion.sandwich_treatment z h1 h0 e Q⟩
  rw [MatrixCompletion.gram_inverse_eq z h1 h0]
  rfl

theorem observational_sandwich_identity {N : ℕ} (phat : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (z : Assignment N)
    (hN : 0 < N) (h1 : 0 < armCount z true) (h0 : 0 < armCount z false)
    (hp : ∀ i, 0 < phat i ∧ phat i < 1) :
    (∀ i, lambda z i * weightedEpsilon phat R g z i = residualContrast phat R g i z / N) ∧
    sandwich z (weightedEpsilon phat R g z) (Matrix.of (fun i j => if j ∈ B i then 1 else 0)) 1 1 =
      oracleHAC phat R B g z := by
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hN)
  have he : ∀ i, lambda z i * weightedEpsilon phat R g z i = residualContrast phat R g i z / N := by
    intro i
    cases hz : z i <;> simp only [lambda,weightedEpsilon,residualContrast,bit,hz]
    all_goals norm_num
    all_goals field_simp [h1.ne',h0.ne',hn,(hp i).1.ne',(sub_pos.mpr (hp i).2).ne']
    all_goals ring
  refine ⟨he,?_⟩
  rw [MatrixCompletion.sandwich_treatment z h1 h0]
  unfold kernelVariance oracleHAC
  have ht : ∀ i j, lambda z i*lambda z j*weightedEpsilon phat R g z i*weightedEpsilon phat R g z j*
      (Matrix.of (fun i j => if j ∈ B i then (1:ℝ) else 0)) i j =
      if j ∈ B i then residualContrast phat R g i z*residualContrast phat R g j z/(N:ℝ)^2 else 0 := by
    intro i j
    rw [show lambda z i*lambda z j*weightedEpsilon phat R g z i*weightedEpsilon phat R g z j =
      (lambda z i*weightedEpsilon phat R g z i)*(lambda z j*weightedEpsilon phat R g z j) by ring]
    rw [he i,he j]
    simp only [Matrix.of_apply]
    split_ifs <;> field_simp <;> ring
  simp_rw [ht]
  simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
  simp only [Finset.sum_div]

theorem hajek_ols {N : ℕ} (R : CircleTable N) (z : Assignment N)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) :
    armCount z true + armCount z false = N ∧
    ∀ μ τ : ℝ,
      (∑ i, (R i z-armMean R z false-hajek R z*bit (z i))^2) ≤
        (∑ i, (R i z-μ-τ*bit (z i))^2) ∧
      ((∑ i, (R i z-μ-τ*bit (z i))^2) =
        (∑ i, (R i z-armMean R z false-hajek R z*bit (z i))^2) →
          μ = armMean R z false ∧ τ = hajek R z) := by
  refine ⟨MatrixCompletion.counts_total z,?_⟩
  intro μ τ
  have hdecomp := MatrixCompletion.ls_square_decomposition R z h1 h0 μ τ
  have hn0 := mul_nonneg h0.le (sq_nonneg (μ-armMean R z false))
  have hn1 := mul_nonneg h1.le (sq_nonneg (μ+τ-armMean R z true))
  refine ⟨by linarith,?_⟩
  intro heq
  have hs0 : (μ-armMean R z false)^2 = 0 := by nlinarith
  have hs1 : (μ+τ-armMean R z true)^2 = 0 := by nlinarith
  have he0 := sq_eq_zero_iff.mp hs0
  have he1 := sq_eq_zero_iff.mp hs1
  unfold hajek
  constructor <;> linarith

end
end AronowAudit.P004
