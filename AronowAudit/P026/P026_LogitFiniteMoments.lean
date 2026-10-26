import AronowAudit.P026.P026_LogitCenterData
import AronowAudit.P026.P026_LogitGeometry
import AronowAudit.P026.P026_VarianceStability
namespace AronowAudit.P026.LogitFiniteMoments
open Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false

variable {Ω I R : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]

def htRawCoefficient (D : Design Ω I R) (w : Ω) (i : I) : R :=
  indicator D true w i/marginal D true i-indicator D false w i/marginal D false i

def pairRawCoefficient (D : Design Ω I R) (a b : Bool) (w : Ω) (i j : I) : R :=
  indicator D a w i*indicator D b w j/(joint D a b i j+epsilon (joint D a b i j))*
    (joint D a b i j-marginal D a i*marginal D b j)/
      (marginal D a i*marginal D b j)

def varianceRawCoefficient (D : Design Ω I R) (w : Ω) (i j : I) : R :=
  if j=i then indicator D true w i/(marginal D true i)^2+
    indicator D false w i/(marginal D false i)^2
  else pairRawCoefficient D true true w i j+pairRawCoefficient D false false w i j-
    2*pairRawCoefficient D true false w i j

lemma ht_expansion (D : Design Ω I R) (N : ℕ) (r : I → R) (w : Ω) :
    ht D N r r w=(∑ i,htRawCoefficient D w i*r i)/(N:R) := by
  unfold ht htTotal htRawCoefficient
  congr 1
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  ring

lemma zeroSum_zero_of_nonzero (D : Design Ω I R) (a : Bool)
    (hn : ∀ i j,i≠j→joint D a a i j≠0) (f : I → I → R) : zeroSum D a a f=0 := by
  unfold zeroSum offSum
  apply sum_eq_zero
  intro i _
  apply sum_eq_zero
  intro j hj
  exact if_neg (hn i j (Ne.symm (ne_of_mem_erase hj)))

lemma variance_expansion (D : Design Ω I R) (N : ℕ) (r : I → R) (w : Ω)
    (ht : ∀ i j,i≠j→joint D true true i j≠0)
    (hf : ∀ i j,i≠j→joint D false false i j≠0) :
    printedVariance D N r r w=(∑ i,∑ j,varianceRawCoefficient D w i j*r i*r j)/(N:R)^2 := by
  have hobs (i : I) : observed D r r w i=r i := by simp [observed]
  have hp (a b : Bool) (i j : I) : estimatedPair D a b r r w i j=
      pairRawCoefficient D a b w i j*r i*r j := by
    simp only [estimatedPair,hobs,pairRawCoefficient]
    ring
  have hzt := zeroSum_zero_of_nonzero D true ht
    (fun i j => indicator D true w i * observed D r r w i^2/(2*marginal D true i)+
      indicator D true w j * observed D r r w j^2/(2*marginal D true j))
  have hzf := zeroSum_zero_of_nonzero D false hf
    (fun i j => indicator D false w i * observed D r r w i^2/(2*marginal D false i)+
      indicator D false w j * observed D r r w j^2/(2*marginal D false j))
  rw [printedVariance,hzt,hzf]
  simp only [hobs,add_zero,hp]
  congr 1
  rw [sum_diagonal_off]
  apply congrArg₂ (·+·)
  · apply sum_congr rfl
    intro i _
    simp [varianceRawCoefficient] <;> ring
  · unfold offSum
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j hj
    simp [varianceRawCoefficient,ne_of_mem_erase hj] <;> ring

lemma rational_ht_L1 : ∀ w, (∑ i,|htRawCoefficient tableDesign w i|)≤(32:ℚ) := by
  simp only [htRawCoefficient]
  simp_rw [table_marginal]
  decide +kernel

lemma rational_variance_L1 : ∀ w, (∑ i,∑ j,|varianceRawCoefficient tableDesign w i j|)≤(256:ℚ) := by
  simp only [varianceRawCoefficient,pairRawCoefficient]
  simp_rw [table_marginal,table_joint]
  decide +kernel

lemma center_HT_variance : variance tableDesign
    (ht tableDesign 16 LogitCompletion.logitApproxResidual LogitCompletion.logitApproxResidual)=
      (58612159883484343193064479/960000000000000000000000000:ℚ) := by
  simp only [variance,covariance,expectation,ht,htTotal]
  simp_rw [table_marginal]
  decide +kernel

lemma center_Vhat_variance : variance tableDesign
    (printedVariance tableDesign 16 LogitCompletion.logitApproxResidual LogitCompletion.logitApproxResidual)=
      (4657309550595374446614050426344914233099246458377343/
        29491200000000000000000000000000000000000000000000000000:ℚ) := by
  simp only [variance,covariance,expectation,printedVariance,estimatedPair,zeroSum,offSum]
  simp_rw [table_marginal,table_joint]
  decide +kernel

lemma real_htRawCoefficient (w : Fin 6 × Fin 15) (i : Fin 10) :
    htRawCoefficient realTableDesign w i=((htRawCoefficient tableDesign w i:ℚ):ℝ) := by
  simp only [htRawCoefficient]
  rw [LogitCompletion.real_table_marginal,LogitCompletion.real_table_marginal]
  simp only [indicator,realTableDesign]
  split_ifs <;> push_cast <;> rfl

lemma real_varianceRawCoefficient (w : Fin 6 × Fin 15) (i j : Fin 10) :
    varianceRawCoefficient realTableDesign w i j=((varianceRawCoefficient tableDesign w i j:ℚ):ℝ) := by
  simp only [varianceRawCoefficient,pairRawCoefficient]
  simp_rw [LogitCompletion.real_table_marginal,LogitCompletion.real_table_joint]
  simp only [indicator,realTableDesign,epsilon,Rat.cast_eq_zero]
  split_ifs <;> push_cast <;> rfl

lemma real_ht_L1 (w : Fin 6 × Fin 15) :
    (∑ i,|htRawCoefficient realTableDesign w i|)≤(32:ℝ) := by
  simp_rw [real_htRawCoefficient]
  exact_mod_cast rational_ht_L1 w

lemma real_variance_L1 (w : Fin 6 × Fin 15) :
    (∑ i,∑ j,|varianceRawCoefficient realTableDesign w i j|)≤(256:ℝ) := by
  simp_rw [real_varianceRawCoefficient]
  exact_mod_cast rational_variance_L1 w

lemma linear_abs_bound {J : Type*} [Fintype J] (c x : J → ℝ) (M : ℝ)
    (hx : ∀ j,|x j|≤M) : |∑ j,c j*x j|≤(∑ j,|c j|)*M := by
  calc
    |∑ j,c j*x j|≤∑ j,|c j*x j| := abs_sum_le_sum_abs _ _
    _=∑ j,|c j| * |x j| := by simp only [abs_mul]
    _≤∑ j,|c j| * M := sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _))
    _=_ := by rw [sum_mul]

lemma double_abs_bound {J : Type*} [Fintype J] (c x : J → J → ℝ) (M : ℝ)
    (hx : ∀ j k,|x j k|≤M) : |∑ j,∑ k,c j k*x j k|≤(∑ j,∑ k,|c j k|)*M := by
  calc
    |∑ j,∑ k,c j k*x j k|≤∑ j,|∑ k,c j k*x j k| := abs_sum_le_sum_abs _ _
    _≤∑ j,(∑ k,|c j k|)*M := sum_le_sum (fun j _=>linear_abs_bound (c j) (x j) M (hx j))
    _=_ := by rw [sum_mul]

lemma ht_abs_bound (r : Fin 10 → ℝ) (hr : ∀ i,|r i|≤1) (w : Fin 6 × Fin 15) :
    |ht realTableDesign 16 r r w|≤2 := by
  rw [ht_expansion,abs_div]
  rw [show |((16:ℕ):ℝ)|=16 by norm_num]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<16)).2
  have h:=linear_abs_bound (htRawCoefficient realTableDesign w) r 1 hr
  nlinarith [real_ht_L1 w]

lemma ht_difference_bound (r s : Fin 10 → ℝ) (δ : ℝ) (hδ : 0≤δ)
    (hc : ∀ i,|r i-s i|≤δ) (w : Fin 6 × Fin 15) :
    |ht realTableDesign 16 r r w-ht realTableDesign 16 s s w|≤2*δ := by
  rw [ht_expansion,ht_expansion,←sub_div]
  have he : (∑ i,htRawCoefficient realTableDesign w i*r i)-
      (∑ i,htRawCoefficient realTableDesign w i*s i)=
      ∑ i,htRawCoefficient realTableDesign w i*(r i-s i) := by
    simp only [mul_sub,sum_sub_distrib]
  rw [he,abs_div]
  rw [show |((16:ℕ):ℝ)|=16 by norm_num]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<16)).2
  have h:=linear_abs_bound (htRawCoefficient realTableDesign w) (fun i=>r i-s i) δ hc
  have hL:=mul_le_mul_of_nonneg_right (real_ht_L1 w) hδ
  nlinarith

lemma printed_expansion (r : Fin 10 → ℝ) (w : Fin 6 × Fin 15) :
    printedVariance realTableDesign 16 r r w=
      (∑ i,∑ j,varianceRawCoefficient realTableDesign w i j*r i*r j)/256 := by
  simpa only [Nat.cast_ofNat,show (16:ℝ)^2=256 by norm_num] using variance_expansion realTableDesign 16 r w
    (fun i j hij=>(LogitCompletion.real_table_same i j hij).1.ne')
    (fun i j hij=>(LogitCompletion.real_table_same i j hij).2.ne')

lemma printed_abs_bound (r : Fin 10 → ℝ) (hr : ∀ i,|r i|≤1) (w : Fin 6 × Fin 15) :
    |printedVariance realTableDesign 16 r r w|≤1 := by
  rw [printed_expansion,abs_div]
  rw [abs_of_nonneg (by norm_num : (0:ℝ)≤256)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<256)).2
  have hprod : ∀ i j,|r i*r j|≤1 := by
    intro i j
    rw [abs_mul]
    simpa using mul_le_mul (hr i) (hr j) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h:=double_abs_bound (varianceRawCoefficient realTableDesign w) (fun i j=>r i*r j) 1 hprod
  have he : (∑ i,∑ j,varianceRawCoefficient realTableDesign w i j*r i*r j)=
      ∑ i,∑ j,varianceRawCoefficient realTableDesign w i j*(r i*r j) := by
    simp only [mul_assoc]
  rw [←he] at h
  nlinarith [real_variance_L1 w]

lemma printed_difference_bound (r s : Fin 10 → ℝ) (δ : ℝ) (hδ : 0≤δ)
    (hr : ∀ i,|r i|≤1) (hs : ∀ i,|s i|≤1) (hc : ∀ i,|r i-s i|≤δ)
    (w : Fin 6 × Fin 15) :
    |printedVariance realTableDesign 16 r r w-printedVariance realTableDesign 16 s s w|≤2*δ := by
  have hprod : ∀ i j,|r i*r j-s i*s j|≤2*δ := by
    intro i j
    calc
      |r i*r j-s i*s j|=|r i*(r j-s j)+(r i-s i)*s j| := by congr 1;ring
      _≤|r i*(r j-s j)| + |(r i-s i)*s j| := abs_add_le _ _
      _=|r i| * |r j-s j| + |r i-s i| * |s j| := by simp only [abs_mul]
      _≤1*δ+δ*1 := add_le_add
        (mul_le_mul (hr i) (hc j) (abs_nonneg _) (by norm_num))
        (mul_le_mul (hc i) (hs j) (abs_nonneg _) hδ)
      _=2*δ := by ring
  rw [printed_expansion,printed_expansion,←sub_div]
  have he : (∑ i,∑ j,varianceRawCoefficient realTableDesign w i j*r i*r j)-
      (∑ i,∑ j,varianceRawCoefficient realTableDesign w i j*s i*s j)=
      ∑ i,∑ j,varianceRawCoefficient realTableDesign w i j*(r i*r j-s i*s j) := by
    simp only [mul_sub,mul_assoc,sum_sub_distrib]
  rw [he,abs_div]
  rw [abs_of_nonneg (by norm_num : (0:ℝ)≤256)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<256)).2
  have h:=double_abs_bound (varianceRawCoefficient realTableDesign w)
    (fun i j=>r i*r j-s i*s j) (2*δ) hprod
  have hL:=mul_le_mul_of_nonneg_right (real_variance_L1 w) (by positivity : 0≤2*δ)
  nlinarith

lemma variance_cast (f : Fin 6 × Fin 15 → ℚ) :
    variance realTableDesign (fun w=>(f w:ℝ))=((variance tableDesign f:ℚ):ℝ) := by
  simp only [variance,covariance,expectation,realTableDesign]
  push_cast <;> rfl

lemma center_real_HT_variance : variance realTableDesign
    (ht realTableDesign 16 (fun i=>(LogitCompletion.logitApproxResidual i:ℝ))
      (fun i=>(LogitCompletion.logitApproxResidual i:ℝ)))=
      (58612159883484343193064479/960000000000000000000000000:ℝ) := by
  have he : ht realTableDesign 16 (fun i=>(LogitCompletion.logitApproxResidual i:ℝ))
      (fun i=>(LogitCompletion.logitApproxResidual i:ℝ))=
      fun w=>((ht tableDesign 16 LogitCompletion.logitApproxResidual LogitCompletion.logitApproxResidual w:ℚ):ℝ) := by
    funext w
    rw [ht_expansion,ht_expansion]
    simp_rw [real_htRawCoefficient]
    push_cast <;> rfl
  rw [he,variance_cast,center_HT_variance]
  norm_num

lemma center_real_Vhat_variance : variance realTableDesign
    (printedVariance realTableDesign 16 (fun i=>(LogitCompletion.logitApproxResidual i:ℝ))
      (fun i=>(LogitCompletion.logitApproxResidual i:ℝ)))=
      (4657309550595374446614050426344914233099246458377343/
        29491200000000000000000000000000000000000000000000000000:ℝ) := by
  have he : printedVariance realTableDesign 16 (fun i=>(LogitCompletion.logitApproxResidual i:ℝ))
      (fun i=>(LogitCompletion.logitApproxResidual i:ℝ))=
      fun w=>((printedVariance tableDesign 16 LogitCompletion.logitApproxResidual LogitCompletion.logitApproxResidual w:ℚ):ℝ) := by
    funext w
    rw [printed_expansion,variance_expansion tableDesign 16 _ w
      (fun i j hij=>ne_of_gt (lt_of_lt_of_le (by norm_num) (table_support.2.2.2.1 i j hij).2.1))
      (fun i j hij=>ne_of_gt (lt_of_lt_of_le (by norm_num) (table_support.2.2.2.1 i j hij).2.2.1))]
    simp_rw [real_varianceRawCoefficient]
    push_cast <;> norm_num
  rw [he,variance_cast,center_Vhat_variance]
  norm_num

lemma logit_numeric_moment_bounds (r : Fin 10 → ℝ) (hr : ∀ i,|r i|≤1)
    (hclose : ∀ i,|r i-(LogitCompletion.logitApproxResidual i:ℝ)|≤1/200000000) :
    (247090/1000000:ℝ)≤Real.sqrt (variance realTableDesign (ht realTableDesign 16 r r)) ∧
    Real.sqrt (variance realTableDesign (ht realTableDesign 16 r r))≤247093/1000000 ∧
    (605/10000:ℝ)≤variance realTableDesign (ht realTableDesign 16 r r) ∧
    variance realTableDesign (ht realTableDesign 16 r r)<615/10000 ∧
    (125/10000:ℝ)≤Real.sqrt (variance realTableDesign (printedVariance realTableDesign 16 r r)) ∧
    Real.sqrt (variance realTableDesign (printedVariance realTableDesign 16 r r))<135/10000 := by
  let r0 : Fin 10 → ℝ := fun i=>(LogitCompletion.logitApproxResidual i:ℝ)
  have hr0 : ∀ i,|r0 i|≤1 := by
    intro i
    have h:=LogitCompletion.logitApproxResidual_bound i
    have hh : |r0 i|≤999/1000 := by
      have hh : ((|LogitCompletion.logitApproxResidual i|:ℚ):ℝ)≤((999/1000:ℚ):ℝ) := Rat.cast_le.mpr h
      norm_num only [Rat.cast_abs,Rat.cast_div,Rat.cast_ofNat] at hh
      exact hh
    linarith
  have hHT := VarianceStability.variance_difference_bound realTableDesign
    LogitCompletion.real_table_probability (ht realTableDesign 16 r r) (ht realTableDesign 16 r0 r0)
    2 (2*(1/200000000)) (by norm_num) (by norm_num)
    (ht_abs_bound r hr) (ht_abs_bound r0 hr0)
    (ht_difference_bound r r0 _ (by norm_num) hclose)
  have hV := VarianceStability.variance_difference_bound realTableDesign
    LogitCompletion.real_table_probability (printedVariance realTableDesign 16 r r)
    (printedVariance realTableDesign 16 r0 r0) 1 (2*(1/200000000)) (by norm_num) (by norm_num)
    (printed_abs_bound r hr) (printed_abs_bound r0 hr0)
    (printed_difference_bound r r0 _ (by norm_num) hr hr0 hclose)
  rw [center_real_HT_variance] at hHT
  rw [center_real_Vhat_variance] at hV
  obtain ⟨hHL,hHU⟩ := abs_le.mp hHT
  obtain ⟨hVL,hVU⟩ := abs_le.mp hV
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  · apply (Real.sqrt_le_left (by norm_num)).2
    norm_num
    linarith
  · linarith
  · linarith
  · apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  · apply (Real.sqrt_lt' (by norm_num)).2
    norm_num
    linarith

end
end AronowAudit.P026.LogitFiniteMoments
