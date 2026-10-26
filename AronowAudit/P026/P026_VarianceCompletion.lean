import AronowAudit.P026.P026_FiniteDesign
/-! Exact finite-design variance identities and support repairs for P026. -/
namespace AronowAudit.P026.VarianceCompletion
open Finset
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {Ω I R:Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]

lemma expectation_finset_sum {J:Type*} (D:Design Ω I R) (s:Finset J) (f:J→Ω→R):
    expectation D (fun w=>∑j∈s,f j w)=∑j∈s,expectation D (f j):=by
  unfold expectation
  simp only [mul_sum]
  rw [sum_comm]

lemma expectation_offSum (D:Design Ω I R) (f:Ω→I→I→R):
    expectation D (fun w=>offSum (f w))=offSum (fun i j=>expectation D (fun w=>f w i j)):=by
  unfold offSum
  rw [expectation_sum]
  apply sum_congr rfl
  intro i _
  exact expectation_finset_sum D _ _

lemma expectation_zeroSum (D:Design Ω I R) (a b:Bool) (f:Ω→I→I→R):
    expectation D (fun w=>zeroSum D a b (f w))=
      zeroSum D a b (fun i j=>expectation D (fun w=>f w i j)):=by
  unfold zeroSum
  rw [expectation_offSum]
  unfold offSum
  apply sum_congr rfl;intro i _
  apply sum_congr rfl;intro j _
  by_cases h:joint D a b i j=0 <;>simp [h,expectation]

lemma offSum_add (f g:I→I→R):offSum (fun i j=>f i j+g i j)=offSum f+offSum g:=by
  simp [offSum,sum_add_distrib]
lemma offSum_sub (f g:I→I→R):offSum (fun i j=>f i j-g i j)=offSum f-offSum g:=by
  simp [offSum,sum_sub_distrib]
lemma offSum_mul (f:I→I→R) (c:R):offSum (fun i j=>f i j*c)=offSum f*c:=by
  simp only [offSum,sum_mul]
lemma offSum_div (f:I→I→R) (c:R):offSum (fun i j=>f i j/c)=offSum f/c:=by
  simp only [offSum,sum_div]

lemma masked_square (D:Design Ω I R) (a:Bool) (x z:I→R) (w:Ω) (i:I):
    indicator D a w i*(observed D x z w i)^2=
      indicator D a w i*(if a then x i else z i)^2:=by
  cases a <;>cases hi:D.treatment w i <;>simp [indicator,observed,hi]

lemma expected_observed_square (D:Design Ω I R) (a:Bool) (x z:I→R) (i:I):
    expectation D (fun w=>indicator D a w i*(observed D x z w i)^2)=
      marginal D a i*(if a then x i else z i)^2:=by
  simp_rw [masked_square]
  exact expectation_mul_const D _ _

lemma expected_square_div (D:Design Ω I R) (a:Bool) (x z:I→R) (i:I) (h:marginal D a i≠0):
    expectation D (fun w=>indicator D a w i*(observed D x z w i)^2/marginal D a i)=
      (if a then x i else z i)^2:=by
  rw [expectation_div,expected_observed_square]
  exact mul_div_cancel_left₀ _ h

lemma expected_scaled_square (D:Design Ω I R) (a:Bool) (x z:I→R) (i:I):
    expectation D (fun w=>indicator D a w i*(observed D x z w i/marginal D a i)^2)=
      marginal D a i*((if a then x i else z i)/marginal D a i)^2:=by
  have he(w:Ω):indicator D a w i*(observed D x z w i/marginal D a i)^2=
      (indicator D a w i*(observed D x z w i)^2)/(marginal D a i)^2:=by ring
  simp_rw [he]
  rw [expectation_div,expected_observed_square]
  ring

lemma masked_pair (D:Design Ω I R) (a b:Bool) (x z:I→R) (w:Ω) (i j:I):
    (indicator D a w i*indicator D b w j)*observed D x z w i*observed D x z w j=
      (indicator D a w i*indicator D b w j)*(if a then x i else z i)*(if b then x j else z j):=by
  have hi:=observed_mask D a x z w i
  have hj:=observed_mask D b x z w j
  calc
    _ =(indicator D a w i*observed D x z w i)*(indicator D b w j*observed D x z w j):=by ring
    _ = _:=by rw [hi,hj];ring

def pairCoeff (D:Design Ω I R) (a b:Bool) (x z:I→R) (i j:I):R:=
  (joint D a b i j-marginal D a i*marginal D b j)*
    ((if a then x i else z i)/marginal D a i)*((if b then x j else z j)/marginal D b j)

lemma expected_pair (D:Design Ω I R) (a b:Bool) (x z:I→R) (i j:I):
    expectation D (fun w=>estimatedPair D a b x z w i j)=
      if joint D a b i j=0 then 0 else pairCoeff D a b x z i j:=by
  have he(w:Ω):estimatedPair D a b x z w i j=
      (indicator D a w i*indicator D b w j)*
      ((joint D a b i j-marginal D a i*marginal D b j)*
        (if a then x i else z i)*(if b then x j else z j)/
        ((joint D a b i j+epsilon (joint D a b i j))*marginal D a i*marginal D b j)):=by
    unfold estimatedPair
    have hi:=masked_pair D a b x z w i j
    have he:(indicator D a w i*indicator D b w j)*observed D x z w i*observed D x z w j=
        (indicator D a w i*indicator D b w j)*(if a then x i else z i)*(if b then x j else z j):=hi
    calc
      _ = ((indicator D a w i*indicator D b w j)*observed D x z w i*observed D x z w j)*
        ((joint D a b i j-marginal D a i*marginal D b j)/
          ((joint D a b i j+epsilon (joint D a b i j))*marginal D a i*marginal D b j)):=by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _ = _:=by rw [he];ring
  simp_rw [he]
  rw [expectation_mul_const]
  change joint D a b i j*_=_
  by_cases h:joint D a b i j=0
  · simp [h]
  · simp only [if_neg h,epsilon,h,ite_false,add_zero,pairCoeff]
    field_simp

lemma expectation_const_mul (D:Design Ω I R) (c:R) (f:Ω→R):
    expectation D (fun w=>c*f w)=c*expectation D f:=by
  simpa only [mul_comm] using expectation_mul_const D f c

lemma offSum_const_mul (c:R) (f:I→I→R):offSum (fun i j=>c*f i j)=c*offSum f:=by
  simpa only [mul_comm] using offSum_mul f c
lemma offSum_congr (f g:I→I→R) (h:∀i j,f i j=g i j):offSum f=offSum g:=by
  unfold offSum
  apply sum_congr rfl;intro i _
  apply sum_congr rfl;intro j _
  exact h i j
lemma zeroSum_add (D:Design Ω I R) (a b:Bool) (f g:I→I→R):
    zeroSum D a b (fun i j=>f i j+g i j)=zeroSum D a b f+zeroSum D a b g:=by
  unfold zeroSum
  rw [←offSum_add]
  apply offSum_congr;intro i j
  by_cases h:joint D a b i j=0 <;>simp [h]
lemma zeroSum_div (D:Design Ω I R) (a b:Bool) (f:I→I→R) (c:R):
    zeroSum D a b (fun i j=>f i j/c)=zeroSum D a b f/c:=by
  unfold zeroSum
  rw [←offSum_div]
  apply offSum_congr;intro i j
  by_cases h:joint D a b i j=0 <;>simp [h]
lemma zeroSum_const_mul (D:Design Ω I R) (a b:Bool) (c:R) (f:I→I→R):
    zeroSum D a b (fun i j=>c*f i j)=c*zeroSum D a b f:=by
  unfold zeroSum
  rw [←offSum_const_mul]
  apply offSum_congr;intro i j
  by_cases h:joint D a b i j=0 <;>simp [h]
lemma zeroSum_congr (D:Design Ω I R) (a b:Bool) (f g:I→I→R)
    (h:∀i j,f i j=g i j):zeroSum D a b f=zeroSum D a b g:=by
  congr 1
  funext i j
  exact h i j

lemma marginal_ne (D:Design Ω I R) (hp:positiveMarginals D) (a:Bool) (i:I):
    marginal D a i≠0:=by
  cases a
  · exact ne_of_gt (hp i).2
  · exact ne_of_gt (hp i).1

lemma expected_pair_gap (D:Design Ω I R) (hp:positiveMarginals D) (a b:Bool)
    (x z:I→R) (i j:I):
    expectation D (fun w=>estimatedPair D a b x z w i j)=pairCoeff D a b x z i j+
      (if joint D a b i j=0 then (if a then x i else z i)*(if b then x j else z j) else 0):=by
  rw [expected_pair]
  by_cases h:joint D a b i j=0
  · simp only [h,ite_true,pairCoeff,zero_sub]
    field_simp [marginal_ne D hp a i,marginal_ne D hp b j]
    ring
  · simp [h]

lemma expected_half_square (D:Design Ω I R) (hp:positiveMarginals D) (a:Bool)
    (x z:I→R) (i:I):
    expectation D (fun w=>indicator D a w i*(observed D x z w i)^2/(2*marginal D a i))=
      (if a then x i else z i)^2/2:=by
  rw [expectation_div,expected_observed_square]
  field_simp [marginal_ne D hp a i]

lemma expected_crossCorrection (D:Design Ω I R) (hp:positiveMarginals D) (x z:I→R):
    expectation D (crossCorrection D x z)=zeroSum D true false (fun i j=>x i^2+z j^2):=by
  unfold crossCorrection
  rw [expectation_zeroSum]
  apply zeroSum_congr;intro i j
  rw [expectation_add,expected_square_div D true x z i (marginal_ne D hp true i),
    expected_square_div D false x z j (marginal_ne D hp false j)]
  rfl

lemma expected_printed_numerator (D:Design Ω I R) (hp:positiveMarginals D)
    (N:ℕ) (x z:I→R):
    expectation D (printedVariance D N x z)=
      ((∑i, (marginal D true i*(x i/marginal D true i)^2+
        marginal D false i*(z i/marginal D false i)^2))+
        offSum (fun i j=>pairCoeff D true true x z i j+pairCoeff D false false x z i j-
          2*pairCoeff D true false x z i j)+
        zeroSum D true true (fun i j=>x i*x j)+zeroSum D false false (fun i j=>z i*z j)-
        2*zeroSum D true false (fun i j=>x i*z j)+
        zeroSum D true true (fun i j=>x i^2/2+x j^2/2)+
        zeroSum D false false (fun i j=>z i^2/2+z j^2/2))/(N:R)^2:=by
  unfold printedVariance
  rw [expectation_div,expectation_add,expectation_add,expectation_add]
  rw [expectation_sum,expectation_offSum,expectation_zeroSum,expectation_zeroSum]
  simp_rw [expectation_sub,expectation_add,expectation_const_mul,expected_scaled_square,
    expected_half_square D hp,expected_pair_gap D hp]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  have he(i j:I):
      pairCoeff D true true x z i j+(if joint D true true i j=0 then x i*x j else 0)+
      (pairCoeff D false false x z i j+(if joint D false false i j=0 then z i*z j else 0))-
      2*(pairCoeff D true false x z i j+(if joint D true false i j=0 then x i*z j else 0))=
      (pairCoeff D true true x z i j+pairCoeff D false false x z i j-2*pairCoeff D true false x z i j)+
      (if joint D true true i j=0 then x i*x j else 0)+
      (if joint D false false i j=0 then z i*z j else 0)-
      2*(if joint D true false i j=0 then x i*z j else 0):=by ring
  simp_rw [he]
  rw [offSum_sub,offSum_add,offSum_add,offSum_const_mul]
  unfold zeroSum
  ring

lemma variance_ht_expanded (D:Design Ω I R) (hp:positiveMarginals D) (N:ℕ) (x z:I→R):
    variance D (ht D N x z)=
      ((∑i,marginal D true i*(1-marginal D true i)*(x i/marginal D true i)^2)+
        (∑i,marginal D false i*(1-marginal D false i)*(z i/marginal D false i)^2)+
        offSum (fun i j=>pairCoeff D true true x z i j+pairCoeff D false false x z i j-
          2*pairCoeff D true false x z i j)+2*(∑i,x i*z i))/(N:R)^2:=by
  change variance D (fun w=>(htTotal D true x w-htTotal D false z w)/(N:R))=_
  rw [variance_sub_div,ht_arm_variance,ht_arm_variance,ht_cluster_covariance D hp]
  unfold armVarianceExpression clusterCovarianceExpression pairCoeff
  simp only [Bool.false_eq_true,ite_true,ite_false]
  rw [offSum_sub,offSum_add,offSum_const_mul]
  ring

lemma diagonal_gap (D:Design Ω I R) (hp:positiveMarginals D) (x z:I→R):
    (∑i, (marginal D true i*(x i/marginal D true i)^2+marginal D false i*(z i/marginal D false i)^2))-
      (∑i,marginal D true i*(1-marginal D true i)*(x i/marginal D true i)^2)-
      (∑i,marginal D false i*(1-marginal D false i)*(z i/marginal D false i)^2)-
      2*(∑i,x i*z i)=∑i,(x i-z i)^2:=by
  rw [mul_sum]
  simp only [←sum_sub_distrib]
  apply sum_congr rfl;intro i _
  field_simp [marginal_ne D hp true i,marginal_ne D hp false i]
  ring

lemma zero_sum_plus_gap (D:Design Ω I R) (a:Bool) (x:I→R):
    zeroSum D a a (fun i j=>x i*x j)+zeroSum D a a (fun i j=>x i^2/2+x j^2/2)=
      zeroSum D a a (fun i j=>(x i+x j)^2)/2:=by
  rw [←zeroSum_add,←zeroSum_div]
  apply zeroSum_congr;intro i j;ring

lemma scale_difference (n a b:R) (hn:n≠0):n*(a/n-b/n)=a-b:=by
  field_simp

lemma printed_variance_bias_completed (D:Design Ω I R) (hp:positiveMarginals D)
    (N:ℕ) (hN:0<N) (x z:I→R):
    (N:R)^2*(expectation D (printedVariance D N x z)-variance D (ht D N x z))=
      (∑i,(x i-z i)^2)+zeroSum D true true (fun i j=>(x i+x j)^2)/2+
        zeroSum D false false (fun i j=>(z i+z j)^2)/2-
        2*zeroSum D true false (fun i j=>x i*z j):=by
  rw [expected_printed_numerator D hp,variance_ht_expanded D hp]
  have hn:(N:R)^2≠0:=pow_ne_zero 2 (by exact_mod_cast hN.ne')
  rw [scale_difference _ _ _ hn]
  have hd:=diagonal_gap D hp x z
  have ht:=zero_sum_plus_gap D true x
  have hf:=zero_sum_plus_gap D false z
  linear_combination hd+ht+hf

lemma expected_masked_pair (D:Design Ω I R) (a b:Bool) (x z:I→R) (i j:I) (c:R):
    expectation D (fun w=>(indicator D a w i*indicator D b w j)*
      observed D x z w i*observed D x z w j*c)=
      joint D a b i j*(if a then x i else z i)*(if b then x j else z j)*c:=by
  simp_rw [masked_pair]
  rw [expectation_mul_const,expectation_mul_const,expectation_mul_const]
  rfl

def rawPair (D:Design Ω I R) (a b:Bool) (x z:I→R) (w:Ω) (i j:I):R:=
  indicator D a w i*indicator D b w j/joint D a b i j*
    (joint D a b i j-marginal D a i*marginal D b j)*
    (observed D x z w i/marginal D a i)*(observed D x z w j/marginal D b j)

lemma expected_raw_pair (D:Design Ω I R) (a b:Bool) (x z:I→R) (i j:I):
    expectation D (fun w=>rawPair D a b x z w i j)=
      expectation D (fun w=>estimatedPair D a b x z w i j):=by
  have he(w:Ω):rawPair D a b x z w i j=
      (indicator D a w i*indicator D b w j)*observed D x z w i*observed D x z w j*
        ((joint D a b i j-marginal D a i*marginal D b j)/
          (joint D a b i j*marginal D a i*marginal D b j)):=by
    unfold rawPair
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  simp_rw [he]
  rw [expected_masked_pair,expected_pair]
  by_cases h:joint D a b i j=0
  · simp [h]
  · simp only [if_neg h,pairCoeff]
    field_simp

lemma expected_printed_covariance (D:Design Ω I R) (hp:positiveMarginals D) (x z:I→R):
    expectation D (printedCovariance D x z)=covarianceBound D x z+
      zeroSum D true false (fun i j=>x i*z j):=by
  change expectation D (fun w=>offSum (rawPair D true false x z w)-
    (∑i,indicator D true w i*(observed D x z w i)^2/(2*marginal D true i))-
    (∑i,indicator D false w i*(observed D x z w i)^2/(2*marginal D false i)))=_
  rw [expectation_sub,expectation_sub,expectation_offSum,expectation_sum,expectation_sum]
  simp_rw [expected_raw_pair,expected_pair_gap D hp,expected_half_square D hp]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  rw [offSum_add]
  unfold covarianceBound zeroSum pairCoeff
  simp only [ite_true,ite_false,Bool.false_eq_true]
  ring

lemma cross_square_gap (D:Design Ω I R) (x z:I→R):
    zeroSum D true false (fun i j=>x i^2+z j^2)=
      zeroSum D true false (fun i j=>(x i-z j)^2)+2*zeroSum D true false (fun i j=>x i*z j):=by
  rw [←zeroSum_const_mul,←zeroSum_add]
  apply zeroSum_congr;intro i j;ring

lemma corrected_covariance_bias_completed (D:Design Ω I R) (hp:positiveMarginals D) (x z:I→R):
    expectation D (correctedCovariance D x z)-covariance D (htTotal D true x) (htTotal D false z)=
      -(∑i,(x i-z i)^2)/2-zeroSum D true false (fun i j=>(x i-z j)^2)/2 ∧
    expectation D (correctedCovariance D x z)≤covariance D (htTotal D true x) (htTotal D false z):=by
  have he:expectation D (correctedCovariance D x z)=
      covarianceBound D x z+zeroSum D true false (fun i j=>x i*z j)-
        zeroSum D true false (fun i j=>x i^2+z j^2)/2:=by
    unfold correctedCovariance
    rw [expectation_sub,expectation_div,expected_printed_covariance D hp,expected_crossCorrection D hp]
  have hg:=covariance_bound_gap D hp x z
  have hz:=cross_square_gap D x z
  have heq:expectation D (correctedCovariance D x z)-covariance D (htTotal D true x) (htTotal D false z)=
      -(∑i,(x i-z i)^2)/2-zeroSum D true false (fun i j=>(x i-z j)^2)/2:=by
    rw [he]
    linear_combination -hg-(1/2:R)*hz
  refine ⟨heq,?_⟩
  have h0:0≤∑i,(x i-z i)^2:=sum_nonneg (fun i _=>sq_nonneg _)
  have h1:=zeroSum_squares_nonneg D true false (fun i j=>x i-z j)
  linarith

lemma corrected_variance_bias_completed (D:Design Ω I R) (hp:positiveMarginals D)
    (N:ℕ) (hN:0<N) (x z:I→R):
    (N:R)^2*(expectation D (correctedVariance D N x z)-variance D (ht D N x z))=
      correctedBiasExpression D x z ∧
    variance D (ht D N x z)≤expectation D (correctedVariance D N x z):=by
  have hn:(N:R)^2≠0:=pow_ne_zero 2 (by exact_mod_cast hN.ne')
  have he:(N:R)^2*(expectation D (correctedVariance D N x z)-variance D (ht D N x z))=
      (N:R)^2*(expectation D (printedVariance D N x z)-variance D (ht D N x z))+
        expectation D (crossCorrection D x z):=by
    unfold correctedVariance
    rw [expectation_add,expectation_div]
    field_simp
    <;>ring
  have heq:(N:R)^2*(expectation D (correctedVariance D N x z)-variance D (ht D N x z))=
      correctedBiasExpression D x z:=by
    rw [he,printed_variance_bias_completed D hp N hN,expected_crossCorrection D hp]
    unfold correctedBiasExpression
    linear_combination cross_square_gap D x z
  refine ⟨heq,?_⟩
  have h0:=correctedBiasExpression_nonneg D x z
  have hNpos:0<(N:R)^2:=by positivity
  have hh:0≤expectation D (correctedVariance D N x z)-variance D (ht D N x z):=
    (mul_nonneg_iff_of_pos_left hNpos).mp (heq.symm ▸ h0)
  linarith

lemma zeroSum_of_positive (D:Design Ω I R) (a b:Bool)
    (h:∀i j,i≠j→0<joint D a b i j) (f:I→I→R):zeroSum D a b f=0:=by
  unfold zeroSum offSum
  apply sum_eq_zero;intro i _
  apply sum_eq_zero;intro j hj
  have hij:i≠j:=(mem_erase.mp hj).1.symm
  simp [ne_of_gt (h i j hij)]

lemma correctedCovariance_eq_printed (D:Design Ω I R) (hc:crossSupport D) (x z:I→R):
    correctedCovariance D x z=printedCovariance D x z:=by
  funext w
  have hz:crossCorrection D x z w=0:=zeroSum_of_positive D true false hc _
  simp [correctedCovariance,hz]

lemma correctedVariance_eq_printed (D:Design Ω I R) (hc:crossSupport D) (N:ℕ) (x z:I→R):
    correctedVariance D N x z=printedVariance D N x z:=by
  funext w
  have hz:crossCorrection D x z w=0:=zeroSum_of_positive D true false hc _
  simp [correctedVariance,hz]

lemma zeroSum_squares_eq_zero (D:Design Ω I R) (a b:Bool) (x z:I→R):
    zeroSum D a b (fun i j=>(x i-z j)^2)=0↔
      ∀i j,i≠j→joint D a b i j=0→x i=z j:=by
  let f:=fun i j=>if joint D a b i j=0 then (x i-z j)^2 else 0
  have hf(i j:I):0≤f i j:=by dsimp [f];split_ifs <;>positivity
  have hr(i:I):0≤∑j∈univ.erase i,f i j:=sum_nonneg (fun j _=>hf i j)
  constructor
  · intro hs i j hij hjoint
    have hj:j∈(univ.erase i:Finset I):=by simp [hij.symm]
    have h1:f i j≤∑j∈univ.erase i,f i j:=single_le_sum (fun j _=>hf i j) hj
    have h2:(∑j∈univ.erase i,f i j)≤offSum f:=single_le_sum (fun k _=>hr k) (mem_univ i)
    have he:offSum f=0:=hs
    have hz:(x i-z j)^2≤0:=by simpa only [f,hjoint,ite_true,he] using h1.trans h2
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hz (sq_nonneg _)))
  · intro h
    unfold zeroSum offSum
    apply sum_eq_zero;intro i _
    apply sum_eq_zero;intro j hj
    by_cases hg:joint D a b i j=0
    · simp [hg,h i j (mem_erase.mp hj).1.symm hg]
    · simp [hg]

lemma corrected_sharp_null_completed (D:Design Ω I R) (hp:positiveMarginals D)
    (N:ℕ) (hN:0<N) (c:I→R)
    (hs:∀i j,i≠j→0<joint D true true i j∧0<joint D false false i j):
    expectation D (correctedVariance D N c c)-variance D (ht D N c c)=
      zeroSum D true false (fun i j=>(c i-c j)^2)/(N:R)^2 ∧
    (expectation D (correctedVariance D N c c)=variance D (ht D N c c)↔
      ∀i j,i≠j→joint D true false i j=0→c i=c j):=by
  have h1:=zeroSum_of_positive D true true (fun i j hij=>(hs i j hij).1) (fun i j=>(c i+c j)^2)
  have h0:=zeroSum_of_positive D false false (fun i j hij=>(hs i j hij).2) (fun i j=>(c i+c j)^2)
  have hn:(N:R)^2≠0:=pow_ne_zero 2 (by exact_mod_cast hN.ne')
  have hb:correctedBiasExpression D c c=zeroSum D true false (fun i j=>(c i-c j)^2):=by
    unfold correctedBiasExpression
    simp only [sub_self,zero_pow (by norm_num:2≠0),sum_const_zero,h1,h0,zero_div,zero_add]
  have hvar:=(corrected_variance_bias_completed D hp N hN c c).1
  rw [hb] at hvar
  have he:expectation D (correctedVariance D N c c)-variance D (ht D N c c)=
      zeroSum D true false (fun i j=>(c i-c j)^2)/(N:R)^2:=
    (eq_div_iff hn).mpr (by simpa only [mul_comm] using hvar)
  refine ⟨he,?_⟩
  constructor
  · intro hEq
    apply (zeroSum_squares_eq_zero D true false c c).mp
    rw [hEq,sub_self,mul_zero] at hvar
    exact hvar.symm
  · intro hEq
    have hz:=(zeroSum_squares_eq_zero D true false c c).mpr hEq
    rw [hz,zero_div] at he
    exact sub_eq_zero.mp he

lemma support_repair_completed (D:Design Ω I R) (hp:positiveMarginals D)
    (hc:crossSupport D) (N:ℕ) (hN:0<N) (x z:I→R):
    expectation D (printedCovariance D x z)-covariance D (htTotal D true x) (htTotal D false z)=
      -(∑i,(x i-z i)^2)/2 ∧
    expectation D (printedCovariance D x z)≤covariance D (htTotal D true x) (htTotal D false z) ∧
    (N:R)^2*(expectation D (printedVariance D N x z)-variance D (ht D N x z))=
      (∑i,(x i-z i)^2)+zeroSum D true true (fun i j=>(x i+x j)^2)/2+
        zeroSum D false false (fun i j=>(z i+z j)^2)/2 ∧
    variance D (ht D N x z)≤expectation D (printedVariance D N x z) ∧
    ((∀i,x i=z i)→(∀i j,i≠j→0<joint D true true i j∧0<joint D false false i j)→
      expectation D (printedVariance D N x z)=variance D (ht D N x z)):=by
  have hcov:=corrected_covariance_bias_completed D hp x z
  have hvar:=corrected_variance_bias_completed D hp N hN x z
  rw [correctedCovariance_eq_printed D hc] at hcov
  rw [correctedVariance_eq_printed D hc] at hvar
  have hz:zeroSum D true false (fun i j=>(x i-z j)^2)=0:=zeroSum_of_positive D true false hc _
  refine ⟨by simpa only [hz,zero_div,sub_zero] using hcov.1,hcov.2,?_,hvar.2,?_⟩
  · simpa only [correctedBiasExpression,hz,add_zero] using hvar.1
  · intro heq hsame
    have hxz:x=z:=funext heq
    subst z
    have hh:=(corrected_sharp_null_completed D hp N hN x hsame).2.mpr
      (fun i j hij hj=>False.elim ((ne_of_gt (hc i j hij)) hj))
    rwa [correctedVariance_eq_printed D hc] at hh

lemma sum_squares_eq_zero (x z:I→R): (∑i,(x i-z i)^2)=0↔∀i,x i=z i:=by
  constructor
  · intro h i
    have hh:(x i-z i)^2≤∑j,(x j-z j)^2:=single_le_sum (fun j _=>sq_nonneg (x j-z j)) (mem_univ i)
    rw [h] at hh
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hh (sq_nonneg _)))
  · intro h
    simp_rw [h]
    simp

lemma appendixE_corrected_completed (D:Design Ω I R) (hp:positiveMarginals D)
    (hc:crossSupport D) (x z:I→R):
    expectation D (printedCovariance D x z)=covarianceBound D x z ∧
    expectation D (printedCovariance D x z)≤covariance D (htTotal D true x) (htTotal D false z) ∧
    (expectation D (printedCovariance D x z)=covariance D (htTotal D true x) (htTotal D false z)↔
      ∀i,x i=z i):=by
  have he:expectation D (printedCovariance D x z)=covarianceBound D x z:=by
    rw [expected_printed_covariance D hp,zeroSum_of_positive D true false hc,add_zero]
  have hg:=covariance_bound_gap D hp x z
  have hn:0≤∑i,(x i-z i)^2:=sum_nonneg (fun i _=>sq_nonneg _)
  refine ⟨he,by linarith,?_⟩
  constructor
  · intro hEq
    apply (sum_squares_eq_zero x z).mp
    linarith
  · intro hEq
    have hz:=(sum_squares_eq_zero x z).mpr hEq
    linarith

lemma expected_arm_diagonal (D:Design Ω I R) (a:Bool) (x z:I→R) (i:I):
    expectation D (fun w=>indicator D a w i*(1-marginal D a i)*
      (observed D x z w i/marginal D a i)^2)=
      marginal D a i*(1-marginal D a i)*((if a then x i else z i)/marginal D a i)^2:=by
  have he(w:Ω):indicator D a w i*(1-marginal D a i)*(observed D x z w i/marginal D a i)^2=
      (1-marginal D a i)*(indicator D a w i*(observed D x z w i/marginal D a i)^2):=by ring
  simp_rw [he]
  rw [expectation_const_mul,expected_scaled_square]
  ring

lemma expected_filtered_pair (D:Design Ω I R) (a:Bool) (x z:I→R) (i j:I):
    expectation D (fun w=>if 0<joint D a a i j then estimatedPair D a a x z w i j else 0)=
      if 0<joint D a a i j then pairCoeff D a a x z i j else 0:=by
  by_cases h:0<joint D a a i j
  · simp only [if_pos h]
    rw [expected_pair,if_neg (ne_of_gt h)]
  · simp [h,expectation]

lemma expected_arm_estimator (D:Design Ω I R) (hp:positiveMarginals D) (a:Bool) (x z:I→R):
    expectation D (armVarianceEstimator D a x z)=armVarianceBound D a (if a then x else z):=by
  unfold armVarianceEstimator
  rw [expectation_add,expectation_add,expectation_sum,expectation_offSum,expectation_zeroSum]
  simp_rw [expected_arm_diagonal,expected_filtered_pair,expectation_add,expected_half_square D hp]
  cases a <;>rfl

lemma filtered_pair_gap (D:Design Ω I R) (hD:probabilityDesign D) (hp:positiveMarginals D)
    (a:Bool) (y:I→R) (i j:I):
    (if 0<joint D a a i j then pairCoeff D a a y y i j else 0)=
      pairCoeff D a a y y i j+(if joint D a a i j=0 then y i*y j else 0):=by
  by_cases h:joint D a a i j=0
  · simp only [h,lt_self_iff_false,ite_false,ite_true,pairCoeff,zero_sub,ite_self]
    field_simp [marginal_ne D hp a i,marginal_ne D hp a j]
    ring
  · have hpJ:0<joint D a a i j:=lt_of_le_of_ne (joint_nonneg D hD a a i j) (Ne.symm h)
    simp [h,hpJ]

lemma arm_bound_gap (D:Design Ω I R) (hD:probabilityDesign D) (hp:positiveMarginals D)
    (a:Bool) (y:I→R):
    armVarianceBound D a y-variance D (htTotal D a y)=
      zeroSum D a a (fun i j=>(y i+y j)^2)/2:=by
  rw [ht_arm_variance]
  have he:armVarianceBound D a y=
      armVarianceExpression D a y+zeroSum D a a (fun i j=>y i*y j)+
        zeroSum D a a (fun i j=>y i^2/2+y j^2/2):=by
    unfold armVarianceBound armVarianceExpression
    have hh(i j:I):
        (if 0<joint D a a i j then
          (joint D a a i j-marginal D a i*marginal D a j)*(y i/marginal D a i)*(y j/marginal D a j) else 0)=
        (joint D a a i j-marginal D a i*marginal D a j)*(y i/marginal D a i)*(y j/marginal D a j)+
          (if joint D a a i j=0 then y i*y j else 0):=by
      simpa only [pairCoeff,ite_self] using filtered_pair_gap D hD hp a y i j
    simp_rw [hh]
    rw [offSum_add]
    unfold zeroSum
    ring
  rw [he]
  linear_combination zero_sum_plus_gap D a y

lemma arm_variance_corrected_completed (D:Design Ω I R) (hD:probabilityDesign D)
    (hp:positiveMarginals D) (a:Bool) (x z:I→R):
    let y:=if a then x else z
    armVarianceBound D a y-variance D (htTotal D a y)=
      zeroSum D a a (fun i j=>(y i+y j)^2)/2 ∧
    expectation D (armVarianceEstimator D a x z)=armVarianceBound D a y ∧
    variance D (htTotal D a y)≤expectation D (armVarianceEstimator D a x z) ∧
    ((∀i j,i≠j→0<joint D a a i j)→
      expectation D (armVarianceEstimator D a x z)=variance D (htTotal D a y)):=by
  let y:=if a then x else z
  have he:=expected_arm_estimator D hp a x z
  have hg:=arm_bound_gap D hD hp a y
  have hn:=zeroSum_squares_nonneg D a a (fun i j=>y i+y j)
  refine ⟨hg,he,?_,?_⟩
  · rw [he]
    linarith
  · intro hs
    have hz:=zeroSum_of_positive D a a hs (fun i j=>(y i+y j)^2)
    rw [hz,zero_div] at hg
    rw [he]
    exact sub_eq_zero.mp hg

lemma indicator_nonneg (D:Design Ω I R) (a:Bool) (w:Ω) (i:I):0 ≤ indicator D a w i:=by
  unfold indicator
  split_ifs <;>norm_num

lemma supported_zero_joint (D:Design Ω I R) (hD:probabilityDesign D) (w:Ω) (hw:0<D.weight w)
    (a b:Bool) (i j:I) (hj:joint D a b i j=0):
    indicator D a w i*indicator D b w j=0:=by
  have hn(v:Ω):0≤D.weight v*(indicator D a v i*indicator D b v j):=
    mul_nonneg (hD.1 v) (mul_nonneg (indicator_nonneg D a v i) (indicator_nonneg D b v j))
  have hh:D.weight w*(indicator D a w i*indicator D b w j)≤joint D a b i j:=by
    simpa only [joint,expectation,mul_assoc] using single_le_sum (fun v _=>hn v) (mem_univ w)
  have hz:D.weight w*(indicator D a w i*indicator D b w j)=0:=
    le_antisymm (by simpa only [hj] using hh) (hn w)
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hw)

lemma supported_pair_filter (D:Design Ω I R) (hD:probabilityDesign D) (w:Ω) (hw:0<D.weight w)
    (a:Bool) (x z:I→R) (i j:I):
    (if 0<joint D a a i j then estimatedPair D a a x z w i j else 0)=
      estimatedPair D a a x z w i j:=by
  by_cases h:0<joint D a a i j
  · simp [h]
  · have hj:joint D a a i j=0:=le_antisymm (not_lt.mp h) (joint_nonneg D hD a a i j)
    have hz:=supported_zero_joint D hD w hw a a i j hj
    simp [h,estimatedPair,hz]

lemma supported_raw_pair (D:Design Ω I R) (hD:probabilityDesign D) (w:Ω) (hw:0<D.weight w)
    (a b:Bool) (x z:I→R) (i j:I):
    rawPair D a b x z w i j=estimatedPair D a b x z w i j:=by
  by_cases h:joint D a b i j=0
  · have hz:=supported_zero_joint D hD w hw a b i j h
    simp [rawPair,estimatedPair,hz]
  · simp [rawPair,estimatedPair,epsilon,h]

lemma printed_variance_decomposition_supported (D:Design Ω I R) (hD:probabilityDesign D)
    (hp:positiveMarginals D) (N:ℕ) (x z:I→R) (w:Ω) (hw:0<D.weight w):
    printedVariance D N x z w=(armVarianceEstimator D true x z w+
      armVarianceEstimator D false x z w-2*printedCovariance D x z w)/(N:R)^2:=by
  have hcov:printedCovariance D x z w=
      offSum (fun i j=>estimatedPair D true false x z w i j)-
        (∑i,indicator D true w i*(observed D x z w i)^2/(2*marginal D true i))-
        (∑i,indicator D false w i*(observed D x z w i)^2/(2*marginal D false i)):=by
    change offSum (fun i j=>rawPair D true false x z w i j)-_-_=_
    simp_rw [supported_raw_pair D hD w hw]
  have hdiag(i:I):
      indicator D true w i*(observed D x z w i/marginal D true i)^2+
      indicator D false w i*(observed D x z w i/marginal D false i)^2=
      indicator D true w i*(1-marginal D true i)*(observed D x z w i/marginal D true i)^2+
      indicator D false w i*(1-marginal D false i)*(observed D x z w i/marginal D false i)^2+
      2*(indicator D true w i*(observed D x z w i)^2/(2*marginal D true i))+
      2*(indicator D false w i*(observed D x z w i)^2/(2*marginal D false i)):=by
    field_simp [marginal_ne D hp true i,marginal_ne D hp false i]
    ring
  rw [hcov]
  unfold printedVariance armVarianceEstimator
  simp_rw [supported_pair_filter D hD w hw,hdiag]
  simp only [sum_add_distrib,←mul_sum]
  rw [offSum_sub,offSum_add,offSum_const_mul]
  ring

lemma corrected_variance_decomposition_completed (D:Design Ω I R) (hD:probabilityDesign D)
    (hp:positiveMarginals D) (N:ℕ) (x z:I→R) (w:Ω) (hw:0<D.weight w):
    correctedVariance D N x z w=(armVarianceEstimator D true x z w+
      armVarianceEstimator D false x z w-2*correctedCovariance D x z w)/(N:R)^2:=by
  unfold correctedVariance correctedCovariance
  rw [printed_variance_decomposition_supported D hD hp N x z w hw]
  ring

lemma corrected_residual_variance_completed (D:Design Ω I R) (hp:positiveMarginals D)
    (N:ℕ) (hN:0<N) (x z r:I→R):
    (N:R)^2*(expectation D (correctedVariance D N (fun i=>x i-r i) (fun i=>z i-r i))-
      variance D (generalized D N x z (fun _=>r)))=
        correctedBiasExpression D (fun i=>x i-r i) (fun i=>z i-r i) ∧
    variance D (generalized D N x z (fun _=>r))≤
      expectation D (correctedVariance D N (fun i=>x i-r i) (fun i=>z i-r i)):=by
  have h:generalized D N x z (fun _=>r)=ht D N (fun i=>x i-r i) (fun i=>z i-r i):=
    funext (fun w=>generalized_residual D N x z (fun _=>r) w)
  rw [h]
  exact corrected_variance_bias_completed D hp N hN _ _

lemma support_residual_variance_completed (D:Design Ω I R) (hp:positiveMarginals D)
    (hc:crossSupport D) (N:ℕ) (hN:0<N) (x z r:I→R):
    variance D (generalized D N x z (fun _=>r))≤
      expectation D (printedVariance D N (fun i=>x i-r i) (fun i=>z i-r i)) ∧
    ((∀i,x i=z i)→(∀i j,i≠j→0<joint D true true i j∧0<joint D false false i j)→
      expectation D (printedVariance D N (fun i=>x i-r i) (fun i=>z i-r i))=
        variance D (generalized D N x z (fun _=>r))):=by
  have h:generalized D N x z (fun _=>r)=ht D N (fun i=>x i-r i) (fun i=>z i-r i):=
    funext (fun w=>generalized_residual D N x z (fun _=>r) w)
  rw [h]
  have hs:=support_repair_completed D hp hc N hN (fun i=>x i-r i) (fun i=>z i-r i)
  refine ⟨hs.2.2.2.1,?_⟩
  intro hn hj
  exact hs.2.2.2.2 (fun i=>by rw [hn i]) hj


end
end AronowAudit.P026.VarianceCompletion

namespace AronowAudit.P026
open Finset
variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

/-- P026-T2(c): exact bias of printed eq. [35], including its missing
cross-arm products. No positivity assumption on any joint is added. -/
theorem printed_variance_bias (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N : ℕ) (hN : 0 < N) (x z : I → ℝ) :
    (N : ℝ)^2 * (expectation D (printedVariance D N x z) - variance D (ht D N x z)) =
      (∑ i, (x i-z i)^2) + zeroSum D true true (fun i j => (x i+x j)^2) / 2 +
      zeroSum D false false (fun i j => (z i+z j)^2) / 2 -
      2 * zeroSum D true false (fun i j => x i*z j) := by
  exact VarianceCompletion.printed_variance_bias_completed D hp N hN x z

/-- P026-T2(d): the corrected covariance estimator has exactly the
negative half-sum of the within-cluster and unavailable cross-pair effect
squares as its bias, and consequently is nonpositively biased. -/
theorem corrected_covariance_bias (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (x z : I → ℝ) :
    expectation D (correctedCovariance D x z) -
      covariance D (htTotal D true x) (htTotal D false z) =
      -(∑ i, (x i-z i)^2) / 2 - zeroSum D true false (fun i j => (x i-z j)^2) / 2 ∧
    expectation D (correctedCovariance D x z) ≤
      covariance D (htTotal D true x) (htTotal D false z) := by
  exact VarianceCompletion.corrected_covariance_bias_completed D hp x z

/-- P026-T2(e): exact squared-gap identity and conservativeness of the
repaired eq. [35] for every assignment distribution with positive marginals. -/
theorem corrected_variance_bias (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N : ℕ) (hN : 0 < N) (x z : I → ℝ) :
    (N : ℝ)^2 * (expectation D (correctedVariance D N x z) - variance D (ht D N x z)) =
      correctedBiasExpression D x z ∧
    variance D (ht D N x z) ≤ expectation D (correctedVariance D N x z) := by
  exact VarianceCompletion.corrected_variance_bias_completed D hp N hN x z

/-- P026-T2(f): under the sharp null and positive same-arm joints,
the repaired variance bias is N⁻²∑_Z10(c_k-c_l)². Equality requires equal
cluster totals on every unavailable directed pair, not merely the sharp null. -/
theorem corrected_sharp_null (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N : ℕ) (hN : 0 < N) (c : I → ℝ)
    (hs : ∀ i j, i ≠ j → 0 < joint D true true i j ∧ 0 < joint D false false i j) :
    expectation D (correctedVariance D N c c) - variance D (ht D N c c) =
      zeroSum D true false (fun i j => (c i-c j)^2) / (N : ℝ)^2 ∧
    (expectation D (correctedVariance D N c c) = variance D (ht D N c c) ↔
      ∀ i j, i ≠ j → joint D true false i j = 0 → c i = c j) := by
  exact VarianceCompletion.corrected_sharp_null_completed D hp N hN c hs

/-- P026-T3(a)-(c): the assumption-only repair keeps eqs. [34]-[35]
and explicitly adds all directed cross-arm support. Its covariance bias is
the negative within-cluster squared gap, and its variance estimator is
conservative, with sharp-null equality under positive same-arm support. -/
theorem support_repair (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (hcross : crossSupport D) (N : ℕ) (hN : 0 < N)
    (x z : I → ℝ) :
    expectation D (printedCovariance D x z) - covariance D (htTotal D true x) (htTotal D false z) =
      -(∑ i, (x i-z i)^2) / 2 ∧
    expectation D (printedCovariance D x z) ≤ covariance D (htTotal D true x) (htTotal D false z) ∧
    (N : ℝ)^2 * (expectation D (printedVariance D N x z) - variance D (ht D N x z)) =
      (∑ i, (x i-z i)^2) + zeroSum D true true (fun i j => (x i+x j)^2) / 2 +
        zeroSum D false false (fun i j => (z i+z j)^2) / 2 ∧
    variance D (ht D N x z) ≤ expectation D (printedVariance D N x z) ∧
    ((∀ i, x i = z i) →
      (∀ i j, i ≠ j → 0 < joint D true true i j ∧ 0 < joint D false false i j) →
      expectation D (printedVariance D N x z) = variance D (ht D N x z)) := by
  exact VarianceCompletion.support_repair_completed D hp hcross N hN x z

/-- P026-T8(c,d): replacing Appendix E's copied display with eq. [34]
estimates [43] without bias under positive directed cross-arm support;
its covariance bias is nonpositive, with equality iff all cluster effects vanish. -/
theorem appendixE_corrected (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (hc : crossSupport D) (x z : I → ℝ) :
    expectation D (printedCovariance D x z) = covarianceBound D x z ∧
    expectation D (printedCovariance D x z) ≤ covariance D (htTotal D true x) (htTotal D false z) ∧
    (expectation D (printedCovariance D x z) = covariance D (htTotal D true x) (htTotal D false z) ↔
      ∀ i, x i = z i) := by
  exact VarianceCompletion.appendixE_corrected_completed D hp hc x z

/-- P026-T11(c)-(f): Appendix D with restored cluster primes; each arm
upper bound is estimated without bias, its gap is the unavailable same-arm
half-sum of squared pair sums, and the estimator is conservative. -/
theorem arm_variance_corrected (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (a : Bool) (x z : I → ℝ) :
    let y := if a then x else z
    armVarianceBound D a y - variance D (htTotal D a y) =
      zeroSum D a a (fun i j => (y i+y j)^2) / 2 ∧
    expectation D (armVarianceEstimator D a x z) = armVarianceBound D a y ∧
    variance D (htTotal D a y) ≤ expectation D (armVarianceEstimator D a x z) ∧
    ((∀ i j, i ≠ j → 0 < joint D a a i j) →
      expectation D (armVarianceEstimator D a x z) = variance D (htTotal D a y)) := by
  exact VarianceCompletion.arm_variance_corrected_completed D hD hp a x z

/-- P026-T2(e), supported-allocation equivalence: the corrected
effect-variance estimate equals N⁻²(V1_C-hat+V0_C-hat-2Cov_C^+-hat),
with eqs. [32]-[33], on every assignment of positive probability. -/
theorem corrected_variance_decomposition (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N : ℕ) (hN : 0 < N) (x z : I → ℝ)
    (w : Ω) (hw : 0 < D.weight w) :
    correctedVariance D N x z w=(armVarianceEstimator D true x z w+
      armVarianceEstimator D false x z w-2*correctedCovariance D x z w)/(N : ℝ)^2 := by
  exact VarianceCompletion.corrected_variance_decomposition_completed D hD hp N x z w hw

/-- P026-T2(g): for fixed prediction cluster totals r, apply the full
scope-preserving variance repair to residual potential outcomes. Its bias
is the same corrected squared-gap expression, and it is conservative for
the sampling variance of the generalized estimator itself. -/
theorem corrected_residual_variance (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (N : ℕ) (hN : 0 < N) (x z r : I → ℝ) :
    (N : ℝ)^2 * (expectation D (correctedVariance D N (fun i => x i-r i) (fun i => z i-r i))-
      variance D (generalized D N x z (fun _ => r))) =
        correctedBiasExpression D (fun i => x i-r i) (fun i => z i-r i) ∧
    variance D (generalized D N x z (fun _ => r)) ≤
      expectation D (correctedVariance D N (fun i => x i-r i) (fun i => z i-r i)) := by
  exact VarianceCompletion.corrected_residual_variance_completed D hp N hN x z r

/-- P026-T3(d): the assumption-only repair applies to fixed residual
predictions; with H+ it is conservative for Var(Δ_G-hat), and becomes
exactly unbiased under the sharp null and positive same-arm joints. -/
theorem support_residual_variance (D : Design Ω I ℝ) (hD : probabilityDesign D)
    (hp : positiveMarginals D) (hc : crossSupport D) (N : ℕ) (hN : 0 < N)
    (x z r : I → ℝ) :
    variance D (generalized D N x z (fun _ => r)) ≤
      expectation D (printedVariance D N (fun i => x i-r i) (fun i => z i-r i)) ∧
    ((∀ i, x i=z i) → (∀ i j, i ≠ j → 0 < joint D true true i j ∧ 0 < joint D false false i j) →
      expectation D (printedVariance D N (fun i => x i-r i) (fun i => z i-r i))=
        variance D (generalized D N x z (fun _ => r))) := by
  exact VarianceCompletion.support_residual_variance_completed D hp hc N hN x z r

end AronowAudit.P026

