import AronowAudit.P026.P026_VarianceCompletion
/-! Unconditional existence and uniqueness of the two actual logistic MLEs; exact finite-design moment clauses. Numerical interval certification is separate. -/
namespace AronowAudit.P026.LogitCompletion
open Finset
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option autoImplicit false


lemma sigmoid_eq_exp_div (t:ℝ):sigmoid t=Real.exp t/(1+Real.exp t):=by
  unfold sigmoid
  have hd:1+Real.exp t≠0:=ne_of_gt (by positivity)
  field_simp
  <;>ring

lemma log_sigmoid (t:ℝ):Real.log (sigmoid t)=t-Real.log (1+Real.exp t):=by
  rw [sigmoid_eq_exp_div,Real.log_div (ne_of_gt (Real.exp_pos t))
    (ne_of_gt (by positivity)),Real.log_exp]

lemma log_one_sub_sigmoid (t:ℝ):
    Real.log (1-sigmoid t)= -Real.log (1+Real.exp t):=by
  have h:1-sigmoid t=1/(1+Real.exp t):=by unfold sigmoid;ring
  rw [h,Real.log_div one_ne_zero (ne_of_gt (by positivity)),Real.log_one]
  ring

def linearPredictor (β:ℝ×ℝ) (i:Fin 16):ℝ:=β.1+β.2*(tableX i:ℝ)
def bernoulliTerm (y t:ℝ):ℝ:=y*t-Real.log (1+Real.exp t)
def trainingSet (b:Bool):Finset (Fin 16):=
  univ.filter (fun i:Fin 16=>if b then 6 ≤ i.val else i.val < 6)

lemma likelihood_eq (b:Bool) (β:ℝ×ℝ):
    logitLikelihood b β=∑i∈trainingSet b,bernoulliTerm (tableY i:ℝ) (linearPredictor β i):=by
  unfold logitLikelihood trainingSet
  apply sum_congr rfl
  intro i _
  rw [log_sigmoid,log_one_sub_sigmoid]
  unfold bernoulliTerm linearPredictor
  ring

lemma log_one_add_exp_nonneg (t:ℝ):0≤Real.log (1+Real.exp t):=by
  apply Real.log_nonneg
  have h:=Real.exp_pos t
  linarith

lemma self_le_log_one_add_exp (t:ℝ):t≤Real.log (1+Real.exp t):=by
  calc
    t=Real.log (Real.exp t):=(Real.log_exp t).symm
    _≤Real.log (1+Real.exp t):=Real.log_le_log (Real.exp_pos t) (by linarith)

lemma bernoulliTerm_zero_le (t:ℝ):bernoulliTerm 0 t≤0:=by
  unfold bernoulliTerm
  linarith [log_one_add_exp_nonneg t]
lemma bernoulliTerm_one_le (t:ℝ):bernoulliTerm 1 t≤0:=by
  unfold bernoulliTerm
  linarith [self_le_log_one_add_exp t]

lemma tableY_binary (i:Fin 16):(tableY i:ℝ)=0∨(tableY i:ℝ)=1:=by
  fin_cases i <;>norm_num [tableY]

lemma table_term_nonpos (β:ℝ×ℝ) (i:Fin 16):
    bernoulliTerm (tableY i:ℝ) (linearPredictor β i)≤0:=by
  rcases tableY_binary i with h|h
  · rw [h];exact bernoulliTerm_zero_le _
  · rw [h];exact bernoulliTerm_one_le _

lemma likelihood_le_term (b:Bool) (β:ℝ×ℝ) (i:Fin 16) (hi:i∈trainingSet b):
    logitLikelihood b β≤bernoulliTerm (tableY i:ℝ) (linearPredictor β i):=by
  rw [likelihood_eq]
  have h:=single_le_sum (s:=trainingSet b)
    (f:=fun j=> -bernoulliTerm (tableY j:ℝ) (linearPredictor β j))
    (fun j _=>neg_nonneg.mpr (table_term_nonpos β j)) hi
  rw [sum_neg_distrib] at h
  linarith


lemma likelihood_le_success (b:Bool) (β:ℝ×ℝ) (i:Fin 16)
    (hi:i∈trainingSet b) (hy:(tableY i:ℝ)=1):
    logitLikelihood b β≤linearPredictor β i:=by
  have h:=likelihood_le_term b β i hi
  rw [hy] at h
  unfold bernoulliTerm at h
  linarith [log_one_add_exp_nonneg (linearPredictor β i)]

lemma likelihood_le_failure (b:Bool) (β:ℝ×ℝ) (i:Fin 16)
    (hi:i∈trainingSet b) (hy:(tableY i:ℝ)=0):
    logitLikelihood b β≤ -linearPredictor β i:=by
  have h:=likelihood_le_term b β i hi
  rw [hy] at h
  unfold bernoulliTerm at h
  linarith [self_le_log_one_add_exp (linearPredictor β i)]

lemma likelihood_controls_parameters (b:Bool) (β:ℝ×ℝ):
    |β.1|≤ -3*logitLikelihood b β ∧ |β.2|≤ -2*logitLikelihood b β:=by
  cases b
  · have h0:=likelihood_le_success false β 1 (by decide) (by norm_num [tableY])
    have h4:=likelihood_le_success false β 0 (by decide) (by norm_num [tableY])
    have h2:=likelihood_le_failure false β 5 (by decide) (by norm_num [tableY])
    norm_num [linearPredictor,tableX] at h0 h4 h2
    constructor <;>rw [abs_le] <;>constructor <;>linarith
  · have h1:=likelihood_le_success true β 7 (by decide) (by norm_num [tableY])
    have h4:=likelihood_le_success true β 6 (by decide) (by norm_num [tableY])
    have h2:=likelihood_le_failure true β 8 (by decide) (by norm_num [tableY])
    norm_num [linearPredictor,tableX] at h1 h4 h2
    constructor <;>rw [abs_le] <;>constructor <;>linarith

lemma likelihood_continuous (b:Bool):Continuous (logitLikelihood b):=by
  have heq:logitLikelihood b=(fun β=>∑i∈trainingSet b,
      bernoulliTerm (tableY i:ℝ) (linearPredictor β i)):=funext (likelihood_eq b)
  rw [heq]
  apply continuous_finsetSum
  intro i _
  have hc:Continuous (fun β:ℝ×ℝ=>linearPredictor β i):=
    continuous_fst.add (continuous_snd.mul continuous_const)
  have hd:Continuous (fun β:ℝ×ℝ=>1+Real.exp (linearPredictor β i)):=
    continuous_const.add (Real.continuous_exp.comp hc)
  exact (continuous_const.mul hc).sub
    (hd.log (fun β=>by positivity))

lemma likelihood_zero_lower (b:Bool): -16≤logitLikelihood b (0,0):=by
  have hl:Real.log 2≤1:=by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  rw [likelihood_eq]
  have hc:(trainingSet b).card≤16:=by
    calc (trainingSet b).card≤Fintype.card (Fin 16):=card_le_univ _
         _=16:=by simp
  have hs:∑i∈trainingSet b,(-1:ℝ)≤
      ∑i∈trainingSet b,bernoulliTerm (tableY i:ℝ) (linearPredictor (0,0) i):=by
    apply sum_le_sum
    intro i _
    simp only [linearPredictor,zero_mul,zero_add,bernoulliTerm,mul_zero,Real.exp_zero]
    norm_num at *
    linarith
  simp only [sum_const,nsmul_eq_mul,mul_neg,mul_one] at hs
  have hcr:((trainingSet b).card:ℝ)≤16:=by exact_mod_cast hc
  linarith

lemma logit_maximizer_exists (b:Bool):∃β,logitMaximizer b β:=by
  let S:Set (ℝ×ℝ):=(Set.Icc (-100:ℝ) 100).prod (Set.Icc (-100:ℝ) 100)
  have hs:IsCompact S:=isCompact_Icc.prod isCompact_Icc
  have h0:((0,0):ℝ×ℝ)∈S:=by
    change ((-100:ℝ)≤0∧(0:ℝ)≤100)∧((-100:ℝ)≤0∧(0:ℝ)≤100)
    norm_num
  obtain ⟨β,hβ,hmax⟩:=hs.exists_isMaxOn ⟨(0,0),h0⟩ (likelihood_continuous b).continuousOn
  refine ⟨β,fun γ=>?_⟩
  by_cases hγ:γ∈S
  · exact hmax hγ
  · have hl:logitLikelihood b γ< -16:=by
      by_contra! hh
      obtain ⟨ha,hb⟩:=likelihood_controls_parameters b γ
      have h1:|γ.1|≤100:=by linarith
      have h2:|γ.2|≤100:=by linarith
      apply hγ
      exact ⟨abs_le.mp h1,abs_le.mp h2⟩
    exact le_trans (le_trans hl.le (likelihood_zero_lower b)) (hmax h0)

lemma sigmoid_strictMono:StrictMono sigmoid:=by
  intro x y hxy
  have h:=one_div_lt_one_div_of_lt (by positivity : 0<1+Real.exp x)
    (by linarith [Real.exp_strictMono hxy] : 1+Real.exp x<1+Real.exp y)
  unfold sigmoid
  linarith

lemma softplus_hasDerivAt (t:ℝ):
    HasDerivAt (fun s:ℝ=>Real.log (1+Real.exp s)) (sigmoid t) t:=by
  have h:=((Real.hasDerivAt_exp t).const_add 1).log
    (ne_of_gt (by positivity : 0<1+Real.exp t))
  convert h using 1
  rw [sigmoid_eq_exp_div]

lemma softplus_strictConvex:StrictConvexOn ℝ Set.univ (fun t:ℝ=>Real.log (1+Real.exp t)):=by
  apply StrictMono.strictConvexOn_univ_of_deriv
  · have hc:Continuous (fun t:ℝ=>1+Real.exp t):=continuous_const.add Real.continuous_exp
    exact hc.log (fun t=>by positivity)
  · simpa only [funext_iff] using
      (show StrictMono (fun t:ℝ=>deriv (fun s:ℝ=>Real.log (1+Real.exp s)) t) from
        fun x y hxy=>by simpa only [(softplus_hasDerivAt x).deriv,
          (softplus_hasDerivAt y).deriv] using sigmoid_strictMono hxy)

lemma bernoulliTerm_strictConcave (y:ℝ):StrictConcaveOn ℝ Set.univ (bernoulliTerm y):=by
  refine ⟨convex_univ,?_⟩
  intro x _ z _ hxz a b ha hb hab
  have h:=softplus_strictConvex.2 (Set.mem_univ x) (Set.mem_univ z) hxz ha hb hab
  simp only [bernoulliTerm,smul_eq_mul] at *
  nlinarith

lemma linearPredictor_combination (β γ:ℝ×ℝ) (a b:ℝ) (i:Fin 16):
    linearPredictor (a • β+b • γ) i=a*linearPredictor β i+b*linearPredictor γ i:=by
  simp only [linearPredictor,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

lemma training_separates_parameters (b:Bool) (β γ:ℝ×ℝ) (h:β≠γ):
    ∃i∈trainingSet b,linearPredictor β i≠linearPredictor γ i:=by
  by_contra! hn
  apply h
  cases b
  · have h0:=hn 1 (by decide)
    have h4:=hn 0 (by decide)
    norm_num [linearPredictor,tableX] at h0 h4
    apply Prod.ext <;>linarith
  · have h1:=hn 7 (by decide)
    have h4:=hn 6 (by decide)
    norm_num [linearPredictor,tableX] at h1 h4
    apply Prod.ext <;>linarith

lemma likelihood_strictConcave (k:Bool):StrictConcaveOn ℝ Set.univ (logitLikelihood k):=by
  refine ⟨convex_univ,?_⟩
  intro β _ γ _ hβγ a b ha hb hab
  obtain ⟨i,hi,hne⟩:=training_separates_parameters k β γ hβγ
  have hweak:∀j∈trainingSet k,
      a*bernoulliTerm (tableY j:ℝ) (linearPredictor β j)+
        b*bernoulliTerm (tableY j:ℝ) (linearPredictor γ j)≤
      bernoulliTerm (tableY j:ℝ) (linearPredictor (a • β+b • γ) j):=by
    intro j _
    rw [linearPredictor_combination]
    exact (bernoulliTerm_strictConcave (tableY j:ℝ)).concaveOn.2
      (Set.mem_univ _) (Set.mem_univ _) ha.le hb.le hab
  have hstrict:a*bernoulliTerm (tableY i:ℝ) (linearPredictor β i)+
      b*bernoulliTerm (tableY i:ℝ) (linearPredictor γ i)<
      bernoulliTerm (tableY i:ℝ) (linearPredictor (a • β+b • γ) i):=by
    rw [linearPredictor_combination]
    exact (bernoulliTerm_strictConcave (tableY i:ℝ)).2
      (Set.mem_univ _) (Set.mem_univ _) hne ha hb hab
  have hs:=sum_lt_sum hweak ⟨i,hi,hstrict⟩
  simpa only [likelihood_eq,sum_add_distrib,←mul_sum,smul_eq_mul] using hs

lemma logit_maximizer_unique (b:Bool):∃!β,logitMaximizer b β:=by
  obtain ⟨β,hβ⟩:=logit_maximizer_exists b
  refine ⟨β,hβ,?_⟩
  intro γ hγ
  exact (likelihood_strictConcave b).eq_of_isMaxOn (fun x _=>hγ x)
    (fun x _=>hβ x) (Set.mem_univ γ) (Set.mem_univ β)

lemma logitCoefficients_maximizer (b:Bool):logitMaximizer b (logitCoefficients b):=by
  unfold logitCoefficients
  rw [dif_pos (logit_maximizer_exists b)]
  exact Classical.choose_spec (logit_maximizer_exists b)

lemma real_table_marginal (a:Bool) (i:Fin 10):
    marginal realTableDesign a i=((marginal tableDesign a i:ℚ):ℝ):=by
  simp only [marginal,expectation,indicator,realTableDesign]
  push_cast
  apply sum_congr rfl
  intro w _
  split_ifs <;>simp_all

lemma real_table_joint (a b:Bool) (i j:Fin 10):
    joint realTableDesign a b i j=((joint tableDesign a b i j:ℚ):ℝ):=by
  simp only [joint,expectation,indicator,realTableDesign]
  push_cast
  apply sum_congr rfl
  intro w _
  by_cases hi:tableDesign.treatment w i=a <;>
    by_cases hj:tableDesign.treatment w j=b <;>simp [hi,hj]

lemma real_table_probability:probabilityDesign realTableDesign:=by
  refine ⟨?_,?_⟩
  · intro w
    change 0≤(tableDesign.weight w:ℝ)
    exact_mod_cast table_support.1.1 w
  · change (∑w,(tableDesign.weight w:ℝ))=1
    exact_mod_cast table_support.1.2

lemma real_table_positive:positiveMarginals realTableDesign:=by
  intro i
  rw [real_table_marginal,real_table_marginal]
  constructor
  · exact_mod_cast (table_support.2.1 i).1
  · exact_mod_cast (table_support.2.1 i).2

lemma real_table_cross:crossSupport realTableDesign:=by
  intro i j hij
  rw [real_table_joint]
  exact_mod_cast table_support.2.2.1 i j hij

lemma real_table_same:∀i j:Fin 10,i≠j→
    0<joint realTableDesign true true i j∧0<joint realTableDesign false false i j:=by
  intro i j hij
  obtain ⟨_,ht,hf,_⟩:=table_support.2.2.2.1 i j hij
  rw [real_table_joint,real_table_joint]
  constructor
  · exact_mod_cast (show (0:ℚ)<joint tableDesign true true i j by linarith)
  · exact_mod_cast (show (0:ℚ)<joint tableDesign false false i j by linarith)

lemma real_table_fixed_moments (r:Fin 10→ℝ):
    expectation realTableDesign (ht realTableDesign 16 r r)=0 ∧
    expectation realTableDesign (printedVariance realTableDesign 16 r r)=
      variance realTableDesign (ht realTableDesign 16 r r):=by
  have hu:=ht_unbiased realTableDesign real_table_probability real_table_positive
    16 (by norm_num) r r
  refine ⟨by simpa only [ate,sub_self,zero_div] using hu.2.2,?_⟩
  exact (support_repair realTableDesign real_table_probability real_table_positive
    real_table_cross 16 (by norm_num) r r).2.2.2.2 (fun _=>rfl) real_table_same

lemma logit_exact_moments:
    expectation realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual)=0 ∧
    expectation realTableDesign
      (printedVariance realTableDesign 16 tableLogitResidual tableLogitResidual)=
      variance realTableDesign (ht realTableDesign 16 tableLogitResidual tableLogitResidual):=
  real_table_fixed_moments tableLogitResidual

end
end AronowAudit.P026.LogitCompletion
