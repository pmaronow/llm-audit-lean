import AronowAudit.P026.P026_LogitGeometry
import AronowAudit.P026.P026_LogitCertificates
/-! Certified local likelihood curvature, actual score and Gram bounds, and unconditional enclosure of the unique actual MLEs. -/
namespace AronowAudit.P026.LogitCompletion
open Finset
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option autoImplicit false

lemma sigmoid_hasDerivAt (t:ℝ):
    HasDerivAt sigmoid (Real.exp t/(1+Real.exp t)^2) t:=by
  have h:= (Real.hasDerivAt_exp t).div ((Real.hasDerivAt_exp t).const_add 1)
    (ne_of_gt (by positivity : 0<1+Real.exp t))
  convert h using 1
  · funext s
    exact sigmoid_eq_exp_div s
  · ring

lemma exp_on_training_interval (t:ℝ) (ht:t∈Set.Icc (-2:ℝ) 3):
    1/16≤Real.exp t∧Real.exp t≤32:=by
  have h1:Real.exp 1≤3:=Real.exp_one_lt_three.le
  have h2:Real.exp 2≤9:=by
    calc Real.exp 2=(Real.exp 1)^2:=by simpa using Real.exp_nat_mul 1 2
         _≤3^2:=pow_le_pow_left₀ (Real.exp_pos 1).le h1 2
         _=9:=by norm_num
  have h3:Real.exp 3≤27:=by
    calc Real.exp 3=(Real.exp 1)^3:=by simpa using Real.exp_nat_mul 1 3
         _≤3^3:=pow_le_pow_left₀ (Real.exp_pos 1).le h1 3
         _=27:=by norm_num
  constructor
  · calc (1/16:ℝ)≤1/9:=by norm_num
         _≤1/Real.exp 2:=one_div_le_one_div_of_le (Real.exp_pos 2) h2
         _=Real.exp (-2):=by rw [Real.exp_neg,one_div]
         _≤Real.exp t:=Real.exp_le_exp.mpr ht.1
  · exact (Real.exp_le_exp.mpr ht.2).trans (by linarith)

lemma sigmoid_derivative_lower (t:ℝ) (ht:t∈Set.Icc (-2:ℝ) 3):
    1/128≤Real.exp t/(1+Real.exp t)^2:=by
  obtain ⟨hl,hu⟩:=exp_on_training_interval t ht
  have hp:=mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)
  have hd:0<(1+Real.exp t)^2:=sq_pos_of_pos (by positivity)
  rw [le_div_iff₀ hd]
  nlinarith

def adjustedSoftplus (t:ℝ):ℝ:=Real.log (1+Real.exp t)-t^2/256
def adjustedDerivative (t:ℝ):ℝ:=sigmoid t-t/128

lemma adjusted_hasDerivAt (t:ℝ):HasDerivAt adjustedSoftplus (adjustedDerivative t) t:=by
  have h:= (softplus_hasDerivAt t).sub (((hasDerivAt_id t).pow 2).div_const 256)
  unfold adjustedSoftplus adjustedDerivative
  convert h using 1
  · funext s
    simp only [Pi.sub_apply,Pi.pow_apply,id_eq]
  · norm_num [id_eq]
    ring

lemma adjusted_derivative_hasDerivAt (t:ℝ):
    HasDerivAt adjustedDerivative (Real.exp t/(1+Real.exp t)^2-1/128) t:=by
  exact (sigmoid_hasDerivAt t).sub ((hasDerivAt_id t).div_const 128)

lemma adjusted_convex:ConvexOn ℝ (Set.Icc (-2:ℝ) 3) adjustedSoftplus:=by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f':=adjustedDerivative)
    (f'':=fun t=>Real.exp t/(1+Real.exp t)^2-1/128) (convex_Icc _ _)
  · have hs:Continuous (fun t:ℝ=>Real.log (1+Real.exp t)):=by
      exact (continuous_const.add Real.continuous_exp).log (fun t=>by
        change 1+Real.exp t≠0
        positivity)
    exact (hs.sub ((continuous_id.pow 2).div_const 256)).continuousOn
  · intro t _
    exact (adjusted_hasDerivAt t).hasDerivWithinAt
  · intro t _
    exact (adjusted_derivative_hasDerivAt t).hasDerivWithinAt
  · intro t ht
    exact sub_nonneg.mpr (sigmoid_derivative_lower t (interior_subset ht))

lemma convex_tangent {S:Set ℝ} {f:ℝ→ℝ} (hf:ConvexOn ℝ S f)
    (s t d:ℝ) (hs:s∈S) (ht:t∈S) (hd:HasDerivAt f d s):
    f s+d*(t-s)≤f t:=by
  rcases lt_trichotomy s t with h|h|h
  · have hh:=hf.le_slope_of_hasDerivAt hs ht h hd
    rw [slope_def_field,le_div_iff₀ (sub_pos.mpr h)] at hh
    linarith
  · subst t
    simp
  · have hh:=hf.slope_le_of_hasDerivAt ht hs h hd
    rw [slope_def_field,div_le_iff₀ (sub_pos.mpr h)] at hh
    nlinarith

lemma softplus_quadratic_lower (s t:ℝ) (hs:s∈Set.Icc (-2:ℝ) 3)
    (ht:t∈Set.Icc (-2:ℝ) 3):
    Real.log (1+Real.exp s)+sigmoid s*(t-s)+(t-s)^2/256≤Real.log (1+Real.exp t):=by
  have h:=convex_tangent adjusted_convex s t (adjustedDerivative s) hs ht (adjusted_hasDerivAt s)
  simp only [adjustedSoftplus,adjustedDerivative] at h
  nlinarith

lemma training_gram_lower (k:Bool) (a b:ℝ):
    (a^2+b^2)/4≤∑i∈trainingSet k,(a+b*(tableX i:ℝ))^2:=by
  cases k <;>norm_num [trainingSet,Finset.sum_filter,Fin.sum_univ_succ,tableX]
  · nlinarith [sq_nonneg (a+3*b),sq_nonneg a,sq_nonneg b]
  · nlinarith [sq_nonneg (9*a+28*b),sq_nonneg a,sq_nonneg b]

def score0 (k:Bool) (c:ℝ×ℝ):ℝ:=
  ∑i∈trainingSet k,((tableY i:ℝ)-sigmoid (linearPredictor c i))
def score1 (k:Bool) (c:ℝ×ℝ):ℝ:=
  ∑i∈trainingSet k,(tableX i:ℝ)*((tableY i:ℝ)-sigmoid (linearPredictor c i))

lemma score_sum_linear (k:Bool) (c:ℝ×ℝ) (a b:ℝ):
    (∑i∈trainingSet k,((tableY i:ℝ)-sigmoid (linearPredictor c i))*(a+b*(tableX i:ℝ)))=
      score0 k c*a+score1 k c*b:=by
  calc
    _=(∑i∈trainingSet k,(((tableY i:ℝ)-sigmoid (linearPredictor c i))*a+
      ((tableX i:ℝ)*((tableY i:ℝ)-sigmoid (linearPredictor c i)))*b)):=by
      apply sum_congr rfl
      intro i _
      ring
    _= _:=by rw [sum_add_distrib,←sum_mul,←sum_mul];rfl

lemma likelihood_quadratic_upper (k:Bool) (c β:ℝ×ℝ)
    (hc:∀i∈trainingSet k,linearPredictor c i∈Set.Icc (-2:ℝ) 3)
    (hβ:∀i∈trainingSet k,linearPredictor β i∈Set.Icc (-2:ℝ) 3):
    logitLikelihood k β≤logitLikelihood k c+score0 k c*(β.1-c.1)+score1 k c*(β.2-c.2)-
      ((β.1-c.1)^2+(β.2-c.2)^2)/1024:=by
  have hs:∀i∈trainingSet k,
      bernoulliTerm (tableY i:ℝ) (linearPredictor β i)≤
        bernoulliTerm (tableY i:ℝ) (linearPredictor c i)+
        ((tableY i:ℝ)-sigmoid (linearPredictor c i))*
          ((β.1-c.1)+(β.2-c.2)*(tableX i:ℝ))-
        ((β.1-c.1)+(β.2-c.2)*(tableX i:ℝ))^2/256:=by
    intro i hi
    have h:=softplus_quadratic_lower _ _ (hc i hi) (hβ i hi)
    have he:linearPredictor β i-linearPredictor c i=
        (β.1-c.1)+(β.2-c.2)*(tableX i:ℝ):=by unfold linearPredictor;ring
    rw [he] at h
    have hey:=congrArg (fun v:ℝ=>(tableY i:ℝ)*v) he
    unfold bernoulliTerm
    nlinarith [hey]
  have hsum:=sum_le_sum hs
  simp only [sum_sub_distrib,sum_add_distrib] at hsum
  rw [←sum_div] at hsum
  rw [←likelihood_eq k β,←likelihood_eq k c,
    score_sum_linear k c (β.1-c.1) (β.2-c.2)] at hsum
  have hg:=training_gram_lower k (β.1-c.1) (β.2-c.2)
  linarith

lemma center_score_bounds (k:Bool):
    |score0 k (LogitCertificates.center k)|≤(1/100000000000000:ℝ) ∧
    |score1 k (LogitCertificates.center k)|≤(1/100000000000000:ℝ):=by
  cases k
  · have h:=LogitCertificates.score_false_bounds
    simp only [abs_le] at h ⊢
    norm_num [score0,score1,trainingSet,Finset.sum_filter,Fin.sum_univ_succ,
      tableY,tableX,linearPredictor,LogitCertificates.center,sigmoid_eq_exp_div,
      LogitCertificates.logisticRatio] at h ⊢
    constructor <;>constructor <;>linarith [h.1.1,h.1.2,h.2.1,h.2.2]
  · have h:=LogitCertificates.score_true_bounds
    simp only [abs_le] at h ⊢
    norm_num [score0,score1,trainingSet,Finset.sum_filter,Fin.sum_univ_succ,
      tableY,tableX,linearPredictor,LogitCertificates.center,sigmoid_eq_exp_div,
      LogitCertificates.logisticRatio] at h ⊢
    constructor <;>constructor <;>linarith [h.1.1,h.1.2,h.2.1,h.2.2]

lemma maximizer_in_box (L:(ℝ×ℝ)→ℝ) (hL:ConcaveOn ℝ Set.univ L)
    (c β:ℝ×ℝ) (hβ:∀γ,L γ≤L β) (r:ℝ) (hr:0<r)
    (hboundary:∀γ:ℝ×ℝ,max |γ.1-c.1| |γ.2-c.2|=r→L γ<L c):
    max |β.1-c.1| |β.2-c.2|<r:=by
  by_contra! hnot
  let d:=max |β.1-c.1| |β.2-c.2|
  have hd:0<d:=hr.trans_le hnot
  let t:=r/d
  have ht:0<t:=div_pos hr hd
  have ht1:t≤1:=(div_le_one hd).mpr hnot
  let γ:ℝ×ℝ:=(1-t) • c+t • β
  have hγ1:γ.1-c.1=t*(β.1-c.1):=by simp [γ];ring
  have hγ2:γ.2-c.2=t*(β.2-c.2):=by simp [γ];ring
  have hγ:max |γ.1-c.1| |γ.2-c.2|=r:=by
    rw [hγ1,hγ2,abs_mul,abs_mul,abs_of_pos ht,←mul_max_of_nonneg _ _ ht.le]
    change (r/d)*d=r
    exact div_mul_cancel₀ r hd.ne'
  have hc:=hL.2 (Set.mem_univ c) (Set.mem_univ β) (sub_nonneg.mpr ht1) ht.le
    (by ring : (1-t)+t=1)
  have hcb:=hβ c
  have hcl:L c≤L γ:=by
    change (1-t)*L c+t*L β≤L γ at hc
    nlinarith
  exact (not_lt_of_ge hcl) (hboundary γ hγ)

lemma predictor_near_center (k:Bool) (β:ℝ×ℝ)
    (h1:|β.1-(LogitCertificates.center k).1|≤(1/1000:ℝ))
    (h2:|β.2-(LogitCertificates.center k).2|≤(1/1000:ℝ)) (i:Fin 16):
    linearPredictor β i∈Set.Icc (-2:ℝ) 3:=by
  obtain ⟨h1a,h1b⟩:=abs_le.mp h1
  obtain ⟨h2a,h2b⟩:=abs_le.mp h2
  cases k <;>fin_cases i <;>
    norm_num [LogitCertificates.center,linearPredictor,tableX] at * <;>
    constructor <;>linarith

lemma center_predictor_interval (k:Bool) (i:Fin 16):
    linearPredictor (LogitCertificates.center k) i∈Set.Icc (-2:ℝ) 3:=by
  exact predictor_near_center k _ (by norm_num) (by norm_num) i

lemma logit_coefficient_enclosure (k:Bool):
    |(logitCoefficients k).1-(LogitCertificates.center k).1|≤(1/1000000000:ℝ) ∧
    |(logitCoefficients k).2-(LogitCertificates.center k).2|≤(1/1000000000:ℝ):=by
  let c:=LogitCertificates.center k
  let r:ℝ:=1/1000000000
  have hr:0<r:=by norm_num [r]
  have hb:∀γ:ℝ×ℝ,max |γ.1-c.1| |γ.2-c.2|=r→logitLikelihood k γ<logitLikelihood k c:=by
    intro γ hγ
    have ha:|γ.1-c.1|≤r:=by
      calc |γ.1-c.1|≤ max |γ.1-c.1| |γ.2-c.2|:=le_max_left _ _
           _=r:=hγ
    have hb:|γ.2-c.2|≤r:=by
      calc |γ.2-c.2|≤ max |γ.1-c.1| |γ.2-c.2|:=le_max_right _ _
           _=r:=hγ
    have hnear1:|γ.1-(LogitCertificates.center k).1|≤(1/1000:ℝ):=by
      change |γ.1-c.1|≤_
      exact ha.trans (by norm_num [r])
    have hnear2:|γ.2-(LogitCertificates.center k).2|≤(1/1000:ℝ):=by
      change |γ.2-c.2|≤_
      exact hb.trans (by norm_num [r])
    have hu:=likelihood_quadratic_upper k c γ (fun i _=>center_predictor_interval k i)
      (fun i _=>predictor_near_center k γ hnear1 hnear2 i)
    obtain ⟨hg0,hg1⟩:=center_score_bounds k
    have hp0:score0 k c*(γ.1-c.1)≤(1/100000000000000:ℝ)*r:=by
      calc _≤|score0 k c*(γ.1-c.1)|:=le_abs_self _
           _=|score0 k c| * |γ.1-c.1|:=abs_mul _ _
           _≤_:=mul_le_mul hg0 ha (abs_nonneg _) (by norm_num)
    have hp1:score1 k c*(γ.2-c.2)≤(1/100000000000000:ℝ)*r:=by
      calc _≤|score1 k c*(γ.2-c.2)|:=le_abs_self _
           _=|score1 k c| * |γ.2-c.2|:=abs_mul _ _
           _≤_:=mul_le_mul hg1 hb (abs_nonneg _) (by norm_num)
    have hn:r^2≤(γ.1-c.1)^2+(γ.2-c.2)^2:=by
      rcases le_total |γ.1-c.1| |γ.2-c.2| with h|h
      · have he:|γ.2-c.2|=r:=by simpa only [max_eq_right h] using hγ
        have he2:(γ.2-c.2)^2=r^2:=by rw [←sq_abs (γ.2-c.2),he]
        nlinarith [sq_nonneg (γ.1-c.1)]
      · have he:|γ.1-c.1|=r:=by simpa only [max_eq_left h] using hγ
        have he2:(γ.1-c.1)^2=r^2:=by rw [←sq_abs (γ.1-c.1),he]
        nlinarith [sq_nonneg (γ.2-c.2)]
    norm_num [r] at *
    nlinarith
  have hm:=maximizer_in_box (logitLikelihood k) (likelihood_strictConcave k).concaveOn c
    (logitCoefficients k) (logitCoefficients_maximizer k) r hr hb
  exact ⟨((le_max_left _ _).trans hm.le),((le_max_right _ _).trans hm.le)⟩

lemma logit_quoted_coefficient_bounds:
    |(logitCoefficients true).1-(-11201076/10000000)|≤(5/10000000:ℝ) ∧
    |(logitCoefficients true).2-(5657586/10000000)|≤(5/10000000:ℝ) ∧
    |(logitCoefficients false).1-(10843223/10000000)|≤(5/10000000:ℝ) ∧
    |(logitCoefficients false).2-(2280259/10000000)|≤(5/10000000:ℝ):=by
  obtain ⟨ht0,ht1⟩:=logit_coefficient_enclosure true
  obtain ⟨hf0,hf1⟩:=logit_coefficient_enclosure false
  norm_num [LogitCertificates.center] at ht0 ht1 hf0 hf1 ⊢
  constructor
  · have h:=abs_sub_le (logitCoefficients true).1 (-1120107551952095111/1000000000000000000:ℝ) (-11201076/10000000)
    norm_num at h
    linarith
  constructor
  · have h:=abs_sub_le (logitCoefficients true).2 (565758555764892319/1000000000000000000:ℝ) (5657586/10000000)
    norm_num at h
    linarith
  constructor
  · have h:=abs_sub_le (logitCoefficients false).1 (1084322295119421469/1000000000000000000:ℝ) (10843223/10000000)
    norm_num at h
    linarith
  · have h:=abs_sub_le (logitCoefficients false).2 (228025945308092530/1000000000000000000:ℝ) (2280259/10000000)
    norm_num at h
    linarith

end
end AronowAudit.P026.LogitCompletion
