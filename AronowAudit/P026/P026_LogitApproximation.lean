import AronowAudit.P026.P026_LogitEnclosure
import AronowAudit.P026.P026_LogitCenterData
/-! Global sigmoid Lipschitz control and certified approximation of every actual logistic cluster residual. -/
namespace AronowAudit.P026.LogitCompletion
open Finset
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option autoImplicit false

lemma sigmoid_sub_le (s t:ℝ):|sigmoid t-sigmoid s|≤(1/4:ℝ)* |t-s|:=by
  have hb:∀x:ℝ,‖Real.exp x/(1+Real.exp x)^2‖≤(1/4:ℝ):=by
    intro x
    have hd:0<(1+Real.exp x)^2:=sq_pos_of_pos (by positivity)
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (Real.exp_pos x).le (sq_nonneg _)),
      div_le_iff₀ hd]
    nlinarith [sq_nonneg (Real.exp x-1)]
  have h:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s:=Set.univ) (f:=sigmoid) (f':=fun x:ℝ=>Real.exp x/(1+Real.exp x)^2)
    (fun x _=>(sigmoid_hasDerivAt x).hasDerivWithinAt) (fun x _=>hb x)
    convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using h

lemma tableX_range (i:Fin 16):0≤(tableX i:ℝ)∧(tableX i:ℝ)≤5:=by
  fin_cases i <;>norm_num [tableX]

lemma actual_prediction_center_error (i:Fin 16):
    |tableLogitPrediction i-sigmoid (linearPredictor (LogitCertificates.center (decide (i.val<6))) i)|≤
      (3/2000000000:ℝ):=by
  let k:=decide (i.val<6)
  obtain ⟨ha,hb⟩:=logit_coefficient_enclosure k
  obtain ⟨hX0,hX5⟩:=tableX_range i
  have hlin:|linearPredictor (logitCoefficients k) i-linearPredictor (LogitCertificates.center k) i|≤
      (6/1000000000:ℝ):=by
    have he:linearPredictor (logitCoefficients k) i-linearPredictor (LogitCertificates.center k) i=
        ((logitCoefficients k).1-(LogitCertificates.center k).1)+
        ((logitCoefficients k).2-(LogitCertificates.center k).2)*(tableX i:ℝ):=by
      unfold linearPredictor
      ring
    rw [he]
    calc
      _≤ |(logitCoefficients k).1-(LogitCertificates.center k).1| +
        |((logitCoefficients k).2-(LogitCertificates.center k).2)*(tableX i:ℝ)|:=abs_add_le _ _
      _=|(logitCoefficients k).1-(LogitCertificates.center k).1| +
        |(logitCoefficients k).2-(LogitCertificates.center k).2| *(tableX i:ℝ):=by
        rw [abs_mul,abs_of_nonneg hX0]
      _≤(1/1000000000:ℝ)+(1/1000000000:ℝ)*5:=
        add_le_add ha (mul_le_mul hb hX5 hX0 (by norm_num))
      _= _:=by norm_num
  have hs:=sigmoid_sub_le (linearPredictor (LogitCertificates.center k) i)
    (linearPredictor (logitCoefficients k) i)
  change |sigmoid (linearPredictor (logitCoefficients k) i)-
    sigmoid (linearPredictor (LogitCertificates.center k) i)|≤_
  exact hs.trans (by nlinarith)

lemma center_prediction_approximation (i:Fin 16):
    |sigmoid (linearPredictor (LogitCertificates.center (decide (i.val<6))) i)-
      ((logitApproxPrediction i:ℚ):ℝ)|≤(1/1000000000000:ℝ):=by
  fin_cases i
  · have h:=LogitCertificates.probability_true_4_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_true_0_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_true_4_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_true_1_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_true_4_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_true_2_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_false_4_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_false_1_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_false_2_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_false_5_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_false_4_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_false_1_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_false_4_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_false_2_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_false_2_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]
  · have h:=LogitCertificates.probability_false_3_bounds
    norm_num [linearPredictor,LogitCertificates.center,tableX,logitApproxPrediction,
      sigmoid_eq_exp_div,LogitCertificates.logisticRatio] at h ⊢
    rw [abs_le]
    constructor <;>linarith [h.1,h.2]

lemma actual_prediction_approximation (i:Fin 16):
    |tableLogitPrediction i-((logitApproxPrediction i:ℚ):ℝ)|≤(1501/1000000000000:ℝ):=by
  have h:=abs_sub_le (tableLogitPrediction i)
    (sigmoid (linearPredictor (LogitCertificates.center (decide (i.val<6))) i))
    ((logitApproxPrediction i:ℚ):ℝ)
  have h1:=actual_prediction_center_error i
  have h2:=center_prediction_approximation i
  linarith

lemma approximate_residual_real (k:Fin 10):
    ((logitApproxResidual k:ℚ):ℝ)=clusterTotal tableCluster
      (fun i=>(tableY i:ℝ)-((logitApproxPrediction i:ℚ):ℝ)) k:=by
  rw [←logitApproxResidual_aggregation k]
  unfold clusterTotal
  push_cast
  rfl

lemma table_cluster_size : ∀k:Fin 10,(univ.filter (fun i:Fin 16=>tableCluster i=k)).card≤3:=by
  decide +kernel

lemma actual_residual_approximation (k:Fin 10):
    |tableLogitResidual k-((logitApproxResidual k:ℚ):ℝ)|≤(1/200000000:ℝ):=by
  rw [approximate_residual_real]
  unfold tableLogitResidual clusterTotal
  rw [←sum_sub_distrib]
  have he:(∑i∈univ.filter (fun i:Fin 16=>tableCluster i=k),
      (((tableY i:ℝ)-tableLogitPrediction i)-((tableY i:ℝ)-((logitApproxPrediction i:ℚ):ℝ))))=
      ∑i∈univ.filter (fun i:Fin 16=>tableCluster i=k),
        (((logitApproxPrediction i:ℚ):ℝ)-tableLogitPrediction i):=by
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  calc
    _≤∑i∈univ.filter (fun i:Fin 16=>tableCluster i=k),
      |((logitApproxPrediction i:ℚ):ℝ)-tableLogitPrediction i|:=abs_sum_le_sum_abs _ _
    _≤∑i∈univ.filter (fun i:Fin 16=>tableCluster i=k),(1501/1000000000000:ℝ):=by
      apply sum_le_sum
      intro i _
      rw [abs_sub_comm]
      exact actual_prediction_approximation i
    _=((univ.filter (fun i:Fin 16=>tableCluster i=k)).card:ℝ)*(1501/1000000000000):=by
      simp only [sum_const,nsmul_eq_mul]
    _≤3*(1501/1000000000000:ℝ):=mul_le_mul_of_nonneg_right
      (by exact_mod_cast table_cluster_size k) (by norm_num)
    _≤_:=by norm_num

lemma actual_residual_bound (k:Fin 10):|tableLogitResidual k|≤1:=by
  have hc:|((logitApproxResidual k:ℚ):ℝ)|≤(999/1000:ℝ):=by
    have hh:((|logitApproxResidual k|:ℚ):ℝ)≤((999/1000:ℚ):ℝ):=
      Rat.cast_le.mpr (logitApproxResidual_bound k)
    norm_num only [Rat.cast_abs,Rat.cast_div,Rat.cast_ofNat] at hh
    exact hh
  have he:=actual_residual_approximation k
  calc
    |tableLogitResidual k|=|tableLogitResidual k-((logitApproxResidual k:ℚ):ℝ)+
      ((logitApproxResidual k:ℚ):ℝ)|:=by congr 1;ring
    _≤ |tableLogitResidual k-((logitApproxResidual k:ℚ):ℝ)| +
      |((logitApproxResidual k:ℚ):ℝ)|:=abs_add_le _ _
    _≤(1/200000000:ℝ)+999/1000:=add_le_add he hc
    _≤1:=by norm_num

end
end AronowAudit.P026.LogitCompletion
