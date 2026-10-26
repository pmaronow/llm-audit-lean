import AronowAudit.P011.P011_DataMatrixCompletion
namespace AronowAudit.P011.SignCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

@[simp] lemma weighted_value {n:ℕ} (y:Fin n→ℝ) (i:Fin n):weighted (signModel n) y i=y i:=by simp [weighted,signModel]
@[simp] lemma family_model (k:ℕ):signFamily.model k=signModel (k+1):=rfl
@[simp] lemma family_size (k:ℕ):signFamily.size k=k+1:=rfl
lemma betaHat_value {n:ℕ}:betaHat (signModel n)=(average:(Fin n→ℝ)→ℝ):=by
  funext y
  change average (weighted (signModel n) y)=average y
  apply congrArg average
  funext i
  exact weighted_value y i
lemma beta_zero (n:ℕ):beta (signModel n)=0:=by rw [beta,betaHat_value];exact DataMatrixCompletion.average_mean
lemma average_memLp (n:ℕ):MemLp (average:(Fin n→ℝ)→ℝ) 2 (signModel n).law:=by
  let : IsProbabilityMeasure (signModel n).law:=(signModel n).probability
  unfold average
  simpa only [div_eq_mul_inv] using
    (memLp_finsetSum Finset.univ (fun i _=>DataMatrixCompletion.coordinate_memLp i)).mul_const ((n:ℝ)⁻¹)
lemma scaled_variance {n:ℕ} (hn:0<n):(n:ℝ)*var (signModel n) (betaHat (signModel n))=1:=by
  have hv:=DataMatrixCompletion.average_variance hn
  rw [ProbabilityTheory.variance_eq_integral (by unfold average;fun_prop:Measurable (average:(Fin n→ℝ)→ℝ)).aemeasurable] at hv
  change var (signModel n) average=1/(n:ℝ) at hv
  rw [betaHat_value,hv]
  exact mul_one_div_cancel (by exact_mod_cast hn.ne')
lemma moment {n:ℕ} (hn:0<n):expectation (signModel n) (fun y=>betaHat (signModel n) y^2)=1/(n:ℝ):=by
  rw [betaHat_value]
  have hv:=DataMatrixCompletion.average_variance hn
  rw [ProbabilityTheory.variance_eq_integral (by unfold average;fun_prop:Measurable (average:(Fin n→ℝ)→ℝ)).aemeasurable] at hv
  have hm:(∫y,average y∂(signModel n).law)=0:=DataMatrixCompletion.average_mean
  simpa only [hm,sub_zero,expectation] using hv
lemma scaling_valid:Scaling signFamily 1 1 1 2∧Valid signFamily:=by
  refine ⟨?_,?_⟩
  · refine ⟨?_,by norm_num,by norm_num,by norm_num,by norm_num,?_,?_,?_,?_,?_⟩
    · constructor
      · intro a b hab;exact Nat.succ_le_succ hab
      · intro k;exact ⟨Fin.castSuccEmb,fun _ _=>rfl⟩
    · intro k
      exact uniform_coordinate_dependency Bool (fun _=>sign) (fun _=>measurable_of_finite _)
    · intro k
      change ∀ᵐ y∂(signModel (k+1)).law,∀i,|weighted (signModel (k+1)) y i-beta (signModel (k+1))|≤1
      rw [beta_zero]
      filter_upwards [DataMatrixCompletion.ae_signs (k+1)] with y hy i
      rcases hy i with hi|hi <;> simp [weighted_value,hi]
    · intro k i
      simp [degree,signFamily,signModel,emptyGraph]
    · have he:(fun k=>(signFamily.size k:ℝ)*var (signFamily.model k) (betaHat (signFamily.model k)))=fun _=>(1:ℝ):=
        funext fun k=>scaled_variance (Nat.succ_pos k)
      rw [he];exact tendsto_const_nhds
    · intro k i;change |(1:ℝ)|<2;norm_num
  · intro k
    constructor
    · intro i j hij;simp [signFamily,signModel,emptyGraph] at hij
    · intro i;simp [degree,signFamily,signModel,emptyGraph]
lemma V2_value {n:ℕ} (hn:0<n) (x:Fin n→ℝ) (hx:∀i,x i=1∨x i=-1):
    (n:ℝ)*V2 (emptyGraph n) x=1-average x^2:=by
  have hsum:(∑i,x i^2)=(n:ℝ):=by
    have hs (i:Fin n):x i^2=1:=by rcases hx i with h|h <;> rw [h] <;> norm_num
    simp [hs]
  unfold V2 sampleVariance
  simp only [adjacency,emptyGraph,Bool.false_eq_true,ite_false,Finset.sum_const_zero,zero_div,add_zero,mul_one]
  rw [DenseCompletion.centered_sq hn,hsum]
  field_simp <;> ring
lemma finite_lower (k:ℕ) (ε:ℝ) (hε:0<ε):1-1/((k+1:ℝ)*ε)≤probability (signFamily.model k)
    {y| |(k+1:ℝ)*V2 (signFamily.model k).G (weighted (signFamily.model k) y)-1| <ε}:=by
  let μ:Measure (Fin (k+1)→ℝ):=(signModel (k+1)).law
  let : IsProbabilityMeasure μ:=(signModel (k+1)).probability
  have hm:(∫y,average y∂μ)=0:=DataMatrixCompletion.average_mean
  have hge:=meas_ge_le_variance_div_sq (average_memLp (k+1)) (Real.sqrt_pos.mpr hε)
  rw [hm,DataMatrixCompletion.average_variance (Nat.succ_pos k),Real.sq_sqrt hε.le] at hge
  have hprob:μ.real {y:Fin (k+1)→ℝ| ε≤average y^2}≤1/((k+1:ℝ)*ε):=by
    have hs:{y:Fin (k+1)→ℝ|ε≤average y^2}={y|Real.sqrt ε≤|average y|}:=by
      ext y
      simpa only [Set.mem_setOf_eq,Real.sq_sqrt hε.le,sq_abs] using
        (sq_le_sq₀ (Real.sqrt_nonneg ε) (abs_nonneg (average y)))
    rw [hs]
    have hb:=(ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hge
    simp only [sub_zero,ENNReal.toReal_ofReal (by positivity :0≤(1/((k+1:ℕ):ℝ))/ε)] at hb
    simpa only [Measure.real,μ,div_div,Nat.cast_add,Nat.cast_one] using hb
  have he:probability (signFamily.model k)
      {y| |(k+1:ℝ)*V2 (signFamily.model k).G (weighted (signFamily.model k) y)-1| <ε}=
      μ.real {y|average y^2<ε}:=by
    apply measureReal_congr
    filter_upwards [DataMatrixCompletion.ae_signs (k+1)] with y hy
    have hv:=V2_value (Nat.succ_pos k) y hy
    have hw:weighted (signFamily.model k) y=y:=by funext i;exact weighted_value y i
    rw [hw]
    change (|(k+1:ℝ)*V2 (emptyGraph (k+1)) y-1| <ε)=(average y^2<ε)
    have hv':(k+1:ℝ)*V2 (emptyGraph (k+1)) y=1-average y^2:=by simpa using hv
    rw [hv']
    have hab:|1-average y^2-1|=average y^2:=by rw [show 1-average y^2-1= -(average y^2) by ring,abs_neg,abs_of_nonneg (sq_nonneg _)]
    rw [hab]
  have hset:MeasurableSet {y:Fin (k+1)→ℝ|ε≤average y^2}:=measurableSet_le measurable_const (by unfold average;fun_prop)
  have hc:=measureReal_compl (μ:=μ) hset
  have hs:{y:Fin (k+1)→ℝ|ε≤average y^2}ᶜ={y|average y^2<ε}:=by ext y;simp
  rw [hs,probReal_univ] at hc
  rw [he,hc]
  linarith
lemma printed_sign_counterexample_completed :
    Scaling signFamily 1 1 1 2 ∧ Valid signFamily ∧
    (∀ k, Homoskedastic (signFamily.model k) ∧ beta (signFamily.model k) = 0 ∧
      scaledTrue signFamily k = 1 ∧
      expectation (signFamily.model k) (fun y => betaHat (signFamily.model k) y ^ 2) = 1/(k+1 : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε →
      (∀ k : ℕ, 1 - 1/((k+1 : ℝ)*ε) ≤ probability (signFamily.model k)
        {y | |(k+1 : ℝ)*V2 (signFamily.model k).G (weighted (signFamily.model k) y)-1| < ε}) ∧
      Tendsto (fun k => probability (signFamily.model k)
        {y | |(k+1 : ℝ)*V2 (signFamily.model k).G (weighted (signFamily.model k) y)-1| < ε})
        atTop (𝓝 1)) := by
  refine ⟨scaling_valid.1,scaling_valid.2,?_,?_⟩
  · intro k
    refine ⟨?_,beta_zero _,scaled_variance (Nat.succ_pos k),?_⟩
    · intro i j
      change covariance (signModel (k+1)) i i=covariance (signModel (k+1)) j j
      simp [DataMatrixCompletion.covariance_formula]
    · change expectation (signModel (k+1)) (fun y=>betaHat (signModel (k+1)) y^2)=1/(k+1:ℝ)
      have hm:=moment (n:=k+1) (by omega)
      simpa only [Nat.cast_add,Nat.cast_one] using hm
  · intro ε hε
    refine ⟨fun k=>finite_lower k ε hε,?_⟩
    have hN:Tendsto (fun k:ℕ=>(k+1:ℝ)*ε) atTop atTop:=by
      apply Tendsto.atTop_mul_const hε
      simpa only [Function.comp_def,Nat.cast_succ] using tendsto_natCast_atTop_atTop.comp
        (tendsto_atTop_mono (fun k=>Nat.le_succ k) tendsto_id)
    have hlo:Tendsto (fun k:ℕ=>1-1/((k+1:ℝ)*ε)) atTop (𝓝 1):=by
      simpa using tendsto_const_nhds.sub (hN.const_div_atTop 1)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
      (fun k=>finite_lower k ε hε)
    intro k
    let : IsProbabilityMeasure (signFamily.model k).law:=(signFamily.model k).probability
    simpa only [probability,probReal_univ] using measureReal_mono (μ:=(signFamily.model k).law)
      (Set.subset_univ {y | |(k+1:ℝ)*V2 (signFamily.model k).G (weighted (signFamily.model k) y)-1| <ε}) (measure_ne_top _ _)
end
end AronowAudit.P011.SignCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
theorem printed_sign_counterexample :
    Scaling signFamily 1 1 1 2 ∧ Valid signFamily ∧
    (∀ k, Homoskedastic (signFamily.model k) ∧ beta (signFamily.model k) = 0 ∧
      scaledTrue signFamily k = 1 ∧
      expectation (signFamily.model k) (fun y => betaHat (signFamily.model k) y ^ 2) = 1/(k+1 : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε →
      (∀ k : ℕ, 1 - 1/((k+1 : ℝ)*ε) ≤ probability (signFamily.model k)
        {y | |(k+1 : ℝ)*V2 (signFamily.model k).G (weighted (signFamily.model k) y)-1| < ε}) ∧
      Tendsto (fun k => probability (signFamily.model k)
        {y | |(k+1 : ℝ)*V2 (signFamily.model k).G (weighted (signFamily.model k) y)-1| < ε})
        atTop (𝓝 1)) := by
  exact SignCompletion.printed_sign_counterexample_completed
end
end AronowAudit.P011
