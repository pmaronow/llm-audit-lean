import AronowAudit.P011.P011_DenseInfrastructure
import AronowAudit.P011.P011_ThreePointCompletion
namespace AronowAudit.P011.DataMatrixCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

lemma rank_one_norm {n:ℕ} (x:Fin n→ℝ):operatorNorm (dataMatrix x)=l2 x^2/|(n:ℝ)|:=by
  let v:EuclideanSpace ℝ (Fin n):=WithLp.toLp 2 x
  have he:(Matrix.toEuclideanLin (dataMatrix x)).toContinuousLinearMap=
      (n:ℝ)⁻¹ • InnerProductSpace.rankOne ℝ v v:=by
    ext z i
    simp [Matrix.toEuclideanLin,Matrix.toLpLin_apply,Matrix.toLin'_apply,dataMatrix,
      InnerProductSpace.rankOne_apply,EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.mulVec,dotProduct,v,Finset.mul_sum,Finset.sum_mul,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
  unfold operatorNorm
  rw [he,norm_smul,InnerProductSpace.norm_rankOne]
  simp only [Real.norm_eq_abs,abs_inv,v,DenseCompletion.l2_norm]
  ring

lemma finite_data {n:ℕ} (hn:0<n) (x:Fin n→ℝ) (hx:∀i,x i=1∨x i=-1):
    operatorNorm (dataMatrix x)=1 ∧Matrix.trace (dataMatrix x)=1∧
      (n:ℝ)*varianceForm (dataMatrix x) x=(1-average x^2)^2:=by
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hs (i:Fin n):x i^2=1:=by rcases hx i with h|h <;> rw [h] <;> norm_num
  have hsum:(∑i,x i^2)=(n:ℝ):=by simp [hs]
  have hprod:(∑i,x i*centered x i)=(n:ℝ)*(1-average x^2):=by
    simp_rw [centered,mul_sub,←pow_two]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,hsum]
    have ha:(∑i,x i)=(n:ℝ)*average x:=by unfold average;field_simp <;> ring
    rw [ha];ring
  refine ⟨?_,?_,?_⟩
  · rw [rank_one_norm,DenseCompletion.l2_sq,hsum,abs_of_pos hnR,div_self hnR.ne']
  · unfold Matrix.trace Matrix.diag dataMatrix
    simp_rw [←pow_two,hs]
    simp [hnR.ne']
  · have hq:quadratic (dataMatrix x) (centered x)=(∑i,x i*centered x i)^2/(n:ℝ):=by
      unfold quadratic dataMatrix
      rw [sq,Finset.sum_mul_sum]
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    unfold varianceForm
    rw [hq,hprod]
    field_simp <;> ring

lemma coord_integral {n:ℕ} (i:Fin n) (g:ℝ→ℝ) (hg:Measurable g):
    expectation (signModel n) (fun y=>g (y i))=(g (-1)+g 1)/2:=by
  have hf:Measurable sign:=measurable_of_finite _
  have hm:=ThreePointCompletion.uniform_marginal Bool sign hf i
  change (signModel n).law.map (fun y=>y i)=_ at hm
  unfold expectation
  rw [←integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable,hm,
    integral_map hf.aemeasurable hg.aestronglyMeasurable,PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply,Fintype.sum_bool,sign]
  ring

lemma ae_signs (n:ℕ):∀ᵐ y∂(signModel n).law,∀i,y i=1∨y i=-1:=by
  let g:=fun (u:Fin n→Bool) i=>sign (u i)
  have hg:Measurable g:=measurable_of_finite _
  have hp:(signModel n).law=(PMF.uniformOfFintype (Fin n→Bool)).toMeasure.map g:=
    (PMF.toMeasure_map g (PMF.uniformOfFintype _) hg).symm
  rw [hp]
  have hs:MeasurableSet {y:Fin n→ℝ|∀i,y i=1∨y i=-1}:=by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).union
      (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)
  apply (ae_map_iff hg.aemeasurable hs).mpr
  filter_upwards [] with u i
  cases h:u i <;> simp [g,sign,h]

lemma coordinate_memLp {n:ℕ} (i:Fin n):MemLp (fun y:Fin n→ℝ=>y i) 2 (signModel n).law:=by
  let : IsProbabilityMeasure (signModel n).law:=(signModel n).probability
  apply MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable 1
  filter_upwards [ae_signs n] with y hy
  rcases hy i with h|h <;> rw [h] <;> norm_num

lemma covariance_formula {n:ℕ} (i j:Fin n):covariance (signModel n) i j=if i=j then 1 else 0:=by
  have hw (y:Fin n→ℝ) (i:Fin n):weighted (signModel n) y i=y i:=by simp [weighted,signModel]
  have hmean (i:Fin n):expectation (signModel n) (fun y=>weighted (signModel n) y i)=0:=by
    simp only [hw]
    rw [coord_integral i (fun x=>x) measurable_id]
    norm_num
  by_cases hij:i=j
  · subst j
    rw [if_pos rfl]
    unfold covariance
    rw [hmean]
    simp only [hw,sub_zero]
    rw [coord_integral i (fun x=>x*x) (by fun_prop)]
    norm_num
  · rw [if_neg hij,QuadraticCompletion.covariance_eq_mathlib]
    have hd:Dependency (signModel n):=uniform_coordinate_dependency Bool (fun _=>sign) (fun _=>measurable_of_finite _)
    have hi:=hd {i} {j} (by simpa using hij) (by simp [signModel,emptyGraph])
    have hh:IndepFun (fun y:Fin n→ℝ=>y i) (fun y=>y j) (signModel n).law:=
      by
        simpa only [Function.comp_def] using hi.comp (measurable_pi_apply ⟨i,by simp⟩) (measurable_pi_apply ⟨j,by simp⟩)
    simpa only [hw] using hh.covariance_eq_zero (coordinate_memLp i) (coordinate_memLp j)

lemma average_mean {n:ℕ}:expectation (signModel n) average=0:=by
  let : IsProbabilityMeasure (signModel n).law:=(signModel n).probability
  unfold average expectation
  rw [integral_div,integral_finsetSum Finset.univ (fun i _=>(coordinate_memLp i).integrable (by norm_num))]
  have he (i:Fin n):(∫y,y i∂(signModel n).law)=0:=by
    change expectation (signModel n) (fun y=>y i)=0
    rw [coord_integral i (fun x=>x) measurable_id];norm_num
  simp [he]

lemma average_variance {n:ℕ} (hn:0<n):ProbabilityTheory.variance (average: (Fin n→ℝ)→ℝ) (signModel n).law=1/(n:ℝ):=by
  let : IsProbabilityMeasure (signModel n).law:=(signModel n).probability
  have hL2 (i:Fin n):MemLp (fun y=>weighted (signModel n) y i) 2 (signModel n).law:=by
    simpa [weighted,signModel] using coordinate_memLp i
  have heb:betaHat (signModel n)=(average:(Fin n→ℝ)→ℝ):=by
    funext y
    apply congrArg average
    funext i
    simp [weighted,signModel]
  have he:var (signModel n) (betaHat (signModel n))=ProbabilityTheory.variance (average:(Fin n→ℝ)→ℝ) (signModel n).law:=by
    rw [heb]
    exact (ProbabilityTheory.variance_eq_integral (by unfold average;fun_prop:Measurable (average:(Fin n→ℝ)→ℝ)).aemeasurable).symm
  rw [←he,QuadraticCompletion.beta_variance _ hL2]
  unfold QuadraticCompletion.total
  simp only [covariance_formula]
  simp
  field_simp <;> ring
lemma average_CP:CoverageCompletion.RowCP (fun k=>(signModel (k+1)).law)
    (fun _ y=>average y) 0:=by
  let (k:ℕ):IsProbabilityMeasure (signModel (k+1)).law:=(signModel (k+1)).probability
  have h2 (k:ℕ):MemLp (average: (Fin (k+1)→ℝ)→ℝ) 2 (signModel (k+1)).law:=by
    unfold average
    simpa only [div_eq_mul_inv] using
      (memLp_finsetSum Finset.univ (fun i _=>coordinate_memLp i)).mul_const (((k+1:ℕ):ℝ)⁻¹)
  have hN:Tendsto (fun k=>((k+1:ℕ):ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp
    (tendsto_atTop_mono (fun k=>Nat.le_succ k) tendsto_id)
  have hv:Tendsto (fun k=>ProbabilityTheory.variance (average:(Fin (k+1)→ℝ)→ℝ) (signModel (k+1)).law) atTop (𝓝 0):=by
    simp_rw [average_variance (Nat.succ_pos _)]
    exact hN.const_div_atTop 1
  have hc:=OracleCompletion.rowCP_of_variance (fun k=>(signModel (k+1)).law)
    (fun _ y=>average y) h2 hv
  have hm (k:ℕ):(∫y,average y∂(signModel (k+1)).law)=0:=average_mean
  simpa only [CoverageCompletion.RowCP,hm] using hc

lemma data_dependent_expansion_failure_completed :
    (∀ n (hn : 0 < n) (x : Fin n → ℝ), (∀ i, x i = 1 ∨ x i = -1) →
      operatorNorm (dataMatrix x) = 1 ∧ Matrix.trace (dataMatrix x) = 1 ∧
      (n : ℝ)*varianceForm (dataMatrix x) x = (1-average x^2)^2) ∧
    InProbability signFamily
      (fun k y => (k+1 : ℝ)*varianceForm (dataMatrix y) y - 1) (fun _ => 0) ∧
    InProbability signFamily
      (fun k y => Matrix.trace (dataMatrix y - 1)/(k+1 : ℝ)) (fun _ => -1) := by
  let (k:ℕ):IsProbabilityMeasure (signModel (k+1)).law:=(signModel (k+1)).probability
  refine ⟨fun n hn x hx=>finite_data hn x hx,?_,?_⟩
  · have hc:=CoverageCompletion.rowCP_continuous_pair (fun k=>(signModel (k+1)).law)
      (fun _ y=>average y) (fun _ _=>(0:ℝ)) 0 0 average_CP
      (CoverageCompletion.rowCP_det _ (fun _=>(0:ℝ)) 0 tendsto_const_nhds)
      (fun p:ℝ×ℝ=>(1-p.1^2)^2-1) (by fun_prop)
    norm_num only [Prod.fst_zero,zero_pow (by decide:2≠0),sub_zero,one_pow,sub_self] at hc
    intro ε hε
    convert hc ε hε using 1
    funext k
    apply measureReal_congr
    filter_upwards [ae_signs (k+1)] with y hy
    have hd:((k+1:ℕ):ℝ)*varianceForm (dataMatrix y) y=(1-average y^2)^2:=
      (finite_data (Nat.succ_pos k) y hy).2.2
    have hd' : (k+1:ℝ)*varianceForm (dataMatrix y) y=(1-average y^2)^2:=by
      simpa only [Nat.cast_add,Nat.cast_one] using hd
    simp only [Set.mem_setOf_eq,hd']
    rfl
  · have hN:Tendsto (fun k:ℕ=>(k+1:ℝ)) atTop atTop:=by
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one,Nat.cast_succ] using tendsto_natCast_atTop_atTop.comp
        (tendsto_atTop_mono (fun k=>Nat.le_succ k) tendsto_id)
    have hl:Tendsto (fun k:ℕ=>(-1:ℝ)+1/(k+1:ℝ)) atTop (𝓝 (-1)):=by
      simpa using tendsto_const_nhds.add (hN.const_div_atTop 1)
    have hc:=CoverageCompletion.rowCP_det (fun k=>(signModel (k+1)).law) (fun k:ℕ=>(-1:ℝ)+1/(k+1:ℝ)) (-1) hl
    intro ε hε
    convert hc ε hε using 1
    funext k
    apply measureReal_congr
    filter_upwards [ae_signs (k+1)] with y hy
    have ht:Matrix.trace (dataMatrix y)=1:=(finite_data (Nat.succ_pos k) y hy).2.1
    have he:Matrix.trace (dataMatrix y-1)/(k+1:ℝ)=(-1:ℝ)+1/(k+1:ℝ):=by
      rw [Matrix.trace_sub,ht,Matrix.trace_one,Fintype.card_fin]
      simp only [signFamily]
      push_cast
      field_simp <;> ring
    simp only [Set.mem_setOf_eq,he]
    rfl
end
end AronowAudit.P011.DataMatrixCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
theorem data_dependent_expansion_failure :
    (∀ n (hn : 0 < n) (x : Fin n → ℝ), (∀ i, x i = 1 ∨ x i = -1) →
      operatorNorm (dataMatrix x) = 1 ∧ Matrix.trace (dataMatrix x) = 1 ∧
      (n : ℝ)*varianceForm (dataMatrix x) x = (1-average x^2)^2) ∧
    InProbability signFamily
      (fun k y => (k+1 : ℝ)*varianceForm (dataMatrix y) y - 1) (fun _ => 0) ∧
    InProbability signFamily
      (fun k y => Matrix.trace (dataMatrix y - 1)/(k+1 : ℝ)) (fun _ => -1) := by
  exact DataMatrixCompletion.data_dependent_expansion_failure_completed
end
end AronowAudit.P011
