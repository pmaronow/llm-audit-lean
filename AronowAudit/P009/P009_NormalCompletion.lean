/- P009 corrected normal approximation and its concrete sparse counterexample.
Uses the licensed dependency-graph CLT through finite Bernoulli bridges. -/
import AronowAudit.P009.P009_OutcomeCompletion
import AronowAudit.P004.P004_SpatialCLTCompletion
import AronowAudit.P053.P053_NormalQuantiles
namespace AronowAudit.P009.NormalCompletion
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def p {n : ℕ} (E : Experiment n) : Fin n→ℝ:=fun i=>marginal E i true

theorem mean_expect {n : ℕ} (E : Experiment n) (hb : Bernoulli E) (f : Assignment n→ℝ) :
    mean E.design f=AronowAudit.P004.expect (p E) f := by
  unfold mean AronowAudit.P004.expect AronowAudit.P004.designWeight AronowAudit.P004.coin p
  simp_rw [hb.2]

theorem ht_eq {n : ℕ} (E : Experiment n) :
    AronowAudit.P004.ht (p E) E.outcome=ht E := by
  funext z
  unfold ht muHat AronowAudit.P004.ht
  rw [←sub_div,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hf : marginal E i false=1-marginal E i true := by linarith [marginal_partition E i]
  cases hz : z i <;> simp [AronowAudit.P004.bit,hz,p,hf]

theorem variance_eq {n : ℕ} (E : Experiment n) (hb : Bernoulli E) (f : Assignment n→ℝ) :
    AronowAudit.P004.variance (p E) f=var E.design f := by
  rw [variance_second_moment]
  simp only [AronowAudit.P004.variance,AronowAudit.P004.cov,mean_expect E hb]
  simp only [pow_two]

theorem ame_eq {n : ℕ} (E : Experiment n) (hb : Bernoulli E) :
    AronowAudit.P004.ame (p E) E.outcome=eate E := by
  rw [←AronowAudit.P004.ht_unbiased (p E) E.outcome hb.1,ht_eq,←mean_expect E hb]
  exact BernoulliCompletion.ht_unbiased E hb

def B {n : ℕ} (E : Experiment n) (i : Fin n) : Finset (Fin n):=
  Finset.univ.filter (fun j=>Dependent E i j)

theorem graph {n : ℕ} (E : Experiment n) (hb : Bernoulli E) :
    AronowAudit.P004.FiniteDependencyGraph (p E)
      (fun i z=>AronowAudit.P004.residualContrast (p E) E.outcome (fun _ _=>0) i z) (B E) := by
  apply AronowAudit.P004.design_dependency_graph _ _ _ _ hb.1
  · intro i
    simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨i,Or.inl rfl,Or.inl rfl⟩
  · intro i j
    constructor
    · intro h
      obtain ⟨l,hi,hj⟩:=(Finset.mem_filter.mp h).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨l,hj,hi⟩⟩
    · intro h
      obtain ⟨l,hj,hi⟩:=(Finset.mem_filter.mp h).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨l,hi,hj⟩⟩
  · intro i j hj hs
    apply hj
    simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
    obtain ⟨l,hi,hj⟩:=hs
    refine ⟨l,?_,?_⟩
    · simpa only [AronowAudit.P004.interferes,Interferes,eq_comm] using hi
    · simpa only [AronowAudit.P004.interferes,Interferes,eq_comm] using hj

theorem B_card {n : ℕ} (E : Experiment n) (i : Fin n) : ((B E i).card:ℝ)=degree E i := by
  simp only [B,degree,d,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem raw_bound {n : ℕ} (E : Experiment n) (k q s b : ℝ) (hr : Regular E k q s)
    (hy : ∀i z,|E.outcome i z|≤b) (i : Fin n) (z : Assignment n) :
    |AronowAudit.P004.residualContrast (p E) E.outcome (fun _ _=>0) i z|≤k*b := by
  have ht:=BernoulliCompletion.regular_marginal_bounds E k q s hr i true
  have hf:=BernoulliCompletion.regular_marginal_bounds E k q s hr i false
  have he : marginal E i false=1-marginal E i true:=by linarith [marginal_partition E i]
  have hb : 0≤b:=(abs_nonneg _).trans (hy i z)
  have h (a : Bool) : |E.outcome i z|/marginal E i a≤k*b := by
    rw [div_eq_mul_inv,mul_comm k b]
    apply mul_le_mul (hy i z) (BernoulliCompletion.regular_marginal_bounds E k q s hr i a).2.2.2
      (inv_nonneg.mpr (BernoulliCompletion.regular_marginal_bounds E k q s hr i a).2.2.1.le) hb
  have hfp : 0<1-marginal E i true:=by rw [←he];exact hf.2.2.1
  cases hz : z i
  · simpa [AronowAudit.P004.residualContrast,AronowAudit.P004.bit,hz,p,he,
      abs_div,abs_of_pos hfp] using h false
  · simpa [AronowAudit.P004.residualContrast,AronowAudit.P004.bit,hz,p,
      abs_div,abs_of_pos ht.2.2.1] using h true

theorem centered_bound {n : ℕ} (E : Experiment n) (k q s b : ℝ) (hr : Regular E k q s)
    (hb : Bernoulli E) (hy : ∀i z,|E.outcome i z|≤b) (i : Fin n) (z : Assignment n) :
    |AronowAudit.P004.CLTCompletion.centeredHT (p E) E.outcome i z|≤2*(k*b) := by
  let T:=AronowAudit.P004.residualContrast (p E) E.outcome (fun _ _=>0) i
  have hT : ∀z,|T z|≤k*b:=raw_bound E k q s b hr hy i
  have hl:=AronowAudit.P004.expect_mono (p E) hb.1 (fun _=> -(k*b)) T
    (fun z=>(abs_le.mp (hT z)).1)
  have hu:=AronowAudit.P004.expect_mono (p E) hb.1 T (fun _=>k*b)
    (fun z=>(abs_le.mp (hT z)).2)
  rw [AronowAudit.P004.expect_const] at hl hu
  have hm : AronowAudit.P004.expect (p E) T=AronowAudit.P004.nodeEffect (p E) E.outcome i := by
    simpa [T,AronowAudit.P004.residualEffect] using
      AronowAudit.P004.residualContrast_mean (p E) E.outcome (fun _ _=>0) i hb.1
  rw [hm] at hl hu
  change |T z-AronowAudit.P004.nodeEffect (p E) E.outcome i|≤_
  have ht:=abs_le.mp (hT z)
  apply abs_le.mpr
  constructor <;> linarith
end
end AronowAudit.P009.NormalCompletion

namespace AronowAudit.P009.NormalCompletion
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem corrected_normal_approximation_completed (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hBER : ∀t,Bernoulli (S.experiment t))
    (hDegree : ∃D,∀t,dMax (S.experiment t)≤D)
    (hVariance : PositiveLiminf (fun t=>size S t*var (S.experiment t).design (ht (S.experiment t)))) :
    InDistribution S (fun t z=>(ht (S.experiment t) z-eate (S.experiment t))/
      Real.sqrt (var (S.experiment t).design (ht (S.experiment t)))) normalCDF := by
  obtain ⟨DR,hDR⟩:=hDegree
  let D:=Nat.ceil DR
  have hD (t : ℕ) (i : Fin (S.N t)) : degree (S.experiment t) i≤(D:ℝ) := by
    apply le_trans (le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i))
    exact (hDR t).trans (Nat.le_ceil DR)
  let C:=Real.rpow k (1+(D:ℝ)/q)
  have hY (t : ℕ) : ∀i z,|(S.experiment t).outcome i z|≤C:=
    (bounded_degree_outcome_bound (S.experiment t) k q s (hReg t) (hBER t) D (hD t)).2
  let μ:=fun t=>AronowAudit.P004.CLTCompletion.designMeasure (p (S.experiment t)) (hBER t).1
  letI (t : ℕ) : IsProbabilityMeasure (μ t) :=
    AronowAudit.P004.CLTCompletion.designMeasure_probability (p (S.experiment t)) (hBER t).1
  let X:=fun t=>AronowAudit.P004.CLTCompletion.centeredHT (p (S.experiment t)) (S.experiment t).outcome
  have hg (t : ℕ) : AronowAudit.P004.DependencyGraph (μ t) (X t) (B (S.experiment t)):=
    AronowAudit.P004.CLTCompletion.centeredHT_graph _ _ _ (hBER t).1 (graph (S.experiment t) (hBER t))
  let Dep : ∀t,Causalean.Mathlib.Probability.SteinMethod.DepGraph (X t) (μ t):=fun t=>{
    G:=fun i j=>j∈B (S.experiment t) i
    decG:=inferInstance
    refl:=(hg t).1
    symm:=fun i j hij=>((hg t).2.1 i j).mp hij
    meas:=fun i=>measurable_of_finite _
    indep:=(hg t).2.2 }
  have hdeg (t : ℕ) (i : Fin (S.N t)) : ((Dep t).nbhd i).card≤D := by
    have he : (Dep t).nbhd i=B (S.experiment t) i:=by ext j;exact (Dep t).mem_nbhd_iff
    rw [he]
    exact_mod_cast (show ((B (S.experiment t) i).card:ℝ)≤(D:ℝ) by rw [B_card];exact hD t i)
  have hm (t : ℕ) (i : Fin (S.N t)) : (∫z,X t i z∂μ t)=0 := by
    dsimp only [μ,X]
    rw [AronowAudit.P004.CLTCompletion.designMeasure_integral]
    exact AronowAudit.P004.CLTCompletion.centeredHT_mean _ _ (hBER t).1 i
  let V:=fun t=>(S.N t:ℝ)^2*var (S.experiment t).design (ht (S.experiment t))
  have hsecond (t : ℕ) :
      (∫z,(Causalean.Mathlib.Probability.SteinMethod.depSum (X t) z)^2∂μ t)=V t := by
    dsimp only [μ,X]
    rw [AronowAudit.P004.CLTCompletion.designMeasure_integral]
    change AronowAudit.P004.expect _ (fun z=>(∑i,AronowAudit.P004.CLTCompletion.centeredHT _ _ i z)^2)=_
    rw [AronowAudit.P004.CLTCompletion.centeredHT_second (p (S.experiment t)) (S.experiment t).outcome (hBER t).1 (S.positive t),ht_eq,variance_eq _ (hBER t)]
  obtain ⟨v,hv,hVN⟩:=hVariance
  have hfloor : ∀ᶠt in atTop,v*(Fintype.card (Fin (S.N t)):ℝ)≤V t := by
    filter_upwards [hVN] with t ht
    simpa only [Fintype.card_fin,size,V,pow_two,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (S.N t):0≤(S.N t:ℝ))
  intro x _hx
  have hh:=Causalean.Mathlib.Probability.SteinMethod.bounded_degree_dependency_clt_ae
    μ X Dep D hdeg (2*(k*C))
    (fun t i=>Eventually.of_forall (centered_bound (S.experiment t) k q s C (hReg t) (hBER t) (hY t) i))
    hm V hsecond v hv hfloor (by simpa only [Fintype.card_fin] using S.grows) x
  apply hh.congr
  intro t
  rw [MeasureTheory.map_measureReal_apply (measurable_of_finite _) measurableSet_Iic]
  change ((AronowAudit.P004.CLTCompletion.designMeasure (p (S.experiment t)) (hBER t).1) _).toReal=_
  rw [AronowAudit.P004.CLTCompletion.designMeasure_apply]
  change AronowAudit.P004.prob (p (S.experiment t)) _=prob (S.experiment t).design _
  rw [AronowAudit.P004.prob,prob,←mean_expect _ (hBER t)]
  apply congrArg (mean (S.experiment t).design)
  funext z
  have hn : (S.N t:ℝ)≠0:=by exact_mod_cast (S.positive t).ne'
  have hsqrt : Real.sqrt (V t)=(S.N t:ℝ)*Real.sqrt (var (S.experiment t).design (ht (S.experiment t))):=by
    dsimp [V]
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]
  simp only [Causalean.Mathlib.Probability.SteinMethod.depSum,X,
    AronowAudit.P004.CLTCompletion.centeredHT_sum _ _ (S.positive t),ht_eq,ame_eq _ (hBER t),hsqrt,
    mul_div_mul_left _ _ hn,Set.mem_preimage,Set.mem_Iic]
end
end AronowAudit.P009.NormalCompletion

namespace AronowAudit.P009.SparseCompletion
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

theorem inv_size_zero : Tendsto (fun t=>1/size sparseStudy t) atTop (nhds 0) :=
  (tendsto_natCast_atTop_atTop.comp sparseStudy.grows).const_div_atTop 1

theorem fair_split (n : ℕ) (f : Assignment (n+1) → ℝ) :
    mean (fairLaw (n+1)) f =
    (mean (fairLaw n) (fun z => f (Fin.cons true z)) +
      mean (fairLaw n) (fun z => f (Fin.cons false z)))/2 := by
  simp only [mean, fairLaw, sum_cube_succ, Fintype.sum_bool, pow_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  simp only [mul_assoc, mul_left_comm (2:ℝ)⁻¹, ← Finset.mul_sum]
  ring


theorem fair_coordinate (n : ℕ) (i : Fin n) (f : Bool → ℝ) :
    mean (fairLaw n) (fun z => f (z i)) = (f true+f false)/2 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases (fair_first_coordinate n f) (fun j => ?_) i
    rw [fair_split]
    simp only [Fin.cons_succ, ih]
    ring


theorem fair_marginal (n : ℕ) (y : Fin n → Assignment n → ℝ) (i : Fin n) (b : Bool) :
    marginal (fairExperiment n y) i b = 1/2 := by
  dsimp only [marginal,prob,fairExperiment]
  convert fair_coordinate n i (fun q => if q=b then (1:ℝ) else 0) using 1
  all_goals first | (congr 1; funext z; congr 1) | (cases b <;> norm_num)


theorem mean_le_constant {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) (c : ℝ)
    (h : ∀ ω, X ω≤c) : mean P X≤c := by
  calc
    _ ≤ mean P (fun _ => c) := Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω))
    _ = c := mean_const P c


theorem fair_regular_bounded (n : ℕ) (y : Fin n → Assignment n → ℝ)
    (hy : ∀ i z, |y i z|≤2) : Regular (fairExperiment n y) 2 4 1 := by
  refine ⟨by norm_num,by norm_num,by norm_num,?_,?_,?_⟩
  · intro i; rw [fair_marginal]; norm_num
  · intro i
    have hpow (x : ℝ) : Real.rpow x 4=x^4 := by simpa using Real.rpow_natCast x 4
    simp only [hpow]
    apply mean_le_constant
    intro z
    change |y i z|^4≤(2:ℝ)^4
    gcongr
    exact hy i z
  · intro i b
    convert mean_le_constant (fairLaw n) (fun z=>|y i (Function.update z i b)|) 2 (fun z=>hy i (Function.update z i b)) using 1 <;> simp [potential,fairExperiment,Real.rpow_one]


theorem fair_BER (n : ℕ) (y : Fin n → Assignment n → ℝ) : Bernoulli (fairExperiment n y) := by
  constructor
  · intro i; rw [fair_marginal]; norm_num
  · intro z
    simp only [fair_marginal]
    simp only [fairExperiment,fairLaw]
    have h (i : Fin n) : (if z i then (1/2:ℝ) else 1-1/2)=1/2 := by cases z i <;> norm_num
    simp only [h,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    simp [div_pow]


theorem bit_bound (b : Bool) : |bit b|≤2 := by cases b <;> norm_num [bit]


theorem sparse_regular_sequence : RegularSequence sparseStudy 2 4 1 := by
  intro t
  apply fair_regular_bounded
  intro i z
  change |if i.val=0 then bit (z i) else 0|≤2
  split_ifs
  · exact bit_bound _
  · norm_num


theorem sparse_BER_sequence : ∀ t, Bernoulli (sparseStudy.experiment t) := by
  intro t; exact fair_BER _ _


theorem sparse_NoI_sequence : ∀ t, NoInterference (sparseStudy.experiment t) := by
  intro t i z w h
  change (if i.val=0 then bit (z i) else 0)=(if i.val=0 then bit (w i) else 0)
  rw [h]


theorem noI_interferes {n : ℕ} (E : Experiment n) (h : NoInterference E) (i j : Fin n) :
    Interferes E i j ↔ i=j := by
  constructor
  · rintro (he | ⟨z,w,hagree,hne⟩)
    · exact he
    · by_contra hij
      exact hne (h j z w (hagree j (Ne.symm hij)))
  · exact Or.inl


theorem noI_d {n : ℕ} (E : Experiment n) (h : NoInterference E) (i j : Fin n) :
    d E i j = if i=j then 1 else 0 := by
  simp only [d,Dependent,noI_interferes E h]
  congr 1
  apply propext
  constructor
  · rintro ⟨l,rfl,rfl⟩; rfl
  · intro he; exact ⟨i,rfl,he⟩


theorem noI_degree {n : ℕ} (E : Experiment n) (h : NoInterference E) (i : Fin n) : degree E i=1 := by
  simp [degree,noI_d E h]


theorem noI_dAvg {n : ℕ} (hn : 0 < n) (E : Experiment n) (h : NoInterference E) : dAvg E=1 := by
  simp [dAvg,noI_degree E h,ne_of_gt hn]


theorem noI_dMax {n : ℕ} (hn : 0 < n) (E : Experiment n) (h : NoInterference E) : dMax E=1 := by
  have hr : Set.range (degree E)={1} := by
    ext x; constructor
    · rintro ⟨i,rfl⟩; simp [noI_degree E h]
    · intro hx; have he : x=1 := by simpa using hx
      subst x; exact ⟨⟨0,hn⟩,noI_degree E h _⟩
  simp [dMax,hr]


theorem sparse_restricted : Restricted sparseStudy := by
  unfold Restricted
  have he (t : ℕ) : dAvg (sparseStudy.experiment t)=1 := noI_dAvg (sparseStudy.positive t) _ (sparse_NoI_sequence t)
  simpa only [he] using (show Tendsto (fun t => 1/size sparseStudy t) atTop (nhds 0) from inv_size_zero)


end
end AronowAudit.P009.SparseCompletion

namespace AronowAudit.P009.SparseCompletion
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
local instance : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1:NNReal)≠0)

theorem sparse_eate (t : ℕ) : eate (sparseStudy.experiment t)=1/size sparseStudy t := by
  rw [←BernoulliCompletion.ht_unbiased _ (sparse_BER_sequence t)]
  exact (sparse_moments_finite t).1

theorem sparse_statistic (t : ℕ) (z : Assignment (t+1)) :
    (ht (sparseStudy.experiment t) z-eate (sparseStudy.experiment t))/
      Real.sqrt (var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t)))=2*bit (z 0)-1 := by
  rw [sparse_eate]
  change (ht (sparseExperiment (t+1)) z-1/(t+1:ℕ))/
    Real.sqrt (var (sparseExperiment (t+1)).design (ht (sparseExperiment (t+1))))=_
  rw [(sparse_estimators_finite t z).1,(sparse_moments_finite t).2.1,
    Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one,Real.sqrt_sq (by positivity : (0:ℝ)≤(t+1:ℕ))]
  have hn : ((t+1:ℕ):ℝ)≠0:=by positivity
  field_simp

theorem sparse_normal_counterexample_completed :
    RegularSequence sparseStudy 2 4 1 ∧ Restricted sparseStudy ∧
    (∀t,Bernoulli (sparseStudy.experiment t) ∧ NoInterference (sparseStudy.experiment t) ∧
      dAvg (sparseStudy.experiment t)=1 ∧ dMax (sparseStudy.experiment t)=1 ∧
      var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t))>0) ∧
    Tendsto (fun t=>size sparseStudy t*var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t))) atTop (nhds 0) ∧
    (∀t b,prob (sparseStudy.experiment t).design (fun z=>
      (ht (sparseStudy.experiment t) z-eate (sparseStudy.experiment t))/
        Real.sqrt (var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t)))=
          (if b then 1 else -1))=1/2) ∧
    ¬InDistribution sparseStudy (fun t z=>
      (ht (sparseStudy.experiment t) z-eate (sparseStudy.experiment t))/
        Real.sqrt (var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t)))) normalCDF := by
  refine ⟨sparse_regular_sequence,sparse_restricted,?_,?_,?_,?_⟩
  · intro t
    refine ⟨sparse_BER_sequence t,sparse_NoI_sequence t,
      noI_dAvg (sparseStudy.positive t) _ (sparse_NoI_sequence t),
      noI_dMax (sparseStudy.positive t) _ (sparse_NoI_sequence t),?_⟩
    change 0<var (sparseExperiment (t+1)).design (ht (sparseExperiment (t+1)))
    rw [(sparse_moments_finite t).2.1];positivity
  · have he (t : ℕ) : size sparseStudy t*var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t))=1/size sparseStudy t := by
      change (t+1:ℕ)*var (sparseExperiment (t+1)).design (ht (sparseExperiment (t+1)))=1/(t+1:ℕ)
      rw [(sparse_moments_finite t).2.1]
      have hn : ((t+1:ℕ):ℝ)≠0:=by positivity
      field_simp
    simpa only [he] using inv_size_zero
  · intro t b
    unfold prob
    change mean (fairLaw (t+1)) _=_
    simp_rw [sparse_statistic]
    change mean (fairLaw (t+1)) (fun z : Assignment (t+1)=>
      if 2*bit (z 0)-1=(if b then 1 else -1) then (1:ℝ) else 0)=1/2
    rw [fair_first_coordinate t (fun a=>if 2*bit a-1=(if b then 1 else -1) then (1:ℝ) else 0)]
    by_cases hb : b <;> norm_num [bit,hb]
  · apply bounded_support_limit_obstruction sparseStudy _ normalCDF 1 1
    · intro t z
      rw [sparse_statistic]
      change 2*bit (z (⟨0,by simp [sparseStudy]⟩))-1≤1
      cases hz : z (⟨0,by simp [sparseStudy]⟩) <;> norm_num [bit,hz]
    · norm_num
    · have hf : normalCDF=(fun x=>cdf (gaussianReal 0 1) x) := by
        funext x
        rw [cdf_eq_real]
        rfl
      rw [hf]
      exact AronowAudit.P053.NormalCompletion.cdf_continuousAt (gaussianReal 0 1) 1
    · have hs:=AronowAudit.P053.NormalCompletion.strictMono_normal_cdf (by norm_num : (1:ℝ)<2)
      have hu:=cdf_le_one (μ:=gaussianReal 0 1) 2
      have he : normalCDF 1=cdf (gaussianReal 0 1) 1 := by rw [cdf_eq_real];rfl
      rw [he]
      exact hs.trans_le hu
end
end AronowAudit.P009.SparseCompletion


namespace AronowAudit.P009
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
/-- T7, p. 693: the explicit sparse Bernoulli sequence has bounded maximum
degree and positive true variance but its standardized law is always the fair
two-point {-1,1} law, so it does not converge to the standard normal law. -/
theorem sparse_normal_counterexample :
    RegularSequence sparseStudy 2 4 1 ∧
    Restricted sparseStudy ∧
    (∀ t, Bernoulli (sparseStudy.experiment t) ∧
      NoInterference (sparseStudy.experiment t) ∧ dAvg (sparseStudy.experiment t) = 1 ∧
      dMax (sparseStudy.experiment t) = 1 ∧
      var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t)) > 0) ∧
    Tendsto (fun t => size sparseStudy t *
      var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t))) atTop (nhds 0) ∧
    (∀ t b, prob (sparseStudy.experiment t).design (fun z =>
      (ht (sparseStudy.experiment t) z - eate (sparseStudy.experiment t)) /
        Real.sqrt (var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t))) =
        (if b then 1 else -1)) = 1/2) ∧
    ¬ InDistribution sparseStudy (fun t z =>
      (ht (sparseStudy.experiment t) z - eate (sparseStudy.experiment t)) /
        Real.sqrt (var (sparseStudy.experiment t).design (ht (sparseStudy.experiment t)))) normalCDF := by
  exact SparseCompletion.sparse_normal_counterexample_completed

/-- T8, corrected normal approximation (p. 693): under Bernoulli assignment,
original Assumption 1 with q≥2, bounded d_MAX and positive liminf of n Var(HT)
give normal convergence after division by the true standard deviation.
No estimated-error claim. -/
theorem corrected_normal_approximation (S : Study) (k q s : ℝ)
    (hReg : RegularSequence S k q s) (hBER : ∀ t, Bernoulli (S.experiment t))
    (hDegree : ∃ D, ∀ t, dMax (S.experiment t) ≤ D)
    (hVariance : PositiveLiminf (fun t => size S t *
      var (S.experiment t).design (ht (S.experiment t)))) :
    InDistribution S (fun t z => (ht (S.experiment t) z - eate (S.experiment t)) /
      Real.sqrt (var (S.experiment t).design (ht (S.experiment t)))) normalCDF := by
  exact NormalCompletion.corrected_normal_approximation_completed S k q s hReg hBER hDegree hVariance

end
end AronowAudit.P009

