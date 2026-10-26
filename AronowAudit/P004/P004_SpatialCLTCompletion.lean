import AronowAudit.P004.P004_VarianceCompletion
import AronowAudit.P061.P061_Foundations
import AronowAudit.External.Causalean.Mathlib.Probability.SteinMethod.AlmostEverywhereDepGraphCLT

namespace AronowAudit.P004.CLTCompletion
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 def atomicDesign {N : ℕ} (p : Fin N→ℝ) (hp : ∀ i,0<p i ∧ p i<1) : AronowAudit.P061.Design (Assignment N) where
  p:=designWeight p
  nonneg:=design_weight_nonneg p hp
  summable:=Summable.of_finite
  total:=by simpa only [tsum_fintype] using design_normalized p

 def designMeasure {N : ℕ} (p : Fin N→ℝ) (hp : ∀ i,0<p i ∧ p i<1) : Measure (Assignment N) :=
  AronowAudit.P061.designLaw (atomicDesign p hp) id

 instance designMeasure_probability {N : ℕ} (p : Fin N→ℝ) (hp : ∀ i,0<p i ∧ p i<1) :
    IsProbabilityMeasure (designMeasure p hp) := by
  dsimp [designMeasure]
  infer_instance

theorem designMeasure_integral {N : ℕ} (p : Fin N→ℝ) (hp : ∀ i,0<p i ∧ p i<1) (F : Assignment N→ℝ) :
    (∫ z,F z ∂designMeasure p hp)=expect p F := by
  have hi : MeasureTheory.Integrable F (designMeasure p hp) := MeasureTheory.Integrable.of_finite
  rw [designMeasure,AronowAudit.P061.designLaw] at hi ⊢
  rw [integral_sum_measure hi]
  simp only [tsum_fintype,integral_smul_measure,integral_dirac,id_eq,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z _
  change (ENNReal.ofReal (designWeight p z)).toReal * F z = _
  rw [ENNReal.toReal_ofReal (design_weight_nonneg p hp z)]

theorem designMeasure_apply {N : ℕ} (p : Fin N→ℝ) (hp : ∀ i,0<p i ∧ p i<1) (S : Set (Assignment N)) :
    (designMeasure p hp S).toReal=prob p (fun z=>z∈S) := by
  have hh := AronowAudit.P061.designLaw_apply (atomicDesign p hp) id S (Set.to_countable S).measurableSet
  change (designMeasure p hp S).toReal=_ at hh
  rw [hh]
  simp only [AronowAudit.P061.probability,tsum_fintype,prob,expect,atomicDesign,id_eq,mul_ite,mul_one,mul_zero]

theorem finiteGraph_to_measureGraph {N : ℕ} (p : Fin N→ℝ) (hp : ∀ i,0<p i ∧ p i<1)
    (V : CircleTable N) (B : Fin N→Finset (Fin N)) (h : FiniteDependencyGraph p V B) :
    DependencyGraph (designMeasure p hp) V B := by
  refine ⟨h.1,h.2.1,?_⟩
  intro I J hsep
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro S T hS hT
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul,designMeasure_apply,designMeasure_apply,designMeasure_apply]
  simpa only [Set.mem_inter_iff,Set.mem_preimage] using h.2.2 I J hsep (fun v=>v∈S) (fun v=>v∈T)

theorem circleAverage_abs_le {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (d b : ℝ) (hWD : WellDefined P d)
    (hb : ∀ x z,|(P.outcome x z)|≤b) (i : Fin N) (z : Assignment N) :
    |circleAverage P d i z|≤b := by
  letI : IsFiniteMeasure (P.zeta.restrict (region P i d)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (hWD i).2.2.1⟩
  have hm : 0<(P.zeta (region P i d)).toReal :=
    ENNReal.toReal_pos (hWD i).2.1.ne' (hWD i).2.2.1.ne
  rw [circleAverage,abs_div,abs_of_pos hm]
  apply (div_le_iff₀ hm).mpr
  calc
    _ ≤ ∫ x in region P i d,|(P.outcome x z)| ∂P.zeta := abs_integral_le_integral_abs
    _ ≤ ∫ x in region P i d,b ∂P.zeta := integral_mono ((hWD i).2.2.2 z).abs (integrable_const b) (fun x=>hb x z)
    _ = _ := by simp [integral_const,measureReal_def,smul_eq_mul,mul_comm]

theorem nodeSeparation_self {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i : Fin N) : nodeSeparation P i i=0 := by
  have hz : (0:ℝ)∈{r:ℝ|∃ x∈P.node i,∃ y∈P.node i,dist x y=r} := by
    obtain ⟨x,hx⟩:=P.node_nonempty i
    exact ⟨x,hx,x,hx,dist_self x⟩
  have hn : ∀ r∈{r:ℝ|∃ x∈P.node i,∃ y∈P.node i,dist x y=r},0≤r := by
    rintro r ⟨x,hx,y,hy,hr⟩
    rw [←hr]
    exact dist_nonneg
  exact le_antisymm (csInf_le ⟨0,hn⟩ hz) (le_csInf ⟨0,hz⟩ hn)

theorem nodeSeparation_symm {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (i j : Fin N) : nodeSeparation P i j=nodeSeparation P j i := by
  unfold nodeSeparation
  congr 1
  ext r
  constructor
  · rintro ⟨x,hx,y,hy,hr⟩
    exact ⟨y,hy,x,hx,by simpa only [dist_comm] using hr⟩
  · rintro ⟨y,hy,x,hx,hr⟩
    exact ⟨x,hx,y,hy,by simpa only [dist_comm] using hr⟩


 def centeredHT {N : ℕ} (p : Fin N→ℝ) (R : CircleTable N) : CircleTable N :=
  fun i z=>residualContrast p R (fun _ _=>0) i z-nodeEffect p R i

theorem centeredHT_mean {N : ℕ} (p : Fin N→ℝ) (R : CircleTable N)
    (hp : ∀i,0<p i ∧ p i<1) (i : Fin N) : expect p (centeredHT p R i)=0 := by
  change expect p (fun z=>residualContrast p R (fun _ _=>0) i z-nodeEffect p R i)=0
  rw [expect_sub,residualContrast_mean p R (fun _ _=>0) i hp,expect_const]
  simp [residualEffect]

theorem centeredHT_sum {N : ℕ} (p : Fin N→ℝ) (R : CircleTable N) (hN : 0<N) (z : Assignment N) :
    (∑i,centeredHT p R i z)=(N:ℝ)*(ht p R z-ame p R) := by
  have hn : (N:ℝ)≠0:=by exact_mod_cast hN.ne'
  simp only [centeredHT,Finset.sum_sub_distrib,ht,ame,residualContrast,sub_zero]
  field_simp

theorem centeredHT_second {N : ℕ} (p : Fin N→ℝ) (R : CircleTable N)
    (hp : ∀i,0<p i ∧ p i<1) (hN : 0<N) :
    expect p (fun z=>(∑i,centeredHT p R i z)^2)=(N:ℝ)^2*variance p (ht p R) := by
  simp_rw [centeredHT_sum p R hN,mul_pow]
  rw [expect_mul]
  congr 1
  rw [variance,cov_centered,ht_unbiased p R hp]
  congr 1
  funext z
  ring

theorem raw_contrast_abs_le {N : ℕ} (p b : ℝ) (R : CircleTable N)
    (hp : 0<p ∧ p<1) (hb : 0≤b) (hR : ∀i z,|R i z|≤b) (i : Fin N) (z : Assignment N) :
    |residualContrast (fun _=>p) R (fun _ _=>0) i z|≤b/p+b/(1-p) := by
  have hp' : 0<1-p:=sub_pos.mpr hp.2
  have ha:=hR i z
  have h0:=div_nonneg hb hp.1.le
  have h1:=div_nonneg hb hp'.le
  cases hz : z i
  · simp only [residualContrast,hz,bit,Bool.false_eq_true,if_false,zero_mul,sub_zero,zero_div,sub_zero,sub_self,one_mul,zero_sub,abs_neg,abs_div,abs_of_pos hp']
    exact (div_le_div_of_nonneg_right ha hp'.le).trans (by linarith)
  · simp only [residualContrast,hz,bit,if_true,one_mul,sub_zero,sub_self,zero_mul,zero_div,sub_zero,abs_div,abs_of_pos hp.1]
    exact (div_le_div_of_nonneg_right ha hp.1.le).trans (by linarith)

theorem centeredHT_abs_le {N : ℕ} (p b : ℝ) (R : CircleTable N)
    (hp : 0<p ∧ p<1) (hb : 0≤b) (hR : ∀i z,|R i z|≤b) (i : Fin N) (z : Assignment N) :
    |centeredHT (fun _=>p) R i z|≤2*(b/p+b/(1-p)) := by
  let T:=residualContrast (fun _:Fin N=>p) R (fun _ _=>0) i
  let C:=b/p+b/(1-p)
  have hT : ∀z,|T z|≤C:=raw_contrast_abs_le p b R hp hb hR i
  have hl:=expect_mono (fun _:Fin N=>p) (fun _=>hp) (fun _=> -C) T (fun z=>(abs_le.mp (hT z)).1)
  have hu:=expect_mono (fun _:Fin N=>p) (fun _=>hp) T (fun _=>C) (fun z=>(abs_le.mp (hT z)).2)
  rw [expect_const] at hl hu
  have hm : expect (fun _=>p) T=nodeEffect (fun _=>p) R i := by
    simpa [T,residualEffect] using residualContrast_mean (fun _:Fin N=>p) R (fun _ _=>0) i (fun _=>hp)
  rw [hm] at hl hu
  have hc : |nodeEffect (fun _=>p) R i|≤C:=abs_le.mpr ⟨hl,hu⟩
  change |T z-nodeEffect (fun _=>p) R i|≤2*C
  have ht:=abs_le.mp (hT z)
  have hc' :=abs_le.mp hc
  apply abs_le.mpr
  constructor <;> linarith

theorem centeredHT_graph {N : ℕ} (p : Fin N→ℝ) (R : CircleTable N)
    (B : Fin N→Finset (Fin N)) (hp : ∀i,0<p i ∧ p i<1)
    (hG : FiniteDependencyGraph p (fun i z=>residualContrast p R (fun _ _=>0) i z) B) :
    DependencyGraph (designMeasure p hp) (centeredHT p R) B := by
  have h:=finiteGraph_to_measureGraph p hp _ B hG
  refine ⟨h.1,h.2.1,?_⟩
  intro I J hsep
  have hh:=(h.2.2 I J hsep).comp
    (φ:=fun v : I→ℝ=>fun i=>v i-nodeEffect p R i)
    (ψ:=fun v : J→ℝ=>fun i=>v i-nodeEffect p R i)
    (by fun_prop) (by fun_prop)
  exact hh


theorem ht_clt_shift (K : ℕ) (p b v : ℝ) (R : ∀N,CircleTable N)
    (B : ∀N,Fin N→Finset (Fin N)) (hp : 0<p ∧ p<1) (hb : 0≤b)
    (hv : 0<v) (hN : ∀n,0<n+K)
    (hR : ∀n i z,|R (n+K) i z|≤b)
    (hG : ∀n,FiniteDependencyGraph (fun _=>p)
      (fun i z=>residualContrast (fun _=>p) (R (n+K)) (fun _ _=>0) i z) (B (n+K)))
    (D : ℕ) (hdeg : ∀n i,(B (n+K) i).card≤D)
    (hvar : ∀n,v≤((n+K:ℕ):ℝ)*variance (fun _=>p) (ht (fun _=>p) (R (n+K)))) :
    ∀x,Tendsto (fun n=>prob (fun _:Fin (n+K)=>p) (fun z=>
      (ht (fun _=>p) (R (n+K)) z-ame (fun _=>p) (R (n+K)))/
      Real.sqrt (variance (fun _=>p) (ht (fun _=>p) (R (n+K))))≤x)) atTop (𝓝 (normalCDF x)) := by
  let μ:=fun n=>designMeasure (fun _:Fin (n+K)=>p) (fun _=>hp)
  let X:=fun n=>centeredHT (fun _:Fin (n+K)=>p) (R (n+K))
  have hgraph (n : ℕ) : DependencyGraph (μ n) (X n) (B (n+K)):=centeredHT_graph _ _ _ (fun _=>hp) (hG n)
  let Dep : ∀n,Causalean.Mathlib.Probability.SteinMethod.DepGraph (X n) (μ n):=fun n=>{
    G:=fun i j=>j∈B (n+K) i
    decG:=inferInstance
    refl:=(hgraph n).1
    symm:=fun i j hij=>((hgraph n).2.1 i j).mp hij
    meas:=fun i=>measurable_of_finite _
    indep:=(hgraph n).2.2 }
  have hdeg' (n : ℕ) (i : Fin (n+K)) : ((Dep n).nbhd i).card≤D:=by
    have he : (Dep n).nbhd i=B (n+K) i:=by
      ext j
      exact (Dep n).mem_nbhd_iff
    rw [he]
    exact hdeg n i
  let vN:=fun n=>((n+K:ℕ):ℝ)^2*variance (fun _=>p) (ht (fun _=>p) (R (n+K)))
  have hmean (n : ℕ) (i : Fin (n+K)) : (∫z,X n i z ∂μ n)=0:=by
    rw [designMeasure_integral]
    exact centeredHT_mean _ _ (fun _=>hp) i
  have hsecond (n : ℕ) : (∫z,(Causalean.Mathlib.Probability.SteinMethod.depSum (X n) z)^2 ∂μ n)=vN n:=by
    rw [designMeasure_integral]
    exact centeredHT_second _ _ (fun _=>hp) (hN n)
  have hfloor : ∀ᶠ n in atTop,v*(Fintype.card (Fin (n+K)):ℝ)≤vN n:=by
    filter_upwards [] with n
    dsimp [vN]
    simpa only [Fintype.card_fin,pow_two,mul_assoc,mul_comm,mul_left_comm] using
      mul_le_mul_of_nonneg_left (hvar n) (Nat.cast_nonneg (n+K):0≤((n+K:ℕ):ℝ))
  intro x
  have hh:=Causalean.Mathlib.Probability.SteinMethod.bounded_degree_dependency_clt_ae
    μ X Dep D hdeg' (2*(b/p+b/(1-p)))
    (fun n i=>Filter.Eventually.of_forall (centeredHT_abs_le p b (R (n+K)) hp hb (hR n) i))
    hmean vN hsecond v hv hfloor
    (by simpa only [Fintype.card_fin] using tendsto_add_atTop_nat K) x
  apply hh.congr
  intro n
  rw [MeasureTheory.map_measureReal_apply (measurable_of_finite _) measurableSet_Iic]
  change (designMeasure (fun _:Fin (n+K)=>p) (fun _=>hp) _).toReal=_
  rw [designMeasure_apply]
  congr 1
  funext z
  have hn : ((n+K:ℕ):ℝ)≠0:=by exact_mod_cast (hN n).ne'
  have hsqrt : Real.sqrt (vN n)=((n+K:ℕ):ℝ)*Real.sqrt (variance (fun _=>p) (ht (fun _=>p) (R (n+K)))):=by
    dsimp [vN]
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]
  simp only [Causalean.Mathlib.Probability.SteinMethod.depSum,X,centeredHT_sum _ _ (hN n),hsqrt,
    mul_div_mul_left _ _ hn,Set.mem_preimage,Set.mem_Iic]


end
end AronowAudit.P004.CLTCompletion

namespace AronowAudit.P004
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter CLTCompletion
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

variable {Space : ℕ→Type*} [∀N,MetricSpace (Space N)] [∀N,MeasurableSpace (Space N)]
/-- T41, Proposition 2, p. 754: the HT central limit statement
under C1–C4 and its own actual variance lower bound. -/
theorem ht_central_limit (P : PopulationSequence Space) (p d : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hP : SpatialLocalConditions P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hv : Nondegenerate (fun N => variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)))) :
    NormalLimit (fun _ _ => p) (fun N z =>
      (ht (fun _ => p) (circleAverage (P N) d) z - ame (fun _ => p) (circleAverage (P N) d)) /
        Real.sqrt (variance (fun _ => p) (ht (fun _ => p) (circleAverage (P N) d)))) := by
  obtain ⟨b,hb,hbout⟩:=hP.1
  obtain ⟨h,hh,hloc⟩:=hP.2.1
  obtain ⟨c,hc⟩:=hP.2.2
  obtain ⟨v,hv,hvN⟩:=hv
  let R:=fun N=>circleAverage (P N) d
  let B : ∀N,Fin N→Finset (Fin N):=fun N i=>ball (nodeSeparation (P N)) i (h d)
  have hevent : ∀ᶠ N in atTop,0<N ∧ (∀i z,|R N i z|≤b) ∧
      LocalAt (R N) (nodeSeparation (P N)) (h d) ∧
      (∀i,((B N i).card:ℝ)≤c (h d)) ∧
      v≤(N:ℝ)*variance (fun _=>p) (ht (fun _=>p) (R N)) := by
    filter_upwards [eventually_gt_atTop 0,hbout,hWD,hloc d hd,hc (h d) (hh d hd),hvN] with N hN hbN hwdN hlocN hcN hvN
    refine ⟨hN,?_,hlocN,hcN,hvN⟩
    intro i z
    exact circleAverage_abs_le (P N) d b hwdN (fun x z=>(hbN x z).le) i z
  obtain ⟨K,hK⟩:=Filter.eventually_atTop.mp hevent
  have hk (n : ℕ):=hK (n+K) (Nat.le_add_left K n)
  have hG (n : ℕ) : FiniteDependencyGraph (fun _=>p)
      (fun i z=>residualContrast (fun _=>p) (R (n+K)) (fun _ _=>0) i z) (B (n+K)) := by
    apply design_dependency_graph _ _ _ _ (fun _=>hp)
    · intro i
      simp only [B,ball,Finset.mem_filter,Finset.mem_univ,true_and,nodeSeparation_self]
      exact hh d hd
    · intro i j
      simp only [B,ball,Finset.mem_filter,Finset.mem_univ,true_and]
      rw [nodeSeparation_symm (P (n+K)) i j]
    · intro i j hj
      apply (hk n).2.2.1 i j
      simpa only [B,ball,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hj
  have hdeg : ∀n i,(B (n+K) i).card≤Nat.ceil (c (h d)):=by
    intro n i
    exact_mod_cast ((hk n).2.2.2.1 i).trans (Nat.le_ceil (c (h d)))
  intro x
  apply (tendsto_add_atTop_iff_nat K).mp
  exact ht_clt_shift K p b v R B hp hb.le hv (fun n=>(hk n).1)
    (fun n=>(hk n).2.1) hG (Nat.ceil (c (h d))) hdeg
    (fun n=>(hk n).2.2.2.2) x


end
end AronowAudit.P004
