/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Complex pole geometry and uniform real Taylor bounds for the logistic function.
The argument uses Mathlib's Cauchy formula, analytic identity theorem,
power-series uniqueness and geometric tail estimate.
-/
import AronowAudit.P015.P015_TaylorCompletion
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.Sigmoid

namespace AronowAudit.P015.UniformTaylorCompletion
open Complex Set Filter Metric
open scoped Topology ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

abbrev fc := TaylorCompletion.fc
def poleRadius (c : ℝ) : ℝ := Real.sqrt (c^2+Real.pi^2)
lemma poleRadius_pos (c : ℝ) : 0 < poleRadius c := by
  unfold poleRadius
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg c,Real.pi_pos]

lemma denominator_re_zero (z : ℂ) (hz : 1+Complex.exp (-z)=0) : z.re=0 := by
  have he : Complex.exp (-z)=Complex.exp (Real.pi*Complex.I) := by
    rw [Complex.exp_pi_mul_I]
    linear_combination hz
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hr := congrArg Complex.re hk
  simpa using hr

lemma denominator_distance (c : ℝ) (z : ℂ) (hz : 1+Complex.exp (-z)=0) : poleRadius c ≤ ‖z-c‖ := by
  have hr := denominator_re_zero z hz
  have hn := TaylorCompletion.denominator_norm_ge_pi z hz
  have hsq := Complex.sq_norm_sub_sq_re z
  have hsq' := Complex.sq_norm_sub_sq_re (z-(c:ℂ))
  simp only [hr,zero_pow,sub_zero,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,zero_sub] at hsq hsq'
  have hsqrt : poleRadius c^2=c^2+Real.pi^2 := Real.sq_sqrt (by positivity)
  have hp := Real.sqrt_nonneg (c^2+Real.pi^2)
  change 0≤poleRadius c at hp
  nlinarith [Complex.norm_nonneg z,Complex.norm_nonneg (z-(c:ℂ)),Real.pi_pos]

lemma denominator_ne_zero (c : ℝ) (z : ℂ) (hz : ‖z-c‖<poleRadius c) : 1+Complex.exp (-z)≠0 := by
  intro h
  exact (not_le_of_gt hz) (denominator_distance c z h)

lemma radius_lower (c : ℝ) (s : FormalMultilinearSeries ℂ ℂ ℂ)
    (hs : HasFPowerSeriesAt fc s (c:ℂ)) : ENNReal.ofReal (poleRadius c) ≤ s.radius := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hrc
  have hri : (r:ℝ)<poleRadius c := by simpa using hrc
  obtain ⟨R,hrR,hRc⟩ := exists_between hri
  let Rn : NNReal := ⟨R,(lt_of_le_of_lt r.coe_nonneg hrR).le⟩
  have hd : DifferentiableOn ℂ fc (closedBall (c:ℂ) Rn) := by
    intro z hz
    apply (TaylorCompletion.differentiableAt_fc z (denominator_ne_zero c z ?_)).differentiableWithinAt
    have hh : ‖z-(c:ℂ)‖≤(Rn:ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hz
    exact hh.trans_lt hRc
  have hp := hd.hasFPowerSeriesOnBall (show 0<Rn from by exact_mod_cast (lt_of_le_of_lt r.coe_nonneg hrR))
  have heq := hs.eq_formalMultilinearSeries hp.hasFPowerSeriesAt
  rw [heq]
  exact (show (r:ENNReal)≤Rn from by exact_mod_cast hrR.le).trans hp.r_le

lemma pole_distance (c : ℝ) : ‖(Real.pi*Complex.I:ℂ)-(c:ℂ)‖=poleRadius c := by
  rw [Complex.norm_def,Complex.normSq_apply]
  unfold poleRadius
  congr 1
  simp
  <;> ring

lemma radius_upper (c : ℝ) (s : FormalMultilinearSeries ℂ ℂ ℂ)
    (hs : HasFPowerSeriesAt fc s (c:ℂ)) : s.radius≤ENNReal.ofReal (poleRadius c) := by
  by_contra h
  have hgt : ENNReal.ofReal (poleRadius c)<s.radius := lt_of_not_ge h
  have hpos : 0<s.radius := (ENNReal.ofReal_pos.mpr (poleRadius_pos c)).trans hgt
  let F : ℂ → ℂ := fun z=>(1+Complex.exp (-z))*s.sum (z-c)
  have hF : AnalyticOnNhd ℂ F (Metric.eball (c:ℂ) s.radius) := by
    intro z hz
    have hm : AnalyticAt ℂ (fun z=>s.sum (z-c)) z := by
      have hg : AnalyticAt ℂ (fun w : ℂ=>w-(c:ℂ)) z := analyticAt_id.sub analyticAt_const
      have ho : AnalyticAt ℂ s.sum (z-c) := s.analyticOnNhd _ (by
        simpa only [Metric.mem_eball,edist_dist,dist_zero_right,dist_eq_norm,sub_zero] using hz)
      exact AnalyticAt.comp (g := s.sum) (f := fun w : ℂ => w-(c:ℂ)) (x := z) ho hg
    exact (analyticAt_const.add (analyticAt_cexp.comp analyticAt_id.neg)).mul hm
  obtain ⟨r,hr⟩ := hs
  have hnear : F=ᶠ[𝓝 (c:ℂ)] (fun _=>1) := by
    have hden0 : 1+Complex.exp (-(c:ℂ))≠0 := denominator_ne_zero c c (by simpa using poleRadius_pos c)
    have hd : ∀ᶠ z in 𝓝 (c:ℂ),1+Complex.exp (-z)≠0 :=
      (continuous_const.add (Complex.continuous_exp.comp continuous_neg)).continuousAt.eventually_ne hden0
    filter_upwards [Metric.eball_mem_nhds (c:ℂ) hr.r_pos,hd] with z hz hden
    have hshift : z-(c:ℂ)∈Metric.eball (0:ℂ) r := by
      simpa only [Metric.mem_eball,edist_dist,dist_zero_right,dist_eq_norm,sub_zero] using hz
    have he : s.sum (z-c)=fc z := by simpa using (hr.sum hshift).symm
    change (1+Complex.exp (-z))*s.sum (z-c)=1
    rw [he]
    exact mul_inv_cancel₀ hden
  have hpole : (Real.pi*Complex.I:ℂ)∈Metric.eball (c:ℂ) s.radius := by
    simpa only [Metric.mem_eball,edist_dist,dist_eq_norm,pole_distance] using hgt
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    isPreconnected_eball (by simpa using hpos) hnear hpole
  have he : Complex.exp (-(Real.pi*Complex.I))= -1 := by
    rw [Complex.exp_neg,Complex.exp_pi_mul_I]
    norm_num
  simp only [F,he,add_neg_cancel,zero_mul] at heq
  exact zero_ne_one heq

theorem real_center_radius (c : ℝ) : ∃ s : FormalMultilinearSeries ℂ ℂ ℂ,
    HasFPowerSeriesAt fc s (c:ℂ) ∧ s.radius=ENNReal.ofReal (poleRadius c) := by
  have ha : AnalyticAt ℂ fc (c:ℂ) :=
    (analyticAt_const.add (analyticAt_cexp.comp analyticAt_id.neg)).inv
      (denominator_ne_zero c c (by simpa using poleRadius_pos c))
  obtain ⟨s,hs⟩ := ha
  exact ⟨s,hs,le_antisymm (radius_upper c s hs) (radius_lower c s hs)⟩

def realSeries (s : FormalMultilinearSeries ℂ ℂ ℂ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  Complex.reCLM.compFormalMultilinearSeries
    ((s.restrictScalars ℝ).compContinuousLinearMap Complex.ofRealCLM)

lemma realSeries_apply (s : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) (x : ℝ) :
    realSeries s n (fun _=>x)=(s n (fun _=>(x:ℂ))).re := rfl

lemma realSeries_hasPower {f : ℂ → ℂ} {g : ℝ → ℝ} {s : FormalMultilinearSeries ℂ ℂ ℂ}
    {c : ℝ} {R : ENNReal} (hf : HasFPowerSeriesOnBall f s (c:ℂ) R)
    (hreal : ∀x : ℝ,(f (x:ℂ)).re=g x) : HasFPowerSeriesOnBall g (realSeries s) c R := by
  have hh := Complex.reCLM.comp_hasFPowerSeriesOnBall
    ((hf.restrictScalars (𝕜 := ℝ)).compContinuousLinearMap (u:=Complex.ofRealCLM) (x:=c))
  simp only [Complex.ofRealCLM_enorm,div_one] at hh
  convert hh using 1
  · ext x
    exact (hreal x).symm
  · rfl

lemma realSeries_partialSum {f : ℂ → ℂ} {g : ℝ → ℝ} {s : FormalMultilinearSeries ℂ ℂ ℂ}
    {c : ℝ} {R : ENNReal} (hf : HasFPowerSeriesOnBall f s (c:ℂ) R)
    (hreal : ∀x : ℝ,(f (x:ℂ)).re=g x) (N : ℕ) (a : ℝ) :
    (realSeries s).partialSum (N+1) (a-c)=taylorWithinEval g N univ c a := by
  have hp := realSeries_hasPower hf hreal
  have hc := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (AnalyticAt.hasFPowerSeriesAt hp.analyticAt)
  rw [hc,FormalMultilinearSeries.partialSum,taylor_within_apply]
  apply Finset.sum_congr rfl
  intro n _
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars,Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
    iteratedDerivWithin_univ]
  ring

lemma cauchy_coeff_bound (f : ℂ → ℂ) (c : ℂ) (R M : ℝ) (hR : 0<R)
    (hM : ∀z∈sphere c R,‖f z‖≤M) (n : ℕ) :
    ‖cauchyPowerSeries f c R n‖≤M*R⁻¹^n := by
  have hbound (z : ℂ) (hz : z∈sphere c R) :
      ‖(z-c)⁻¹^n • (z-c)⁻¹ • f z‖≤M/R^(n+1) := by
    simp only [norm_smul,norm_pow,norm_inv,mem_sphere_iff_norm.mp hz]
    calc
      R⁻¹^n*(R⁻¹*‖f z‖) ≤ R⁻¹^n*(R⁻¹*M) := by gcongr;exact hM z hz
      _ = M/R^(n+1) := by rw [inv_pow,pow_succ];field_simp [hR.ne']
  calc
    ‖cauchyPowerSeries f c R n‖ = ‖(2*Real.pi*Complex.I:ℂ)⁻¹ •
      ∮z in C(c,R),(z-c)⁻¹^n • (z-c)⁻¹ • f z‖ := by simp [cauchyPowerSeries]
    _ ≤ R*(M/R^(n+1)) := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hbound
    _ = M*R⁻¹^n := by rw [inv_pow, pow_succ];field_simp [hR.ne']

lemma real_taylor_cauchy_bound (f : ℂ → ℂ) (g : ℝ → ℝ) (c r M : ℝ) (R : NNReal)
    (hR : 0<R) (hr : 0≤r) (hrR : r<R)
    (hd : DifferentiableOn ℂ f (closedBall (c:ℂ) R))
    (hreal : ∀x : ℝ,(f (x:ℂ)).re=g x)
    (hM0 : 0≤M) (hM : ∀z∈sphere (c:ℂ) R,‖f z‖≤M)
    (N : ℕ) (a : ℝ) (ha : |a-c|≤r) :
    |g a-taylorWithinEval g N univ c a|≤M*(r/(R:ℝ))^(N+1)/(1-r/(R:ℝ)) := by
  let s := cauchyPowerSeries f (c:ℂ) R
  have hp : HasFPowerSeriesOnBall f s (c:ℂ) R := hd.hasFPowerSeriesOnBall hR
  have hpr := realSeries_hasPower hp hreal
  have hRpos : 0<(R:ℝ) := by exact_mod_cast hR
  have hratio : r/(R:ℝ)<1 := (div_lt_one hRpos).mpr hrR
  have hgeometric (n : ℕ) : ‖realSeries s n (fun _=>a-c)‖≤M*(r/(R:ℝ))^n := by
    rw [realSeries_apply,Real.norm_eq_abs]
    calc
      |(s n (fun _=>((a-c:ℝ):ℂ))).re| ≤ ‖s n (fun _=>((a-c:ℝ):ℂ))‖ := Complex.abs_re_le_norm _
      _ ≤ ‖s n‖*|a-c|^n := by simpa only [Complex.norm_real,Real.norm_eq_abs,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using (s n).le_opNorm (fun _=>((a-c:ℝ):ℂ))
      _ ≤ (M*(R:ℝ)⁻¹^n)*r^n := mul_le_mul
        (cauchy_coeff_bound f (c:ℂ) R M hRpos hM n) (pow_le_pow_left₀ (abs_nonneg _) ha n)
        (pow_nonneg (abs_nonneg _) n) (mul_nonneg hM0 (by positivity))
      _ = M*(r/(R:ℝ))^n := by rw [div_eq_mul_inv,mul_pow];ring
  have hδ : a-c∈Metric.eball (0:ℝ) (R:ENNReal) := by
    rw [mem_eball,edist_dist,Real.dist_eq,sub_zero,ENNReal.ofReal_lt_coe_iff]
    · exact ha.trans_lt hrR
    · exact abs_nonneg _
  have hsum : HasSum (fun n=>realSeries s n (fun _=>a-c)) (g a) := by
    simpa using hpr.hasSum hδ
  have hb := norm_sub_le_of_geometric_bound_of_hasSum hratio hgeometric hsum (N+1)
  rw [← FormalMultilinearSeries.partialSum,realSeries_partialSum hp hreal N a] at hb
  simpa only [Real.norm_eq_abs,abs_sub_comm] using hb


lemma real_fc (x : ℝ) : (fc (x:ℂ)).re=Real.sigmoid x := by
  have he : fc (x:ℂ)=(Real.sigmoid x:ℂ) := by
    simp only [fc,TaylorCompletion.fc,Real.sigmoid_def,Complex.ofReal_inv,
      Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_exp,Complex.ofReal_neg]
  rw [he,Complex.ofReal_re]

lemma uniform_sigmoid_taylor (c r ρ : ℝ) (hr : 0≤r) (hrρ : r<ρ)
    (hρ : ρ<poleRadius c) :
    let M := sSup ((fun z : ℂ=>‖fc z‖) '' sphere (c:ℂ) ρ)
    (∀ N : ℕ,∀ a : ℝ,|a-c|≤r →
      |Real.sigmoid a-taylorWithinEval Real.sigmoid N univ c a|≤M*(r/ρ)^(N+1)/(1-r/ρ)) ∧
    Tendsto (fun N : ℕ=>M*(r/ρ)^(N+1)/(1-r/ρ)) atTop (𝓝 0) := by
  let M := sSup ((fun z : ℂ=>‖fc z‖) '' sphere (c:ℂ) ρ)
  have hρpos : 0<ρ := hr.trans_lt hrρ
  have hd : DifferentiableOn ℂ fc (closedBall (c:ℂ) ρ) := by
    intro z hz
    apply (TaylorCompletion.differentiableAt_fc z ?_).differentiableWithinAt
    apply denominator_ne_zero c z
    exact (mem_closedBall_iff_norm.mp hz).trans_lt hρ
  have hcont : ContinuousOn (fun z : ℂ=>‖fc z‖) (sphere (c:ℂ) ρ) :=
    hd.continuousOn.norm.mono sphere_subset_closedBall
  have hMbound : BddAbove ((fun z : ℂ=>‖fc z‖) '' sphere (c:ℂ) ρ) :=
    (isCompact_sphere (c:ℂ) ρ).bddAbove_image hcont
  have hM (z : ℂ) (hz : z∈sphere (c:ℂ) ρ) : ‖fc z‖≤M :=
    le_csSup hMbound (mem_image_of_mem _ hz)
  have hz : (c:ℂ)+ρ∈sphere (c:ℂ) ρ := by
    rw [mem_sphere_iff_norm]
    simpa using abs_of_pos hρpos
  have hM0 : 0≤M := (norm_nonneg _).trans (hM _ hz)
  refine ⟨?_,?_⟩
  · intro N a ha
    exact real_taylor_cauchy_bound fc Real.sigmoid c r M ⟨ρ,hρpos.le⟩
      hρpos hr hrρ hd real_fc hM0 hM N a ha
  · have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr hρpos.le)
      ((div_lt_one hρpos).mpr hrρ)
    have hs : Tendsto (fun N : ℕ=>(r/ρ)^(N+1)) atTop (𝓝 0) := by
      simpa only [pow_succ,zero_mul] using hp.mul_const (r/ρ)
    simpa only [mul_zero,zero_div] using (hs.const_mul M).div_const (1-r/ρ)

end
end AronowAudit.P015.UniformTaylorCompletion
