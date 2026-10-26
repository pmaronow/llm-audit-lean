/- P011 T3(iii): sample-variance concentration. The moving centre retains average marginal variance plus between-unit mean spread, allowing heterogeneous means and variances. -/
import AronowAudit.P011.P011_ExpectationCompletion

namespace AronowAudit.P011.SampleCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open Causalean.Mathlib.Probability.SteinMethod
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
local instance : ENNReal.HolderTriple (4:ENNReal) 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]⟩

lemma bounded_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω→ℝ) (hX : Measurable X) (B : ℝ)
    (hb : ∀ᵐ ω ∂μ, |X ω|≤B) (p : ENNReal) : MemLp X p μ := by
  exact MemLp.of_bound hX.aestronglyMeasurable B
    (hb.mono fun ω hω => by simpa only [Real.norm_eq_abs] using hω)

lemma bounded_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω→ℝ) (hX : Measurable X) (B : ℝ) (hB : 0≤B)
    (hb : ∀ᵐ ω ∂μ, |X ω|≤B) : ProbabilityTheory.variance X μ≤B^2 := by
  have h2 := bounded_memLp μ X hX B hb 2
  have hs : (∫ω,X ω^2∂μ)≤B^2 := by
    calc
      _ ≤ ∫_,B^2∂μ := integral_mono_ae h2.integrable_sq (integrable_const _) (by
        filter_upwards [hb] with ω hω
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (X ω)) hB).mpr hω)
      _ = _ := by simp
  have hv := ProbabilityTheory.variance_eq_sub h2
  simp only [Pi.pow_apply] at hv
  linarith [sq_nonneg (∫ω,X ω∂μ)]

lemma bounded_covariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : Ω→ℝ) (hX : Measurable X) (hY : Measurable Y)
    (B : ℝ) (hB : 0≤B) (hbX : ∀ᵐω∂μ,|X ω|≤B) (hbY : ∀ᵐω∂μ,|Y ω|≤B) :
    |ProbabilityTheory.covariance X Y μ|≤B^2 := by
  have h2X := bounded_memLp μ X hX B hbX 2
  have h2Y := bounded_memLp μ Y hY B hbY 2
  have hvX := bounded_variance μ X hX B hB hbX
  have hvY := bounded_variance μ Y hY B hB hbY
  have hp := ProbabilityTheory.variance_nonneg (fun ω => X ω+Y ω) μ
  have hm := ProbabilityTheory.variance_nonneg (fun ω => X ω-Y ω) μ
  rw [ProbabilityTheory.variance_fun_add h2X h2Y] at hp
  rw [ProbabilityTheory.variance_fun_sub h2X h2Y] at hm
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma graph_variance_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι→Ω→ℝ) (D : DepGraph X μ)
    (B d : ℝ) (hB : 0≤B) (hb : ∀i,∀ᵐω∂μ,|X i ω|≤B)
    (hd : ∀i,((D.nbhd i).card:ℝ)≤d) :
    ProbabilityTheory.variance (fun ω=>∑i,X i ω) μ≤(Fintype.card ι:ℝ)*d*B^2 := by
  classical
  have h2 (i : ι) := bounded_memLp μ (X i) (D.meas i) B (hb i) 2
  have hzero (i j : ι) (hj : j∉D.nbhd i) : ProbabilityTheory.covariance (X i) (X j) μ=0 := by
    have hsep : ∀a∈({i}:Finset ι),∀b∈({j}:Finset ι),¬D.G a b := by
      intro a ha b hb
      simp only [Finset.mem_singleton] at ha hb
      subst a
      subst b
      exact fun h => hj (D.mem_nbhd_iff.mpr h)
    have hi := (D.indep {i} {j} hsep).comp
      (measurable_pi_apply ⟨i,by simp⟩) (measurable_pi_apply ⟨j,by simp⟩)
    have hij : IndepFun (X i) (X j) μ := by simpa only [Function.comp_def] using hi
    exact hij.covariance_eq_zero (h2 i) (h2 j)
  have hrow (i : ι) : (∑j,ProbabilityTheory.covariance (X i) (X j) μ)=
      ∑j∈D.nbhd i,ProbabilityTheory.covariance (X i) (X j) μ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    exact hzero i j hj
  rw [ProbabilityTheory.variance_fun_sum h2]
  calc
    _ = ∑i,∑j∈D.nbhd i,ProbabilityTheory.covariance (X i) (X j) μ :=
      Finset.sum_congr rfl (fun i _ => hrow i)
    _ ≤ ∑i,∑_j∈D.nbhd i,B^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (le_abs_self _).trans (bounded_covariance μ (X i) (X j) (D.meas i) (D.meas j) B hB (hb i) (hb j))
    _ ≤ ∑_i:ι,d*B^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hd i) (sq_nonneg B)
    _ = _ := by simp;ring

def squareDep {n : ℕ} (m : Model n) (hdep : Dependency m) :
    DepGraph (fun i y => (OracleCompletion.U m i y)^2) m.law := by
  classical
  let D := OracleCompletion.betaDep m hdep
  exact {
    G := D.G
    decG := D.decG
    refl := D.refl
    symm := D.symm
    meas := fun i => (D.meas i).pow_const 2
    indep := by
      intro S T hST
      have hS : Measurable (fun (v : S→ℝ) => fun i => (v i)^2) :=
        Measurable.of_eval fun i => (measurable_pi_apply i).pow_const 2
      have hT : Measurable (fun (v : T→ℝ) => fun i => (v i)^2) :=
        Measurable.of_eval fun i => (measurable_pi_apply i).pow_const 2
      simpa only [Function.comp_def] using (D.indep S T hST).comp hS hT }

lemma U_variance_bound {n : ℕ} (hn : 0<n) (m : Model n) (c d : ℝ) (hc : 0≤c)
    (hdep : Dependency m) (hb : ∀ᵐy∂m.law,∀i,|weighted m y i-beta m|≤c)
    (hd : ∀i,(degree m.G i:ℝ)+1≤d) : var m (AronowAudit.P011.U m)≤d*c^4/(n:ℝ) := by
  classical
  let : IsProbabilityMeasure m.law := m.probability
  let D := squareDep m hdep
  have hbound (i : Fin n) : ∀ᵐy∂m.law,|(OracleCompletion.U m i y)^2|≤c^2 := by
    filter_upwards [hb] with y hy
    rw [abs_of_nonneg (sq_nonneg _)]
    have hi : |OracleCompletion.U m i y|≤c := hy i
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hc).mpr hi
  have hdegree (i : Fin n) : ((D.nbhd i).card:ℝ)≤d := by
    have he : D.nbhd i=(OracleCompletion.betaDep m hdep).nbhd i := by
      ext j
      rw [DepGraph.mem_nbhd_iff,DepGraph.mem_nbhd_iff]
      rfl
    rw [he,OracleCompletion.betaDep_degree]
    exact_mod_cast hd i
  have hv := graph_variance_sum m.law _ D (c^2) d (sq_nonneg _) hbound hdegree
  simp only [Fintype.card_fin] at hv
  have hmeas : Measurable (AronowAudit.P011.U m) := by
    unfold AronowAudit.P011.U
    exact (Finset.measurable_sum Finset.univ (fun i _ => D.meas i)).div_const _
  have he : var m (AronowAudit.P011.U m)=ProbabilityTheory.variance (AronowAudit.P011.U m) m.law :=
    (ProbabilityTheory.variance_eq_integral hmeas.aemeasurable).symm
  rw [he]
  change ProbabilityTheory.variance (fun y => (∑i,(OracleCompletion.U m i y)^2)/(n:ℝ)) m.law≤_
  simp only [div_eq_mul_inv]
  rw [ProbabilityTheory.variance_mul_const]
  calc
    _ ≤ ((n:ℝ)*d*(c^2)^2)*((n:ℝ)⁻¹)^2 := mul_le_mul_of_nonneg_right hv (sq_nonneg _)
    _ = _ := by
      have hn0 : (n:ℝ)≠0 := by positivity
      field_simp <;> ring

lemma U_mean {n : ℕ} (m : Model n) (c : ℝ)
    (hb : ∀ᵐy∂m.law,∀i,|weighted m y i-beta m|≤c) :
    expectation m (AronowAudit.P011.U m)=meanVariance m+meanSpread m := by
  let : IsProbabilityMeasure m.law := m.probability
  have hL2 := ProbabilityCompletion.weighted_memLp m c hb
  have hi (i : Fin n) : Integrable (fun y => (OracleCompletion.U m i y)^2) m.law :=
    (OracleCompletion.U_memLp m c hb 2 i).integrable_sq
  have he (i : Fin n) : expectation m (fun y => (OracleCompletion.U m i y)^2)=covariance m i i+(delta m i)^2 := by
    simpa only [pow_two] using OracleCompletion.U_pair_mean m hL2 i i
  unfold expectation AronowAudit.P011.U
  rw [integral_div]
  change (∫y,∑i,(OracleCompletion.U m i y)^2∂m.law)/(n:ℝ)=_
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  change (∑i,expectation m (fun y => (OracleCompletion.U m i y)^2))/(n:ℝ)=_
  simp_rw [he]
  simp only [Finset.sum_add_distrib,add_div,meanVariance,meanSpread]

lemma sample_center_identity {n : ℕ} (hn : 0<n) (m : Model n) (y : Fin n→ℝ) :
    sampleVariance (weighted m y)=AronowAudit.P011.U m y-(betaHat m y-beta m)^2 := by
  have hn0 : (n:ℝ)≠0 := by positivity
  unfold sampleVariance centered average AronowAudit.P011.U betaHat average
  simp only [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ←Finset.sum_mul,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp <;> ring

lemma U_memLp_two {n : ℕ} (m : Model n) (c : ℝ)
    (hb : ∀ᵐy∂m.law,∀i,|weighted m y i-beta m|≤c) :
    MemLp (AronowAudit.P011.U m) 2 m.law := by
  have hu (i : Fin n) := OracleCompletion.U_memLp m c hb 4 i
  have hi (i : Fin n) : MemLp (fun y => (OracleCompletion.U m i y)^2) 2 m.law := by
    have he : (OracleCompletion.U m i*OracleCompletion.U m i)=ᵐ[m.law]
        (fun y => (OracleCompletion.U m i y)^2) :=
      Eventually.of_forall fun y => by simp only [Pi.mul_apply,pow_two]
    exact (memLp_congr_ae he).mp ((hu i).mul (hu i))
  have hs : MemLp (fun y => ∑i,(OracleCompletion.U m i y)^2) 2 m.law :=
    memLp_finsetSum Finset.univ (fun i _ => hi i)
  unfold AronowAudit.P011.U
  change MemLp (fun y => (∑i,(OracleCompletion.U m i y)^2)/(n:ℝ)) 2 m.law
  have he : (fun y => (∑i,(OracleCompletion.U m i y)^2)/(n:ℝ))=
      fun y => (n:ℝ)⁻¹*(∑i,(OracleCompletion.U m i y)^2) := by funext y;ring
  rw [he]
  exact hs.const_mul _

lemma revised_sample_variance_completed (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) :
    InProbability F (fun k y => sampleVariance (weighted (F.model k) y))
      (fun k => meanVariance (F.model k)+meanSpread (F.model k)) := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  rcases h with ⟨hNested,hc1,hc2,hc3,hc4,hDep,hBound,hDeg,hVar,hTheta⟩
  have hN : Tendsto (fun k => (F.size k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp F.grows
  have hd (k : ℕ) (i : Fin (F.size k)) : (degree (F.model k).G i:ℝ)+1≤1+c2 := by linarith [hDeg k i]
  have hL2 (k : ℕ) := ProbabilityCompletion.weighted_memLp (F.model k) c1 (hBound k)
  have hU2 (k : ℕ) : MemLp (AronowAudit.P011.U (F.model k)) 2 (F.model k).law :=
    U_memLp_two (F.model k) c1 (hBound k)
  have hUV : Tendsto (fun k => ProbabilityTheory.variance (AronowAudit.P011.U (F.model k)) (F.model k).law) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => ProbabilityTheory.variance_nonneg _ _) (fun k => ?_) (hN.const_div_atTop ((1+c2)*c1^4))
    have hv := U_variance_bound (F.positive k) (F.model k) c1 (1+c2) hc1.le (hDep k) (hBound k) (hd k)
    unfold var expectation at hv
    rw [←ProbabilityTheory.variance_eq_integral (hU2 k).aemeasurable] at hv
    exact hv
  have hUC := OracleCompletion.rowCP_of_variance (fun k => (F.model k).law)
    (fun k => AronowAudit.P011.U (F.model k)) hU2 hUV
  have hUC' : ∀ε>0,Tendsto (fun k => (F.model k).law.real
      {y | |AronowAudit.P011.U (F.model k) y-(meanVariance (F.model k)+meanSpread (F.model k))| > ε}) atTop (𝓝 0) := by
    have he (k : ℕ) : (∫y,AronowAudit.P011.U (F.model k) y∂(F.model k).law)=
        meanVariance (F.model k)+meanSpread (F.model k) := U_mean (F.model k) c1 (hBound k)
    simpa only [he] using hUC
  have hBV : Tendsto (fun k => ProbabilityTheory.variance (betaHat (F.model k)) (F.model k).law) atTop (𝓝 0) := by
    have hv := hVar.div_atTop hN
    have he (k : ℕ) : ((F.size k:ℝ)*var (F.model k) (betaHat (F.model k)))/(F.size k:ℝ)=
        ProbabilityTheory.variance (betaHat (F.model k)) (F.model k).law := by
      rw [ProbabilityTheory.variance_eq_integral (ProbabilityCompletion.betaHat_measurable _).aemeasurable]
      change _=var (F.model k) (betaHat (F.model k))
      have hn0 : (F.size k:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (F.positive k)
      field_simp
    simpa only [he] using hv
  have hBC : CoverageCompletion.RowCP (fun k => (F.model k).law)
      (fun k y => betaHat (F.model k) y-beta (F.model k)) 0 := by
    simpa only [CoverageCompletion.RowCP,sub_zero,beta,expectation] using
      OracleCompletion.rowCP_of_variance (fun k => (F.model k).law) (fun k => betaHat (F.model k))
        (fun k => ProbabilityCompletion.betaHat_memLp _ (hL2 k)) hBV
  have hE : CoverageCompletion.RowCP (fun k => (F.model k).law)
      (fun k y => sampleVariance (weighted (F.model k) y)-AronowAudit.P011.U (F.model k) y) 0 := by
    have hh := CoverageCompletion.rowCP_continuous_pair (fun k => (F.model k).law)
      (fun k y => betaHat (F.model k) y-beta (F.model k)) (fun _ _ => (0:ℝ)) 0 0 hBC
      (CoverageCompletion.rowCP_det _ (fun _ => (0:ℝ)) 0 tendsto_const_nhds)
      (fun p:ℝ×ℝ => -(p.1)^2) (by fun_prop)
    have he (k : ℕ) (y : Fin (F.size k)→ℝ) : sampleVariance (weighted (F.model k) y)-AronowAudit.P011.U (F.model k) y=
        -(betaHat (F.model k) y-beta (F.model k))^2 := by rw [sample_center_identity (F.positive k)];ring
    simpa only [he,zero_pow (by decide:2≠0),neg_zero] using hh
  exact OracleCompletion.row_moving_add_error (fun k => (F.model k).law) _ _ _ hUC' hE

end
end AronowAudit.P011.SampleCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem revised_sample_variance (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) :
    InProbability F (fun k y => sampleVariance (weighted (F.model k) y))
      (fun k => meanVariance (F.model k) + meanSpread (F.model k)) := by
  exact SampleCompletion.revised_sample_variance_completed F c1 c2 c3 c4 h
end AronowAudit.P011

