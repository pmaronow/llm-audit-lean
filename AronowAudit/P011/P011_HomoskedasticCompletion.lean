/- P011 T12 finite rate bounds and T36 Proposition 2, with exact constants, heterogeneous means, zero early variances and the conservative probability limit. -/
import AronowAudit.P011.P011_SampleCompletion
import AronowAudit.P011.P011_CorrelationCompletion

namespace AronowAudit.P011.HomoskedasticCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
local instance : ENNReal.HolderTriple (4:ENNReal) 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]⟩

lemma beta_error_bound {n : ℕ} (hn : 0<n) (m : Model n) (c : ℝ)
    (hb : ∀ᵐy∂m.law,∀i,|weighted m y i-beta m|≤c) :
    ∀ᵐy∂m.law,|betaHat m y-beta m|≤c := by
  have hnR : 0<(n:ℝ) := by positivity
  have hn0 : (n:ℝ)≠0 := ne_of_gt hnR
  filter_upwards [hb] with y hy
  have he : betaHat m y-beta m=(∑i,(weighted m y i-beta m))/(n:ℝ) := by
    unfold betaHat average
    rw [Finset.sum_sub_distrib,Finset.sum_const]
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp <;> ring
  rw [he,abs_div,abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑i,|weighted m y i-beta m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_i:Fin n,c := Finset.sum_le_sum (fun i _ => hy i)
    _ = _ := by simp [mul_comm]

lemma beta_fourth_bound {n : ℕ} (hn : 0<n) (m : Model n) (c d : ℝ) (hc : 0≤c)
    (hdep : Dependency m) (hb : ∀ᵐy∂m.law,∀i,|weighted m y i-beta m|≤c)
    (hd : ∀i,(degree m.G i:ℝ)+1≤d) :
    expectation m (fun y => (betaHat m y-beta m)^4)≤d*c^4/(n:ℝ) := by
  let : IsProbabilityMeasure m.law := m.probability
  let a := fun y => betaHat m y-beta m
  have ha : Measurable a := (ProbabilityCompletion.betaHat_measurable m).sub_const _
  have hab : ∀ᵐy∂m.law,|a y|≤c := beta_error_bound hn m c hb
  have ha2 := SampleCompletion.bounded_memLp m.law a ha c hab 2
  have ha4 := SampleCompletion.bounded_memLp m.law a ha c hab 4
  have haa : MemLp (fun y => (a y)^2) 2 m.law := by
    have he : (a*a)=ᵐ[m.law](fun y => (a y)^2) := Eventually.of_forall fun y => by simp only [Pi.mul_apply,pow_two]
    exact (memLp_congr_ae he).mp (ha4.mul ha4)
  have ha4Int : Integrable (fun y => (a y)^4) m.law :=
    haa.integrable_sq.congr (Eventually.of_forall fun y => by ring)
  have hvar : expectation m (fun y => (a y)^2)≤d*c^2/(n:ℝ) :=
    ExpectationCompletion.beta_variance_bound hn m c d hc hdep hb hd
  calc
    _ ≤ ∫y,c^2*(a y)^2∂m.law := integral_mono_ae ha4Int (ha2.integrable_sq.const_mul _) (by
      filter_upwards [hab] with y hy
      have hs : (a y)^2≤c^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hc).mpr hy
      have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (a y))
      nlinarith)
    _ = c^2*expectation m (fun y => (a y)^2) := integral_const_mul _ _
    _ ≤ c^2*(d*c^2/(n:ℝ)) := mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
    _ = _ := by ring

lemma remainder_second_bound {n : ℕ} (hn : 0<n) (m : Model n) (c d : ℝ) (hc : 0≤c)
    (hdep : Dependency m) (hb : ∀ᵐy∂m.law,∀i,|weighted m y i-beta m|≤c)
    (hd : ∀i,(degree m.G i:ℝ)+1≤d) :
    expectation m (fun y => varianceRemainder m y^2)≤4*d*c^4/(n:ℝ) := by
  let : IsProbabilityMeasure m.law := m.probability
  let a := fun y => betaHat m y-beta m
  let z := fun y => AronowAudit.P011.U m y-expectation m (AronowAudit.P011.U m)
  have ha : Measurable a := (ProbabilityCompletion.betaHat_measurable m).sub_const _
  have hab : ∀ᵐy∂m.law,|a y|≤c := beta_error_bound hn m c hb
  have ha4 := SampleCompletion.bounded_memLp m.law a ha c hab 4
  have ha2 : MemLp (fun y => (a y)^2) 2 m.law := by
    have he : (a*a)=ᵐ[m.law](fun y => (a y)^2) := Eventually.of_forall fun y => by simp only [Pi.mul_apply,pow_two]
    exact (memLp_congr_ae he).mp (ha4.mul ha4)
  have ha4Int : Integrable (fun y => (a y)^4) m.law :=
    ha2.integrable_sq.congr (Eventually.of_forall fun y => by ring)
  have hU := SampleCompletion.U_memLp_two m c hb
  have hz : MemLp z 2 m.law := by
    exact (memLp_congr_ae (Eventually.of_forall fun y => rfl)).mp (hU.sub (memLp_const _))
  have he (y : Fin n→ℝ) : varianceRemainder m y=z y-(a y)^2 := by
    unfold varianceRemainder
    rw [SampleCompletion.sample_center_identity hn]
    dsimp [z,a]
    rw [SampleCompletion.U_mean m c hb]
    ring
  have hR : MemLp (varianceRemainder m) 2 m.law := by
    exact (memLp_congr_ae (Eventually.of_forall fun y => (he y).symm)).mp (hz.sub ha2)
  have hp (y : Fin n→ℝ) : varianceRemainder m y^2≤2*(z y)^2+2*(a y)^4 := by
    rw [he]
    nlinarith [sq_nonneg (z y+(a y)^2)]
  have hvarU := SampleCompletion.U_variance_bound hn m c d hc hdep hb hd
  have hfour := beta_fourth_bound hn m c d hc hdep hb hd
  change expectation m (fun y => (a y)^4)≤d*c^4/(n:ℝ) at hfour
  have hsum : (∫y,2*(z y)^2+2*(a y)^4∂m.law)=
      2*var m (AronowAudit.P011.U m)+2*expectation m (fun y => (a y)^4) := by
    rw [integral_add (hz.integrable_sq.const_mul _) (ha4Int.const_mul _),integral_const_mul,integral_const_mul]
    rfl
  calc
    _ ≤ ∫y,2*(z y)^2+2*(a y)^4∂m.law :=
      integral_mono_ae hR.integrable_sq ((hz.integrable_sq.const_mul _).add (ha4Int.const_mul _))
        (Eventually.of_forall hp)
    _ = _ := hsum
    _ ≤ 2*(d*c^4/(n:ℝ))+2*(d*c^4/(n:ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hvarU (by norm_num))
        (mul_le_mul_of_nonneg_left hfour (by norm_num))
    _ = _ := by ring

lemma second_moment_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (R : Ω→ℝ) (hR : MemLp R 2 μ) (r : ℝ) (hr : 0<r) :
    μ.real {ω | |R ω| > r}≤(∫ω,(R ω)^2∂μ)/r^2 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => sq_nonneg (R ω)) hR.integrable_sq (r^2)
  have hsub : {ω | |R ω| > r}⊆{ω | r^2≤(R ω)^2} := by
    intro ω hω
    change r< |R ω| at hω
    change r^2≤(R ω)^2
    have hs := (sq_le_sq₀ hr.le (abs_nonneg (R ω))).mpr hω.le
    simpa only [sq_abs] using hs
  apply le_trans (measureReal_mono (μ:=μ) hsub (measure_ne_top _ _))
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  linarith

lemma remainder_memLp_two {n : ℕ} (hn : 0<n) (m : Model n) (c : ℝ)
    (hb : ∀ᵐy∂m.law,∀i,|weighted m y i-beta m|≤c) : MemLp (varianceRemainder m) 2 m.law := by
  let : IsProbabilityMeasure m.law := m.probability
  let a := fun y => betaHat m y-beta m
  have ha := SampleCompletion.bounded_memLp m.law a
    ((ProbabilityCompletion.betaHat_measurable m).sub_const _) c (beta_error_bound hn m c hb) 4
  have ha2 : MemLp (fun y => (a y)^2) 2 m.law := by
    have he : (a*a)=ᵐ[m.law](fun y => (a y)^2) := Eventually.of_forall fun y => by simp only [Pi.mul_apply,pow_two]
    exact (memLp_congr_ae he).mp (ha.mul ha)
  have hU := SampleCompletion.U_memLp_two m c hb
  have hz := (hU.sub (memLp_const (meanVariance m+meanSpread m))).sub ha2
  apply (memLp_congr_ae (Eventually.of_forall fun y => ?_)).mp hz
  dsimp only [Pi.sub_apply]
  unfold varianceRemainder
  rw [SampleCompletion.sample_center_identity hn]
  dsimp [a]
  ring

lemma homoskedastic_repair_completed (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hs : ∀ k, Homoskedastic (F.model k)) :
    (∀ k,
      (∀ y, sampleVariance (weighted (F.model k) y) = U (F.model k) y-(betaHat (F.model k) y-beta (F.model k))^2) ∧
      expectation (F.model k) (U (F.model k)) = meanVariance (F.model k)+meanSpread (F.model k) ∧
      var (F.model k) (U (F.model k)) ≤ (1+c2)*c1^4/(F.size k : ℝ) ∧
      expectation (F.model k) (fun y => (betaHat (F.model k) y-beta (F.model k))^2) ≤ (1+c2)*c1^2/(F.size k : ℝ) ∧
      expectation (F.model k) (fun y => (betaHat (F.model k) y-beta (F.model k))^4) ≤ (1+c2)*c1^4/(F.size k : ℝ) ∧
      expectation (F.model k) (fun y => varianceRemainder (F.model k) y^2) ≤ 4*(1+c2)*c1^4/(F.size k : ℝ) ∧
      scaledTrue F k ≤ meanVariance (F.model k)*gFactor (F.model k) ∧
      1 ≤ gFactor (F.model k) ∧ gFactor (F.model k) ≤ 1+c2 ∧
      (∀ y, (F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) =
        gFactor (F.model k)*sampleVariance (weighted (F.model k) y) ∧
        scaledTrue F k-(F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) ≤
          (1+c2)*|varianceRemainder (F.model k) y|) ∧
      (∀ ε : ℝ, 0 < ε → probability (F.model k)
        {y | scaledTrue F k-(F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) > ε}
          ≤ 4*(1+c2)^3*c1^4/((F.size k : ℝ)*ε^2))) ∧
    Conservative F (fun k y => V2 (F.model k).G (weighted (F.model k) y)) := by
  have hScaling := h
  rcases h with ⟨hNested,hc1,hc2,hc3,hc4,hDep,hBound,hDeg,hVar,hTheta⟩
  have hfinite :
      (∀ k,
        (∀ y, sampleVariance (weighted (F.model k) y) = U (F.model k) y-(betaHat (F.model k) y-beta (F.model k))^2) ∧
        expectation (F.model k) (U (F.model k)) = meanVariance (F.model k)+meanSpread (F.model k) ∧
        var (F.model k) (U (F.model k)) ≤ (1+c2)*c1^4/(F.size k : ℝ) ∧
        expectation (F.model k) (fun y => (betaHat (F.model k) y-beta (F.model k))^2) ≤ (1+c2)*c1^2/(F.size k : ℝ) ∧
        expectation (F.model k) (fun y => (betaHat (F.model k) y-beta (F.model k))^4) ≤ (1+c2)*c1^4/(F.size k : ℝ) ∧
        expectation (F.model k) (fun y => varianceRemainder (F.model k) y^2) ≤ 4*(1+c2)*c1^4/(F.size k : ℝ) ∧
        scaledTrue F k ≤ meanVariance (F.model k)*gFactor (F.model k) ∧
        1 ≤ gFactor (F.model k) ∧ gFactor (F.model k) ≤ 1+c2 ∧
        (∀ y, (F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) =
          gFactor (F.model k)*sampleVariance (weighted (F.model k) y) ∧
          scaledTrue F k-(F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) ≤
            (1+c2)*|varianceRemainder (F.model k) y|) ∧
        (∀ ε : ℝ, 0 < ε → probability (F.model k)
          {y | scaledTrue F k-(F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) > ε}
            ≤ 4*(1+c2)^3*c1^4/((F.size k : ℝ)*ε^2))) := by
    intro k
    let m := F.model k
    let d := 1+c2
    let : IsProbabilityMeasure m.law := m.probability
    have hnR : 0<(F.size k:ℝ) := by exact_mod_cast F.positive k
    have hn0 : (F.size k:ℝ)≠0 := ne_of_gt hnR
    have hd0 : 0<d := by dsimp [d];linarith
    have hd (i : Fin (F.size k)) : (degree m.G i:ℝ)+1≤d := by dsimp [d,m];linarith [hDeg k i]
    have hL2 := ProbabilityCompletion.weighted_memLp m c1 (hBound k)
    have hR := remainder_memLp_two (F.positive k) m c1 (hBound k)
    have hRsecond := remainder_second_bound (F.positive k) m c1 d hc1.le (hDep k) (hBound k) hd
    have hGB : 1≤gFactor m ∧ gFactor m≤d := printed_auxiliary_degree_bound F c1 c2 c3 c4 hScaling k
    have hCorr := pairwise_correlation_repair (F.positive k) m (hDep k) (hs k) hL2
    have hσ : 0≤meanVariance m := CorrelationCompletion.meanVariance_nonneg (F.positive k) m (hs k) hL2
    have hAdj (i j : Fin (F.size k)) : 0≤adjacency m.G i j := by unfold adjacency;split_ifs <;>norm_num
    have hSum : (∑i,∑j,adjacency m.G i j*rho m i j)≤∑i,∑j,adjacency m.G i j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hCorr.2.1 i j) (hAdj i j)
    have hTrue : scaledTrue F k≤meanVariance m*gFactor m := by
      rw [scaledTrue,hCorr.1]
      apply mul_le_mul_of_nonneg_left ?_ hσ
      unfold gFactor
      linarith [div_le_div_of_nonneg_right hSum hnR.le]
    have hScaled (y : Fin (F.size k)→ℝ) : (F.size k:ℝ)*V2 m.G (weighted m y)=
        gFactor m*sampleVariance (weighted m y) := by
      unfold V2 gFactor
      field_simp <;>ring
    have hSpread : 0≤meanSpread m := div_nonneg (Finset.sum_nonneg (fun i _=>sq_nonneg _)) hnR.le
    have hPoint (y : Fin (F.size k)→ℝ) : scaledTrue F k-(F.size k:ℝ)*V2 m.G (weighted m y)≤d*|varianceRemainder m y| := by
      rw [hScaled]
      have hRdef : sampleVariance (weighted m y)=meanVariance m+meanSpread m+varianceRemainder m y := by
        unfold varianceRemainder
        ring
      rw [hRdef]
      have hg0 : 0≤gFactor m := by linarith [hGB.1]
      have h1 := mul_nonneg hg0 hSpread
      have h2 := mul_le_mul_of_nonneg_left (neg_le_abs (varianceRemainder m y)) hg0
      have h3 := mul_le_mul_of_nonneg_right hGB.2 (abs_nonneg (varianceRemainder m y))
      nlinarith [hTrue]
    have hRate (ε : ℝ) (hε : 0<ε) : probability m
        {y | scaledTrue F k-(F.size k:ℝ)*V2 m.G (weighted m y)>ε}≤
          4*d^3*c1^4/((F.size k:ℝ)*ε^2) := by
      have hsub : {y | scaledTrue F k-(F.size k:ℝ)*V2 m.G (weighted m y)>ε}⊆
          {y | |varianceRemainder m y| > ε/d} := by
        intro y hy
        change ε<scaledTrue F k-(F.size k:ℝ)*V2 m.G (weighted m y) at hy
        change ε/d < |varianceRemainder m y|
        apply (div_lt_iff₀ hd0).mpr
        nlinarith [hPoint y]
      calc
        _ ≤ m.law.real {y | |varianceRemainder m y| > ε/d} := measureReal_mono (μ:=m.law) hsub (measure_ne_top _ _)
        _ ≤ (∫y,varianceRemainder m y^2∂m.law)/(ε/d)^2 := second_moment_tail m.law _ hR _ (div_pos hε hd0)
        _ ≤ (4*d*c1^4/(F.size k:ℝ))/(ε/d)^2 := div_le_div_of_nonneg_right hRsecond (sq_nonneg _)
        _ = _ := by
          have hdne : d≠0 := ne_of_gt hd0
          have hεne : ε≠0 := ne_of_gt hε
          field_simp <;>ring
    exact ⟨SampleCompletion.sample_center_identity (F.positive k) m,
      SampleCompletion.U_mean m c1 (hBound k),
      SampleCompletion.U_variance_bound (F.positive k) m c1 d hc1.le (hDep k) (hBound k) hd,
      ExpectationCompletion.beta_variance_bound (F.positive k) m c1 d hc1.le (hDep k) (hBound k) hd,
      beta_fourth_bound (F.positive k) m c1 d hc1.le (hDep k) (hBound k) hd,
      hRsecond,hTrue,hGB.1,hGB.2,fun y=>⟨hScaled y,hPoint y⟩,hRate⟩
  refine ⟨hfinite,?_⟩
  intro ε hε
  have hN : Tendsto (fun k=>(F.size k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp F.grows
  apply squeeze_zero (fun k=>measureReal_nonneg) (fun k=>?_) (hN.const_div_atTop (4*(1+c2)^3*c1^4/ε^2))
  · rcases hfinite k with ⟨_,_,_,_,_,_,_,_,_,_,hRate⟩
    have hr := hRate ε hε
    have hn0 : (F.size k:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (F.positive k)
    have he : 4*(1+c2)^3*c1^4/((F.size k:ℝ)*ε^2)=
        (4*(1+c2)^3*c1^4/ε^2)/(F.size k:ℝ) := by ring
    rw [he] at hr
    simpa only [probability,scaledTrue,mul_sub] using hr

end
end AronowAudit.P011.HomoskedasticCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem homoskedastic_repair (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hs : ∀ k, Homoskedastic (F.model k)) :
    (∀ k,
      (∀ y, sampleVariance (weighted (F.model k) y) = U (F.model k) y-(betaHat (F.model k) y-beta (F.model k))^2) ∧
      expectation (F.model k) (U (F.model k)) = meanVariance (F.model k)+meanSpread (F.model k) ∧
      var (F.model k) (U (F.model k)) ≤ (1+c2)*c1^4/(F.size k : ℝ) ∧
      expectation (F.model k) (fun y => (betaHat (F.model k) y-beta (F.model k))^2) ≤ (1+c2)*c1^2/(F.size k : ℝ) ∧
      expectation (F.model k) (fun y => (betaHat (F.model k) y-beta (F.model k))^4) ≤ (1+c2)*c1^4/(F.size k : ℝ) ∧
      expectation (F.model k) (fun y => varianceRemainder (F.model k) y^2) ≤ 4*(1+c2)*c1^4/(F.size k : ℝ) ∧
      scaledTrue F k ≤ meanVariance (F.model k)*gFactor (F.model k) ∧
      1 ≤ gFactor (F.model k) ∧ gFactor (F.model k) ≤ 1+c2 ∧
      (∀ y, (F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) =
        gFactor (F.model k)*sampleVariance (weighted (F.model k) y) ∧
        scaledTrue F k-(F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) ≤
          (1+c2)*|varianceRemainder (F.model k) y|) ∧
      (∀ ε : ℝ, 0 < ε → probability (F.model k)
        {y | scaledTrue F k-(F.size k : ℝ)*V2 (F.model k).G (weighted (F.model k) y) > ε}
          ≤ 4*(1+c2)^3*c1^4/((F.size k : ℝ)*ε^2))) ∧
    Conservative F (fun k y => V2 (F.model k).G (weighted (F.model k) y)) := by
  exact HomoskedasticCompletion.homoskedastic_repair_completed F c1 c2 c3 c4 h hs

theorem proposition_two (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (hs : ∀ k, Homoskedastic (F.model k)) :
    Conservative F (fun k y => V2 (F.model k).G (weighted (F.model k) y)) := by
  exact (homoskedastic_repair F c1 c2 c3 c4 h hs).2
end AronowAudit.P011

