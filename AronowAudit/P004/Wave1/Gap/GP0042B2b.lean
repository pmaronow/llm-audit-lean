import AronowAudit.P004.Wave1.AreaSum
import AronowAudit.P004.Wave1.Gap.GP0042B1
import AronowAudit.P004.P004_MatrixCompletion
import AronowAudit.P053.P053_NormalQuantiles

namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Classical Topology
open MeasureTheory Filter
noncomputable section

set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/- Projection of the Euclidean area-integral witness. -/

theorem area_sum_counterexample_proof :
    (∀ x z, areaBinaryPopulation.outcome x z = 0 ∨ areaBinaryPopulation.outcome x z = 1) ∧
    (∀ j : Fin 6, WellDefined areaBinaryPopulation j) ∧
    WellDefined areaBinaryPopulation 6 ∧
    (∀ i (j : Fin 6), (volume (region areaBinaryPopulation i j)).toReal =
      Real.pi*(2*(j : ℝ)+1)) ∧
    (∑ j : Fin 6, hajek (circleAverage areaBinaryPopulation j) areaWitnessAssignment) = -(17/500 : ℝ) ∧
    (∑ j : Fin 6, ame (fun _ => 1/2) (circleAverage areaBinaryPopulation j)) = -(17/500 : ℝ) ∧
    ame (fun _ => 1/2) (circleAverage areaBinaryPopulation 6) = (121/18000 : ℝ) ∧
    (0 : ℝ) < 121/18000 ∧ -(17/500 : ℝ) ≠ 121/18000 := by
  exact area_sum_spatial_caseB.2.2.2

/- Finite probability and Gaussian adapters. -/

theorem GP0042B2b_capped_pd_prob_nonneg {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A : Assignment N → Prop) :
    0 ≤ prob p A := by
  calc
    0 = expect p (fun _ => 0) := (expect_const p 0).symm
    _ ≤ prob p A := by
      apply expect_mono p hp
      intro z
      split_ifs <;> norm_num

theorem GP0042B2b_capped_pd_prob_mono {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B : Assignment N → Prop)
    (hAB : ∀ z, A z → B z) : prob p A ≤ prob p B := by
  unfold prob
  apply expect_mono p hp
  intro z
  by_cases ha : A z
  · simp only [if_pos ha, if_pos (hAB z ha), le_refl]
  · by_cases hb : B z <;> simp [ha, hb]

/-- The three-event lower bound avoids any need for convergence of the
coverage probabilities themselves. -/
theorem GP0042B2b_capped_pd_prob_difference {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1)
    (A B Bad C : Assignment N → Prop)
    (hcover : ∀ z, A z → ¬ B z → ¬ Bad z → C z) :
    prob p A - prob p B - prob p Bad ≤ prob p C := by
  change expect p (fun z => if A z then 1 else 0) -
      expect p (fun z => if B z then 1 else 0) -
      expect p (fun z => if Bad z then 1 else 0) ≤ _
  rw [← expect_sub, ← expect_sub]
  apply expect_mono p hp
  intro z
  by_cases ha : A z
  · by_cases hb : B z
    · by_cases hg : Bad z <;> by_cases hc : C z <;> norm_num [ha, hb, hg, hc]
    · by_cases hg : Bad z
      · by_cases hc : C z <;> norm_num [ha, hb, hg, hc]
      · simp [ha, hb, hg, hcover z ha hb hg]
  · by_cases hb : B z <;> by_cases hg : Bad z <;> by_cases hc : C z <;>
      norm_num [ha, hb, hg, hc]

theorem GP0042B2b_capped_pd_prob_two_upper {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (A B C : Assignment N → Prop)
    (hcover : ∀ z, A z → B z ∨ C z) :
    prob p A ≤ prob p B + prob p C := by
  change _ ≤ expect p (fun z => if B z then 1 else 0) +
    expect p (fun z => if C z then 1 else 0)
  rw [← expect_add]
  apply expect_mono p hp
  intro z
  by_cases ha : A z
  · rcases hcover z ha with hb | hc
    · by_cases hc : C z <;> simp [ha, hb, hc]
    · by_cases hb : B z <;> simp [ha, hb, hc]
  · by_cases hb : B z <;> by_cases hc : C z <;> simp [ha, hb, hc]

/-- Squeeze with eventual bounds, expressed using the order definition of a
real limit so no measure-convergence bridge is necessary. -/
theorem GP0042B2b_capped_pd_tendsto_zero_of_le (a b : ℕ → ℝ)
    (ha : ∀ N, 0 ≤ a N) (hab : ∀ᶠ N in atTop, a N ≤ b N)
    (hb : Tendsto b atTop (nhds 0)) : Tendsto a atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro x hx
    exact Filter.Eventually.of_forall (fun N => hx.trans_le (ha N))
  · intro x hx
    filter_upwards [hab, (tendsto_order.mp hb).2 x hx] with N hle hlt
    exact hle.trans_lt hlt

theorem GP0042B2b_capped_pd_inProb_add (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1)
    (U W : ∀ N, Assignment N → ℝ) (hU : InProb p U) (hW : InProb p W) :
    InProb p (fun N z => U N z + W N z) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  apply GP0042B2b_capped_pd_tendsto_zero_of_le _
    (fun N => prob (p N) (fun z => ε/2 < |U N z|) +
      prob (p N) (fun z => ε/2 < |W N z|))
  · intro N
    exact GP0042B2b_capped_pd_prob_nonneg _ (hp N) _
  · exact Filter.Eventually.of_forall (fun N =>
      GP0042B2b_capped_pd_prob_two_upper (p N) (hp N) _ _ _ (by
        intro z hz
        by_contra h
        have hnot := not_or.mp h
        have h1 : |U N z| ≤ ε/2 := le_of_not_gt hnot.1
        have h2 : |W N z| ≤ ε/2 := le_of_not_gt hnot.2
        have ht := abs_add_le (U N z) (W N z)
        linarith))
  · simpa only [zero_add] using (hU (ε/2) hhalf).add (hW (ε/2) hhalf)

theorem GP0042B2b_capped_pd_normalCDF_eq_cdf (x : ℝ) :
    normalCDF x = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x := by
  exact AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf x

theorem GP0042B2b_capped_pd_normalCDF_continuous : Continuous normalCDF := by
  letI : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  rw [show normalCDF = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) from
    funext GP0042B2b_capped_pd_normalCDF_eq_cdf]
  apply continuous_iff_continuousAt.mpr
  intro x
  exact AronowAudit.P053.NormalCompletion.cdf_continuousAt
    (ProbabilityTheory.gaussianReal 0 1) x

theorem GP0042B2b_capped_pd_normalCDF_neg (x : ℝ) : normalCDF (-x) = 1 - normalCDF x := by
  simpa only [← GP0042B2b_capped_pd_normalCDF_eq_cdf] using
    AronowAudit.P053.NormalCompletion.normal_cdf_neg x

theorem GP0042B2b_capped_pd_quantile (α : ℝ) (hα : 0 < α ∧ α < 1) :
    0 < normalQuantile (1-α/2) ∧
      normalCDF (normalQuantile (1-α/2)) = 1-α/2 := by
  have heq : normalQuantile (1-α/2) = AronowAudit.P053.normalCritical α := by
    unfold normalQuantile AronowAudit.P053.normalCritical
    rfl
  rw [heq]
  exact ⟨AronowAudit.P053.NormalCompletion.normalCritical_pos α hα.1 hα.2,
    AronowAudit.P053.NormalCompletion.normalCritical_cdf α hα.1 hα.2⟩

/-- Pointwise radius comparison on a variance-floor event. -/
theorem GP0042B2b_capped_pd_radius (u v w q s : ℝ) (hv : 0 < v)
    (hq : 0 ≤ q) (hs : 0 < s) (hfloor : s*v ≤ w)
    (hu : |u / Real.sqrt v| ≤ q*Real.sqrt s) :
    0 < w ∧ |u| ≤ q*Real.sqrt w := by
  have hvroot : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hw : 0 < w := (mul_pos hs hv).trans_le hfloor
  have hu' : |u| ≤ (q*Real.sqrt s)*Real.sqrt v := by
    apply (div_le_iff₀ hvroot).mp
    simpa only [abs_div, abs_of_pos hvroot] using hu
  refine ⟨hw, hu'.trans ?_⟩
  calc
    (q*Real.sqrt s)*Real.sqrt v = q*Real.sqrt (s*v) := by
      rw [Real.sqrt_mul hs.le v]
      ring
    _ ≤ q*Real.sqrt w := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfloor) hq

/-- Generic one-sided Wald lemma. `hshort` is only a lower-tail condition;
no deterministic variance-ratio limit is required. -/
theorem GP0042B2b_capped_pd_one_sided_wald (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1)
    (U W : ∀ N, Assignment N → ℝ) (V : ℕ → ℝ)
    (hV : ∀ᶠ N in atTop, 0 < V N)
    (hCLT : NormalLimit p (fun N z => U N z / Real.sqrt (V N)))
    (hshort : ∀ η : ℝ, 0 < η → η < 1 →
      Tendsto (fun N => prob (p N) (fun z => W N z < (1-η)*V N)) atTop (nhds 0))
    (α : ℝ) (hα : 0 < α ∧ α < 1) :
    Conservative (fun N => prob (p N) (fun z => 0 < W N z ∧
      |U N z| ≤ normalQuantile (1-α/2)*Real.sqrt (W N z))) α := by
  let q := normalQuantile (1-α/2)
  obtain ⟨hq, hqcdf⟩ := GP0042B2b_capped_pd_quantile α hα
  change 0 < q at hq
  change normalCDF q = 1-α/2 at hqcdf
  let F : ℝ → ℝ := fun s => normalCDF (q*Real.sqrt s) - normalCDF (-(q*Real.sqrt s))
  have hF : ContinuousAt F 1 := by
    exact (GP0042B2b_capped_pd_normalCDF_continuous.continuousAt.comp
      (continuousAt_const.mul Real.continuous_sqrt.continuousAt)).sub
        (GP0042B2b_capped_pd_normalCDF_continuous.continuousAt.comp
          (continuousAt_const.mul Real.continuous_sqrt.continuousAt).neg)
  have hF1 : F 1 = 1-α := by
    dsimp only [F]
    rw [Real.sqrt_one, mul_one, GP0042B2b_capped_pd_normalCDF_neg, hqcdf]
    ring
  intro ε hε
  have hnear : ∀ᶠ s in nhds (1 : ℝ), 1-α-ε/2 < F s := by
    apply hF.eventually
    apply eventually_gt_nhds
    rw [hF1]
    linarith
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp hnear
  let e : ℝ := min δ 1 / 2
  have he : 0 < e := div_pos (lt_min hδ (by norm_num)) (by norm_num)
  have heδ : e < δ := by
    have := min_le_left δ 1
    dsimp only [e]
    linarith
  have he1 : e ≤ 1/2 := by
    have := min_le_right δ 1
    dsimp only [e]
    linarith
  let s : ℝ := 1-e
  have hs : 0 < s := by dsimp only [s]; linarith
  have hs1 : s < 1 := by dsimp only [s]; linarith
  have hsnear : s ∈ Metric.ball (1 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    have heq : s-1 = -e := by dsimp only [s]; ring
    rw [heq, abs_neg, abs_of_pos he]
    exact heδ
  have hmass : 1-α-ε/2 < F s := hδball hsnear
  let t : ℝ := q*Real.sqrt s
  have hbad := hshort (1-s) (by linarith) (by linarith)
  have hlim : Tendsto (fun N =>
      prob (p N) (fun z => U N z / Real.sqrt (V N) ≤ t) -
      prob (p N) (fun z => U N z / Real.sqrt (V N) ≤ -t) -
      prob (p N) (fun z => W N z < s*V N)) atTop (nhds (F s)) := by
    have h := ((hCLT t).sub (hCLT (-t))).sub hbad
    simpa only [sub_sub_cancel, sub_zero, F, t] using h
  have hlower : ∀ᶠ N in atTop,
      1-α-ε < prob (p N) (fun z => U N z / Real.sqrt (V N) ≤ t) -
        prob (p N) (fun z => U N z / Real.sqrt (V N) ≤ -t) -
        prob (p N) (fun z => W N z < s*V N) :=
    (tendsto_order.mp hlim).1 _ (by linarith)
  filter_upwards [hV, hlower] with N hv hbound
  apply le_of_lt
  apply hbound.trans_le
  apply GP0042B2b_capped_pd_prob_difference (p N) (hp N)
  intro z hupper hlower hnotbad
  have hlow : -t < U N z / Real.sqrt (V N) := lt_of_not_ge hlower
  have habs : |U N z / Real.sqrt (V N)| ≤ t :=
    abs_le.mpr ⟨hlow.le, hupper⟩
  exact GP0042B2b_capped_pd_radius (U N z) (V N) (W N z) q s hv hq.le hs
    (le_of_not_gt hnotbad) habs

/- Finite spectral comparison, including assignments with empty arms. -/

theorem GP0042B2b_capped_pd_spectral_domination {N : ℕ} (values : Fin N → ℝ)
    (vectors : Matrix (Fin N) (Fin N) ℝ) (z : Assignment N) (e : Fin N → ℝ) :
    kernelVariance z e (spectralKernel values vectors false) ≤
      cappedVariance (kernelVariance z e (spectralKernel values vectors true))
        (adjustmentMu z (spectralKernel values vectors true)) := by
  obtain ⟨hQ, hD⟩ := MatrixCompletion.spectral_psd values vectors
  have hraw : kernelVariance z e (spectralKernel values vectors false) ≤
      kernelVariance z e (spectralKernel values vectors true) := by
    have h := MatrixCompletion.kernel_variance_nonneg z e _ hD
    rw [MatrixCompletion.kernel_variance_sub] at h
    linarith
  exact hraw.trans (capped_variance_ge _ _
    (MatrixCompletion.kernel_variance_nonneg z e _ hQ))

theorem GP0042B2b_capped_pd_pointwise {N : ℕ} (values : Fin N → ℝ)
    (vectors : Matrix (Fin N) (Fin N) ℝ) (z : Assignment N) (R : CircleTable N)
    (K : Matrix (Fin N) (Fin N) ℝ)
    (heigen : spectralKernel values vectors false = K)
    (q c err : ℝ) (hq : 0 ≤ q) (hc : q ≤ c)
    (herr : |err| ≤ q*Real.sqrt (kernelVariance z (residual R z) K)) :
    |err| ≤ c*Real.sqrt (cappedVariance
      (kernelVariance z (residual R z) (spectralKernel values vectors true))
      (adjustmentMu z (spectralKernel values vectors true))) := by
  have hV := GP0042B2b_capped_pd_spectral_domination values vectors z (residual R z)
  rw [heigen] at hV
  apply herr.trans
  exact mul_le_mul hc (Real.sqrt_le_sqrt hV) (Real.sqrt_nonneg _) (hq.trans hc)

/-- Row sums of local products still depend on the entire family of sources
of the row neighborhood. This is stronger than pairwise independence. -/
theorem GP0042B2b_capped_pd_row_depends {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N))
    (hself : ∀ i, i ∈ B i) (i : Fin N) :
    DependsOn (fun z => ∑ j ∈ B i,
      residualContrast p R g i z * residualContrast p R g j z)
      (GraphCompletion.sources R (B i)) := by
  intro x y hxy
  have hf := GraphCompletion.residual_family_depends p R g (B i)
  have heq := hf hxy
  apply Finset.sum_congr rfl
  intro j hj
  have hi : residualContrast p R g i x = residualContrast p R g i y := congrFun heq ⟨i, hself i⟩
  have hj' : residualContrast p R g j x = residualContrast p R g j y := congrFun heq ⟨j, hj⟩
  rw [hi, hj']

theorem GP0042B2b_capped_pd_row_cov_zero {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N))
    (hself : ∀ i, i ∈ B i) (i k : Fin N)
    (hsep : ∀ a ∈ B i, ∀ b ∈ B k, ¬ sharesSource R a b) :
    cov p (fun z => ∑ j ∈ B i,
      residualContrast p R g i z * residualContrast p R g j z)
      (fun z => ∑ l ∈ B k,
        residualContrast p R g k z * residualContrast p R g l z) = 0 := by
  have hsub : GraphCompletion.sources R (B k) ⊆
      (GraphCompletion.sources R (B i))ᶜ := by
    rintro s ⟨b, hb, hbs⟩ ⟨a, ha, has⟩
    exact hsep a ha b hb ⟨s, has, hbs⟩
  have hk := (GP0042B2b_capped_pd_row_depends p R g B hself k).mono hsub
  unfold cov
  rw [GraphCompletion.expect_mul_of_disjoint_depends p
    (GraphCompletion.sources R (B i)) _ _
    (GP0042B2b_capped_pd_row_depends p R g B hself i) hk, sub_self]

theorem GP0042B2b_capped_pd_row_bound {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N))
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ i z, |residualContrast p R g i z| ≤ C)
    (i : Fin N) (z : Assignment N) :
    |∑ j ∈ B i, residualContrast p R g i z * residualContrast p R g j z| ≤
      ((B i).card : ℝ)*C^2 := by
  calc
    _ ≤ ∑ j ∈ B i, |residualContrast p R g i z * residualContrast p R g j z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ B i, C^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, pow_two]
      exact mul_le_mul (hT i z) (hT j z) (abs_nonneg _) hC
    _ = _ := by simp

/-- Finite expectation identity from finite covariance algebra. -/
theorem GP0042B2b_capped_pd_oracle_mean {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (p d h : ℝ) (hN : 0 < N)
    (hp : 0 < p ∧ p < 1) (hh : 0 ≤ h)
    (hloc : LocalAt (circleAverage P d) (nodeSeparation P) h) :
    expect (fun _ => p) (oracleHAC (fun _ => p) (circleAverage P d)
      (fun i => ball (nodeSeparation P) i h)
      (fun _ a => barMu (fun _ => p) (circleAverage P d) a)) =
    variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage P d)) +
      homophilyQ (fun _ => p) (circleAverage P d)
        (fun i => ball (nodeSeparation P) i h)
        (fun _ a => barMu (fun _ => p) (circleAverage P d) a) / N := by
  let R := circleAverage P d
  let B := fun i => ball (nodeSeparation P) i h
  let g := fun (_ : Fin N) a => barMu (fun _ => p) R a
  have hself : ∀ i, i ∈ B i := by
    intro i
    simpa only [B, ball, Finset.mem_filter, Finset.mem_univ, true_and,
      CLTCompletion.nodeSeparation_self] using hh
  have hout : ∀ i j, j ∉ B i → ¬ sharesSource R i j := by
    intro i j hij
    apply hloc i j
    have hnle : ¬ nodeSeparation P i j ≤ h := by
      simpa only [B, ball, Finset.mem_filter, Finset.mem_univ, true_and] using hij
    exact lt_of_not_ge hnle
  have hmean : expect (fun _ => p) (oracleHAC (fun _ => p) R B g) =
      secondMomentBound (fun _ => p) R B g := by
    unfold oracleHAC
    rw [expect_div, expect_sum]
    simp_rw [GraphCompletion.expect_finset_sum]
    exact GraphCompletion.local_second_sum (fun _ => p) R g B (fun _ => hp) hself
  have hid := (hajek_homophily_identity (fun _ => p) R B hN
    (fun _ => hp) hself hout).1
  change expect (fun _ => p) (oracleHAC (fun _ => p) R B g) = _
  rw [hmean]
  change secondMomentBound (fun _ => p) R B g -
    variance (fun _ => p) (linearHajek (fun _ => p) R) =
      homophilyQ (fun _ => p) R B g / N at hid
  linarith

/-- Translate absolute error at scale N into the required relative lower
tail, using the exact nondegeneracy definition. -/
theorem GP0042B2b_capped_pd_shortfall (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1)
    (W : ∀ N, Assignment N → ℝ) (E V : ℕ → ℝ)
    (hv : Nondegenerate V) (hEV : ∀ᶠ N in atTop, V N ≤ E N)
    (herror : InProb p (fun N z => (N : ℝ)*(W N z-E N))) :
    ∀ η : ℝ, 0 < η → η < 1 →
      Tendsto (fun N => prob (p N) (fun z => W N z < (1-η)*V N)) atTop (nhds 0) := by
  obtain ⟨v, hvpos, hvfloor⟩ := hv
  intro η hη _
  have hηv : 0 < η*v := mul_pos hη hvpos
  apply GP0042B2b_capped_pd_tendsto_zero_of_le _
    (fun N => prob (p N) (fun z => η*v < |(N : ℝ)*(W N z-E N)|))
  · intro N
    exact GP0042B2b_capped_pd_prob_nonneg _ (hp N) _
  · filter_upwards [hEV, hvfloor, eventually_gt_atTop (0 : ℕ)] with N hEV hfloor hN
    apply GP0042B2b_capped_pd_prob_mono _ (hp N)
    intro z hz
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hdiff : W N z-E N < -η*V N := by nlinarith
    have hmul := mul_lt_mul_of_pos_left hdiff hn
    have hf := mul_le_mul_of_nonneg_left hfloor hη.le
    have habs := neg_le_abs ((N : ℝ)*(W N z-E N))
    nlinarith
  · exact herror (η*v) hηv


/-- Three graph steps contain every pair of potentially dependent local-product rows. -/
def GP0042B2b_triple {N : ℕ} (B : Fin N → Finset (Fin N)) (i : Fin N) : Finset (Fin N) :=
  (B i).biUnion (fun a => (B a).biUnion B)

lemma GP0042B2b_triple_symm {N : ℕ} (B : Fin N → Finset (Fin N))
    (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j) (i k : Fin N) :
    k ∈ GP0042B2b_triple B i ↔ i ∈ GP0042B2b_triple B k := by
  simp only [GP0042B2b_triple, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, b, hb, hk⟩
    exact ⟨b, (hsymm b k).mp hk, a, (hsymm a b).mp hb, (hsymm i a).mp ha⟩
  · rintro ⟨b, hb, a, ha, hi⟩
    exact ⟨a, (hsymm a i).mp hi, b, (hsymm b a).mp ha, (hsymm k b).mp hb⟩

lemma GP0042B2b_triple_card {N : ℕ} (B : Fin N → Finset (Fin N)) (D : ℕ)
    (hdeg : ∀ i, (B i).card ≤ D) (i : Fin N) :
    (GP0042B2b_triple B i).card ≤ D^3 := by
  have htwo (a : Fin N) : ((B a).biUnion B).card ≤ D*D :=
    (Finset.card_biUnion_le_card_mul (B a) B D (fun b _ => hdeg b)).trans
      (Nat.mul_le_mul_right D (hdeg a))
  exact (Finset.card_biUnion_le_card_mul (B i) _ (D*D) (fun a _ => htwo a)).trans
    (by nlinarith [Nat.mul_le_mul_right (D*D) (hdeg i)])

lemma GP0042B2b_oracle_variance {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (g : Fin N → Bool → ℝ) (B : Fin N → Finset (Fin N))
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hN : 0 < N)
    (hself : ∀ i, i ∈ B i) (hsymm : ∀ i j, j ∈ B i ↔ i ∈ B j)
    (hout : ∀ i j, j ∉ B i → ¬sharesSource R i j)
    (D : ℕ) (hdeg : ∀ i, (B i).card ≤ D)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ i z, |residualContrast p R g i z| ≤ C) :
    variance p (fun z => (N : ℝ)*oracleHAC p R B g z) ≤
      (D : ℝ)^3*((D : ℝ)*C^2)^2/N := by
  let T := fun i z => ∑ j ∈ B i, residualContrast p R g i z * residualContrast p R g j z
  have hrow (i : Fin N) (z : Assignment N) : |T i z| ≤ (D:ℝ)*C^2 :=
    (GP0042B2b_capped_pd_row_bound p R g B C hC hT i z).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg i) (sq_nonneg C))
  have hsecond (i : Fin N) : expect p (fun z => (T i z)^2) ≤ ((D:ℝ)*C^2)^2 := by
    rw [← expect_const p (((D:ℝ)*C^2)^2)]
    apply expect_mono p hp
    intro z
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (T i z)) (hrow i z) 2
  have houtT (i k : Fin N) (hik : k ∉ GP0042B2b_triple B i) : cov p (T i) (T k) = 0 := by
    apply GP0042B2b_capped_pd_row_cov_zero p R g B hself i k
    intro a ha b hb hab
    have hba : b ∈ B a := by
      by_contra h
      exact hout a b h hab
    apply hik
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_biUnion.mpr
      ⟨b, hba, (hsymm k b).mp hb⟩⟩
  have hv := finite_covariance_degree_bound p hp T (GP0042B2b_triple B)
    (GP0042B2b_triple_symm B hsymm) houtT
  have hsum : (∑ i, (GP0042B2b_triple B i).card * expect p (fun z => (T i z)^2)) ≤
      (N:ℝ)*(D:ℝ)^3*((D:ℝ)*C^2)^2 := by
    calc
      _ ≤ ∑ _i : Fin N, (D:ℝ)^3*((D:ℝ)*C^2)^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact (mul_le_mul_of_nonneg_left (hsecond i) (Nat.cast_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast GP0042B2b_triple_card B D hdeg i) (sq_nonneg _))
      _ = _ := by simp [mul_assoc]
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have heq : (fun z => (N:ℝ)*oracleHAC p R B g z) = fun z => (∑ i, T i z)/N := by
    funext z
    dsimp only [oracleHAC, T]
    field_simp
  rw [heq]
  exact hv.trans ((div_le_div_of_nonneg_right hsum (sq_nonneg (N:ℝ))).trans_eq
    (by field_simp))

lemma GP0042B2b_second_inProb (p : ∀ N, Fin N → ℝ)
    (hp : ∀ N i, 0 < p N i ∧ p N i < 1) (X : ∀ N, Assignment N → ℝ)
    (K : ℝ) (hX : ∀ᶠ N in atTop, expect (p N) (fun z => (X N z)^2) ≤ K/N) :
    InProb p X := by
  intro ε hε
  have hbound : ∀ᶠ N in atTop,
      prob (p N) (fun z => ε < |X N z|) ≤ (K/N)/ε^2 := by
    filter_upwards [hX] with N hN
    exact (T34_chebyshev (p N) (hp N) (X N) ε hε).trans
      (div_le_div_of_nonneg_right hN (sq_nonneg ε))
  have hlim : Tendsto (fun N : ℕ => (K/N)/ε^2) atTop (nhds 0) := by
    have hnlim : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_natCast_atTop_atTop.inv_tendsto_atTop
    simpa [div_eq_mul_inv] using (hnlim.const_mul K).div_const (ε^2)
  exact squeeze_zero' (Eventually.of_forall (fun N => T34_prob_nonneg _ (hp N) _)) hbound hlim

variable {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]

lemma GP0042B2b_oracle_concentration (P : PopulationSequence Space) (p d h : ℝ)
    (hp : 0 < p ∧ p < 1) (hh : 0 ≤ h) (hP : SpatialLocalConditions P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h) :
    let W := fun N => oracleHAC (fun _ => p) (circleAverage (P N) d)
      (spatialNeighborhoods P h N) (fun _ a => barMu (fun _ => p) (circleAverage (P N) d) a)
    InProb (fun _ _ => p) (fun N z => (N:ℝ)*(W N z-expect (fun _ => p) (W N))) := by
  dsimp only
  obtain ⟨M, hM, hb⟩ := hP.1
  obtain ⟨c, hc⟩ := hP.2.2
  let D := Nat.ceil (c h)
  let C := 2*M/p+2*M/(1-p)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (div_nonneg (by positivity) hp.1.le)
      (div_nonneg (by positivity) (sub_pos.mpr hp.2).le)
  apply GP0042B2b_second_inProb _ (fun _ _ => hp) _ ((D:ℝ)^3*((D:ℝ)*C^2)^2)
  filter_upwards [eventually_gt_atTop 0, hb, hWD, hloc, hc h hh] with N hN hbN hwdN hlN hdN
  let R := circleAverage (P N) d
  let B := spatialNeighborhoods P h N
  let g := fun (_ : Fin N) a => barMu (fun _ => p) R a
  let W := oracleHAC (fun _ => p) R B g
  have hR := CLTCompletion.circleAverage_abs_le (P N) d M hwdN (fun x z => (hbN x z).le)
  have hres : ∀ i z, |R i z-g i (z i)| ≤ 2*M := by
    intro i z
    exact (abs_sub _ _).trans (by linarith [hR i z, T42_barMu_bound p R hp hN M hR (z i)])
  have hTabs : ∀ i z, |residualContrast (fun _ => p) R g i z| ≤ C := by
    intro i z
    have ht := CLTCompletion.raw_contrast_abs_le p (2*M) (fun i z => R i z-g i (z i)) hp
      (by positivity) hres i z
    convert ht using 1
    cases hz : z i <;> simp [residualContrast, bit, hz]
  have hself (i : Fin N) : i ∈ B i := by
    simpa only [B, spatialNeighborhoods, ball, Finset.mem_filter, Finset.mem_univ, true_and,
      CLTCompletion.nodeSeparation_self] using hh
  have hsymm (i j : Fin N) : j ∈ B i ↔ i ∈ B j := by
    simp only [B, spatialNeighborhoods, ball, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [CLTCompletion.nodeSeparation_symm (P N) i j]
  have hout (i j : Fin N) (hij : j ∉ B i) : ¬sharesSource R i j := by
    apply hlN i j
    simpa only [B, spatialNeighborhoods, ball, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hij
  have hdeg (i : Fin N) : (B i).card ≤ D := by
    exact_mod_cast (hdN i).trans (Nat.le_ceil (c h))
  have hv := GP0042B2b_oracle_variance (fun _ => p) R g B (fun _ => hp) hN
    hself hsymm hout D hdeg C hC hTabs
  have heq : (fun z => ((N:ℝ)*(W z-expect (fun _ => p) W))^2) =
      fun z => ((N:ℝ)*W z-expect (fun _ => p) (fun z => (N:ℝ)*W z)) *
        ((N:ℝ)*W z-expect (fun _ => p) (fun z => (N:ℝ)*W z)) := by
    simp only [expect_mul]
    funext z
    ring
  change expect (fun _ => p) (fun z => ((N:ℝ)*(W z-expect (fun _ => p) W))^2) ≤ _
  rw [heq, ← cov_centered]
  exact hv

lemma GP0042B2b_div_perturbation (r b c A δ : ℝ) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2) (hr : |r| ≤ A)
    (hb : |b| ≤ δ) (hc : |c-1| ≤ δ) :
    |(r-b/c)/c-r| ≤ (2*A+4)*δ := by
  have hcpos : 0 < c := by have := (abs_le.mp hc).1; linarith
  have hchalf : 1/2 ≤ c := by have := (abs_le.mp hc).1; linarith
  have hbdiv : |b/c| ≤ 2*δ := by
    rw [abs_div, abs_of_pos hcpos]
    apply (div_le_iff₀ hcpos).mpr
    nlinarith
  have heq : (r-b/c)/c-r = (r*(1-c)-b/c)/c := by field_simp; ring
  rw [heq, abs_div, abs_of_pos hcpos]
  apply (div_le_iff₀ hcpos).mpr
  have habs : |r*(1-c)-b/c| ≤ A*δ+2*δ := by
    calc
      _ ≤ |r*(1-c)|+|b/c| := abs_sub _ _
      _ = |r| *|c-1|+|b/c| := by rw [abs_mul, abs_sub_comm 1 c]
      _ ≤ A*δ+2*δ := add_le_add (mul_le_mul hr hc (abs_nonneg _) hA) hbdiv
  nlinarith [mul_nonneg hA hδ]

lemma GP0042B2b_arm_centering {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (hN : 0 < N) (z : Assignment N) (a : Bool)
    (hcnt : 0 < armCount z a) :
    armMean R z a-barMu (fun _ => p) R a =
      T42_B p R a z / (T42_E p a z+1) := by
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hc := (T42_coin_pos p hp a).ne'
  have hsum : (∑ i, if z i=a then R i z-barMu (fun _ => p) R a else 0) =
      (∑ i, if z i=a then R i z else 0)-armCount z a*barMu (fun _ => p) R a := by
    simp only [armCount, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  unfold T42_B T42_E
  rw [sub_add_cancel, hsum]
  unfold armMean
  field_simp [hn, hc, hcnt.ne']
  <;> ring

lemma GP0042B2b_scaled_residual {N : ℕ} (p : ℝ) (R : CircleTable N)
    (hp : 0 < p ∧ p < 1) (hN : 0 < N) (M δ : ℝ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2)
    (hR : ∀ i z, |R i z| ≤ M) (z : Assignment N)
    (hB : ∀ a, |T42_B p R a z| ≤ δ) (hE : ∀ a, |T42_E p a z| ≤ δ) (i : Fin N) :
    |(N:ℝ)*lambda z i*residual R z i-
      residualContrast (fun _ => p) R (fun _ a => barMu (fun _ => p) R a) i z| ≤
        ((4*M+4)*(1/p+1/(1-p)))*δ := by
  let a := z i
  let c := T42_E p a z+1
  let b := T42_B p R a z
  let r := R i z-barMu (fun _ => p) R a
  have hcnear : |c-1| ≤ δ := by simpa only [c, add_sub_cancel_right] using hE a
  have hcpos : 0 < c := by have := (abs_le.mp hcnear).1; linarith
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hcoin : 0 < coin p a := T42_coin_pos p hp a
  have hcnt : 0 < armCount z a := by
    have he : c = armCount z a/(N*coin p a) := by simp only [c, T42_E, sub_add_cancel]
    rw [he] at hcpos
    exact (div_pos_iff_of_pos_right (mul_pos (Nat.cast_pos.mpr hN) hcoin)).mp hcpos
  have hmean := GP0042B2b_arm_centering p R hp hN z a hcnt
  have hr : |r| ≤ 2*M := by
    exact (abs_sub _ _).trans (by linarith [hR i z, T42_barMu_bound p R hp hN M hR a])
  have hd := GP0042B2b_div_perturbation r b c (2*M) δ (by positivity)
    hδ hδhalf hr (hB a) hcnear
  have heq : (N:ℝ)*lambda z i*residual R z i-
      residualContrast (fun _ => p) R (fun _ a => barMu (fun _ => p) R a) i z =
      armSign a / coin p a * ((r-b/c)/c-r) := by
    have hres : residual R z i = r-b/c := by
      dsimp only [residual, r, b, c, a] at hmean ⊢
      linarith
    rw [hres]
    dsimp only [r, c, a]
    cases hz : z i <;> simp only [lambda, residualContrast, bit, hz, Bool.false_eq_true,
      ite_false, ite_true, zero_div, one_mul, zero_mul, sub_zero, sub_self, zero_sub,
      armSign, coin, T42_E, sub_add_cancel]
    all_goals simp only [a, hz] at hcnt
    all_goals field_simp [hn, hp.1.ne', (sub_pos.mpr hp.2).ne', hcnt.ne']
    all_goals ring
  have hsign : |armSign a| = 1 := by cases a <;> norm_num [armSign]
  have hinv : 1/coin p a ≤ 1/p+1/(1-p) := by
    have hp0 : 0 ≤ 1/p := (one_div_pos.mpr hp.1).le
    have hq0 : 0 ≤ 1/(1-p) := (one_div_pos.mpr (sub_pos.mpr hp.2)).le
    cases a <;> norm_num [coin] <;> linarith
  rw [heq, abs_mul, abs_div, hsign, abs_of_pos hcoin]
  exact (mul_le_mul_of_nonneg_left hd (one_div_pos.mpr hcoin).le).trans
    (by
      have hh := mul_le_mul_of_nonneg_right hinv (by positivity : 0 ≤ (2*(2*M)+4)*δ)
      nlinarith [hh])

lemma GP0042B2b_product_compare {N : ℕ} (A T : Fin N → ℝ) (C L δ : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hT : ∀ i, |T i| ≤ C) (hAT : ∀ i, |A i-T i| ≤ L*δ) (i j : Fin N) :
    |A i*A j-T i*T j| ≤ L*(2*C+L)*δ := by
  have hA (k : Fin N) : |A k| ≤ C+L := by
    have ha := abs_add_le (A k-T k) (T k)
    rw [sub_add_cancel] at ha
    have hld := mul_le_mul_of_nonneg_left hδ1 hL
    linarith [hT k, hAT k]
  calc
    _ = |(A i-T i)*A j+T i*(A j-T j)| := by congr 1; ring
    _ ≤ |(A i-T i)*A j|+|T i*(A j-T j)| := abs_add_le _ _
    _ = |A i-T i| *|A j|+|T i| *|A j-T j| := by rw [abs_mul, abs_mul]
    _ ≤ (L*δ)*(C+L)+C*(L*δ) := add_le_add
      (mul_le_mul (hAT i) (hA j) (abs_nonneg _) (mul_nonneg hL hδ))
      (mul_le_mul (hT i) (hAT j) (abs_nonneg _) hC)
    _ = _ := by ring

lemma GP0042B2b_local_compare {N : ℕ} (A T : Fin N → ℝ)
    (B : Fin N → Finset (Fin N)) (hN : 0 < N) (D C L δ : ℝ)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdeg : ∀ i, ((B i).card:ℝ) ≤ D)
    (hT : ∀ i, |T i| ≤ C) (hAT : ∀ i, |A i-T i| ≤ L*δ) :
    |(∑ i, ∑ j ∈ B i, (A i*A j-T i*T j))/(N:ℝ)| ≤ D*L*(2*C+L)*δ := by
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  rw [abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i, ∑ j ∈ B i, |A i*A j-T i*T j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, ∑ _j ∈ B i, L*(2*C+L)*δ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        GP0042B2b_product_compare A T C L δ hC hL hδ hδ1 hT hAT i j))
    _ ≤ ∑ _i : Fin N, D*(L*(2*C+L)*δ) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right (hdeg i) (by positivity : 0 ≤ L*(2*C+L)*δ)
    _ = _ := by simp [mul_assoc]; ring

lemma GP0042B2b_kernel_local {N : ℕ} (R : CircleTable N) (z : Assignment N)
    (D : Fin N → Fin N → ℝ) (h : ℝ) (p : ℝ) (hN : 0 < N) :
    (N:ℝ)*(kernelVariance z (residual R z) (uniformDistanceKernel D h)-
      oracleHAC (fun _ => p) R (fun i => ball D i h)
        (fun _ a => barMu (fun _ => p) R a) z) =
    (∑ i, ∑ j ∈ ball D i h,
      (((N:ℝ)*lambda z i*residual R z i)*((N:ℝ)*lambda z j*residual R z j)-
        residualContrast (fun _ => p) R (fun _ a => barMu (fun _ => p) R a) i z*
        residualContrast (fun _ => p) R (fun _ a => barMu (fun _ => p) R a) j z))/(N:ℝ) := by
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hk : kernelVariance z (residual R z) (uniformDistanceKernel D h) =
      ∑ i, ∑ j ∈ ball D i h, lambda z i*lambda z j*residual R z i*residual R z j := by
    simp only [kernelVariance, uniformDistanceKernel, Matrix.of_apply, ball, mul_ite, mul_one, mul_zero,
      Finset.sum_filter]
  have hscale : (∑ i, ∑ j ∈ ball D i h,
      ((N:ℝ)*lambda z i*residual R z i)*((N:ℝ)*lambda z j*residual R z j)) =
      (N:ℝ)^2*(∑ i, ∑ j ∈ ball D i h, lambda z i*lambda z j*residual R z i*residual R z j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hk]
  unfold oracleHAC
  simp only [Finset.sum_sub_distrib]
  rw [hscale]
  field_simp


lemma GP0042B2b_plugin_bound {N : ℕ} (p : ℝ) (R : CircleTable N)
    (D : Fin N → Fin N → ℝ) (h : ℝ) (hp : 0 < p ∧ p < 1) (hN : 0 < N)
    (M K δ : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1/2)
    (hR : ∀ i z, |R i z| ≤ M) (hdeg : ∀ i, ((ball D i h).card:ℝ) ≤ K)
    (z : Assignment N) (hB : ∀ a, |T42_B p R a z| ≤ δ) (hE : ∀ a, |T42_E p a z| ≤ δ) :
    let S := 1/p+1/(1-p)
    let C := 2*M*S
    let L := (4*M+4)*S
    |(N:ℝ)*(kernelVariance z (residual R z) (uniformDistanceKernel D h)-
      oracleHAC (fun _ => p) R (fun i => ball D i h)
        (fun _ a => barMu (fun _ => p) R a) z)| ≤ K*L*(2*C+L)*δ := by
  dsimp only
  let S := 1/p+1/(1-p)
  let C := 2*M*S
  let L := (4*M+4)*S
  have hS : 0 ≤ S := add_nonneg (one_div_pos.mpr hp.1).le
    (one_div_pos.mpr (sub_pos.mpr hp.2)).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  rw [GP0042B2b_kernel_local R z D h p hN]
  apply GP0042B2b_local_compare _ _ _ hN K C L δ hK hC hL hδ (by linarith) hdeg
  · intro i
    have hr : ∀ i z, |R i z-barMu (fun _ => p) R (z i)| ≤ 2*M := by
      intro i z
      exact (abs_sub _ _).trans (by linarith [hR i z, T42_barMu_bound p R hp hN M hR (z i)])
    have ht := CLTCompletion.raw_contrast_abs_le p (2*M)
      (fun i z => R i z-barMu (fun _ => p) R (z i)) hp (by positivity) hr i z
    have he : C = 2*M/p+2*M/(1-p) := by dsimp [C, S]; ring
    rw [he]
    convert ht using 1
    cases hz : z i <;> simp [residualContrast, bit, hz]
  · exact GP0042B2b_scaled_residual p R hp hN M δ hM hδ hδhalf hR z hB hE

/-- Four errors with second-moment bounds from the Hájek CLT. -/
def GP0042B2b_errors {N : ℕ} (p : ℝ) (R : CircleTable N) (z : Assignment N) : ℝ :=
  (T42_B p R true z)^2+(T42_B p R false z)^2+
    (T42_E p true z)^2+(T42_E p false z)^2

lemma GP0042B2b_errors_small {N : ℕ} (p : ℝ) (R : CircleTable N) (z : Assignment N)
    (δ : ℝ) (hδ : 0 ≤ δ) (he : GP0042B2b_errors p R z ≤ δ^2) :
    (∀ a, |T42_B p R a z| ≤ δ) ∧ (∀ a, |T42_E p a z| ≤ δ) := by
  have hB1 := sq_nonneg (T42_B p R true z)
  have hB0 := sq_nonneg (T42_B p R false z)
  have hE1 := sq_nonneg (T42_E p true z)
  have hE0 := sq_nonneg (T42_E p false z)
  dsimp only [GP0042B2b_errors] at he
  constructor
  · intro a
    cases a <;> apply (sq_le_sq₀ (abs_nonneg _) hδ).mp <;>
      simpa only [sq_abs] using (by nlinarith : (T42_B p R _ z)^2 ≤ δ^2)
  · intro a
    cases a <;> apply (sq_le_sq₀ (abs_nonneg _) hδ).mp <;>
      simpa only [sq_abs] using (by nlinarith : (T42_E p _ z)^2 ≤ δ^2)

lemma GP0042B2b_plugin_concentration (P : PopulationSequence Space) (p d h : ℝ)
    (hp : 0 < p ∧ p < 1) (hh : 0 ≤ h) (hP : SpatialLocalConditions P)
    (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h) :
    let R := fun N => circleAverage (P N) d
    let W := fun N => oracleHAC (fun _ => p) (R N) (spatialNeighborhoods P h N)
      (fun _ a => barMu (fun _ => p) (R N) a)
    let H := fun N z => kernelVariance z (residual (R N) z)
      (uniformDistanceKernel (nodeSeparation (P N)) h)
    InProb (fun _ _ => p) (fun N z => (N:ℝ)*(H N z-W N z)) := by
  dsimp only
  obtain ⟨M, hM, hb⟩ := hP.1
  obtain ⟨c, hc⟩ := hP.2.2
  let D := |c h|+1
  let S := 1/p+1/(1-p)
  let C := 2*M*S
  let L := (4*M+4)*S
  let A := D*L*(2*C+L)
  let KB := D*((2*M)/p+(2*M)/(1-p))^2
  let K1 := (1-p)/p
  let K0 := p/(1-p)
  let K := 2*KB+K1+K0
  have hD : 0 < D := by dsimp [D]; positivity
  have hS : 0 < S := add_pos (one_div_pos.mpr hp.1)
    (one_div_pos.mpr (sub_pos.mpr hp.2))
  have hC : 0 < C := by dsimp [C]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  intro ε hε
  let δ := min (1/2:ℝ) (ε/(A+1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδhalf : δ ≤ 1/2 := min_le_left _ _
  have hAδ : A*δ ≤ ε := by
    have hd := (le_div_iff₀ (by linarith : 0 < A+1)).mp (min_le_right (1/2:ℝ) (ε/(A+1)))
    dsimp only [δ]
    nlinarith [hδ]
  have hbound : ∀ᶠ N in atTop,
      prob (fun _ : Fin N => p) (fun z => ε < |(N:ℝ)*
        (kernelVariance z (residual (circleAverage (P N) d) z)
          (uniformDistanceKernel (nodeSeparation (P N)) h)-
        oracleHAC (fun _ => p) (circleAverage (P N) d) (spatialNeighborhoods P h N)
          (fun _ a => barMu (fun _ => p) (circleAverage (P N) d) a) z)|) ≤ (K/N)/δ^2 := by
    filter_upwards [eventually_gt_atTop 0, hb, hWD, hloc, hc h hh] with N hN hbN hwdN hlN hdN
    let R := circleAverage (P N) d
    let B := spatialNeighborhoods P h N
    have hR := CLTCompletion.circleAverage_abs_le (P N) d M hwdN (fun x z => (hbN x z).le)
    have hdeg (i : Fin N) : ((B i).card:ℝ) ≤ D :=
      (hdN i).trans ((le_abs_self _).trans (by dsimp [D]; linarith))
    have hsymm (i j : Fin N) : j ∈ B i ↔ i ∈ B j := by
      simp only [B, spatialNeighborhoods, ball, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [CLTCompletion.nodeSeparation_symm (P N) i j]
    have hout (i j : Fin N) (hij : j ∉ B i) : ¬sharesSource R i j := by
      apply hlN i j
      simpa only [B, spatialNeighborhoods, ball, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hij
    have hb1 := T42_B_moment p R B hp hN M D hM.le hD.le hR hsymm hout hdeg true
    have hb0 := T42_B_moment p R B hp hN M D hM.le hD.le hR hsymm hout hdeg false
    have he1 : expect (fun _ : Fin N => p) (fun z => (T42_E p true z)^2) = K1/N := by
      simpa [coin, K1] using T42_E_moment p hp hN true
    have he0 : expect (fun _ : Fin N => p) (fun z => (T42_E p false z)^2) = K0/N := by
      simpa [coin, K0, sub_sub_cancel] using T42_E_moment p hp hN false
    have hQ : expect (fun _ : Fin N => p) (GP0042B2b_errors p R) ≤ K/N := by
      change expect (fun _ : Fin N => p) (fun z =>
        (T42_B p R true z)^2+(T42_B p R false z)^2+
          (T42_E p true z)^2+(T42_E p false z)^2) ≤ _
      rw [expect_add, expect_add, expect_add, he1, he0]
      change _ ≤ (2*KB+K1+K0)/N
      change _ ≤ KB/N at hb1 hb0
      linear_combination hb1+hb0
    have hinc : ∀ z : Assignment N, ε < |(N:ℝ)*
        (kernelVariance z (residual R z) (uniformDistanceKernel (nodeSeparation (P N)) h)-
        oracleHAC (fun _ => p) R B (fun _ a => barMu (fun _ => p) R a) z)| →
        δ^2 < GP0042B2b_errors p R z := by
      intro z hz
      by_contra hnot
      obtain ⟨hBs, hEs⟩ := GP0042B2b_errors_small p R z δ hδ.le (le_of_not_gt hnot)
      have hh := GP0042B2b_plugin_bound p R (nodeSeparation (P N)) h hp hN M D δ hM.le hD.le
        hδ.le hδhalf hR hdeg z hBs hEs
      change _ ≤ A*δ at hh
      exact (not_lt_of_ge (hh.trans hAδ)) hz
    have hmono := T34_prob_mono (fun _ : Fin N => p) (fun _ => hp) _ _ hinc
    have hmark := T34_markov (fun _ : Fin N => p) (fun _ => hp)
      (fun z => δ^2 < GP0042B2b_errors p R z) (GP0042B2b_errors p R) (δ^2)
      (sq_pos_of_pos hδ) (fun z => by dsimp [GP0042B2b_errors]; positivity) (fun z hz => hz.le)
    exact hmono.trans (hmark.trans (div_le_div_of_nonneg_right hQ (sq_nonneg δ)))
  have hlim : Tendsto (fun N : ℕ => (K/N)/δ^2) atTop (nhds 0) := by
    have hnlim : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_natCast_atTop_atTop.inv_tendsto_atTop
    simpa [div_eq_mul_inv] using (hnlim.const_mul K).div_const (δ^2)
  exact squeeze_zero' (Eventually.of_forall (fun N => T34_prob_nonneg _ (fun _ => hp) _)) hbound hlim

theorem capped_pd_coverage_proof (P : PopulationSequence Space) (p d h α : ℝ)
    (hp : 0 < p ∧ p < 1) (hd : 0 ≤ d) (hh : 0 ≤ h) (hα : 0 < α ∧ α < 1)
    (hP : SpatialLocalConditions P) (hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
    (hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
    (hv : Nondegenerate (fun N => variance (fun _ => p) (linearHajek (fun _ => p) (circleAverage (P N) d))))
    (values : ∀ N, Fin N → ℝ) (vectors : ∀ N, Matrix (Fin N) (Fin N) ℝ)
    (horth : ∀ N, (vectors N).transpose * vectors N = 1)
    (heigen : ∀ N, spectralKernel (values N) (vectors N) false = uniformDistanceKernel (nodeSeparation (P N)) h)
    (hhom : ∀ᶠ N in atTop, 0 ≤ homophilyQ (fun _ => p) (circleAverage (P N) d) (spatialNeighborhoods P h N)
      (fun _ a => barMu (fun _ => p) (circleAverage (P N) d) a))
    (c : ∀ N, Assignment N → ℝ) (hc : ∀ N z, normalQuantile (1-α/2) ≤ c N z) :
    Conservative (fun N => prob (fun _ => p) (fun z =>
      let R := circleAverage (P N) d
      let Q := spectralKernel (values N) (vectors N) true
      |hajek R z-ame (fun _ => p) R| ≤ c N z *
        Real.sqrt (cappedVariance (kernelVariance z (residual R z) Q) (adjustmentMu z Q)))) α := by
  let R := fun N => circleAverage (P N) d
  let π := fun (N : ℕ) (_ : Fin N) => p
  let V := fun N => variance (π N) (linearHajek (π N) (R N))
  let U := fun N z => hajek (R N) z - ame (π N) (R N)
  let W := fun N => oracleHAC (π N) (R N) (spatialNeighborhoods P h N)
    (fun _ a => barMu (π N) (R N) a)
  let H := fun N z => kernelVariance z (residual (R N) z)
    (uniformDistanceKernel (nodeSeparation (P N)) h)
  let E := fun N => expect (π N) (W N)
  have hπ : ∀ N i, 0 < π N i ∧ π N i < 1 := fun _ _ => hp
  have hCLT : NormalLimit π (fun N z => U N z / Real.sqrt (V N)) :=
    hajek_central_limit_proof P p d hp hd hP hWD hv
  have hconcentration : InProb π (fun N z => (N : ℝ)*(W N z-E N)) :=
    GP0042B2b_oracle_concentration P p d h hp hh hP hWD hloc
  have hplugin : InProb π (fun N z => (N : ℝ)*(H N z-W N z)) :=
    GP0042B2b_plugin_concentration P p d h hp hh hP hWD hloc
  have hEV : ∀ᶠ N in atTop, V N ≤ E N := by
    filter_upwards [hloc, hhom, eventually_gt_atTop (0 : ℕ)] with N hlocal hQ hN
    have hm := GP0042B2b_capped_pd_oracle_mean (P N) p d h hN hp hh hlocal
    change E N = V N + _ at hm
    rw [hm]
    exact le_add_of_nonneg_right (div_nonneg hQ (Nat.cast_nonneg N))
  have htotal : InProb π (fun N z => (N : ℝ)*(H N z-E N)) := by
    have hsum := GP0042B2b_capped_pd_inProb_add π hπ _ _ hplugin hconcentration
    have heq : (fun (N : ℕ) (z : Assignment N) => (N : ℝ)*(H N z-E N)) =
        (fun (N : ℕ) (z : Assignment N) => (N : ℝ)*(H N z-W N z) + (N : ℝ)*(W N z-E N)) := by
      funext N z
      ring
    rw [heq]
    exact hsum
  have hshort := GP0042B2b_capped_pd_shortfall π hπ H E V hv hEV htotal
  have hV : ∀ᶠ N in atTop, 0 < V N := by
    obtain ⟨v, hvpos, hvfloor⟩ := hv
    filter_upwards [hvfloor, eventually_gt_atTop (0 : ℕ)] with N hfloor hN
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hprod : 0 < (N : ℝ)*V N := hvpos.trans_le hfloor
    by_contra hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hn.le (le_of_not_gt hnot)
    linarith
  have hraw := GP0042B2b_capped_pd_one_sided_wald π hπ U H V hV hCLT hshort α hα
  obtain ⟨hq, _⟩ := GP0042B2b_capped_pd_quantile α hα
  intro ε hε
  filter_upwards [hraw ε hε] with N hN
  apply hN.trans
  apply GP0042B2b_capped_pd_prob_mono (π N) (hπ N)
  intro z hz
  exact GP0042B2b_capped_pd_pointwise (values N) (vectors N) z (R N) _ (heigen N)
    _ (c N z) (U N z) hq.le (hc N z) hz.2

end
end AronowAudit.P004.Wave1
