import SAP.P031.Defs.WholeW3
import SAP.P031.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P031.WH.W3

open scoped BigOperators Topology
open Finset Filter

noncomputable section

/-- Finite fourth-moment concentration inputs. For a uniform M-subset of an
N-unit schedule with divisor-N fourth moment at most C, the first and second
sample raw moments have mean squared errors at most sqrt(C)/M and C/M;
the squared population mean and population variance are at most sqrt(C).
Route: finite Cauchy--Schwarz bounds the population second moment by sqrt(C).
Use `pop_variance_raw` to bound both population variances by their raw moments,
then `sample_mean_squared_error` for v and v^2. Its sampling coefficient is
between zero and 1/M because 2 <= M <= N. No outcome independence is used.
This is a finite algebra/Cauchy--Schwarz leaf (about 100--180 lines). -/
def T6_L1 : Prop :=
  ∀ (N M : ℕ) (v : Fin N → ℝ) (C : ℝ),
    2 ≤ M → M ≤ N → 0 ≤ C → fourthMomentW3 v ≤ C →
    expectation M (fun s => (groupMean s v - groupMean univ v) ^ 2) ≤
        Real.sqrt C / M ∧
    expectation M (fun s =>
      (groupMean s (fun i => v i ^ 2) - groupMean univ (fun i => v i ^ 2)) ^ 2) ≤
        C / M ∧
    (groupMean univ v) ^ 2 ≤ Real.sqrt C ∧ popVariance v ≤ Real.sqrt C

/-- Finite L1 concentration of the centered unbiased sample variance under a
fourth-moment bound. The first leaf is the only unproved input.
Route: write s^2 = M/(M-1) (sample raw second moment - sample mean squared).
For d = sample mean - population mean, use
|sample mean squared - population mean squared| <= d^2 + 2 |mean| |d|.
Use the first leaf and finite `ExpectationAbsSqrt` for the two raw errors.
The resulting bound is at most
6 sqrt(C/M) + 2 sqrt(C)/M + sqrt(C)/(M-1) <= 16 sqrt(C/M).
All expectations are finite averages; M >= 2 handles every denominator, and
C = 0 is included. Estimated proof length: 150--250 lines. -/
def T6_L2 : Prop :=
  T6_L1 → ∀ (N M : ℕ) (v : Fin N → ℝ) (C : ℝ),
    2 ≤ M → M ≤ N → 0 ≤ C → fourthMomentW3 v ≤ C →
    expectation M (fun s => |sampleVariance s v - popVariance v|) ≤
      16 * Real.sqrt (C / M)

/-- The two fourth-moment leaves give consistency of both sample arm variances.
The control arm uses the exact complement bijection of the uniform design. -/
theorem armConsistencyW3 (h1 : T6_L1) (h2 : T6_L2)
    (P : ℕ → Population) (p : ℝ) (hN : GrowingPopulations P)
    (hp : 0 < p) (hp1 : p < 1)
    (hAlloc : Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (𝓝 p))
    (hFourth : UniformFourthMomentsW3 P) : ArmSecondMomentsConverge P := by
  let Q := fun n => Bridge.toPopulation (P n)
  obtain ⟨C, hC, hBound⟩ := hFourth
  have hSizes : ∀ n, 2 ≤ (P n).M ∧ 2 ≤ (P n).N - (P n).M ∧
      (P n).M ≤ (P n).N ∧ 4 ≤ (P n).N :=
    fun n => AronowAudit.P031.population_sizes (Q n)
  have hNr : Tendsto (fun n => ((P n).N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hN0 : ∀ n, ((P n).N : ℝ) ≠ 0 := by
    intro n
    have hn : (4 : ℝ) ≤ (P n).N := by exact_mod_cast (hSizes n).2.2.2
    linarith
  have hMr : Tendsto (fun n => ((P n).M : ℝ)) atTop atTop := by
    apply (hNr.atTop_mul_pos hp hAlloc).congr
    intro n
    field_simp [hN0 n]
  have hComp : Tendsto (fun n => 1 - ((P n).M : ℝ) / (P n).N)
      atTop (𝓝 (1 - p)) := tendsto_const_nhds.sub hAlloc
  have hKr : Tendsto (fun n => (((P n).N - (P n).M : ℕ) : ℝ)) atTop atTop := by
    apply (hNr.atTop_mul_pos (by linarith : 0 < 1 - p) hComp).congr
    intro n
    rw [Nat.cast_sub (hSizes n).2.2.1]
    field_simp [hN0 n]
  have hOneArm : ∀ (m : ℕ → ℕ), (∀ n, 2 ≤ m n) → (∀ n, m n ≤ (P n).N) →
      Tendsto (fun n => (m n : ℝ)) atTop atTop →
      ∀ v : (n : ℕ) → Fin (P n).N → ℝ, (∀ n, fourthMomentW3 (v n) ≤ C) →
      Tendsto (fun n => expectation (m n)
        (fun s => |sampleVariance s (v n) - popVariance (v n)|)) atTop (𝓝 0) := by
    intro m hm hmn hmTop v hv
    have hUpper : Tendsto (fun n => 16 * Real.sqrt (C / (m n : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
      simpa using ((hmTop.const_div_atTop C).sqrt).const_mul 16
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    · intro n
      exact AronowAudit.P031.expectation_nonneg _ _ (fun _ _ => abs_nonneg _)
    · intro n
      exact h2 h1 (P n).N (m n) (v n) C (hm n) (hmn n) hC (hv n)
  have hT := hOneArm (fun n => (P n).M)
    (fun n => (hSizes n).1) (fun n => (hSizes n).2.2.1)
    hMr (fun n => (P n).y1) (fun n => (hBound n).1)
  have hK := hOneArm (fun n => (P n).N - (P n).M)
    (fun n => (hSizes n).2.1) (fun n => Nat.sub_le _ _)
    hKr (fun n => (P n).y0) (fun n => (hBound n).2)
  have hK' : Tendsto (fun n => expectation (P n).M
      (fun s => |sampleVariance sᶜ (P n).y0 - popVariance (P n).y0|))
      atTop (𝓝 (0 : ℝ)) := by
    apply hK.congr
    intro n
    symm
    have he := AronowAudit.P031.expectation_compl (P n).M
      (by simpa using (hSizes n).2.2.1)
      (fun s => |sampleVariance s (P n).y0 - popVariance (P n).y0|)
    simp only [Fintype.card_fin] at he
    exact he
  constructor
  · change AronowAudit.P031.ConvergesInProbability Q
      (fun R s => AronowAudit.P031.sampleVariance s R.y1 -
        AronowAudit.P031.popVariance R.y1) 0
    apply AronowAudit.P031.probability_limit_of_mean_absolute_error
    convert hT using 1
    simp only [sub_zero]
    rfl
  · change AronowAudit.P031.ConvergesInProbability Q
      (fun R s => AronowAudit.P031.sampleVariance sᶜ R.y0 -
        AronowAudit.P031.popVariance R.y0) 0
    apply AronowAudit.P031.probability_limit_of_mean_absolute_error
    convert hK' using 1
    simp only [sub_zero]
    rfl

/-- Weighted-sum probability calculus yields N times Neyman's probability limit.
This is glue to the existing finite-design results, not a new analytic leaf. -/
theorem neymanProbabilityLimitW3 (P : ℕ → Population)
    (p v1 v0 : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hAlloc : Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (𝓝 p))
    (hV1 : Tendsto (fun n => popVariance (P n).y1) atTop (𝓝 v1))
    (hV0 : Tendsto (fun n => popVariance (P n).y0) atTop (𝓝 v0))
    (hArm : ArmSecondMomentsConverge P) :
    ConvergesInProbability P (fun R s => (R.N : ℝ) * neymanEstimator R s)
      (v1 / p + v0 / (1 - p)) := by
  let Q := fun n => Bridge.toPopulation (P n)
  let F : AronowAudit.P031.Population → ℝ := fun R => (R.N : ℝ) / R.M
  let G : AronowAudit.P031.Population → ℝ := fun R => (R.N : ℝ) / (R.N - R.M : ℕ)
  have hF : Tendsto (fun n => F (Q n)) atTop (𝓝 (1 / p)) := by
    have h : Tendsto (fun n => 1 / (((P n).M : ℝ) / (P n).N))
        atTop (𝓝 (1 / p)) := tendsto_const_nhds.div hAlloc hp.ne'
    apply h.congr
    intro n
    simp only [one_div_div]
    rfl
  have hG : Tendsto (fun n => G (Q n)) atTop (𝓝 (1 / (1 - p))) := by
    have hComp : Tendsto (fun n => 1 - ((P n).M : ℝ) / (P n).N)
        atTop (𝓝 (1 - p)) := tendsto_const_nhds.sub hAlloc
    have hpc : 1 - p ≠ 0 := by linarith
    have h : Tendsto (fun n => 1 / (1 - ((P n).M : ℝ) / (P n).N))
        atTop (𝓝 (1 / (1 - p))) := tendsto_const_nhds.div hComp hpc
    apply h.congr
    intro n
    have hs := AronowAudit.P031.population_sizes (Q n)
    have hn : ((P n).N : ℝ) ≠ 0 := by
      have hh : (4 : ℝ) ≤ (P n).N := by exact_mod_cast hs.2.2.2
      linarith
    dsimp only [G, Q, Bridge.toPopulation]
    rw [Nat.cast_sub (show (P n).M ≤ (P n).N from hs.2.2.1)]
    field_simp [hn]
  have hH : Tendsto (fun n => F (Q n) * popVariance (P n).y1 +
      G (Q n) * popVariance (P n).y0) atTop (𝓝 (v1 / p + v0 / (1 - p))) := by
    have h := (hF.mul hV1).add (hG.mul hV0)
    have he : 1 / p * v1 + 1 / (1 - p) * v0 = v1 / p + v0 / (1 - p) := by ring
    rw [he] at h
    exact h
  have hWeighted := AronowAudit.P031.Wave1.FootnoteThreeProbability.n8_proof
    AronowAudit.P031.Wave1.FootnoteThreeProbability.n7_proof Q F G
    (fun R => F R * AronowAudit.P031.popVariance R.y1 +
      G R * AronowAudit.P031.popVariance R.y0)
    (fun R s => AronowAudit.P031.sampleVariance s R.y1 - AronowAudit.P031.popVariance R.y1)
    (fun R s => AronowAudit.P031.sampleVariance sᶜ R.y0 - AronowAudit.P031.popVariance R.y0)
    (1 / p) (1 / (1 - p)) (v1 / p + v0 / (1 - p)) hF hG hH hArm.1 hArm.2
  change AronowAudit.P031.ConvergesInProbability Q
    (fun R s => (R.N : ℝ) * AronowAudit.P031.neymanEstimator R s) _
  apply AronowAudit.P031.probability_limit_congr Q _ _ hWeighted
  intro n s hs
  have hc := (mem_powersetCard.mp hs).2
  have hkc : sᶜ.card = (Q n).N - (Q n).M := by
    rw [card_compl, hc, Fintype.card_fin]
  rw [AronowAudit.P031.neymanEstimator, AronowAudit.P031.observed_neyman,
    hc, hkc]
  dsimp only [F, G]
  ring

/-- The cited regular regime and its normal limit imply the positive Neyman/HC2
coverage contrast. The finite treatment-effect variance makes the leading Neyman
limit at least the leading actual variance. The existing random-cutoff normal
limit theorem then gives conservative coverage, with HC2 transferred exactly. -/
theorem conservativeContrastW3 (h1 : T6_L1) (h2 : T6_L2)
    (P : ℕ → Population) (hR : RegularFamilyW3 P)
    (hNormal : StandardizedNormalLimit P) (z : ℝ) (hz : 0 < z) :
    ConservativeCoverage P neymanEstimator z ∧ ConservativeCoverage P hc2Estimator z := by
  obtain ⟨p, μ1, μ0, v1, v0, c, hReg⟩ := hR
  let Q := fun n => Bridge.toPopulation (P n)
  let D : ℝ := (1 - p) / p * v1 + p / (1 - p) * v0 + 2 * c
  let B : ℝ := v1 / p + v0 / (1 - p)
  have hArm := armConsistencyW3 h1 h2 P p hReg.growing
    hReg.allocation_pos hReg.allocation_lt_one hReg.allocation hReg.fourth
  have hB := neymanProbabilityLimitW3 P p v1 v0 hReg.allocation_pos
    hReg.allocation_lt_one hReg.allocation hReg.variance_treatment
    hReg.variance_control hArm
  obtain ⟨hD, _, _, hEffect⟩ := AronowAudit.P031.corrected_footnote_three_limits Q
    hReg.growing p v1 v0 c hReg.allocation_pos hReg.allocation_lt_one
    hReg.allocation hReg.variance_treatment hReg.variance_control hReg.covariance
  have hEffectNonneg : 0 ≤ v1 + v0 - 2 * c := by
    apply ge_of_tendsto' hEffect
    intro n
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hDB : D ≤ B := by
    have hp : p ≠ 0 := hReg.allocation_pos.ne'
    have hpc : 1 - p ≠ 0 := by linarith [hReg.allocation_lt_one]
    have hEq : B - D = v1 + v0 - 2 * c := by
      dsimp only [B, D]
      field_simp [hp, hpc]
      ring
    linarith
  have hDpos : 0 < D := hReg.contrast_variance_pos
  have hLimit := AronowAudit.P031.Wave1.T6_coverage_limit Q
    AronowAudit.P031.neymanEstimator B D z hNormal hD hDpos hB hz
  have hNominal : 2 * normalCDF z - 1 ≤
      2 * normalCDF (z * Real.sqrt (B / D)) - 1 := by
    have hOne : 1 ≤ Real.sqrt (B / D) := by
      apply Real.le_sqrt_of_sq_le
      norm_num only [one_pow]
      exact (le_div_iff₀ hDpos).mpr (by simpa using hDB)
    have hzle : z ≤ z * Real.sqrt (B / D) := by nlinarith
    have hPhi := (ProbabilityTheory.monotone_cdf (ProbabilityTheory.gaussianReal 0 1)) hzle
    change normalCDF z ≤ normalCDF (z * Real.sqrt (B / D)) at hPhi
    linarith
  have hNey : ConservativeCoverage P neymanEstimator z := by
    intro ε hε
    have hClose := Metric.tendsto_nhds.mp hLimit ε hε
    filter_upwards [hClose] with n hn
    rw [Real.dist_eq, abs_lt] at hn
    change 2 * normalCDF z - 1 - ε ≤
      AronowAudit.P031.coverage (Q n) AronowAudit.P031.neymanEstimator z
    change -ε < AronowAudit.P031.coverage (Q n) AronowAudit.P031.neymanEstimator z -
      (2 * normalCDF (z * Real.sqrt (B / D)) - 1) ∧ _ at hn
    linarith [hn.1]
  refine ⟨hNey, ?_⟩
  intro ε hε
  filter_upwards [hNey ε hε] with n hn
  change _ ≤ AronowAudit.P031.coverage (Q n) AronowAudit.P031.hc2Estimator z
  rw [← AronowAudit.P031.coverage_neyman_eq_hc2]
  exact hn

/-- Explicit nondegenerate regular sign families. Their outcomes are bounded,
so their fourth moments are bounded; no new proof leaf is needed for these
witness conditions. -/
theorem footnoteRegularW3 (a : ℝ) (ha : 0 < a) : RegularFamilyW3 (footnotePopulation a) := by
  refine ⟨1 / 4, 2, 0, a ^ 2, 1, a, ?_⟩
  refine ⟨(AronowAudit.P031.footnote_population_growth a).1, by norm_num, by norm_num,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, by positivity, by norm_num, ?_⟩
  · exact tendsto_const_nhds.congr
      (fun n => (AronowAudit.P031.footnote_population_moments a n).1.symm)
  · let B : ℝ := |a| + 2
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    refine ⟨B ^ 4, by positivity, ?_⟩
    intro n
    have hSize : (0 : ℝ) < (footnotePopulation a n).N := by
      change (0 : ℝ) < (4 * (n + 2) : ℕ)
      positivity
    have hPoint : ∀ i : Fin (footnotePopulation a n).N,
        |(footnotePopulation a n).y1 i| ≤ B ∧ |(footnotePopulation a n).y0 i| ≤ B := by
      intro i
      dsimp only [footnotePopulation, footnoteSigns]
      split_ifs <;> constructor
      · calc
          |a * (-1) + 2| ≤ |a * (-1)| + |(2 : ℝ)| := abs_add_le _ _
          _ = B := by simp [B]
      · simp only [abs_neg, abs_one]
        dsimp only [B]
        linarith [abs_nonneg a]
      · calc
          |a * 1 + 2| ≤ |a * 1| + |(2 : ℝ)| := abs_add_le _ _
          _ = B := by simp [B]
      · simp only [abs_one]
        dsimp only [B]
        linarith [abs_nonneg a]
    have hBound : ∀ y : Fin (footnotePopulation a n).N → ℝ,
        (∀ i, |y i| ≤ B) → fourthMomentW3 y ≤ B ^ 4 := by
      intro y hy
      have hPoint4 : ∀ i, y i ^ 4 ≤ B ^ 4 := by
        intro i
        simpa only [pow_abs, abs_of_nonneg (by positivity : 0 ≤ y i ^ 4)] using
          pow_le_pow_left₀ (abs_nonneg (y i)) (hy i) 4
      unfold fourthMomentW3 groupMean
      apply (div_le_iff₀ (by simpa using hSize)).mpr
      calc
        _ ≤ ∑ _i : Fin (footnotePopulation a n).N, B ^ 4 :=
          sum_le_sum (fun i _ => hPoint4 i)
        _ = _ := by simp [mul_comm]
    exact ⟨hBound _ (fun i => (hPoint i).1), hBound _ (fun i => (hPoint i).2)⟩
  · exact tendsto_const_nhds.congr
      (fun n => (AronowAudit.P031.footnote_population_moments a n).2.2.1.symm)
  · exact tendsto_const_nhds.congr
      (fun n => (AronowAudit.P031.footnote_population_moments a n).2.1.symm)
  · exact tendsto_const_nhds.congr
      (fun n => (AronowAudit.P031.footnote_population_moments a n).2.2.2.2.2.1.symm)
  · exact tendsto_const_nhds.congr
      (fun n => (AronowAudit.P031.footnote_population_moments a n).2.2.2.2.1.symm)
  · exact tendsto_const_nhds.congr
      (fun n => (AronowAudit.P031.footnote_population_moments a n).2.2.2.2.2.2.symm)
  · norm_num
    nlinarith [sq_nonneg a]

/-- Restricted positive T6 candidate, assembled from two finite concentration leaves and existing
finite-design variance, explicit sign-family, and Gaussian coverage theorems. -/
theorem T6_assembly (h1 : T6_L1) (h2 : T6_L2) : T6CitedRegimeStatement := by
  refine ⟨?_, ?_, conservativeContrastW3 h1 h2⟩
  · have hU : UnbalancedVarianceLimit (footnotePopulation 2) (28 / 3) (49 / 3) := by
      refine ⟨(AronowAudit.P031.footnote_population_growth 2).1,
        (AronowAudit.P031.footnote_population_growth 2).2, by norm_num, ?_, ?_, ?_⟩
      · have h := (AronowAudit.P031.footnote_deterministic_limits 2).1
        norm_num at h
        exact h
      · have h := AronowAudit.P031.footnote_ols_probability_limit 2
        norm_num at h
        exact h
      · have h := AronowAudit.P031.footnote_ce_probability_limit 2
        norm_num at h
        exact h
    have hNormal : StandardizedNormalLimit (footnotePopulation 2) :=
      AronowAudit.P031.Wave1.T6_standardized_normal
    refine ⟨footnotePopulation 2, 28 / 3, 49 / 3, footnoteRegularW3 2 (by norm_num),
      hU, by norm_num, hNormal, ?_⟩
    intro z hz
    refine ⟨2 * normalCDF (z * Real.sqrt ((28 / 3 : ℝ) / (49 / 3))) - 1, ?_, ?_, ?_⟩
    · have hs : Real.sqrt ((28 / 3 : ℝ) / (49 / 3)) < 1 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
        norm_num
      have ht : z * Real.sqrt ((28 / 3 : ℝ) / (49 / 3)) < z := by nlinarith
      have hPhi := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf ht
      change normalCDF (z * Real.sqrt ((28 / 3 : ℝ) / (49 / 3))) < normalCDF z at hPhi
      linarith
    · exact AronowAudit.P031.Wave1.T6_coverage_limit
        (fun n => Bridge.toPopulation (footnotePopulation 2 n))
        AronowAudit.P031.olsEstimator _ _ z hNormal hU.2.2.2.1 hU.2.2.1 hU.2.2.2.2.1 hz
    · exact AronowAudit.P031.Wave1.T6_coverage_limit
        (fun n => Bridge.toPopulation (footnotePopulation 2 n))
        AronowAudit.P031.ceEstimator _ _ z hNormal hU.2.2.2.1 hU.2.2.1 hU.2.2.2.2.2 hz
  · refine ⟨footnotePopulation (1 / 2), 13 / 3, 25 / 12,
      footnoteRegularW3 (1 / 2) (by norm_num), ?_, by norm_num⟩
    refine ⟨(AronowAudit.P031.footnote_population_growth (1 / 2)).1,
      (AronowAudit.P031.footnote_population_growth (1 / 2)).2, by norm_num, ?_, ?_, ?_⟩
    · have h := (AronowAudit.P031.footnote_deterministic_limits (1 / 2)).1
      norm_num at h
      exact h
    · have h := AronowAudit.P031.footnote_ols_probability_limit (1 / 2)
      norm_num at h
      exact h
    · have h := AronowAudit.P031.footnote_ce_probability_limit (1 / 2)
      norm_num at h
      exact h

end
end SAP.P031.WH.W3
