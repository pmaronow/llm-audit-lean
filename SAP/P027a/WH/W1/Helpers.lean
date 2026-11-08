import SAP.P027a.WH.W1.Helpers.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.WH.W1

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory SAP.P027a.Bridge
attribute [local instance] Classical.propDecidable

/-- The existing family theorem supplies its four principal identities. -/
theorem alternating_family_core : AlternatingFamily := by
  intro r m hr hm
  have h := AronowAudit.P027.alternating_family_witness r m hr hm
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Explicit normalization, table specializations and nonvanishing of the family. -/
theorem alternating_family_details : AlternatingFamilyWholeDetails := by
  have hn (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
      let D := phaseOriginal r m hr
      let z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ :=
        fun k => if k.1.2 = 0 then -1 else 1
      let q : ℝ := 2*r
      let N : ℝ := m*q
      biasA D z = -N^2/q ∧ biasA D z/N^2 = -1/q := by
    dsimp only
    have ha : biasA (phaseOriginal r m hr)
        (fun k => if k.1.2 = 0 then (-1:ℝ) else 1) = -(2*r)*(m:ℝ)^2 :=
      (AronowAudit.P027.alternating_family_witness r m hr hm).2.1
    rw [ha]
    have hmR : (m:ℝ) ≠ 0 := by positivity
    have hrR : (r:ℝ) ≠ 0 := by positivity
    constructor <;> field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro r m hr hm
    dsimp only
    refine ⟨?_, (hn r m hr hm).1, (hn r m hr hm).2, ?_⟩
    · intro g
      by_cases hg : g.2 = 0 <;> simp [groupTotal, hg]
    · rw [(hn r m hr hm).2]
      exact (AronowAudit.P027.alternating_family_witness r m hr hm).2.2.2.1
  · intro row
    let m := ppsConfigurationM row
    let r := if row.val % 2 = 0 then 2 else 10
    have hm : 0 < m := by fin_cases row <;> norm_num [m, ppsConfigurationM]
    have hr : 0 < r := by dsimp [r]; split <;> norm_num
    have hN : ppsConfigurationN row = m*(2*r) := by
      fin_cases row <;> norm_num [r, m, ppsConfigurationN, ppsConfigurationM]
    refine ⟨hN, ?_⟩
    have hb : expect (phaseOriginal r m hr)
        (fun ω => htVarianceEstimator (phaseOriginal r m hr)
          (fun k => if k.1.2 = 0 then (-1:ℝ) else 1) ω/((m:ℝ)*(2*r))^2) -
        variance (phaseOriginal r m hr) (htMean (phaseOriginal r m hr)
          (fun k => if k.1.2 = 0 then (-1:ℝ) else 1)) = -1/(2*r) :=
      (AronowAudit.P027.alternating_family_witness r m hr hm).2.2.2.1
    rw [hN]
    have hcast : (↑(m*(2*r)) : ℝ) = (m:ℝ)*(2*r) := by push_cast; ring
    rw [hcast]
    refine hb.trans ?_
    dsimp [r]
    split_ifs <;> norm_num
  · intro r hr
    dsimp only
    let A := fun j : ℕ => biasA (phaseOriginal r (j+1) hr)
      (fun k => if k.1.2 = 0 then (-1:ℝ) else 1)
    have hq : (0:ℝ) < 2*r := by positivity
    have hA (j : ℕ) : A j = -(2*r)*((j:ℝ)+1)^2 := by
      have ha : biasA (phaseOriginal r (j+1) hr)
          (fun k => if k.1.2 = 0 then (-1:ℝ) else 1) = -(2*r)*((j+1:ℕ):ℝ)^2 :=
        (AronowAudit.P027.alternating_family_witness r (j+1) hr (by omega)).2.1
      simpa only [A, Nat.cast_add, Nat.cast_one] using
        ha
    have hf (j : ℕ) : A j/(((j:ℝ)+1)*(2*r))^2 = -1/(2*r) := by
      simpa only [A, Nat.cast_add, Nat.cast_one] using (hn r (j+1) hr (by omega)).2
    constructor
    · intro h
      have hlim := le_of_tendsto h (Eventually.of_forall (fun j : ℕ => show A j ≤ -(2*r) by
        rw [hA]
        have hs : (1:ℝ) ≤ ((j:ℝ)+1)^2 := by
          nlinarith [show (0:ℝ) ≤ j by positivity, sq_nonneg (j:ℝ)]
        have hp := mul_nonneg hq.le (sub_nonneg.mpr hs)
        nlinarith))
      linarith
    · intro h
      have hlim := le_of_tendsto h (Eventually.of_forall (fun j : ℕ => (hf j).le))
      have hneg : (-1:ℝ)/(2*r) < 0 := div_neg_of_neg_of_pos (by norm_num) hq
      linarith

/-- The calibrated scalar formula is uniformly negative on physical populations. -/
theorem calibrated_uniform_bound (q N ρ : ℝ) (hq : 2 ≤ q) (hN : 2 ≤ N)
    (hρ : |ρ| ≤ 1) : calibratedMeanBias q ρ N ≤ -450*ρ^2/q := by
  have hq0 : 0 < q := by linarith
  have hN0 : 0 < N := by linarith
  have hr2 : 0 ≤ 1-ρ^2 := by
    have h := (sq_le_one_iff_abs_le_one ρ).mpr hρ
    linarith
  have hqm1 : 0 ≤ q-1 := by linarith
  have hres : 0 ≤ 900*(1-ρ^2)*(q-1)/(q*N) := by positivity
  have hsig : -900*ρ^2*(N-1)/(q*N) ≤ -450*ρ^2/q := by
    apply (div_le_div_iff₀ (mul_pos hq0 hN0) hq0).mpr
    have hp : 0 ≤ 450*ρ^2*q*(N-2) := by positivity
    nlinarith
  dsimp [calibratedMeanBias]
  linarith

/-- Derive beta from the empirical size standard deviation, then use the
existing model-bias theorem and the elementary uniform scalar bound. -/
theorem periodic_calibration : PeriodicCalibrationWhole := by
  intro Ξ _ μ _ r m hr hm ρ hρ ε hε
  dsimp only
  let N : ℝ := m*(2*r)
  have hN : 2 ≤ N := by
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
    dsimp [N]
    nlinarith
  have hN0 : 0 < N := by linarith
  have hNm1 : 0 < N-1 := by linarith
  have hsize : (∑ k : (Σ _ : Fin r × Fin 2, Fin m), (phaseSize k-6)^2)/(N-1) =
      16*N/(N-1) := (AronowAudit.P027.periodic_size_moments r m hr hm).2.2
  rw [hsize]
  let sx := Real.sqrt (16*N/(N-1))
  have hsv : 0 < 16*N/(N-1) := by positivity
  have hsx : 0 < sx := Real.sqrt_pos.mpr hsv
  have hsq : sx^2 = 16*N/(N-1) := Real.sq_sqrt hsv.le
  have hb : (ρ*(30/sx))^2 = 900*ρ^2*(N-1)/(16*N) := by
    rw [mul_pow, div_pow, hsq]
    field_simp
    ring
  refine ⟨hsx, hb, ?_, ?_⟩
  · exact AronowAudit.P027.periodic_calibrated_bias μ r m hr hm ρ (ρ*(30/sx)) hρ ε hε hb
  · intro hne
    have hq : (2:ℝ) ≤ 2*r := by exact_mod_cast (show 2 ≤ 2*r by omega)
    refine ⟨calibrated_uniform_bound _ _ _ hq hN hρ, ?_⟩
    have hq0 : (0:ℝ) < 2*r := by positivity
    exact div_neg_of_neg_of_pos (by nlinarith [sq_pos_of_ne_zero hne]) hq0

/-- Existing unreindexed limit and the exact numerical specializations. -/
theorem periodic_limit : PeriodicLimitWhole := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num⟩
  intro r hr ρ
  exact AronowAudit.P027.fixed_fraction_bias_limit r hr ρ

/-- Existing support-wise aggregation theorem in SAP coordinates. -/
theorem ae_preservation_core : AEAggregationPreservation := by
  intro G Ω _ _ n hn D hv hp hae y
  exact AronowAudit.P027.Wave1.aggregation_ae_partition_bridge n hn (toAudit D hv) hp hae y

/-- All existing exact-lift aggregation algebra. -/
theorem aggregation_exact_core : AggregationClaim := by
  intro G Ω _ _ D hv hp n hn y
  exact ⟨AronowAudit.P027.aggregation_preservation (toAudit D hv) hp n hn y,
    AronowAudit.P027.quadraticA_lift (toAudit D hv) hp n y,
    AronowAudit.P027.aggregation_bias_change (toAudit D hv) hp n hn y,
    AronowAudit.P027.aggregation_degree_bound (toAudit D hv) hp n hn y⟩

/-- Bias equals A+A-star under the claimed positive marginals. -/
theorem c2_bias_add {U Ω : Type} [Fintype U] [Fintype Ω]
    (D : Design U Ω) (hv : Valid D) (hp : Positive D) (y : U → ℝ) :
    wholeC2Bias D y = biasA D y+quadraticA D y := by
  have h : expect D (c2Estimator D y) =
      variance D (htTotal D y)+biasA D y+quadraticA D y :=
    AronowAudit.P027.c2_expectation (toAudit D hv) hp y
  dsimp [wholeC2Bias]
  rw [h]
  ring

/-- The ordered and unordered notations retain exactly the same factor 1/2. -/
theorem quadraticA_edge {G Ω : Type} [Fintype G] [Fintype Ω]
    (D : Design G Ω) (Y : G → ℝ) :
    quadraticA D Y = wholeEdgeSum D (fun g h => Y g^2+Y h^2) := by
  simp only [quadraticA, wholeEdgeSum, Finset.sum_div, ite_div, zero_div]

theorem squared_edge {G Ω : Type} [Fintype G] [Fintype Ω]
    (D : Design G Ω) (Y : G → ℝ) :
    squaredZeroPairs D Y = wholeEdgeSum D (fun g h => (Y g+Y h)^2) := by
  simp only [squaredZeroPairs, wholeEdgeSum, Finset.sum_div, ite_div, zero_div]

/-- Squared-sum form of the conservative C2 bias. -/
theorem c2_bias_squared {U Ω : Type} [Fintype U] [Fintype Ω]
    (D : Design U Ω) (hv : Valid D) (hp : Positive D) (y : U → ℝ) :
    wholeC2Bias D y = squaredZeroPairs D y :=
  AronowAudit.P027.c2_bias_identity (toAudit D hv) hp y

/-- The four-unit reduction is another small finite calculation. -/
theorem aggregation_reduction : AggregationReductionWhole := by
  let D := liftDesign cluster2 (fun _ => 2)
  let Y := groupTotal (fun _ : Fin 2 => 2) fourClusterOutcome
  have hv : Valid D := by norm_num [D, Valid, liftDesign, cluster2, Fin.sum_univ_succ]
  have hp : Positive D :=
    AronowAudit.P027.lift_positive AronowAudit.P027.cluster2
      AronowAudit.P027.aggregation_counterexample_positive.2.1 (fun _ => 2)
  refine ⟨hv, hp, ?_, ?_, ?_⟩
  · intro g
    fin_cases g <;> norm_num [Y, groupTotal, fourClusterOutcome, Fin.sum_univ_succ]
  · norm_num [D, wholeC2Bias, pi, joint, expect, indicator, htTotal, variance,
      c2Estimator, htVarianceEstimator, quadraticCorrection, inclusionCov,
      liftDesign, cluster2, fourClusterOutcome, Fintype.sum_sigma, Fin.sum_univ_succ]
  · norm_num [Y, wholeC2Bias, pi, joint, expect, indicator, htTotal, variance,
      c2Estimator, htVarianceEstimator, quadraticCorrection, inclusionCov,
      cluster2, groupTotal, fourClusterOutcome, Fin.sum_univ_succ]

end
end SAP.P027a.WH.W1
