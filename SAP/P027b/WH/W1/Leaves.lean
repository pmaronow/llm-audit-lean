import SAP.P027b.Defs.WholeW1
import SAP.P027b.Bridge
import AronowAudit.P027.Wave1.GaussianMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b.WH.W1

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Integrability of the actual finite-design quadratic quantities from second
moments. Use strata_finite_formulas for the sample estimators and design variance.
shifted_noise_second_moment makes each squared outcome integrable;
noise_linear_moments does the same for squared within-stratum means and the
sampled difference. Commute finite sums with integrals using outcomeE_expect
(its first conclusion is integrability), then use Integrable.sub for the biases.
No expansion into M squared samples is needed. -/
def T14_L1 : Prop :=
  ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
      (M : ℕ) (hM : 2 ≤ M) (α : ℝ) (ε : (Fin M × Fin 2) → Ξ → ℝ),
    NoiseMoments μ ε 1 → WholeStrataIntegrable μ hM α ε

/-- Convert the fair-sign and independent standard Gaussian laws to the package's
pair moments and L2 bounds. Transfer the Gaussian first and second moments with
GaussianMoments.n1_proof; transfer the sign law by integral_map and
integral_bernoulliMeasure, obtaining its mean zero and square one. The sign is
bounded, hence in L2 by MemLp.of_bound. Transfer Gaussian L2 by memLp_map_measure_iff.
Use iIndepFun.indepFun and GaussianMoments.n2_proof for each cross moment. -/
def T16_L1 : Prop :=
  ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
      (X : Fin 3 → Ξ → ℝ), WholeGaussianPair μ X →
    PairMoments μ (X 0) (X 1) (X 2) ∧ ∀ i, MemLp (X i) 2 μ

/-- Conditioning on either common stratum preserves the independent Gaussian
error-pair law. Extract independence of (X 1, X 2) from X 0 using
iIndepFun.indepFun_prodMk. The sign marginal gives event mass 1/2.
Use cond_apply and IndepFun.measure_inter_preimage_eq_mul to show that the
conditional error-pair law is the product of two standard Gaussian laws.
Under this conditional measure X 0 equals s almost everywhere; thus the two
outcomes are s/2 plus the respective errors. Transfer L2 and variance from the
Gaussian marginals and use independence for covariance zero. This is a finite
conditioning calculation; no regular conditional distribution is needed. -/
def T16_L2 : Prop :=
  ∀ (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
      (X : Fin 3 → Ξ → ℝ), WholeGaussianPair μ X →
    ∀ s : ℝ, s = 1 ∨ s = -1 →
      μ {ξ | X 0 ξ = s} = 1/2 ∧
      let ν := ProbabilityTheory.cond μ {ξ | X 0 ξ = s}
      IsProbabilityMeasure ν ∧
      MemLp (wholePairY X) 2 ν ∧ MemLp (wholePairY' X) 2 ν ∧
      ProbabilityTheory.variance (wholePairY X) ν = 1 ∧
      ProbabilityTheory.variance (wholePairY' X) ν = 1 ∧
      ProbabilityTheory.covariance (wholePairY X) (wholePairY' X) ν = 0

/-- Reuse the fixed-population witness and the actual model-moment theorem;
only existence of the added outcome expectations needs a new leaf. -/
theorem T14_assembly (h1 : T14_L1) : T14WholeStatement := by
  refine ⟨Bridge.T14_proof, by norm_num, ?_, ?_, ?_⟩
  · intro ω
    norm_num [strataDesign]
  · intro Ξ _ μ _ ε hε
    have hnoise : NoiseMoments μ ε 1 :=
      AronowAudit.P027.Wave1.gaussian_noise_moments μ ε 1 (by norm_num) hε
    refine ⟨h1 Ξ μ 5 (by norm_num) 0 ε hnoise,
      h1 Ξ μ 5 (by norm_num) 2 ε hnoise, ?_⟩
    have hm0 := AronowAudit.P027.strata_model_moments μ 5 (by norm_num) 0 ε hnoise
    have hm2 := AronowAudit.P027.strata_model_moments μ 5 (by norm_num) 2 ε hnoise
    let BC := fun α => outcomeE μ (fun ξ =>
      wholeStrataC (by norm_num : 2 ≤ 5) α ε ξ - wholeStrataV (by norm_num) α ε ξ)
    let BS := fun α => outcomeE μ (fun ξ =>
      wholeStrataCS (by norm_num : 2 ≤ 5) α ε ξ - wholeStrataV (by norm_num) α ε ξ)
    have bc0 : BC 0 = strataC2BiasFormula 5 0 := hm0.2.2.2.2.1
    have bs0 : BS 0 = strataCSBiasFormula 5 0 := hm0.2.2.2.2.2
    have bc2 : BC 2 = strataC2BiasFormula 5 2 := hm2.2.2.2.2.1
    have bs2 : BS 2 = strataCSBiasFormula 5 2 := hm2.2.2.2.2.2
    norm_num [strataC2BiasFormula, strataCSBiasFormula] at bc0 bs0 bc2 bs2
    change BC 0 = 2/5 ∧ BS 0 = 1/10 ∧ BS 0 < BC 0 ∧
      BC 2 = 18/5 ∧ BS 2 = 41/10 ∧ BC 2 < BS 2
    exact ⟨bc0, bs0, by linarith, bc2, bs2, by linarith⟩
  · intro Ξ _ μ _ ε hε
    have hnoise : NoiseMoments μ ε 1 :=
      AronowAudit.P027.Wave1.gaussian_noise_moments μ ε 1 (by norm_num) hε
    refine ⟨h1 Ξ μ 500 (by norm_num) 0 ε hnoise, ?_⟩
    have hm := AronowAudit.P027.strata_model_moments μ 500 (by norm_num) 0 ε hnoise
    have hv : outcomeE μ (wholeStrataV (by norm_num : 2 ≤ 500) 0 ε) =
        ((500:ℝ)-1)/(2*500) := hm.1
    have hc : outcomeE μ (wholeStrataC (by norm_num : 2 ≤ 500) 0 ε) =
        ((500:ℝ)-1)/500*(1+0^2) := hm.2.2.1
    have hs : outcomeE μ (wholeStrataCS (by norm_num : 2 ≤ 500) 0 ε) =
        (0:ℝ)^2+1/2 := hm.2.2.2.1
    dsimp only
    rw [hv, hc, hs]
    norm_num

/-- The Gaussian adapter supplies the general pair theorem's hypotheses.
Centered variances, covariance, the discrepancy, and both fixed-mean variance
conventions are direct calculations; the second leaf supplies conditioning. -/
theorem T16_assembly (h1 : T16_L1) (h2 : T16_L2) : T16WholeStatement := by
  constructor
  · norm_num [stratumMeans, stratumMeansVariance, wholeMeansPopulationVariance,
      heterogeneity, Fin.sum_univ_two]
  intro Ξ _ μ _ X hX
  obtain ⟨hm, hLp⟩ := h1 Ξ μ X hX
  have hY : MemLp (wholePairY X) 2 μ := ((hLp 0).const_mul (1/2)).add (hLp 1)
  have hY' : MemLp (wholePairY' X) 2 μ := ((hLp 0).const_mul (1/2)).add (hLp 2)
  have hp := Bridge.T17_proof.1 Ξ μ (1/2) (X 0) (X 1) (X 2) hm
  change outcomeE μ (wholePairY X) = 0 ∧ outcomeE μ (wholePairY' X) = 0 ∧
    outcomeE μ (fun ξ => wholePairY X ξ^2) = (1/2:ℝ)^2+1 ∧
    outcomeE μ (fun ξ => wholePairY' X ξ^2) = (1/2:ℝ)^2+1 ∧
    outcomeE μ (fun ξ => wholePairY X ξ*wholePairY' X ξ) = (1/2:ℝ)^2 ∧
    _ at hp
  have vY : ProbabilityTheory.variance (wholePairY X) μ = 5/4 := by
    rw [ProbabilityTheory.variance_eq_integral hY.aemeasurable]
    change (∫ ξ, (wholePairY X ξ - outcomeE μ (wholePairY X))^2 ∂μ) = 5/4
    simp only [hp.1, sub_zero]
    exact hp.2.2.1.trans (by norm_num)
  have vY' : ProbabilityTheory.variance (wholePairY' X) μ = 5/4 := by
    rw [ProbabilityTheory.variance_eq_integral hY'.aemeasurable]
    change (∫ ξ, (wholePairY' X ξ - outcomeE μ (wholePairY' X))^2 ∂μ) = 5/4
    simp only [hp.2.1, sub_zero]
    exact hp.2.2.2.1.trans (by norm_num)
  have cY : ProbabilityTheory.covariance (wholePairY X) (wholePairY' X) μ = 1/4 := by
    unfold ProbabilityTheory.covariance
    change (∫ ξ, (wholePairY X ξ - outcomeE μ (wholePairY X))*
      (wholePairY' X ξ - outcomeE μ (wholePairY' X)) ∂μ) = 1/4
    simp only [hp.1, hp.2.1, sub_zero]
    exact hp.2.2.2.2.1.trans (by norm_num)
  have corr : wholePearson μ (wholePairY X) (wholePairY' X) = 1/5 := by
    unfold wholePearson
    rw [vY, vY', cY]
    norm_num
  have printed : heterogeneity (1/2) = 1/3 := by norm_num [heterogeneity]
  have effect : ProbabilityTheory.variance (fun ξ => (1/2:ℝ)*X 0 ξ) μ =
      wholeMeansPopulationVariance (1/2) := by
    have hSmean : outcomeE μ (X 0) = 0 := hm.2.1
    have hmean : outcomeE μ (fun ξ => (1/2:ℝ)*X 0 ξ) = 0 := by
      simp only [outcomeE, integral_const_mul] at hSmean ⊢
      rw [hSmean, mul_zero]
    have hsquare : (fun ξ => ((1/2:ℝ)*X 0 ξ)^2) =ᵐ[μ] (fun _ => (1/4:ℝ)) := by
      filter_upwards [hm.1] with ξ hξ
      rcases hξ with hξ | hξ <;> norm_num [hξ]
    rw [ProbabilityTheory.variance_eq_integral ((hLp 0).const_mul (1/2)).aemeasurable]
    change (∫ ξ, ((1/2:ℝ)*X 0 ξ - outcomeE μ (fun ξ => (1/2:ℝ)*X 0 ξ))^2 ∂μ) = _
    simp only [hmean, sub_zero]
    rw [integral_congr_ae hsquare]
    norm_num [wholeMeansPopulationVariance, stratumMeans, Fin.sum_univ_two]
  refine ⟨hm, hLp, hY, hY', hp.1, hp.2.1, vY, vY', cY, corr, printed,
    ?_, ?_, effect, ?_⟩
  · rw [printed, corr]
    norm_num
  · rw [corr, printed]
    norm_num
  · intro s hs
    obtain ⟨hevent, hν, hy, hy', vy, vy', cy⟩ := h2 Ξ μ X hX s hs
    refine ⟨hevent, hν, hy, hy', vy, vy', cy, ?_⟩
    simp only [wholePearson, cy, zero_div]

end
end SAP.P027b.WH.W1
