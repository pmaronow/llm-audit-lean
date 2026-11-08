import SAP.P001d.WH.W2.Leaves
import AronowAudit.P001.Wave1.Lib.TailA.MedianTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction
open AronowAudit.P001

noncomputable section

namespace SAP.P001d.WH.W2.P.T61_L5

local instance instDecidableT61L5 (p : Prop) : Decidable p := Classical.propDecidable p

/-- The finite conditional law of the centered sign fraction is the centered
binomial-count law at the empirical threshold probability. -/
theorem wholeSign_centeredBootstrap_cdf {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (z : ℝ) :
    (AronowAudit.P001.TailA.CenteredBootstrapLaw
      (fun y => SAP.P001d.wholeSignStatistic y) x).real (Set.Iic z) =
      AronowAudit.P001.TailA.binomialCountCDF n
        (AronowAudit.P001.TailA.empiricalThresholdProbability x 0) z := by
  classical
  let p := AronowAudit.P001.TailA.empiricalThresholdProbability x 0
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hs : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hscale (a : Fin n → Fin n) :
      Real.sqrt n * (SAP.P001d.wholeSignStatistic
          (AronowAudit.P001.resample x a) -
        SAP.P001d.wholeSignStatistic x) =
        (((Finset.univ.filter (fun i => x (a i) ≤ 0)).card : ℝ) -
          (n : ℝ) * (p : ℝ)) / Real.sqrt n := by
    dsimp [p, SAP.P001d.wholeSignStatistic, SAP.P001d.wholeEmpiricalCDF,
      AronowAudit.P001.resample]
    rw [AronowAudit.P001.TailA.empirical_threshold_probability_eq]
    have hsq : (Real.sqrt (n : ℝ))^2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    field_simp [hnR, hs]
    rw [hsq]
    ring
  change (((AronowAudit.P001.TailA.UniformResampling n).map
      (fun a => Real.sqrt n *
        (SAP.P001d.wholeSignStatistic
          (AronowAudit.P001.resample x a) -
          SAP.P001d.wholeSignStatistic x))) (Set.Iic z)).toReal = _
  rw [Measure.map_apply Measurable.of_discrete measurableSet_Iic]
  change prob (AronowAudit.P001.TailA.UniformResampling n)
      {a | Real.sqrt n *
        (SAP.P001d.wholeSignStatistic
            (AronowAudit.P001.resample x a) -
          SAP.P001d.wholeSignStatistic x) ≤ z} = _
  unfold AronowAudit.P001.TailA.binomialCountCDF
  rw [← AronowAudit.P001.TailA.bootstrap_threshold_count_law x 0]
  simp only [SAP.P001d.prob, AronowAudit.P001.prob]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  congr 2
  ext k
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [hscale k]

/-- The empirical success probabilities converge in probability to one half, so
random-binomial CDF convergence gives every conditional sign CDF. -/
theorem wholeSign_conditional_cdf_cp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiid : AronowAudit.P001.IID μ X) (hhalf : cdf μ (X 0) 0 = 1/2)
    (z : ℝ) :
    CP μ (fun k ω =>
      (AronowAudit.P001.TailA.CenteredBootstrapLaw
        (fun y => SAP.P001d.wholeSignStatistic y)
        (firstSample X (k+1) ω)).real (Set.Iic z))
      (prob (gaussianReal 0 (1/4)) (Set.Iic z)) := by
  let p := fun k : ℕ => fun ω : Ω =>
    AronowAudit.P001.TailA.empiricalThresholdProbability
      (firstSample X (k+1) ω) 0
  have hpmeas : ∀ k, Measurable (p k) := by
    intro k
    exact AronowAudit.P001.TailA.medianWeak_parameter_measurable X hiid.1
      (k+1) (fun _ => 0) measurable_const
  have hcons := AronowAudit.P001.empirical_cdf_consistency μ X hiid 0
  have hcons' := SAP.P001d.Bridge.cp_succ μ _ (cdf μ (X 0) 0) hcons
  rw [hhalf] at hcons'
  have hp : CP μ (fun k ω => (p k ω : ℝ)) (1/2) := by
    have hsample : ∀ k ω,
        (p k ω : ℝ) = AronowAudit.P001.sampleMean
          (fun i ω => if X i ω ≤ 0 then (1 : ℝ) else 0) (k+1) ω := by
      intro k ω
      dsimp [p]
      rw [AronowAudit.P001.TailA.empirical_threshold_probability_eq]
      exact AronowAudit.P001.Wave1.regular_sign_count X (k+1) ω
    convert hcons' using 1
    funext k ω
    exact hsample k ω
  have hbin := AronowAudit.P001.TailA.random_binomial_moving_cdf μ
    (fun k => k+1) (tendsto_add_atTop_nat 1) p (1/2) (by norm_num)
    hpmeas hp (fun _ _ => z) z (fun _ => measurable_const) (by
      intro ε hε
      simpa [dist_self, not_le_of_gt hε, AronowAudit.P001.prob,
        SAP.P001d.prob] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)))
  have hvar :
      (⟨(1/2 : ℝ) * (1-1/2),
        mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
          (sub_nonneg.mpr (by norm_num : (1/2:ℝ) ≤ 1))⟩ : ℝ≥0) = 1/4 := by
    apply Subtype.ext
    change (1/2 : ℝ) * (1-1/2) = (1:ℝ)/4
    norm_num
  have hbin' : CP μ (fun k ω =>
      AronowAudit.P001.TailA.binomialCountCDF (k+1) (p k ω) z)
      (prob (gaussianReal 0 (1/4)) (Set.Iic z)) := by
    apply (SAP.P001d.Bridge.cp_iff μ _ _).mpr
    change AronowAudit.P001.CP μ (fun k ω =>
      AronowAudit.P001.TailA.binomialCountCDF (k+1) (p k ω) z)
      (AronowAudit.P001.prob (gaussianReal 0 (1/4)) (Set.Iic z))
    rw [hvar] at hbin
    exact hbin.1
  intro ε hε
  have h := hbin' ε hε
  convert h using 1
  funext k
  apply congrArg (fun s : Set Ω => prob μ s)
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [← wholeSign_centeredBootstrap_cdf (Nat.succ_pos k)
    (firstSample X (k+1) ω) z]

end SAP.P001d.WH.W2.P.T61_L5

theorem SAP.P001d.WH.W2.T61_L5_proof : SAP.P001d.WH.W2.T61_L5 := by
  intro Ω instΩ μ hμ X hiid hhalf
  intro f hf hbound
  rcases hbound with ⟨C, hC⟩
  let Q : ℕ → Ω → ProbabilityMeasure ℝ := fun k ω =>
    ⟨AronowAudit.P001.TailA.CenteredBootstrapLaw
      (fun y => SAP.P001d.wholeSignStatistic y)
      (firstSample X (k+1) ω), inferInstance⟩
  let G : ProbabilityMeasure ℝ := ⟨gaussianReal 0 (1/4), inferInstance⟩
  have hCDF : ∀ q : ℚ,
      CP μ (fun k ω => (Q k ω : Measure ℝ).real (Set.Iic (q : ℝ)))
        ((G : Measure ℝ).real (Set.Iic (q : ℝ))) := by
    intro q
    change CP μ (fun k ω =>
      (AronowAudit.P001.TailA.CenteredBootstrapLaw
        (fun y => SAP.P001d.wholeSignStatistic y)
        (firstSample X (k+1) ω)).real (Set.Iic (q : ℝ)))
      ((gaussianReal 0 (1/4)).real (Set.Iic (q : ℝ)))
    exact SAP.P001d.WH.W2.P.T61_L5.wholeSign_conditional_cdf_cp
      μ X hiid hhalf (q : ℝ)
  let g : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2*C)
    (fun x y => by
      change |f x - f y| ≤ 2*C
      have hxy := abs_sub_le (f x) 0 (f y)
      simp only [sub_zero, zero_sub, abs_neg] at hxy
      linarith [hC x, hC y])
  have htest := AronowAudit.P001.TailA.medianTransport_test_cp μ Q G hCDF g
  change CP μ (fun k ω =>
      mean (AronowAudit.P001.TailA.CenteredBootstrapLaw
        (fun y => SAP.P001d.wholeSignStatistic y)
        (firstSample X (k+1) ω)) f)
    (mean (gaussianReal 0 (1/4)) f) at htest
  have hsum : CP μ (fun k ω =>
      AronowAudit.P001.bootstrapTestMean
        (fun y => SAP.P001d.wholeSignStatistic y)
        (firstSample X (k+1) ω) f) (mean (gaussianReal 0 (1/4)) f) := by
    simpa only [AronowAudit.P001.TailA.centered_bootstrap_test _ _ hf.measurable]
      using htest
  simpa only [SAP.P001d.bootstrapTestMean, AronowAudit.P001.bootstrapTestMean,
    AronowAudit.P001.mean] using hsum
