import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W1.P.T9_L1

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

local instance signSampleProbability (N : ℕ) :
    IsProbabilityMeasure (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) := by
  change IsProbabilityMeasure
    (AronowAudit.P018.unitSampleLaw
      (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel) N)
  exact AronowAudit.P018.Wave1.printed_sign_probability N

local instance signSampleFinite (N : ℕ) :
    IsFiniteMeasure (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) := by
  letI : IsProbabilityMeasure
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N) :=
    AronowAudit.P018.Wave1.printed_sign_probability N
  change IsFiniteMeasure
    (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N)
  infer_instance

lemma sample_integrable {N : ℕ} (f : (Fin N → Bool) → ℝ) :
    Integrable f (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) := by
  exact @AronowAudit.P018.Wave1.printed_finite_integrable
    (Fin N → Bool) inferInstance inferInstance inferInstance
    (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N)
    (SAP.P018a.WH.W1.P.T9_L1.signSampleFinite N) f

lemma sign_abs (b : Bool) : |SAP.P018a.signValue b| = 1 := by
  cases b <;> norm_num [SAP.P018a.signValue]

lemma sign_response_bound {N : ℕ} (ω : Fin N → Bool) (d : SAP.P018a.Dyad N) :
    |AronowAudit.P018.response AronowAudit.P018.signKernel ω d| ≤ 2 := by
  change |AronowAudit.P018.signValue (ω (AronowAudit.P018.firstUnit d)) +
    AronowAudit.P018.signValue (ω (AronowAudit.P018.secondUnit d))| ≤ 2
  calc
    _ ≤ |AronowAudit.P018.signValue (ω (AronowAudit.P018.firstUnit d))| +
        |AronowAudit.P018.signValue (ω (AronowAudit.P018.secondUnit d))| := abs_add_le _ _
    _ = 2 := by
      rw [AronowAudit.P018.Wave1.appendixB_sign_abs,
        AronowAudit.P018.Wave1.appendixB_sign_abs]
      norm_num

lemma sap_response_bound {N : ℕ} (ω : Fin N → Bool) (d : SAP.P018a.Dyad N) :
    |SAP.P018a.response SAP.P018a.signKernel ω d| ≤ 2 := by
  change |SAP.P018a.signValue (ω (SAP.P018a.firstUnit d)) +
    SAP.P018a.signValue (ω (SAP.P018a.secondUnit d))| ≤ 2
  calc
    _ ≤ |SAP.P018a.signValue (ω (SAP.P018a.firstUnit d))| +
        |SAP.P018a.signValue (ω (SAP.P018a.secondUnit d))| := abs_add_le _ _
    _ = 2 := by rw [sign_abs, sign_abs]; norm_num

lemma coord_mean {N : ℕ} (i : Fin N) :
    (∫ ω, SAP.P018a.signValue (ω i) ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) = 0 := by
  change (∫ ω, AronowAudit.P018.signValue (ω i) ∂
    AronowAudit.P018.unitSampleLaw
      (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel) N) = 0
  exact AronowAudit.P018.Wave1.appendixB_coord_mean i

lemma weighted_population_score_mean_zero {N : ℕ} (w : SAP.P018a.Dyad N → ℝ) :
    meanVec (unitSampleLaw SAP.P018a.signKernel N)
      (fun ω => ∑ d, score (design SAP.P018a.signKernel ω d)
        (w d * SAP.P018a.response SAP.P018a.signKernel ω d)) = 0 := by
  classical
  ext a
  fin_cases a
  simp only [meanVec, Pi.zero_apply]
  simp only [Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul,
    design, Matrix.cons_val_fin_one, mul_one]
  change (∫ ω, ∑ d ∈ (Finset.univ : Finset (SAP.P018a.Dyad N)),
    w d * SAP.P018a.response SAP.P018a.signKernel ω d *
      SAP.P018a.signKernel.X (ω (SAP.P018a.firstUnit d))
        (ω (SAP.P018a.secondUnit d)) 0
    ∂ unitSampleLaw SAP.P018a.signKernel N) = 0
  rw [integral_finsetSum _ (fun d _ =>
    SAP.P018a.WH.W1.P.T9_L1.sample_integrable
      (fun ω => w d * SAP.P018a.response SAP.P018a.signKernel ω d *
        SAP.P018a.signKernel.X (ω (SAP.P018a.firstUnit d))
          (ω (SAP.P018a.secondUnit d)) 0))]
  apply Finset.sum_eq_zero
  intro d hd
  have hi := coord_mean (SAP.P018a.firstUnit d)
  have hj := coord_mean (SAP.P018a.secondUnit d)
  simp only [SAP.P018a.response, SAP.P018a.signKernel,
    Matrix.cons_val_fin_one, mul_one] at ⊢
  change (∫ ω, w d * (SAP.P018a.signValue
      (ω (SAP.P018a.firstUnit d)) + SAP.P018a.signValue
      (ω (SAP.P018a.secondUnit d)))
      ∂ unitSampleLaw SAP.P018a.signKernel N) = 0
  rw [integral_const_mul,
    integral_add
      (SAP.P018a.WH.W1.P.T9_L1.sample_integrable
        (fun ω => SAP.P018a.signValue (ω (SAP.P018a.firstUnit d))))
      (SAP.P018a.WH.W1.P.T9_L1.sample_integrable
        (fun ω => SAP.P018a.signValue (ω (SAP.P018a.secondUnit d)))), hi, hj]
  ring

lemma weighted_fit_abs_le_two {N : ℕ} (hN : 2 ≤ N) (ω : Fin N → Bool) :
    |weightedOLS SAP.P018a.signKernel SAP.P018a.concentratedWeight ω 0| ≤ 2 := by
  have hbridge : weightedOLS SAP.P018a.signKernel SAP.P018a.concentratedWeight ω =
      AronowAudit.P018.weightedOLS
        (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel)
        AronowAudit.P018.concentratedWeight ω := rfl
  rw [hbridge]
  change |AronowAudit.P018.weightedOLS AronowAudit.P018.signKernel
    AronowAudit.P018.concentratedWeight ω 0| ≤ 2
  rw [AronowAudit.P018.Wave1.concentrated_weights_ols_scalar]
  have hW : 0 < AronowAudit.P018.Wave1.concentrated_weights_W N :=
    lt_of_lt_of_le (by norm_num) (AronowAudit.P018.Wave1.concentrated_weights_W_lower hN)
  have hnum : |∑ d : AronowAudit.P018.Dyad N,
      AronowAudit.P018.concentratedWeight d *
        AronowAudit.P018.response AronowAudit.P018.signKernel ω d| ≤
      2 * AronowAudit.P018.Wave1.concentrated_weights_W N := by
    calc
      _ ≤ ∑ d : AronowAudit.P018.Dyad N,
          |AronowAudit.P018.concentratedWeight d *
            AronowAudit.P018.response AronowAudit.P018.signKernel ω d| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d : AronowAudit.P018.Dyad N,
          AronowAudit.P018.concentratedWeight d *
            |AronowAudit.P018.response AronowAudit.P018.signKernel ω d| := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [abs_mul, abs_of_pos (AronowAudit.P018.Wave1.concentrated_weights_bounds d).1]
      _ ≤ ∑ d : AronowAudit.P018.Dyad N,
          2 * AronowAudit.P018.concentratedWeight d := by
        apply Finset.sum_le_sum
        intro d hd
        calc
          _ ≤ AronowAudit.P018.concentratedWeight d * 2 :=
            mul_le_mul_of_nonneg_left (sign_response_bound ω d)
              (le_of_lt (AronowAudit.P018.Wave1.concentrated_weights_bounds d).1)
          _ = 2 * AronowAudit.P018.concentratedWeight d := by ring
      _ = 2 * AronowAudit.P018.Wave1.concentrated_weights_W N := by
        simp [AronowAudit.P018.Wave1.concentrated_weights_W, Finset.mul_sum]
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hW))]
  have hWne : AronowAudit.P018.Wave1.concentrated_weights_W N ≠ 0 := ne_of_gt hW
  have : (AronowAudit.P018.Wave1.concentrated_weights_W N)⁻¹ *
      |∑ d : AronowAudit.P018.Dyad N,
        AronowAudit.P018.concentratedWeight d *
          AronowAudit.P018.response AronowAudit.P018.signKernel ω d| ≤ 2 := by
    calc
      _ ≤ (AronowAudit.P018.Wave1.concentrated_weights_W N)⁻¹ *
          (2 * AronowAudit.P018.Wave1.concentrated_weights_W N) :=
        mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr (le_of_lt hW))
      _ = 2 := by field_simp
  simpa [abs_of_nonneg (inv_nonneg.mpr (le_of_lt hW)), abs_mul] using this

lemma two_record_gram {N : ℕ} (ω : Fin N → Bool) :
    recordWeightedGram SAP.P018a.W1TwoSignRecords
      (fun d _ => SAP.P018a.concentratedWeight d) ω =
    weightedGram SAP.P018a.signKernel
      (fun d => 2 * SAP.P018a.concentratedWeight d) ω := by
  classical
  ext a b
  dsimp [SAP.P018a.W1TwoSignRecords, SAP.P018a.recordWeightedGram,
    SAP.P018a.weightedGram, SAP.P018a.repeatedX, SAP.P018a.design,
    SAP.P018a.signKernel, SAP.P018a.outer]
  fin_cases a
  fin_cases b
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  change (∑ t : Fin 2,
      (SAP.P018a.concentratedWeight d • outer (![1] : SAP.P018a.Vec 1)
        (![1] : SAP.P018a.Vec 1)) 0 0) =
    ((2 * SAP.P018a.concentratedWeight d) •
      outer (![1] : SAP.P018a.Vec 1) (![1] : SAP.P018a.Vec 1)) 0 0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_one, Matrix.smul_apply,
    smul_eq_mul, outer]
  ring

lemma two_record_xy {N : ℕ} (ω : Fin N → Bool) :
    recordWeightedXY SAP.P018a.W1TwoSignRecords
      (fun d _ => SAP.P018a.concentratedWeight d) ω =
    ∑ d : SAP.P018a.Dyad N,
      score (design SAP.P018a.signKernel ω d)
        ((2 * SAP.P018a.concentratedWeight d) *
          SAP.P018a.response SAP.P018a.signKernel ω d) := by
  classical
  ext a
  fin_cases a
  dsimp [SAP.P018a.W1TwoSignRecords, SAP.P018a.recordWeightedXY,
    SAP.P018a.repeatedX, SAP.P018a.repeatedY, SAP.P018a.design,
    SAP.P018a.response, SAP.P018a.signKernel, SAP.P018a.score]
  simp only [Finset.sum_apply, Matrix.cons_val_fin_one, smul_eq_mul, mul_one]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_fin_one]
  ring

lemma two_record_ols {N : ℕ} (ω : Fin N → Bool) :
    recordWeightedOLS SAP.P018a.W1TwoSignRecords
        (fun d _ => SAP.P018a.concentratedWeight d) ω =
      weightedOLS SAP.P018a.signKernel
        (fun d => 2 * SAP.P018a.concentratedWeight d) ω := by
  rw [recordWeightedOLS, two_record_gram, two_record_xy]
  rfl

lemma two_record_reductions {N : ℕ} (ω : Fin N → Bool) :
    recordWeightedOLS SAP.P018a.W1TwoSignRecords
        (fun d _ => SAP.P018a.concentratedWeight d) ω =
      weightedOLS SAP.P018a.signKernel
        (fun d => 2 * SAP.P018a.concentratedWeight d) ω ∧
    recordWeightedVariance SAP.P018a.W1TwoSignRecords
        (fun d _ => SAP.P018a.concentratedWeight d) ω =
      weightedVariance SAP.P018a.signKernel
        (fun d => 2 * SAP.P018a.concentratedWeight d) ω := by
  constructor
  · exact two_record_ols ω
  · have hscore : recordWeightedBlockScore SAP.P018a.W1TwoSignRecords
        (fun d _ => SAP.P018a.concentratedWeight d)
        (recordWeightedOLS SAP.P018a.W1TwoSignRecords
          (fun d _ => SAP.P018a.concentratedWeight d) ω) ω =
        fun d => score (design SAP.P018a.signKernel ω d)
          ((2 * SAP.P018a.concentratedWeight d) *
            (SAP.P018a.response SAP.P018a.signKernel ω d -
              dot (design SAP.P018a.signKernel ω d)
                (weightedOLS SAP.P018a.signKernel
                  (fun d => 2 * SAP.P018a.concentratedWeight d) ω))) := by
      funext d
      ext a
      fin_cases a
      rw [two_record_ols]
      change (∑ t : Fin 2, score (![1] : SAP.P018a.Vec 1)
          (SAP.P018a.concentratedWeight d *
            ((SAP.P018a.signValue (ω (SAP.P018a.firstUnit d)) +
                SAP.P018a.signValue (ω (SAP.P018a.secondUnit d))) -
              dot (![1] : SAP.P018a.Vec 1)
                (weightedOLS SAP.P018a.signKernel
                  (fun d => 2 * SAP.P018a.concentratedWeight d) ω)))) 0 =
        (score (![1] : SAP.P018a.Vec 1)
          ((2 * SAP.P018a.concentratedWeight d) *
            ((SAP.P018a.signValue (ω (SAP.P018a.firstUnit d)) +
                SAP.P018a.signValue (ω (SAP.P018a.secondUnit d))) -
              dot (![1] : SAP.P018a.Vec 1)
                (weightedOLS SAP.P018a.signKernel
                  (fun d => 2 * SAP.P018a.concentratedWeight d) ω)))) 0
      simp only [Finset.sum_apply, Fin.sum_univ_succ, Fin.sum_univ_one]
      simp [score, dot]
      ring
    rw [recordWeightedVariance, two_record_gram, hscore]
    rfl

end SAP.P018a.WH.W1.P.T9_L1

theorem SAP.P018a.WH.W1.T9_L1_proof : SAP.P018a.WH.W1.T9_L1 := by
  have hStanding : SAP.P018a.Standing SAP.P018a.signKernel := by
    apply (SAP.P018a.Bridge.kernel_assumptions_agree SAP.P018a.signKernel).2
    change AronowAudit.P018.Standing AronowAudit.P018.signKernel
    exact AronowAudit.P018.Wave1.appendixB_standing
  have hRank : SAP.P018a.SampleRank SAP.P018a.signKernel := by
    change AronowAudit.P018.SampleRank
      (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel)
    exact AronowAudit.P018.Wave1.appendixB_sampleRank
  have hBeta : SAP.P018a.populationBeta SAP.P018a.signKernel = 0 := by
    change AronowAudit.P018.populationBeta
      (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel) = 0
    exact AronowAudit.P018.Wave1.appendixB_populationBeta
  refine ⟨hStanding, hRank, hBeta, ?_, ?_, ?_⟩
  · intro N hN
    refine ⟨?_, ?_⟩
    · classical
      unfold weightedPopulationBeta
      rw [SAP.P018a.WH.W1.P.T9_L1.weighted_population_score_mean_zero]
      simp
    · intro ω
      refine ⟨?_, ?_⟩
      · change (AronowAudit.P018.Dreal N)⁻¹ •
          AronowAudit.P018.sampleGram
            (AronowAudit.P018.design AronowAudit.P018.signKernel ω) = 1
        rw [AronowAudit.P018.Wave1.printed_gram]
        have hD : AronowAudit.P018.Dreal N ≠ 0 :=
          ne_of_gt (AronowAudit.P018.Wave1.printed_Dpos hN)
        simp [smul_smul, inv_mul_cancel₀ hD]
      · intro d
        constructor
        · have he : SAP.P018a.epsilon SAP.P018a.signKernel ω d =
              SAP.P018a.response SAP.P018a.signKernel ω d := by
            simp [SAP.P018a.epsilon, SAP.P018a.populationResidual,
              SAP.P018a.dot, SAP.P018a.response, hBeta]
          rw [he]
          exact SAP.P018a.WH.W1.P.T9_L1.sap_response_bound ω d
        · have hfit := SAP.P018a.WH.W1.P.T9_L1.weighted_fit_abs_le_two hN ω
          have hresp := SAP.P018a.WH.W1.P.T9_L1.sap_response_bound ω d
          have hres :
              |SAP.P018a.response SAP.P018a.signKernel ω d -
                weightedOLS SAP.P018a.signKernel
                  SAP.P018a.concentratedWeight ω 0| ≤ 4 := by
            calc
              _ ≤ |SAP.P018a.response SAP.P018a.signKernel ω d| +
                  |weightedOLS SAP.P018a.signKernel
                    SAP.P018a.concentratedWeight ω 0| := abs_sub _ _
              _ ≤ 4 := by linarith
          simpa [SAP.P018a.design, SAP.P018a.signKernel, SAP.P018a.dot] using hres
  · intro N M d f hfirst hsecond
    simp [SAP.P018a.concentratedWeight, hfirst, hsecond]
  · intro N hN ω
    have hred := SAP.P018a.WH.W1.P.T9_L1.two_record_reductions ω
    have hscale : weightedOLS SAP.P018a.signKernel
          (fun d => 2 * SAP.P018a.concentratedWeight d) ω =
        weightedOLS SAP.P018a.signKernel SAP.P018a.concentratedWeight ω ∧
      weightedVariance SAP.P018a.signKernel
          (fun d => 2 * SAP.P018a.concentratedWeight d) ω =
        weightedVariance SAP.P018a.signKernel SAP.P018a.concentratedWeight ω := by
      change AronowAudit.P018.weightedOLS
          (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel)
          (fun d => 2 * AronowAudit.P018.concentratedWeight d) ω =
          AronowAudit.P018.weightedOLS
            (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel)
            AronowAudit.P018.concentratedWeight ω ∧
        AronowAudit.P018.weightedVariance
          (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel)
          (fun d => 2 * AronowAudit.P018.concentratedWeight d) ω =
          AronowAudit.P018.weightedVariance
            (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel)
            AronowAudit.P018.concentratedWeight ω
      exact AronowAudit.P018.Wave1.concentrated_repetitions_scale_total
        (w := AronowAudit.P018.concentratedWeight) ω 2 (by norm_num)
    constructor
    · rw [hred.1]
      exact hscale.1
    · rw [hred.2]
      exact hscale.2
