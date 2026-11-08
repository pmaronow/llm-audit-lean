import SAP.P027b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem SAP.P027b.WH.W1.T16_L1_proof : SAP.P027b.WH.W1.T16_L1 := by
  intro Ξ mΞ μ hμ X hX
  rcases hX with ⟨hmeas, hS_law, hX1_law, hX2_law, hInd⟩
  let p : unitInterval := ⟨1 / 2, by norm_num⟩
  have hBern_support : ∀ᵐ y ∂SAP.P027b.wholeFairSignLaw,
      y = 1 ∨ y = -1 := by
    rw [ae_iff]
    change SAP.P027b.wholeFairSignLaw {y : ℝ | ¬ (y = 1 ∨ y = -1)} = 0
    rw [SAP.P027b.wholeFairSignLaw,
      bernoulliMeasure_apply p (by measurability)]
    norm_num
  have hsupport : ∀ᵐ ξ ∂μ, X 0 ξ = 1 ∨ X 0 ξ = -1 := by
    have hmap : ∀ᵐ y ∂μ.map (X 0), y = 1 ∨ y = -1 := by
      rw [hS_law]
      exact hBern_support
    exact (ae_map_iff (hmeas 0).aemeasurable (by measurability)).1 hmap
  have hS_lp : MemLp (X 0) 2 μ := by
    refine MemLp.of_bound (hmeas 0).aestronglyMeasurable 1 ?_
    filter_upwards [hsupport] with ξ hξ
    rcases hξ with hξ | hξ <;> simp [hξ]
  have hS_int : Integrable (X 0) μ := hS_lp.integrable (by norm_num)
  have hS_mean_int : ∫ ξ, X 0 ξ ∂μ = 0 := by
    have hIdInt : Integrable (id : ℝ → ℝ) (μ.map (X 0)) := by
      rw [hS_law, SAP.P027b.wholeFairSignLaw]
      exact integrable_bernoulliMeasure 1 (-1) p id
    calc
      (∫ ξ, X 0 ξ ∂μ) = ∫ y : ℝ, y ∂μ.map (X 0) :=
        (integral_map (hmeas 0).aemeasurable aestronglyMeasurable_id).symm
      _ = ∫ y : ℝ, y ∂SAP.P027b.wholeFairSignLaw := by rw [hS_law]
      _ = (1 / 2 : ℝ) • (1 : ℝ) + (1 - (1 / 2 : ℝ)) • (-1 : ℝ) := by
        rw [SAP.P027b.wholeFairSignLaw, integral_bernoulliMeasure]
      _ = 0 := by norm_num
  have hS_mean : outcomeE μ (X 0) = 0 := by simpa [outcomeE] using hS_mean_int
  have hG1 := AronowAudit.P027.Wave1.GaussianMoments.n1_proof
    μ (X 1) (1 : ℝ≥0) (hmeas 1).aemeasurable hX1_law
  have hG2 := AronowAudit.P027.Wave1.GaussianMoments.n1_proof
    μ (X 2) (1 : ℝ≥0) (hmeas 2).aemeasurable hX2_law
  rcases hG1 with ⟨⟨hX1_int, hX1_mean_int⟩, ⟨hX1_sq_int_mul, hX1_sq_mean_mul⟩⟩
  rcases hG2 with ⟨⟨hX2_int, hX2_mean_int⟩, ⟨hX2_sq_int_mul, hX2_sq_mean_mul⟩⟩
  have hX1_mean : outcomeE μ (X 1) = 0 := by simpa [outcomeE] using hX1_mean_int
  have hX2_mean : outcomeE μ (X 2) = 0 := by simpa [outcomeE] using hX2_mean_int
  have hX1_sq_int : Integrable (fun ξ => (X 1 ξ) ^ 2) μ := by
    simpa only [pow_two] using hX1_sq_int_mul
  have hX2_sq_int : Integrable (fun ξ => (X 2 ξ) ^ 2) μ := by
    simpa only [pow_two] using hX2_sq_int_mul
  have hX1_sq_mean : outcomeE μ (fun ξ => (X 1 ξ) ^ 2) = 1 := by
    simpa only [outcomeE, pow_two, NNReal.coe_one] using hX1_sq_mean_mul
  have hX2_sq_mean : outcomeE μ (fun ξ => (X 2 ξ) ^ 2) = 1 := by
    simpa only [outcomeE, pow_two, NNReal.coe_one] using hX2_sq_mean_mul

  have hX1_lp : MemLp (X 1) 2 μ := by
    have hmap : MemLp (id : ℝ → ℝ) 2 (μ.map (X 1)) := by
      rw [hX1_law]
      exact memLp_id_gaussianReal (μ := 0) (v := 1) 2
    simpa only [Function.comp_def, id_eq] using
      (memLp_map_measure_iff aestronglyMeasurable_id (hmeas 1).aemeasurable).mp hmap
  have hX2_lp : MemLp (X 2) 2 μ := by
    have hmap : MemLp (id : ℝ → ℝ) 2 (μ.map (X 2)) := by
      rw [hX2_law]
      exact memLp_id_gaussianReal (μ := 0) (v := 1) 2
    simpa only [Function.comp_def, id_eq] using
      (memLp_map_measure_iff aestronglyMeasurable_id (hmeas 2).aemeasurable).mp hmap

  have h01 : IndepFun (X 0) (X 1) μ := hInd.indepFun (by decide)
  have h02 : IndepFun (X 0) (X 2) μ := hInd.indepFun (by decide)
  have h12 : IndepFun (X 1) (X 2) μ := hInd.indepFun (by decide)
  obtain ⟨h01_int, h01_mean_int⟩ :=
    AronowAudit.P027.Wave1.GaussianMoments.n2_proof μ (X 0) (X 1)
      h01 hS_int hX1_int hS_mean_int hX1_mean_int
  obtain ⟨h02_int, h02_mean_int⟩ :=
    AronowAudit.P027.Wave1.GaussianMoments.n2_proof μ (X 0) (X 2)
      h02 hS_int hX2_int hS_mean_int hX2_mean_int
  obtain ⟨h12_int, h12_mean_int⟩ :=
    AronowAudit.P027.Wave1.GaussianMoments.n2_proof μ (X 1) (X 2)
      h12 hX1_int hX2_int hX1_mean_int hX2_mean_int

  refine ⟨?_, ?_⟩
  · unfold PairMoments
    refine ⟨hsupport, hS_mean, hS_int, hX1_int, hX2_int,
      ⟨hX1_mean, hX2_mean⟩,
      ⟨hX1_sq_int, hX2_sq_int, hX1_sq_mean, hX2_sq_mean⟩,
      ⟨h01_int, h02_int, h12_int, ?_, ?_, ?_⟩⟩
    · simpa [outcomeE] using h01_mean_int
    · simpa [outcomeE] using h02_mean_int
    · simpa [outcomeE] using h12_mean_int
  · intro i
    fin_cases i <;> assumption
