import SAP.P018b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b.WH.W1.P.T20_L2

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Matrix.Norms.Elementwise
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem rare_term_integrable (N : ℕ) (d : AronowAudit.P018.Dyad N) :
    Integrable (fun ω : Fin N → AronowAudit.P018.RareUnit =>
      (AronowAudit.P018.Wave1.TailB_rare_s ω d)^2)
      (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  letI : IsProbabilityMeasure
      (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw))
    infer_instance
  have hm : AEStronglyMeasurable (fun ω : Fin N → AronowAudit.P018.RareUnit =>
      (AronowAudit.P018.Wave1.TailB_rare_s ω d)^2)
      (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) :=
    (measurable_of_countable _).aestronglyMeasurable
  apply (integrable_const (1 : ℝ)).mono' hm
  filter_upwards with ω
  have hs := AronowAudit.P018.Wave1.TailB_rare_s_bounds
    (ω (AronowAudit.P018.firstUnit d)) (ω (AronowAudit.P018.secondUnit d))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_one_iff_abs_le_one _).2 (by
    change |AronowAudit.P018.rareS (ω (AronowAudit.P018.firstUnit d))
      (ω (AronowAudit.P018.secondUnit d))| ≤ 1
    rw [abs_of_pos hs.1]
    exact hs.2)

private theorem rare_S_integral (N : ℕ) :
    (∫ ω, AronowAudit.P018.Wave1.TailB_rare_S ω
      ∂ AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) =
      AronowAudit.P018.Dreal N * AronowAudit.P018.rareQ := by
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  letI : IsProbabilityMeasure
      (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw))
    infer_instance
  have htermInt (d : AronowAudit.P018.Dyad N) := rare_term_integrable N d
  have hterm (d : AronowAudit.P018.Dyad N) :
      (∫ ω, (AronowAudit.P018.Wave1.TailB_rare_s ω d)^2
        ∂ AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) =
        AronowAudit.P018.rareQ := by
    have hind : iIndepFun (fun i (ω : Fin N → AronowAudit.P018.RareUnit) => ω i)
        (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw)) :=
      iIndepFun_pi (μ := fun _ : Fin N => AronowAudit.P018.rareLaw)
        (X := fun _ => id) (fun _ => aemeasurable_id)
    have heval (i : Fin N) :
        MeasurePreserving (fun ω : Fin N → AronowAudit.P018.RareUnit => ω i)
          (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N)
          AronowAudit.P018.rareLaw :=
      measurePreserving_eval (fun _ : Fin N => AronowAudit.P018.rareLaw) i
    have h := AronowAudit.P018.Wave1.GP0182B2b_kernel_pair_integral
      (fun i (ω : Fin N → AronowAudit.P018.RareUnit) => ω i) hind heval
      (K := fun uv : AronowAudit.P018.RareUnit × AronowAudit.P018.RareUnit =>
        (AronowAudit.P018.rareS uv.1 uv.2)^2)
      (measurable_of_countable _)
      (i := AronowAudit.P018.firstUnit d) (j := AronowAudit.P018.secondUnit d)
      (AronowAudit.P018.Wave1.WeightedConsistency.firstUnit_ne_secondUnit d)
    simpa [AronowAudit.P018.Wave1.TailB_rare_s, AronowAudit.P018.rareQ,
      AronowAudit.P018.repeatedLaw, AronowAudit.P018.rareRepeated] using h
  change (∫ ω, (∑ d : AronowAudit.P018.Dyad N,
      (AronowAudit.P018.Wave1.TailB_rare_s ω d)^2)
      ∂ AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) = _
  rw [integral_finsetSum _ (fun d _ => htermInt d)]
  rw [Finset.sum_congr rfl (fun d _ => hterm d)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    AronowAudit.P018.Wave1.printed_card_real]

private theorem rare_expected_H (N : ℕ) (hN : 2 ≤ N) :
    wholeRepeatedH (wholeRareKernel rareModel) N =
      !![1, 1; 1, 1 + wholeRareQ rareModel] := by
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  letI : IsProbabilityMeasure
      (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw))
    infer_instance
  have hS := rare_S_integral N
  have hS' : Integrable (fun ω : Fin N → AronowAudit.P018.RareUnit =>
      AronowAudit.P018.Wave1.TailB_rare_S ω)
      (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
    unfold AronowAudit.P018.Wave1.TailB_rare_S
    exact integrable_finsetSum _ (fun d _ => rare_term_integrable N d)
  have hgram :
      AronowAudit.P018.meanMat
        (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N)
        (AronowAudit.P018.repeatedGram AronowAudit.P018.rareRepeated) =
        !![2 * AronowAudit.P018.Dreal N, 2 * AronowAudit.P018.Dreal N;
          2 * AronowAudit.P018.Dreal N,
          2 * AronowAudit.P018.Dreal N + 2 * AronowAudit.P018.Dreal N * AronowAudit.P018.rareQ] := by
    have hGfun : AronowAudit.P018.repeatedGram (N := N)
        AronowAudit.P018.rareRepeated =
        (fun ω : Fin N → AronowAudit.P018.RareUnit => !![2 * AronowAudit.P018.Dreal N,
          2 * AronowAudit.P018.Dreal N; 2 * AronowAudit.P018.Dreal N,
          2 * AronowAudit.P018.Dreal N +
            2 * AronowAudit.P018.Wave1.TailB_rare_S (N := N) ω]) := by
      funext ω
      exact AronowAudit.P018.Wave1.TailB_rare_gram ω
    rw [hGfun]
    ext i j
    simp only [AronowAudit.P018.meanMat]
    fin_cases i <;> fin_cases j
    · simp
    · simp
    · simp
    · change (∫ ω, (2 * AronowAudit.P018.Dreal N +
        2 * AronowAudit.P018.Wave1.TailB_rare_S ω)
        ∂ AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) = _
      rw [integral_add (integrable_const _) (hS'.const_mul 2)]
      rw [integral_const, integral_const_mul, hS]
      simp
      ring
  change (AronowAudit.P018.repeatedL AronowAudit.P018.rareRepeated N)⁻¹ •
      AronowAudit.P018.meanMat
        (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N)
        (AronowAudit.P018.repeatedGram AronowAudit.P018.rareRepeated) = _
  rw [hgram]
  have hQ : wholeRareQ rareModel = AronowAudit.P018.rareQ := rfl
  rw [hQ]
  have hL : AronowAudit.P018.repeatedL AronowAudit.P018.rareRepeated N =
      2 * AronowAudit.P018.Dreal N := by
    rw [AronowAudit.P018.repeatedL]
    change (∑ d : AronowAudit.P018.Dyad N, (2 : ℝ)) = _
    rw [Finset.sum_const]
    simp only [Finset.card_univ, nsmul_eq_mul,
      AronowAudit.P018.Wave1.printed_card_real]
    ring
  rw [hL]
  have hD : AronowAudit.P018.Dreal N ≠ 0 :=
    (ne_of_gt (AronowAudit.P018.Wave1.TailB_rare_D_pos hN))
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.smul_apply] <;>
    field_simp [hD] <;> ring

private theorem rareOLS_nonL2 (N : ℕ) (hN : 3 ≤ N) :
    ¬ MemLp (fun ω => repeatedOLS (wholeRareKernel rareModel) ω 1 -
      repeatedBeta (wholeRareKernel rareModel) N 1) 2
      (repeatedLaw (wholeRareKernel rareModel) N) := by
  intro hmem
  have hbeta : repeatedBeta (wholeRareKernel rareModel) N = 0 := by
    change AronowAudit.P018.repeatedBeta AronowAudit.P018.rareRepeated N = 0
    exact AronowAudit.P018.Wave1.tb09_rare_population_beta N
  simp only [hbeta, Pi.zero_apply, sub_zero] at hmem
  have hmem' : MemLp (fun ω : Fin N → AronowAudit.P018.RareUnit =>
      AronowAudit.P018.repeatedOLS AronowAudit.P018.rareRepeated ω 1) 2
      (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
    change MemLp (fun ω => repeatedOLS (wholeRareKernel rareModel) ω 1) 2
      (repeatedLaw (wholeRareKernel rareModel) N)
    exact hmem
  have hinf := AronowAudit.P018.Wave1.TailB_rare_coefficient_integrals N hN
  have hsq := hmem'.integrable_sq
  have hfinite :
      (∫⁻ ω, ENNReal.ofReal
        ((AronowAudit.P018.repeatedOLS AronowAudit.P018.rareRepeated ω 1)^2)
        ∂ AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) < ∞ := by
    have ht := (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hsq.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => sq_nonneg _))).2 hsq
    exact (lt_top_iff_ne_top).2 ht
  rw [hinf.1] at hfinite
  exact (lt_irrefl _) hfinite

private theorem rareOLS_nonintegrable (N : ℕ) (hN : 3 ≤ N) :
    ¬ Integrable (fun ω => wholeWeightedOLS (wholeRareKernel rareModel)
        (fun _ _ => 1) ω 1 -
      wholeWeightedBeta (N := N) (wholeRareKernel rareModel)
        (fun _ _ => 1) 1)
      (repeatedLaw (wholeRareKernel rareModel) N) := by
  intro hi
  have hweightOLS :
      (fun ω : Fin N → AronowAudit.P018.RareUnit =>
        wholeWeightedOLS (N := N) (wholeRareKernel rareModel) (fun _ _ => 1) ω) =
      (fun ω => repeatedOLS (wholeRareKernel rareModel) ω) := by
    funext ω
    simp [wholeWeightedOLS, wholeWeightedGram, wholeWeightedXY,
      repeatedOLS, repeatedGram, repeatedX, repeatedY]
  have hWG : wholeWeightedGram (N := N) (wholeRareKernel rareModel)
      (fun _ _ => 1) = repeatedGram (N := N) (wholeRareKernel rareModel) := by
    ext ω i j
    simp [wholeWeightedGram, repeatedGram]
  have hWXY : ∀ ω : Fin N → AronowAudit.P018.RareUnit,
      wholeWeightedXY (N := N) (wholeRareKernel rareModel) (fun _ _ => 1) ω =
        ∑ d : Dyad N, ∑ t,
          score (repeatedX (wholeRareKernel rareModel) ω d t)
            (repeatedY (wholeRareKernel rareModel) ω d t) := by
    intro ω
    simp [wholeWeightedXY, repeatedX, repeatedY]
  have hWXYfun :
      (fun ω : Fin N → AronowAudit.P018.RareUnit =>
        wholeWeightedXY (N := N) (wholeRareKernel rareModel) (fun _ _ => 1) ω) =
      (fun ω => ∑ d : Dyad N, ∑ t,
        score (repeatedX (wholeRareKernel rareModel) ω d t)
          (repeatedY (wholeRareKernel rareModel) ω d t)) := by
    funext ω
    exact hWXY ω
  have hweightBeta :
      wholeWeightedBeta (N := N) (wholeRareKernel rareModel) (fun _ _ => 1) =
        repeatedBeta (wholeRareKernel rareModel) N := by
    simp only [wholeWeightedBeta, repeatedBeta, hWG, hWXYfun]
  have hbeta : repeatedBeta (wholeRareKernel rareModel) N = 0 := by
    change AronowAudit.P018.repeatedBeta AronowAudit.P018.rareRepeated N = 0
    exact AronowAudit.P018.Wave1.tb09_rare_population_beta N
  have hi' : Integrable (fun ω : Fin N → AronowAudit.P018.RareUnit =>
      AronowAudit.P018.repeatedOLS AronowAudit.P018.rareRepeated ω 1)
      (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) := by
    have hi'' : Integrable (fun ω =>
        repeatedOLS (wholeRareKernel rareModel) ω 1)
        (repeatedLaw (wholeRareKernel rareModel) N) := by
      simpa only [hweightOLS, hweightBeta, hbeta, Pi.zero_apply, sub_zero] using hi
    change Integrable (fun ω => repeatedOLS (wholeRareKernel rareModel) ω 1)
      (repeatedLaw (wholeRareKernel rareModel) N)
    exact hi''
  have hfinite :
      (∫⁻ ω, ENNReal.ofReal
        |AronowAudit.P018.repeatedOLS AronowAudit.P018.rareRepeated ω 1| ∂
          AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) < ∞ := by
    simpa [Real.norm_eq_abs] using
      (MeasureTheory.hasFiniteIntegral_iff_norm
        (fun ω : Fin N → AronowAudit.P018.RareUnit =>
          AronowAudit.P018.repeatedOLS AronowAudit.P018.rareRepeated ω 1)
        (μ := AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N)).mp
          hi'.hasFiniteIntegral
  have hinf := AronowAudit.P018.Wave1.TailB_rare_coefficient_integrals N hN
  rw [hinf.2] at hfinite
  exact (lt_irrefl _) hfinite

end SAP.P018b.WH.W1.P.T20_L2

open Finset Matrix MeasureTheory ProbabilityTheory SAP.P018b SAP.P018b.WH.W1
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

theorem SAP.P018b.WH.W1.T20_L2_proof : SAP.P018b.WH.W1.T20_L2 := by
  constructor
  · intro N hN
    rw [SAP.P018b.WH.W1.P.T20_L2.rare_expected_H N hN]
    have hq : 0 < wholeRareQ rareModel := by
      change 0 < AronowAudit.P018.rareQ
      exact AronowAudit.P018.Wave1.tb09_rare_Q_pos
    change 0 < ((!![1, 1; 1, 1 + wholeRareQ rareModel] : Mat 2).det)
    norm_num [Matrix.det_fin_two]
    exact hq
  constructor
  · intro N hN
    exact ⟨SAP.P018b.WH.W1.P.T20_L2.rareOLS_nonL2 N hN,
      SAP.P018b.WH.W1.P.T20_L2.rareOLS_nonintegrable N hN⟩
  · intro hui
    have hfirst := hui.1 3 1
    have hbad := SAP.P018b.WH.W1.P.T20_L2.rareOLS_nonL2 3 (by norm_num)
    let c : ℝ := Real.sqrt (3 : ℕ)
    have hc : c ≠ 0 := by dsimp [c]; positivity
    have hscaled : MemLp (fun ω =>
        (c • (repeatedOLS (wholeRareKernel rareModel) ω -
          repeatedBeta (wholeRareKernel rareModel) 3)) 1) 2
        (repeatedLaw (wholeRareKernel rareModel) 3) := by
      simpa [c] using hfirst
    have htmp := hscaled.const_smul (1 / c)
    have hunscaled : MemLp (fun ω => repeatedOLS (wholeRareKernel rareModel) ω 1 -
        repeatedBeta (wholeRareKernel rareModel) 3 1) 2
        (repeatedLaw (wholeRareKernel rareModel) 3) := by
      convert htmp using 1
      ext ω
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp [hc]
    exact hbad hunscaled

