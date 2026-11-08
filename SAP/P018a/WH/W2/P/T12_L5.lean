import SAP.P018a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P018a.WH.W2.P.T12_L5

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Elementwise

private lemma dyad_card_real (N : ℕ) :
    (Fintype.card (Dyad N) : ℝ) = Dreal N := by
  change (Fintype.card (AronowAudit.P018.Dyad N) : ℝ) = Dreal N
  exact AronowAudit.P018.Wave1.printed_card_real N

private lemma dyad_set_card_real (N : ℕ) :
    ((dyads N).card : ℝ) = Dreal N := by
  simpa only [Fintype.card_coe] using dyad_card_real N

private lemma repeatedL_formula (N m : ℕ) :
    repeatedL (wholeRepeatedSign m) N = (m : ℝ) * Dreal N := by
  change (∑ d : Dyad N, (m : ℝ)) = (m : ℝ) * Dreal N
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [dyad_card_real]
  ring

private lemma repeatedGram_formula (N m : ℕ) (ω : Fin N → Bool) :
    repeatedGram (wholeRepeatedSign m) ω = ((m : ℝ) * Dreal N) • (1 : Mat 1) := by
  unfold repeatedGram
  change (∑ d : Dyad N, ∑ t : Fin m, outer (![1] : Vec 1) (![1])) =
    ((m : ℝ) * Dreal N) • (1 : Mat 1)
  ext a b
  fin_cases a
  fin_cases b
  simp only [Matrix.sum_apply]
  simp [outer, Matrix.cons_val_zero]
  rw [dyad_set_card_real]
  ring

private lemma fair_sign_mean : (∫ b, signValue b ∂ fairLaw) = 0 := by
  letI : IsProbabilityMeasure fairLaw := by
    unfold fairLaw
    infer_instance
  rw [integral_fintype (AronowAudit.P018.Wave1.printed_finite_integrable _ _)]
  norm_num [fairLaw, Measure.real, PMF.toMeasure_uniformOfFintype_apply,
    signValue, Fintype.sum_bool, Fintype.card_bool]

private lemma signKernel_beta_zero : populationBeta signKernel = 0 := by
  letI : IsProbabilityMeasure fairLaw := by
    unfold fairLaw
    infer_instance
  have hm : meanVec (fairLaw.prod fairLaw)
      (fun uv : Bool × Bool => score (![1] : Vec 1)
        (signValue uv.1 + signValue uv.2)) = 0 := by
    ext a
    fin_cases a
    simp only [meanVec, score, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_fin_one, mul_one, Pi.zero_apply]
    rw [integral_prod _
      (AronowAudit.P018.Wave1.printed_finite_integrable _ _)]
    change (∫ u, ∫ v, signValue u + signValue v ∂ fairLaw ∂ fairLaw) = 0
    have hi (u : Bool) :
        (∫ v, signValue u + signValue v ∂ fairLaw) = signValue u := by
      rw [integral_add (integrable_const _)
        (AronowAudit.P018.Wave1.printed_finite_integrable _ _)]
      rw [integral_const, fair_sign_mean]
      have hs : ({false, true} : Set Bool) = Set.univ := by
        ext b
        cases b <;> simp
      have hset : fairLaw.real ({false, true} : Set Bool) =
          fairLaw.real Set.univ := congrArg (fun s : Set Bool => fairLaw.real s) hs
      have hmass : fairLaw.real ({false, true} : Set Bool) = 1 := by
        rw [hset, probReal_univ]
      simp [hmass]
    simp_rw [hi]
    exact fair_sign_mean
  have hG : populationGram signKernel = (1 : Mat 1) := by
    ext a b
    fin_cases a
    fin_cases b
    simp [populationGram, signKernel, meanMat, outer]
  unfold populationBeta
  change (populationGram signKernel)⁻¹.mulVec
      (meanVec (fairLaw.prod fairLaw) (fun uv : Bool × Bool =>
        score (![1] : Vec 1) (signValue uv.1 + signValue uv.2))) = 0
  rw [hG, hm]
  simp

private lemma scoreSum_sign_formula (N : ℕ) (ω : Fin N → Bool) :
    scoreSum signKernel ω 0 = ((N : ℝ) - 1) * wholeSignSum ω := by
  exact AronowAudit.P018.Wave1.appendixB_scoreSum ω

private lemma signScore_variance (N : ℕ) :
    varMat (unitSampleLaw signKernel N) (scoreSum signKernel) =
      !![(N : ℝ) * ((N : ℝ) - 1)^2] := by
  ext a b
  fin_cases a
  fin_cases b
  change ProbabilityTheory.covariance
      (fun ω => scoreSum signKernel ω 0)
      (fun ω => scoreSum signKernel ω 0) (unitSampleLaw signKernel N) = _
  simp_rw [show (fun ω : Fin N → Bool => scoreSum signKernel ω 0) =
      (fun ω => ((N : ℝ) - 1) * wholeSignSum ω) from
        funext (scoreSum_sign_formula N)]
  rw [covariance_self (measurable_of_countable _).aemeasurable, variance_const_mul]
  change ((N : ℝ) - 1)^2 * ProbabilityTheory.variance
    (fun ω => wholeSignSum ω) (unitSampleLaw signKernel N) =
      (N : ℝ) * ((N : ℝ) - 1)^2
  rw [show ProbabilityTheory.variance (fun ω => wholeSignSum ω)
      (unitSampleLaw signKernel N) = (N : ℝ) from
        AronowAudit.P018.Wave1.printed_S_variance N]
  ring

private lemma repeatedXY_formula (N m : ℕ) :
    (fun ω : Fin N → Bool =>
      ∑ d : Dyad N, ∑ t : Fin ((wholeRepeatedSign m).T N d),
        score (repeatedX (wholeRepeatedSign m) ω d t)
          (repeatedY (wholeRepeatedSign m) ω d t)) =
      fun ω => (m : ℝ) • scoreSum signKernel ω := by
  funext ω
  ext a
  fin_cases a
  dsimp [wholeRepeatedSign, repeatedX, repeatedY]
  simp only [Finset.sum_apply, Matrix.cons_val_zero]
  have hpairs :
      (∑ d : Dyad N,
        (signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)))) =
        scoreSum signKernel ω 0 := by
    simp only [scoreSum, epsilon, populationResidual]
    rw [signKernel_beta_zero]
    simp [design, signKernel, score, dot]
  have huniv : (Finset.univ : Finset (Dyad N)) = (dyads N).attach := by
    ext d
    simp
  have hpairs_attach : (∑ d ∈ (dyads N).attach,
      (signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)))) =
      scoreSum signKernel ω 0 := by
    simpa [huniv] using hpairs
  change (∑ d ∈ (dyads N).attach, ∑ t : Fin m,
      score (![1] : Vec 1)
        (signValue (ω (firstUnit d)) + signValue (ω (secondUnit d))) 0) =
      (m : ℝ) * scoreSum signKernel ω 0
  simp only [score, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_fin_one]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin]
  simp only [mul_one]
  rw [← Finset.mul_sum, hpairs_attach]

private lemma wholeSignSum_mean (N : ℕ) :
    (∫ ω, wholeSignSum ω ∂ unitSampleLaw signKernel N) = 0 := by
  letI : IsProbabilityMeasure fairLaw := by
    unfold fairLaw
    infer_instance
  change (∫ ω : Fin N → Bool, ∑ i : Fin N, signValue (ω i)
      ∂ Measure.pi (fun _ : Fin N => fairLaw)) = 0
  rw [integral_finsetSum _ (fun i hi =>
    AronowAudit.P018.Wave1.printed_finite_integrable _ _)]
  have hi (i : Fin N) :
      (∫ ω : Fin N → Bool, signValue (ω i)
        ∂ Measure.pi (fun _ : Fin N => fairLaw)) = 0 := by
    have hm := (measurePreserving_eval (fun _ : Fin N => fairLaw) i).map_eq
    calc
      _ = ∫ b, signValue b ∂
          (Measure.pi (fun _ : Fin N => fairLaw)).map
            (fun ω : Fin N → Bool => ω i) :=
        (integral_map_of_stronglyMeasurable (measurable_pi_apply i)
          (measurable_of_countable signValue).stronglyMeasurable).symm
      _ = 0 := by rw [hm, fair_sign_mean]
  simp [hi]

private lemma repeatedXY_mean_zero (N m : ℕ) :
    meanVec (repeatedLaw (wholeRepeatedSign m) N)
      (fun ω => ∑ d : Dyad N,
        ∑ t : Fin ((wholeRepeatedSign m).T N d),
          score (repeatedX (wholeRepeatedSign m) ω d t)
            (repeatedY (wholeRepeatedSign m) ω d t)) = 0 := by
  rw [repeatedXY_formula]
  ext a
  fin_cases a
  change (∫ ω, (m : ℝ) * scoreSum signKernel ω 0
    ∂ repeatedLaw (wholeRepeatedSign m) N) = 0
  rw [show repeatedLaw (wholeRepeatedSign m) N = unitSampleLaw signKernel N from rfl]
  simp_rw [scoreSum_sign_formula]
  rw [integral_const_mul, integral_const_mul, wholeSignSum_mean]
  ring

private lemma repeatedBeta_zero (N m : ℕ) :
    repeatedBeta (wholeRepeatedSign m) N = 0 := by
  unfold repeatedBeta
  rw [repeatedXY_mean_zero]
  simp

private lemma repeatedH_one (N m : ℕ) (hN : 2 ≤ N) (hm : 0 < m) :
    repeatedH (wholeRepeatedSign m) N = (1 : Mat 1) := by
  letI : IsProbabilityMeasure (repeatedLaw (wholeRepeatedSign m) N) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => fairLaw))
    letI : IsProbabilityMeasure fairLaw := by
      unfold fairLaw
      infer_instance
    infer_instance
  have hgram : meanMat (repeatedLaw (wholeRepeatedSign m) N)
      (repeatedGram (wholeRepeatedSign m)) =
        ((m : ℝ) * Dreal N) • (1 : Mat 1) := by
    ext a b
    fin_cases a
    fin_cases b
    simp [meanMat, repeatedGram_formula]
  have hD : Dreal N ≠ 0 := ne_of_gt (AronowAudit.P018.Wave1.printed_Dpos hN)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [repeatedH, repeatedL_formula, hgram]
  simp only [smul_smul]
  field_simp [hmR, hD]
  simp

private lemma repeatedTotalScore_formula (N m : ℕ) :
    (fun ω : Fin N → Bool =>
      ∑ d : Dyad N, repeatedBlockScore (wholeRepeatedSign m)
        (repeatedBeta (wholeRepeatedSign m) N) ω d) =
      fun ω => (m : ℝ) • scoreSum signKernel ω := by
  funext ω
  rw [repeatedBeta_zero]
  have h := congrFun (repeatedXY_formula N m) ω
  simpa [repeatedBlockScore, wholeRepeatedSign, repeatedX, repeatedY,
    dot, score] using h

private lemma covariance_score_scale_local {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : Ω → Vec 1) (a : ℝ) :
    varMat μ (fun ω => a • q ω) = (a^2) • varMat μ q := by
  ext i j
  fin_cases i
  fin_cases j
  simp only [varMat, covMat, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right]
  ring

private lemma repeatedTarget_four (N m : ℕ) (hN : 3 ≤ N) (hm : 0 < m) :
    repeatedTarget (wholeRepeatedSign m) N = !![4] := by
  have hN2 : 2 ≤ N := by omega
  have hD : Dreal N ≠ 0 := ne_of_gt (AronowAudit.P018.Wave1.printed_Dpos hN2)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hscale : (m : ℝ) * Dreal N ≠ 0 := mul_ne_zero hmR hD
  have hH := repeatedH_one N m hN2 hm
  have hscore := repeatedTotalScore_formula N m
  have hvar : varMat (repeatedLaw (wholeRepeatedSign m) N)
      (fun ω => ∑ d : Dyad N, repeatedBlockScore (wholeRepeatedSign m)
        (repeatedBeta (wholeRepeatedSign m) N) ω d) =
      ((m : ℝ)^2) • !![(N : ℝ) * ((N : ℝ) - 1)^2] := by
    rw [hscore, covariance_score_scale_local]
    rw [show repeatedLaw (wholeRepeatedSign m) N = unitSampleLaw signKernel N from rfl,
      signScore_variance]
  ext a b
  fin_cases a
  fin_cases b
  rw [repeatedTarget, repeatedL_formula, hH, hvar]
  simp only [sandwich, inv_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_fin_one]
  change ((N : ℝ) / (((m : ℝ) * Dreal N)^2)) *
      (((m : ℝ)^2) * ((N : ℝ) * ((N : ℝ) - 1)^2)) = 4
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  dsimp [Dreal]
  field_simp [hmR, hN0, hNm1, hscale]
  <;> ring

private lemma signTarget_four (N : ℕ) (hN : 3 ≤ N) :
    trueTarget signKernel N = !![4] := by
  have hN2 : 2 ≤ N := by omega
  have hvar := signScore_variance N
  ext a b
  fin_cases a
  fin_cases b
  have hG : populationGram signKernel = (1 : Mat 1) := by
    letI : IsProbabilityMeasure fairLaw := by
      unfold fairLaw
      infer_instance
    ext a b
    fin_cases a
    fin_cases b
    simp [populationGram, signKernel, meanMat, outer]
  simp only [trueTarget, hG, inv_one, sandwich, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_apply, smul_eq_mul, hvar, Matrix.of_apply,
    Matrix.cons_val_fin_one]
  change ((N : ℝ) / (Dreal N)^2) *
      ((N : ℝ) * ((N : ℝ) - 1)^2) = 4
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hNm1 : (N : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  dsimp [Dreal]
  field_simp [hN0, hNm1]
  <;> ring

end SAP.P018a.WH.W2.P.T12_L5

theorem SAP.P018a.WH.W2.T12_L5_proof : SAP.P018a.WH.W2.T12_L5 := by
  constructor
  · intro N m hN hm
    exact SAP.P018a.WH.W2.P.T12_L5.repeatedTarget_four N m hN hm
  · intro N hN
    have hN2 : 2 ≤ N := by omega
    have hK : AronowAudit.P018.Standing
        (SAP.P018a.Bridge.toKernel signKernel) := by
      simpa [SAP.P018a.Bridge.toKernel, SAP.P018a.signKernel,
        SAP.P018a.fairLaw, SAP.P018a.signValue,
        AronowAudit.P018.signKernel, AronowAudit.P018.fairLaw,
        AronowAudit.P018.signValue] using
        AronowAudit.P018.Wave1.appendixB_standing
    have h := AronowAudit.P018.Wave1.corrected_target_reductions_proof
      (SAP.P018a.Bridge.toKernel signKernel) hK hN2
    have hlocal : weightedTarget signKernel (fun _ : Dyad N => 1) =
        trueTarget signKernel N := by
      change AronowAudit.P018.weightedTarget
          (SAP.P018a.Bridge.toKernel signKernel)
          (fun _ : AronowAudit.P018.Dyad N => 1) =
        AronowAudit.P018.trueTarget (SAP.P018a.Bridge.toKernel signKernel) N
      exact h.2
    rw [hlocal, SAP.P018a.WH.W2.P.T12_L5.signTarget_four N hN]
