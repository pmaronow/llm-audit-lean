import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
noncomputable section
namespace SAP.P018a.WH.W1.P.T11_L3

open Finset Matrix MeasureTheory ProbabilityTheory
open AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

local instance : IsProbabilityMeasure SAP.P018a.fairLaw := by
  unfold SAP.P018a.fairLaw
  infer_instance

lemma dyadCard_real (N : ℕ) : (Fintype.card (Dyad N) : ℝ) = Dreal N := by
  simp only [Fintype.card_coe]
  change ((dyads N).card : ℝ) = Dreal N
  simp only [dyads, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact Nat.cast_choose_two ℝ N

lemma dyadCardFinset_real (N : ℕ) : ((dyads N).card : ℝ) = Dreal N := by
  simpa only [Fintype.card_coe] using dyadCard_real N

lemma Dreal_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Dreal N := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : (0 : ℝ) < N := by linarith
  have h1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  dsimp [Dreal]
  positivity

lemma signPopulationBeta : populationBeta signKernel = 0 := by
  have hpair : meanVec (fairLaw.prod fairLaw)
      (fun uv : Bool × Bool => score (![1] : Vec 1)
        (signValue uv.1 + signValue uv.2)) = 0 := by
    change AronowAudit.P018.meanVec
      (AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw)
      (fun uv : Bool × Bool => AronowAudit.P018.score (![1] : AronowAudit.P018.Vec 1)
        (AronowAudit.P018.signValue uv.1 + AronowAudit.P018.signValue uv.2)) = 0
    have hb := AronowAudit.P018.Wave1.appendixB_populationBeta
    change (AronowAudit.P018.populationGram AronowAudit.P018.signKernel)⁻¹.mulVec
      (AronowAudit.P018.meanVec
        (AronowAudit.P018.fairLaw.prod AronowAudit.P018.fairLaw)
        (fun uv : Bool × Bool => AronowAudit.P018.score (![1] : AronowAudit.P018.Vec 1)
          (AronowAudit.P018.signValue uv.1 + AronowAudit.P018.signValue uv.2))) = 0 at hb
    rw [AronowAudit.P018.Wave1.appendixB_populationGram, inv_one] at hb
    simpa [Matrix.mulVec, dotProduct] using hb
  have hgram : populationGram signKernel = (1 : Mat 1) := by
    change AronowAudit.P018.populationGram AronowAudit.P018.signKernel = _
    exact AronowAudit.P018.Wave1.appendixB_populationGram
  rw [populationBeta, hgram, inv_one]
  simpa [Matrix.mulVec, dotProduct, signKernel] using hpair

lemma scoreSumSign (N : ℕ) (ω : Fin N → Bool) :
    (scoreSum signKernel ω) 0 = ((N : ℝ)-1) * AronowAudit.P018.Wave1.printed_S ω := by
  have h := AronowAudit.P018.Wave1.appendixB_scoreSum ω
  change (AronowAudit.P018.scoreSum AronowAudit.P018.signKernel ω) 0 = _ at h
  change (AronowAudit.P018.scoreSum AronowAudit.P018.signKernel ω) 0 = _
  exact h

lemma scoreSumMeanZero (N : ℕ) :
    meanVec (unitSampleLaw signKernel N) (scoreSum signKernel) = 0 := by
  ext a
  fin_cases a
  change (∫ ω, (scoreSum signKernel ω) 0 ∂ unitSampleLaw signKernel N) = 0
  simp_rw [scoreSumSign]
  change (∫ ω, ((N : ℝ)-1) * AronowAudit.P018.Wave1.printed_S ω
    ∂ AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N) = 0
  rw [integral_const_mul, AronowAudit.P018.Wave1.printed_S_mean]
  simp

lemma mat1_scalar (x : ℝ) : (!![x] : Mat 1) = x • (1 : Mat 1) := by
  ext i j
  fin_cases i
  fin_cases j
  simp

lemma repeatedL_eq (T N : ℕ) :
    repeatedL (W1IdenticalSign T) N = (T : ℝ) * Dreal N := by
  calc
    repeatedL (W1IdenticalSign T) N = (Fintype.card (Dyad N) : ℝ) * (T : ℝ) := by
      simp [repeatedL, W1IdenticalSign, Finset.sum_const]
    _ = (T : ℝ) * Dreal N := by rw [dyadCard_real]; ring

lemma repeatedBlockScore_zero (T N : ℕ) (ω : Fin N → Bool) (d : Dyad N) :
    repeatedBlockScore (W1IdenticalSign T) 0 ω d =
      (T : ℝ) • score (design signKernel ω d) (response signKernel ω d) := by
  ext a
  fin_cases a
  simp only [repeatedBlockScore, W1IdenticalSign, repeatedX, repeatedY, score,
    Pi.smul_apply, smul_eq_mul]
  simp only [Finset.sum_apply]
  simp only [design, response, signKernel]
  change (∑ t : Fin ((W1IdenticalSign T).T N d),
      ((signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)) -
        dot (![1] : Vec 1) 0) * (![1] : Vec 1) 0)) =
    (T : ℝ) * ((signValue (ω (firstUnit d)) + signValue (ω (secondUnit d))) *
      (![1] : Vec 1) 0)
  rw [show (W1IdenticalSign T).T N d = T by rfl]
  simp [dot]
  <;> ring

lemma epsilon_eq_response (N : ℕ) (ω : Fin N → Bool) (d : Dyad N) :
    epsilon signKernel ω d = response signKernel ω d := by
  unfold epsilon response populationResidual
  rw [signPopulationBeta]
  simp [signKernel, dot]

lemma repeatedScoreSum_zero (T N : ℕ) (ω : Fin N → Bool) :
    (∑ d : Dyad N, repeatedBlockScore (W1IdenticalSign T) 0 ω d) =
      (T : ℝ) • scoreSum signKernel ω := by
  simp_rw [repeatedBlockScore_zero]
  ext a
  fin_cases a
  simp only [scoreSum, Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul,
    epsilon_eq_response]
  rw [Finset.mul_sum]

lemma repeatedGram_eq (T N : ℕ) (ω : Fin N → Bool) :
    repeatedGram (W1IdenticalSign T) ω = ((T : ℝ) * Dreal N) • (1 : Mat 1) := by
  have hrecord (d : Dyad N) :
      (∑ t : Fin T, outer (![1] : Vec 1) (![1] : Vec 1)) =
        (T : ℝ) • (1 : Mat 1) := by
    ext a b
    fin_cases a
    fin_cases b
    simp [outer, Finset.sum_const]
  have hsum : repeatedGram (W1IdenticalSign T) ω =
      ∑ d : Dyad N, (T : ℝ) • (1 : Mat 1) := by
    unfold repeatedGram
    apply Finset.sum_congr rfl
    intro d hd
    change (∑ t : Fin T, outer (![1] : Vec 1) (![1] : Vec 1)) = _
    exact hrecord d
  rw [hsum]
  ext i j
  fin_cases i
  fin_cases j
  simp only [Finset.sum_const, Fintype.card_coe, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Finset.card_univ, nsmul_eq_mul]
  rw [dyadCardFinset_real]
  ring
  <;> ring

lemma repeatedMeanGram_eq (T N : ℕ) :
    meanMat (repeatedLaw (W1IdenticalSign T) N) (repeatedGram (W1IdenticalSign T)) =
      ((T : ℝ) * Dreal N) • (1 : Mat 1) := by
  rw [show (repeatedGram (W1IdenticalSign T) : (Fin N → Bool) → Mat 1) =
      fun _ => ((T : ℝ) * Dreal N) • (1 : Mat 1) by funext ω; exact repeatedGram_eq T N ω]
  ext i j
  fin_cases i
  fin_cases j
  haveI : IsProbabilityMeasure (W1IdenticalSign T).μ := by
    change IsProbabilityMeasure SAP.P018a.fairLaw
    unfold SAP.P018a.fairLaw
    infer_instance
  haveI : IsProbabilityMeasure (repeatedLaw (W1IdenticalSign T) N) := by
    unfold repeatedLaw
    infer_instance
  simp [meanMat, Matrix.smul_apply, smul_eq_mul, integral_const, probReal_univ]

lemma repeatedBeta_eq (T N : ℕ) : repeatedBeta (W1IdenticalSign T) N = 0 := by
  rw [repeatedBeta, repeatedMeanGram_eq]
  have hscore : meanVec (repeatedLaw (W1IdenticalSign T) N)
      (fun ω => ∑ d : Dyad N, ∑ t,
        score (repeatedX (W1IdenticalSign T) ω d t) (repeatedY (W1IdenticalSign T) ω d t)) = 0 := by
    have hpoint : (fun ω : Fin N → Bool => ∑ d : Dyad N, ∑ t,
        score (repeatedX (W1IdenticalSign T) ω d t) (repeatedY (W1IdenticalSign T) ω d t)) =
        fun ω => (T : ℝ) • scoreSum signKernel ω := by
      funext ω
      calc
        _ = ∑ d : Dyad N, repeatedBlockScore (W1IdenticalSign T) 0 ω d := by
          congr 1
          funext d
          simp [repeatedBlockScore, score, dot]
        _ = _ := repeatedScoreSum_zero T N ω
    rw [hpoint]
    have hscale : meanVec (repeatedLaw (W1IdenticalSign T) N)
        (fun ω => (T : ℝ) • scoreSum signKernel ω) =
        (T : ℝ) • meanVec (repeatedLaw (W1IdenticalSign T) N)
          (scoreSum signKernel) := by
      ext a
      simp [meanVec, integral_const_mul]
    have hmeanR : meanVec (repeatedLaw (W1IdenticalSign T) N)
        (scoreSum signKernel) = 0 := by
      simpa [repeatedLaw, unitSampleLaw, W1IdenticalSign, signKernel] using
        scoreSumMeanZero N
    calc
      meanVec (repeatedLaw (W1IdenticalSign T) N)
          (fun ω => (T : ℝ) • scoreSum signKernel ω) =
          (T : ℝ) • meanVec (repeatedLaw (W1IdenticalSign T) N) (scoreSum signKernel) := hscale
      _ = 0 := by rw [hmeanR]; simp
  rw [hscore]
  simp

lemma repeatedH_eq (T N : ℕ) (hT : 1 ≤ T) (hN : 3 ≤ N) :
    repeatedH (W1IdenticalSign T) N = 1 := by
  have hTD : (T : ℝ) * Dreal N ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (show T ≠ 0 by omega)
    · exact ne_of_gt (Dreal_pos (by omega : 2 ≤ N))
  simp only [repeatedH, repeatedL_eq, repeatedMeanGram_eq]
  rw [smul_smul, inv_mul_cancel₀ hTD, one_smul]

lemma repeatedScoreVariance (T N : ℕ) :
    varMat (repeatedLaw (W1IdenticalSign T) N)
      (fun ω => ∑ d : Dyad N, repeatedBlockScore (W1IdenticalSign T) 0 ω d) =
      !![(T : ℝ)^2 * (N : ℝ) * ((N : ℝ)-1)^2] := by
  have hpoint : (fun ω : Fin N → Bool =>
      ∑ d : Dyad N, repeatedBlockScore (W1IdenticalSign T) 0 ω d) =
      fun ω => (T : ℝ) • scoreSum signKernel ω := by
    funext ω
    exact repeatedScoreSum_zero T N ω
  rw [hpoint]
  have hv : varMat (unitSampleLaw signKernel N) (scoreSum signKernel) =
      !![(N : ℝ) * ((N : ℝ)-1)^2] := by
    ext i j
    fin_cases i
    fin_cases j
    unfold varMat covMat
    rw [ProbabilityTheory.covariance_self (measurable_of_countable _).aemeasurable]
    change ProbabilityTheory.variance (fun ω => (scoreSum signKernel ω) 0)
      (unitSampleLaw signKernel N) = _
    rw [show (fun ω => (scoreSum signKernel ω) 0) =
        fun ω => ((N : ℝ)-1) * AronowAudit.P018.Wave1.printed_S ω by
      funext ω
      exact scoreSumSign N ω]
    rw [variance_const_mul]
    rw [show unitSampleLaw signKernel N =
        AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N by rfl,
      AronowAudit.P018.Wave1.printed_S_variance]
    simp [Matrix.of_apply]
    ring
  have hscale' : ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      (q : Ω → Vec 1) (a : ℝ),
      varMat μ (fun ω => a • q ω) = a^2 • varMat μ q := by
    intro Ω _ μ q a
    ext i j
    simp only [varMat, covMat, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      ProbabilityTheory.covariance_const_mul_left,
      ProbabilityTheory.covariance_const_mul_right]
    ring
  calc
    varMat (repeatedLaw (W1IdenticalSign T) N)
        (fun ω => (T : ℝ) • scoreSum signKernel ω) =
        (T : ℝ)^2 • varMat (repeatedLaw (W1IdenticalSign T) N) (scoreSum signKernel) :=
          hscale' _ _ _
    _ = !![(T : ℝ)^2 * (N : ℝ) * ((N : ℝ)-1)^2] := by
      rw [show repeatedLaw (W1IdenticalSign T) N = unitSampleLaw signKernel N by rfl, hv]
      rw [mat1_scalar ((N : ℝ) * ((N : ℝ)-1)^2),
        mat1_scalar ((T : ℝ)^2 * (N : ℝ) * ((N : ℝ)-1)^2)]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.smul_apply, Matrix.one_apply, smul_smul]
      <;> ring

lemma coefficientBlockGram_eq (T N : ℕ) (d : Dyad N) :
    W1CoefficientBlockGram (W1IdenticalSign T) d = !![(T : ℝ)] := by
  have hb (u v : Bool) : W1BlockX (W1IdenticalSign T) d u v =
      (fun (_ : Fin T) (_ : Fin 1) => (1 : ℝ)) := by
    ext t a
    fin_cases a
    rfl
  have hp (u v : Bool) :
      (W1BlockX (W1IdenticalSign T) d u v).transpose *
        W1BlockX (W1IdenticalSign T) d u v = !![(T : ℝ)] := by
    rw [hb u v]
    ext a b
    fin_cases a
    fin_cases b
    change (∑ t : Fin T, (1 : ℝ) * 1) = (T : ℝ)
    simp
  ext i j
  fin_cases i
  fin_cases j
  change ∫ uv : Bool × Bool,
      ((W1BlockX (W1IdenticalSign T) d uv.1 uv.2).transpose *
        W1BlockX (W1IdenticalSign T) d uv.1 uv.2) 0 0 ∂ (fairLaw.prod fairLaw) = T
  simp_rw [hp]
  simp [integral_const, probReal_univ]

lemma wrongBlockGram_eq (T N : ℕ) (d : Dyad N) :
    W1WrongBlockGram (W1IdenticalSign T) d = (fun _ _ => (1 : ℝ)) := by
  have hb (u v : Bool) : W1BlockX (W1IdenticalSign T) d u v =
      (fun (_ : Fin T) (_ : Fin 1) => (1 : ℝ)) := by
    ext t a
    fin_cases a
    rfl
  have hp (u v : Bool) :
      W1BlockX (W1IdenticalSign T) d u v *
        (W1BlockX (W1IdenticalSign T) d u v).transpose = (fun _ _ => 1) := by
    rw [hb u v]
    ext i j
    change (∑ a : Fin 1, (1 : ℝ) * 1) = 1
    simp
  ext i j
  change ∫ uv : Bool × Bool,
      (W1BlockX (W1IdenticalSign T) d uv.1 uv.2 *
        (W1BlockX (W1IdenticalSign T) d uv.1 uv.2).transpose) i j ∂ (fairLaw.prod fairLaw) = 1
  simp_rw [hp]
  simp [integral_const, probReal_univ]

lemma wrongBread_sandwich (T N : ℕ) (hT : 1 ≤ T) (hN : 3 ≤ N) :
    ((N : ℝ)/(repeatedL (W1IdenticalSign T) N)^2) •
      sandwich (!![(T : ℝ)] : Mat 1)⁻¹
        !![(T : ℝ)^2*(N : ℝ)*((N : ℝ)-1)^2] = !![4/(T : ℝ)^2] := by
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : (N : ℝ)-1 ≠ 0 := by
    have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hinv : (!![(T : ℝ)] : Mat 1)⁻¹ = (T : ℝ)⁻¹ • (1 : Mat 1) := by
    have hmat : (!![(T : ℝ)] : Mat 1) = (T : ℝ) • (1 : Mat 1) := by ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hmat, AronowAudit.P018.matrix_inverse_scale_total _ _ hT0]
    simp
  let M : ℝ := (T : ℝ)^2 * (N : ℝ) * ((N : ℝ)-1)^2
  have hSand : sandwich ((T : ℝ)⁻¹ • (1 : Mat 1)) (!![M] : Mat 1) =
      (((T : ℝ)⁻¹)^2 * M) • (1 : Mat 1) := by
    rw [mat1_scalar M]
    ext i j
    fin_cases i
    fin_cases j
    simp [sandwich, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply]
    <;> ring
  rw [repeatedL_eq, hinv, hSand, mat1_scalar (4 / (T : ℝ)^2)]
  rw [smul_smul]
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.smul_apply, Matrix.one_apply]
  change ((N : ℝ) / ((T : ℝ) * Dreal N)^2) *
      (((T : ℝ)^2)⁻¹ * M) = 4 / (T : ℝ)^2
  dsimp [M, Dreal]
  field_simp [hT0, hN0, hN1]
  ring

lemma repeatedTarget_eq (T N : ℕ) (hT : 1 ≤ T) (hN : 3 ≤ N) :
    repeatedTarget (W1IdenticalSign T) N = !![4] := by
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  have hTD : (T : ℝ) * Dreal N ≠ 0 := by
    apply mul_ne_zero hT0
    exact ne_of_gt (Dreal_pos (by omega : 2 ≤ N))
  have hvar := repeatedScoreVariance T N
  rw [repeatedTarget, repeatedH_eq T N hT hN]
  simp only [inv_one, sandwich, Matrix.one_mul, Matrix.mul_one]
  rw [repeatedBeta_eq, repeatedL_eq, repeatedScoreVariance]
  rw [mat1_scalar ((T : ℝ)^2 * (N : ℝ) * ((N : ℝ)-1)^2), mat1_scalar 4]
  rw [smul_smul]
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.smul_apply, Matrix.one_apply]
  change ((N : ℝ) / ((T : ℝ) * Dreal N)^2) *
      ((T : ℝ)^2 * (N : ℝ) * ((N : ℝ)-1)^2) = 4
  dsimp [Dreal]
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hn1 : (N : ℝ)-1 ≠ 0 := by
    have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  field_simp [hT0, hn0, hn1]
  <;> ring

end SAP.P018a.WH.W1.P.T11_L3

open SAP.P018a.WH.W1.P.T11_L3

theorem SAP.P018a.WH.W1.T11_L3_proof : SAP.P018a.WH.W1.T11_L3 := by
  intro T N hT hN
  refine ⟨repeatedL_eq T N, repeatedBeta_eq T N,
    repeatedH_eq T N hT hN, repeatedScoreVariance T N, ?_, ?_, ?_⟩
  · intro d
    exact ⟨coefficientBlockGram_eq T N d, wrongBlockGram_eq T N d⟩
  · exact wrongBread_sandwich T N hT hN
  · exact repeatedTarget_eq T N hT hN
