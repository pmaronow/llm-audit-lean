import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W1.P.T11_L2

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Topology BoundedContinuousFunction
open AronowAudit.P018
open AronowAudit.P018.Wave1
open scoped BigOperators Matrix.Norms.Elementwise ENNReal

-- The cited donor modules live over AronowAudit.P018's copy of the sample
-- definitions.  Local aliases keep this helper in that same copy despite the
-- similarly named SAP.P018a definitions in the parent namespace.
export AronowAudit.P018 (Vec Mat Dyad dyads members members_card firstUnit secondUnit
  signValue signKernel design response dot outer score unitScore dyadMeat meat sandwich
  sampleGram sampleVariance sampleOLS fittedResidual Dreal)

/-- The exact fitted sandwich identity remains valid at the boundary N=3.
The algebra uses only the nonsingularity condition N ≥ 2; in the resulting meat
formula the factor N-3 forces the meat to vanish at N=3. -/
lemma scaled_sample_formula {N : ℕ} (hN : 3 ≤ N) (ω : Fin N → Bool) :
    (N : ℝ) * (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 =
      (4 * ((N : ℝ)-2) * ((N : ℝ)-3) / ((N : ℝ)-1)^2) *
        (1 - (printed_S ω / (N : ℝ))^2) := by
  classical
  have hN2 : 2 ≤ N := by omega
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
  let v : Fin N → ℝ := fun i => signValue (ω i) - printed_S ω / (N : ℝ)
  have hvsum : (∑ i, v i) = 0 := by
    dsimp [v]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change printed_S ω - (N : ℝ) * (printed_S ω / (N : ℝ)) = 0
    field_simp [hn0] <;> ring
  have hvsq : (∑ i, (v i)^2) = (N : ℝ) - (printed_S ω)^2 / (N : ℝ) := by
    have he (i : Fin N) : (v i)^2 = (signValue (ω i))^2 -
        2 * (printed_S ω / (N : ℝ)) * signValue (ω i) + (printed_S ω / (N : ℝ))^2 := by
      dsimp [v]
      ring
    have hs (i : Fin N) : (signValue (ω i))^2 = 1 :=
      AronowAudit.P018.Wave1.printed_sign_square (ω i)
    simp_rw [he, hs]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, mul_one]
    change (N : ℝ) - 2 * (printed_S ω / (N : ℝ)) * printed_S ω +
      (N : ℝ) * (printed_S ω / (N : ℝ))^2 = _
    field_simp [hn0]
    <;> ring
  have he (d : Dyad N) : fittedResidual (design signKernel ω) (response signKernel ω) d =
      v (firstUnit d) + v (secondUnit d) := by
    simp only [fittedResidual, dot, Fin.sum_univ_one]
    rw [AronowAudit.P018.Wave1.printed_fit hN2 ω]
    simp [response, design, signKernel, v] <;> ring
  let q : Dyad N → Vec 1 := fun d => score (design signKernel ω d)
    (fittedResidual (design signKernel ω) (response signKernel ω) d)
  have hq (d : Dyad N) : q d 0 = v (firstUnit d) + v (secondUnit d) := by
    simp only [q, score, Pi.smul_apply, smul_eq_mul, he]
    simp [design, signKernel]
  have hu (i : Fin N) : unitScore members q i 0 = ((N : ℝ)-2) * v i := by
    simp only [unitScore, Finset.sum_apply, ite_apply, Pi.zero_apply, hq]
    rw [AronowAudit.P018.Wave1.printed_incident_add v i, hvsum, add_zero]
  have hm : meat members q =
      (∑ i, outer (unitScore members q i) (unitScore members q i)) - dyadMeat q :=
    AronowAudit.P018.overlap_meat_identity members members_card (fun d e h => Subtype.ext h) q
  have hm00 : meat members q 0 0 =
      ((N : ℝ)-2) * ((N : ℝ)-3) * ((N : ℝ) - (printed_S ω)^2 / (N : ℝ)) := by
    rw [hm]
    simp only [Matrix.sub_apply, Matrix.sum_apply, outer, Matrix.of_apply, hu,
      dyadMeat, hq]
    have hsquare := AronowAudit.P018.Wave1.printed_pair_square v
    rw [hvsum, zero_pow (by decide : 2 ≠ 0), add_zero] at hsquare
    have hterm (i : Fin N) : (((N : ℝ)-2) * v i) * (((N : ℝ)-2) * v i) =
        ((N : ℝ)-2)^2 * (v i)^2 := by ring
    have hedge (d : Dyad N) :
        (v (firstUnit d) + v (secondUnit d)) * (v (firstUnit d) + v (secondUnit d)) =
          (v (firstUnit d) + v (secondUnit d))^2 := by ring
    simp_rw [hterm, hedge, ← Finset.mul_sum]
    rw [hsquare, hvsq]
    ring
  change (N : ℝ) * sandwich (sampleGram (design signKernel ω))⁻¹ (meat members q) 0 0 = _
  rw [AronowAudit.P018.Wave1.printed_gram_inv hN2 ω]
  simp only [sandwich, Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply,
    Matrix.one_apply, if_true, smul_eq_mul]
  rw [hm00]
  dsimp [Dreal]
  field_simp [hn0, hn1]
  <;> ring

lemma sample_variance_agrees (N : ℕ) (ω : Fin N → Bool) :
    SAP.P018a.sampleVariance SAP.P018a.members
      (SAP.P018a.design SAP.P018a.signKernel ω)
      (SAP.P018a.response SAP.P018a.signKernel ω) =
    AronowAudit.P018.sampleVariance AronowAudit.P018.members
      (AronowAudit.P018.design AronowAudit.P018.signKernel ω)
      (AronowAudit.P018.response AronowAudit.P018.signKernel ω) := by
  rfl

lemma sample_law_agrees (N : ℕ) :
    SAP.P018a.unitSampleLaw SAP.P018a.signKernel N =
      AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N := by
  rfl

lemma sign_mean_agrees {N : ℕ} (hN : 3 ≤ N) (ω : Fin N → Bool) :
    SAP.P018a.W1SignMean ω =
      AronowAudit.P018.Wave1.printed_S ω / (N : ℝ) := by
  have hn0 : (N : ℝ) ≠ 0 := by
    have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold SAP.P018a.W1SignMean AronowAudit.P018.Wave1.printed_S
  change (N : ℝ)⁻¹ * ∑ i, AronowAudit.P018.signValue (ω i) =
    (∑ i, AronowAudit.P018.signValue (ω i)) / (N : ℝ)
  field_simp [hn0]
  <;> ring

end SAP.P018a.WH.W1.P.T11_L2

theorem SAP.P018a.WH.W1.T11_L2_proof : SAP.P018a.WH.W1.T11_L2 := by
  intro N hN
  constructor
  · intro ω
    by_cases h4 : 4 ≤ N
    · change (N : ℝ) * SAP.P018a.sampleVariance SAP.P018a.members
        (SAP.P018a.design SAP.P018a.signKernel ω)
        (SAP.P018a.response SAP.P018a.signKernel ω) 0 0 =
        (4 * ((N : ℝ)-2) * ((N : ℝ)-3) / ((N : ℝ)-1)^2) *
          (1 - (SAP.P018a.W1SignMean ω)^2)
      rw [SAP.P018a.WH.W1.P.T11_L2.sample_variance_agrees,
        SAP.P018a.WH.W1.P.T11_L2.sign_mean_agrees hN ω]
      exact AronowAudit.P018.Wave1.printed_scaled_sandwich h4 ω
    · have h3 : N = 3 := by omega
      subst N
      change (3 : ℝ) * SAP.P018a.sampleVariance SAP.P018a.members
        (SAP.P018a.design SAP.P018a.signKernel ω)
        (SAP.P018a.response SAP.P018a.signKernel ω) 0 0 =
        (4 * ((3 : ℝ)-2) * ((3 : ℝ)-3) / ((3 : ℝ)-1)^2) *
          (1 - (SAP.P018a.W1SignMean ω)^2)
      rw [SAP.P018a.WH.W1.P.T11_L2.sample_variance_agrees,
        SAP.P018a.WH.W1.P.T11_L2.sign_mean_agrees hN ω]
      exact SAP.P018a.WH.W1.P.T11_L2.scaled_sample_formula hN ω
  · by_cases h4 : 4 ≤ N
    · change (∫ ω, (N : ℝ) *
        (SAP.P018a.sampleVariance SAP.P018a.members
          (SAP.P018a.design SAP.P018a.signKernel ω)
          (SAP.P018a.response SAP.P018a.signKernel ω)) 0 0
        ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) = _
      have hvar (ω : Fin N → Bool) :
          SAP.P018a.sampleVariance SAP.P018a.members
            (SAP.P018a.design SAP.P018a.signKernel ω)
            (SAP.P018a.response SAP.P018a.signKernel ω) 0 0 =
          AronowAudit.P018.sampleVariance AronowAudit.P018.members
            (AronowAudit.P018.design AronowAudit.P018.signKernel ω)
            (AronowAudit.P018.response AronowAudit.P018.signKernel ω) 0 0 :=
        congrArg (fun M : SAP.P018a.Mat 1 => M 0 0)
          (SAP.P018a.WH.W1.P.T11_L2.sample_variance_agrees N ω)
      simp_rw [hvar]
      rw [SAP.P018a.WH.W1.P.T11_L2.sample_law_agrees N]
      rw [MeasureTheory.integral_const_mul,
        AronowAudit.P018.Wave1.appendixB_variance_mean h4]
      have hn0 : (N : ℝ) ≠ 0 := by
        have hn : (4 : ℝ) ≤ N := by exact_mod_cast h4
        linarith
      field_simp [hn0]
      <;> ring
    · have h3 : N = 3 := by omega
      subst N
      have hz (ω : Fin 3 → Bool) : SAP.P018a.W1ScaledSignSandwich ω = 0 := by
        change (3 : ℝ) * SAP.P018a.sampleVariance SAP.P018a.members
          (SAP.P018a.design SAP.P018a.signKernel ω)
          (SAP.P018a.response SAP.P018a.signKernel ω) 0 0 = 0
        rw [SAP.P018a.WH.W1.P.T11_L2.sample_variance_agrees]
        calc
          (3 : ℝ) * AronowAudit.P018.sampleVariance AronowAudit.P018.members
              (AronowAudit.P018.design AronowAudit.P018.signKernel ω)
              (AronowAudit.P018.response AronowAudit.P018.signKernel ω) 0 0 =
              (4 * ((3 : ℝ)-2) * ((3 : ℝ)-3) / ((3 : ℝ)-1)^2) *
                (1 - (AronowAudit.P018.Wave1.printed_S ω / (3 : ℝ))^2) :=
            SAP.P018a.WH.W1.P.T11_L2.scaled_sample_formula hN ω
          _ = 0 := by norm_num
      have hfun : (fun ω : Fin 3 → Bool => W1ScaledSignSandwich ω) = fun _ => (0 : ℝ) :=
        funext hz
      rw [hfun, MeasureTheory.integral_const]
      simp
