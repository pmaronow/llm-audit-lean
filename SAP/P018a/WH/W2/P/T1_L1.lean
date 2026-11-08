import SAP.P018a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P018a.WH.W2.P.T1_L1

open MeasureTheory Matrix ProbabilityTheory
open scoped BigOperators

theorem nonlinear_row_conditional (N : ℕ) (_hN : 3 ≤ N) (d : Dyad N) :
    MeasureTheory.condExp (wholeRowSigma nonlinearKernel d) (unitSampleLaw nonlinearKernel N)
      (fun ω => response nonlinearKernel ω d) =ᵐ[unitSampleLaw nonlinearKernel N]
        (fun ω => (design nonlinearKernel ω d 1 - 2)^2) := by
  let μ := unitSampleLaw nonlinearKernel N
  have hKA : AronowAudit.P018.Standing AronowAudit.P018.nonlinearKernel :=
    AronowAudit.P018.nonlinear_model_assumptions
  have hK : Standing nonlinearKernel := by
    apply (SAP.P018a.Bridge.kernel_assumptions_agree nonlinearKernel).mpr
    change AronowAudit.P018.Standing AronowAudit.P018.nonlinearKernel
    exact hKA
  letI : IsProbabilityMeasure nonlinearKernel.μ := hK.1
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, unitSampleLaw]
    infer_instance
  have hdesign : Measurable (design nonlinearKernel : (Fin N → ℝ) → Dyad N → Vec 2) := by
    apply Measurable.of_eval
    intro q
    have hp : Measurable (fun ω : Fin N → ℝ => (ω (firstUnit q), ω (secondUnit q))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact hK.2.1.comp hp
  have hle : wholeRowSigma nonlinearKernel d ≤ (inferInstance : MeasurableSpace (Fin N → ℝ)) := by
    exact ((measurable_pi_apply d).comp hdesign).comap_le
  have hrow : Measurable[wholeRowSigma nonlinearKernel d]
      (design nonlinearKernel · d) := comap_measurable _
  have hx : Measurable[wholeRowSigma nonlinearKernel d]
      (fun ω : Fin N → ℝ => design nonlinearKernel ω d 1) :=
    (measurable_pi_apply 1).comp hrow
  have heq : (fun ω : Fin N → ℝ => response nonlinearKernel ω d) =
      (fun ω => (design nonlinearKernel ω d 1 - 2)^2) := by
    funext ω
    simp [response, design, nonlinearKernel]
    ring
  have hs : StronglyMeasurable[wholeRowSigma nonlinearKernel d]
      (fun ω : Fin N → ℝ => response nonlinearKernel ω d) := by
    rw [heq]
    exact ((hx.sub_const 2).pow_const 2).stronglyMeasurable
  have hi : Integrable (fun ω : Fin N → ℝ => response nonlinearKernel ω d) μ := by
    have hp := AronowAudit.P018.Wave1.corrected_pair_preserving
      AronowAudit.P018.nonlinearKernel d
    obtain ⟨C, hC, hbound⟩ := hKA.2.2.2.2.1
    have hbpair := hp.quasiMeasurePreserving.ae hbound
    have hbω : ∀ᵐ ω ∂ μ, |response nonlinearKernel ω d| ≤ C := by
      have hbpair' := hbpair.mono fun ω hω => hω.2
      simpa [μ, SAP.P018a.unitSampleLaw, AronowAudit.P018.unitSampleLaw,
        SAP.P018a.nonlinearKernel, AronowAudit.P018.nonlinearKernel,
        SAP.P018a.uniformUnitLaw, AronowAudit.P018.uniformUnitLaw,
        SAP.P018a.firstUnit, AronowAudit.P018.firstUnit,
        SAP.P018a.secondUnit, AronowAudit.P018.secondUnit,
        SAP.P018a.members, AronowAudit.P018.members,
        SAP.P018a.response, AronowAudit.P018.response,
        SAP.P018a.design, AronowAudit.P018.design] using hbpair'
    have hmeas : Measurable (fun ω : Fin N → ℝ => response nonlinearKernel ω d) := by
      have hpair : Measurable (fun ω : Fin N → ℝ =>
          (ω (firstUnit d), ω (secondUnit d))) :=
        (measurable_pi_apply _).prodMk (measurable_pi_apply _)
      have hY : Measurable (fun uv : ℝ × ℝ => nonlinearKernel.Y uv.1 uv.2) :=
        hK.2.2.1
      exact hY.comp (by simpa [SAP.P018a.response, SAP.P018a.design] using hpair)
    have hmem : MemLp (fun ω : Fin N → ℝ => response nonlinearKernel ω d) 2 μ :=
      MemLp.of_bound hmeas.aestronglyMeasurable C hbω
    exact hmem.integrable one_le_two
  have hcond := condExp_of_stronglyMeasurable hle hs hi
  filter_upwards [] with ω
  calc
    _ = response nonlinearKernel ω d := congrFun hcond ω
    _ = (design nonlinearKernel ω d 1 - 2)^2 := congrFun heq ω

theorem no_affine_representation :
    ¬ (∃ b : Vec 2, ∀ᵐ uv ∂ uniformUnitLaw.prod uniformUnitLaw,
      nonlinearKernel.Y uv.1 uv.2 = dot (nonlinearKernel.X uv.1 uv.2) b) := by
  change ¬ (∃ b : AronowAudit.P018.Vec 2,
    ∀ᵐ uv ∂ AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw,
      AronowAudit.P018.nonlinearKernel.Y uv.1 uv.2 =
        AronowAudit.P018.dot (AronowAudit.P018.nonlinearKernel.X uv.1 uv.2) b)
  rintro ⟨b, hb⟩
  let μ := AronowAudit.P018.uniformUnitLaw.prod AronowAudit.P018.uniformUnitLaw
  let hK : AronowAudit.P018.Standing AronowAudit.P018.nonlinearKernel :=
    AronowAudit.P018.nonlinear_model_assumptions
  letI : IsProbabilityMeasure AronowAudit.P018.nonlinearKernel.μ := hK.1
  have hproj := AronowAudit.P018.nonlinear_population_projection
  have hproducts := AronowAudit.P018.Wave1.corrected_pair_products
    AronowAudit.P018.nonlinearKernel hK
  have hnormal :
      (AronowAudit.P018.populationGram AronowAudit.P018.nonlinearKernel).mulVec b =
      AronowAudit.P018.meanVec μ (fun uv => AronowAudit.P018.score
        (AronowAudit.P018.nonlinearKernel.X uv.1 uv.2)
        (AronowAudit.P018.nonlinearKernel.Y uv.1 uv.2)) := by
    ext j
    change (∑ l : Fin 2, (∫ uv : ℝ × ℝ,
        AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 j *
          AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 l ∂ μ) * b l) =
      ∫ uv : ℝ × ℝ, AronowAudit.P018.score
        (AronowAudit.P018.nonlinearKernel.X uv.1 uv.2)
        (AronowAudit.P018.nonlinearKernel.Y uv.1 uv.2) j ∂ μ
    have hae : (fun uv : ℝ × ℝ =>
        AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 j *
          AronowAudit.P018.nonlinearKernel.Y uv.1 uv.2) =ᵐ[μ]
        (fun uv => AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 j *
          AronowAudit.P018.dot (AronowAudit.P018.nonlinearKernel.X uv.1 uv.2) b) :=
      hb.mono (fun uv huv => by
        change AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 j *
          AronowAudit.P018.nonlinearKernel.Y uv.1 uv.2 = _
        rw [huv])
    have hterms : ∀ l : Fin 2, Integrable (fun uv : ℝ × ℝ =>
        (AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 j *
          AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 l) * b l) μ :=
      fun l => by
        simpa [μ, AronowAudit.P018.nonlinearKernel,
          mul_comm, mul_left_comm, mul_assoc] using
          (hproducts.1 j l).const_mul (b l)
    calc
      _ = ∑ l : Fin 2, ∫ uv : ℝ × ℝ,
          (AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 j *
            AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 l) * b l ∂ μ := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [integral_mul_const]
      _ = ∫ uv : ℝ × ℝ, ∑ l : Fin 2,
          (AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 j *
            AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 l) * b l ∂ μ := by
        symm
        exact integral_finset_sum Finset.univ (fun l hl => hterms l)
      _ = ∫ uv : ℝ × ℝ, AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 j *
          AronowAudit.P018.dot (AronowAudit.P018.nonlinearKernel.X uv.1 uv.2) b ∂ μ := by
        congr 1
        funext uv
        simp only [AronowAudit.P018.dot]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = ∫ uv : ℝ × ℝ, AronowAudit.P018.nonlinearKernel.X uv.1 uv.2 j *
          AronowAudit.P018.nonlinearKernel.Y uv.1 uv.2 ∂ μ := integral_congr_ae hae.symm
      _ = ∫ uv : ℝ × ℝ, AronowAudit.P018.score
          (AronowAudit.P018.nonlinearKernel.X uv.1 uv.2)
          (AronowAudit.P018.nonlinearKernel.Y uv.1 uv.2) j ∂ μ := by
        congr 1
        funext uv
        simp [AronowAudit.P018.score, smul_eq_mul, mul_comm]
  have hQb : AronowAudit.P018.nonlinearQ.mulVec b = ![2/3,4/3] := by
    rw [← hproj.1, hnormal, hproj.2.1]
  have hQdet : AronowAudit.P018.nonlinearQ.det ≠ 0 := by
    rw [hproj.2.2.1]
    norm_num
  have hbeta : AronowAudit.P018.populationBeta AronowAudit.P018.nonlinearKernel = ![2/3,0] :=
    hproj.2.2.2
  have hQbeta : AronowAudit.P018.nonlinearQ.mulVec
      (AronowAudit.P018.populationBeta AronowAudit.P018.nonlinearKernel) = ![2/3,4/3] := by
    rw [hbeta]
    ext j
    fin_cases j <;>
      norm_num [AronowAudit.P018.nonlinearQ, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ]
  have hbβ : b = AronowAudit.P018.populationBeta AronowAudit.P018.nonlinearKernel := by
    apply Matrix.mulVec_injective_of_det_ne_zero hQdet
    rw [hQb, hQbeta]
  have hAeY : (fun uv : ℝ × ℝ =>
      AronowAudit.P018.nonlinearKernel.Y uv.1 uv.2) =ᵐ[μ]
      (fun uv => AronowAudit.P018.dot
        (AronowAudit.P018.nonlinearKernel.X uv.1 uv.2)
        (AronowAudit.P018.populationBeta AronowAudit.P018.nonlinearKernel)) := by
    filter_upwards [hb] with uv huv
    rw [← hbβ, huv]
  have hscore := AronowAudit.P018.Wave1.GP0182B2b_score_memLp
    AronowAudit.P018.nonlinearKernel hK 0 2
  have hsq : Integrable (fun uv : ℝ × ℝ =>
      (AronowAudit.P018.populationScore AronowAudit.P018.nonlinearKernel uv.1 uv.2 0)^2) μ :=
    hscore.integrable_sq
  have hH := AronowAudit.P018.Wave1.nonlinear_counterexample_proof
  have hH00 : AronowAudit.P018.scoreH AronowAudit.P018.nonlinearKernel 0 0 = 28/45 := by
    rw [hH.2.2.2.2.2.1]
    norm_num [AronowAudit.P018.nonlinearH]
  have hIntegral : (∫ uv : ℝ × ℝ,
      (AronowAudit.P018.populationScore AronowAudit.P018.nonlinearKernel uv.1 uv.2 0)^2 ∂ μ) =
      28/45 := by
    calc
      _ = ∫ uv : ℝ × ℝ, AronowAudit.P018.outer
          (AronowAudit.P018.populationScore AronowAudit.P018.nonlinearKernel uv.1 uv.2)
          (AronowAudit.P018.populationScore AronowAudit.P018.nonlinearKernel uv.1 uv.2) 0 0 ∂ μ := by
        congr 1
        funext uv
        simp [AronowAudit.P018.outer, pow_two]
      _ = AronowAudit.P018.scoreH AronowAudit.P018.nonlinearKernel 0 0 := rfl
      _ = 28/45 := hH00
  have hz : (fun uv : ℝ × ℝ =>
      AronowAudit.P018.populationScore AronowAudit.P018.nonlinearKernel uv.1 uv.2 0) =ᵐ[μ]
      (fun _ => 0) := by
    filter_upwards [hAeY] with uv huv
    simp [AronowAudit.P018.populationScore, AronowAudit.P018.populationResidual,
      AronowAudit.P018.score, huv]
  have hzero : (∫ uv : ℝ × ℝ,
      (AronowAudit.P018.populationScore AronowAudit.P018.nonlinearKernel uv.1 uv.2 0)^2 ∂ μ) =
      0 := by
    have hz2 : (fun uv : ℝ × ℝ =>
        (AronowAudit.P018.populationScore AronowAudit.P018.nonlinearKernel uv.1 uv.2 0)^2) =ᵐ[μ]
        (fun _ => 0) := hz.mono fun uv huv => by simp [huv]
    calc
      _ = ∫ _uv : ℝ × ℝ, (0 : ℝ) ∂ μ := integral_congr_ae hz2
      _ = 0 := by simp
  linarith

end SAP.P018a.WH.W2.P.T1_L1

theorem SAP.P018a.WH.W2.T1_L1_proof : SAP.P018a.WH.W2.T1_L1 := by
  change SAP.P018a.T1Conditional
  constructor
  · intro N hN d
    exact SAP.P018a.WH.W2.P.T1_L1.nonlinear_row_conditional N hN d
  · exact SAP.P018a.WH.W2.P.T1_L1.no_affine_representation
