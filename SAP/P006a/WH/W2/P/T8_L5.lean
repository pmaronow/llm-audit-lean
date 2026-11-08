import SAP.P006a.WH.W2.Leaves
import AronowAudit.P006.Wave1.Gap.GP006B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

open SAP.P006a

theorem SAP.P006a.WH.W2.T8_L5_proof : SAP.P006a.WH.W2.T8_L5 := by
  intro Ω X U A _ _ _ _ n E PiSet π hπ hpa S Q Z f hA
  let μ := E.law π
  let C := X × U
  let Dsgn := (Fin n → X × U) × (Fin n → Bool)
  let V : Ω → Dsgn := fun ω => ((fun j => E.X j ω), (fun j => E.T π j ω))
  let φ : A × C → C × ℝ := fun z => (z.2, f (z.1, z.2.1))
  let F : A × C → ℝ := fun z => f (z.1, z.2.1)
  let gC : C → ℝ := fun c => ∫ a, f (a, c.1) ∂Q
  letI : IsProbabilityMeasure Q := hA.probability
  letI : IsProbabilityMeasure E.PX := S.px_probability
  letI : IsProbabilityMeasure μ := S.law_probability
  have hV : Measurable V := by
    dsimp [V, Dsgn]
    exact (measurable_pi_iff.mpr (fun i => (S.measurable_units i).1)).prodMk
      (measurable_pi_iff.mpr (fun i => (S.measurable_units i).2.2.2))
  have hZ : Measurable Z := hA.measurable_Z
  have hφ : Measurable φ := by
    dsimp [φ, F]
    exact measurable_snd.prodMk
      (hA.measurable_f.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  have hF : Measurable F := by
    dsimp [F]
    exact hA.measurable_f.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hJoint (i : Fin n) :
      IdentDistrib (fun ω => (Z ω, E.X i ω)) id μ (Q.prod E.PX) := by
    have hproj : Measurable (fun d : Dsgn => d.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    have hi : IndepFun Z (E.X i) μ := by
      have h := (hA.independent π hπ).comp measurable_id hproj
      change IndepFun Z ((fun d : Dsgn => d.1 i) ∘ V) μ at h
      convert h using 1 <;> funext ω <;> rfl
    have hmap := hi.map_prod_eq_prod_map_map hZ.aemeasurable
      (S.measurable_units i).1.aemeasurable
    have hZlaw : μ.map Z = Q := by
      simpa using (hA.law_Z π hπ).map_eq
    have hXlaw : μ.map (E.X i) = E.PX := by
      simpa using (S.covariate_law i).map_eq
    rw [hZlaw, hXlaw] at hmap
    exact ⟨(hZ.prodMk (S.measurable_units i).1).aemeasurable,
      measurable_id.aemeasurable, by simpa using hmap⟩
  have hEvalLaw (i : Fin n) :
      IdentDistrib (fun ω => (E.X i ω, E.μhat π ω (E.X i ω))) id μ
        (SAP.P006a.AuxiliaryLawW2 E Q f) := by
    have hcmp := (hJoint i).comp hφ
    have heval : (fun ω => (E.X i ω, E.μhat π ω (E.X i ω))) =
        (fun ω => φ (Z ω, E.X i ω)) := by
      funext ω
      dsimp [φ]
      congr 1
      exact hA.representation π hπ ω (E.X i ω)
    have hmap : μ.map (fun ω => (E.X i ω, E.μhat π ω (E.X i ω))) =
        SAP.P006a.AuxiliaryLawW2 E Q f := by
      calc
        μ.map (fun ω => (E.X i ω, E.μhat π ω (E.X i ω))) =
            μ.map (fun ω => φ (Z ω, E.X i ω)) :=
          Measure.map_congr (Eventually.of_forall fun ω => congrFun heval ω)
        _ = (Q.prod E.PX).map φ := by
          change μ.map (φ ∘ (fun ω => (Z ω, E.X i ω))) =
            (Q.prod E.PX).map (φ ∘ id)
          exact hcmp.map_eq
        _ = SAP.P006a.AuxiliaryLawW2 E Q f := rfl
    exact ⟨hcmp.aemeasurable_fst.congr
        (Eventually.of_forall fun ω => (congrFun heval ω).symm),
      measurable_id.aemeasurable, by simpa using hmap⟩
  have hD : IsProbabilityMeasure (SAP.P006a.AuxiliaryLawW2 E Q f) := by
    change IsProbabilityMeasure ((Q.prod E.PX).map φ)
    infer_instance
  refine ⟨hD, ?_, ?_⟩
  · intro i
    exact hEvalLaw i
  · intro hEvalInt
    intro i
    let t : Ω → ℝ := fun ω => bit (E.T π i ω)
    let p : Ω → ℝ := fun ω => π (E.X i ω)
    let g : Dsgn → ℝ := fun d => gC (d.1 i)
    let H : Ω → ℝ := fun ω => E.μhat π ω (E.X i ω)
    let FV : A × Dsgn → ℝ := fun z => f (z.1, (z.2.1 i).1)
    have hHint : Integrable H μ := by
      simpa [H, μ] using hEvalInt i
    have hXiV : Measurable[MeasurableSpace.comap V
        (inferInstance : MeasurableSpace Dsgn)] (E.X i) := by
      change Measurable[MeasurableSpace.comap V
        (inferInstance : MeasurableSpace Dsgn)] (E.X i)
      convert ((measurable_pi_apply i).comp measurable_fst).comp
        (comap_measurable V) using 1 <;> funext ω <;> rfl
    have hsmall : E.covariateSigma i ≤ E.vectorSigma π := by
      change MeasurableSpace.comap (E.X i) _ ≤
        MeasurableSpace.comap (fun ω => ((fun j => E.X j ω), (fun j => E.T π j ω))) _
      exact hXiV.comap_le
    have hVle : E.vectorSigma π ≤ (inferInstance : MeasurableSpace Ω) := by
      simpa only [SAP.P006a.Experiment.vectorSigma, V] using hV.comap_le
    have hIndV : IndepFun Z V μ := by
      simpa [V] using hA.independent π hπ
    have hFV : Measurable FV := by
      dsimp [FV]
      have hpub : Measurable (fun z : A × Dsgn => (z.2.1 i).1) :=
        measurable_fst.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_snd))
      exact hA.measurable_f.comp (measurable_fst.prodMk hpub)
    have hgCsm : StronglyMeasurable gC := by
      dsimp [gC]
      exact (hA.measurable_f.comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).stronglyMeasurable
        |>.integral_prod_left'
    have hgCmeas : Measurable gC := hgCsm.measurable
    have hgV : Measurable g := by
      dsimp [g]
      exact hgCmeas.comp ((measurable_pi_apply i).comp measurable_fst)
    have hgCi : StronglyMeasurable[E.covariateSigma i]
        (fun ω => gC (E.X i ω)) := by
      exact (hgCmeas.comp (comap_measurable (E.X i))).stronglyMeasurable
    have hgi : Integrable (fun ω => g (V ω)) μ := by
      have hProd : Integrable F (Q.prod E.PX) := by
        have hID := (hJoint i).comp hF
        have hH : Integrable (fun ω => F (Z ω, E.X i ω)) μ := by
          have heq : (fun ω => F (Z ω, E.X i ω)) = H := by
            funext ω
            simp [F, H]
            exact (hA.representation π hπ ω (E.X i ω)).symm
          exact hHint.congr (Eventually.of_forall fun ω => (congrFun heq ω).symm)
        have h := hID.integrable_iff.mp hH
        simpa [Function.comp_def] using h
      have hgCint : Integrable gC E.PX := by
        exact hProd.integral_prod_right
      have hcov := ((S.covariate_law i).comp hgCmeas).integrable_iff.mpr hgCint
      change Integrable (fun ω => gC (E.X i ω)) (E.law π) at hcov
      simpa [μ] using hcov
    have hHrep : (fun ω => FV (Z ω, V ω)) = H := by
      funext ω
      simp [FV, V, H]
      exact (hA.representation π hπ ω (E.X i ω)).symm
    have hFi : Integrable (fun ω => FV (Z ω, V ω)) μ := by
      rw [hHrep]
      exact hHint
    have hmean (d : Dsgn) :
        (∫ a, FV (a, d) ∂μ.map Z) = g d := by
      have hZlaw : μ.map Z = Q := by
        simpa using (hA.law_Z π hπ).map_eq
      rw [hZlaw]
    have hce := AronowAudit.P006.Wave1.RepairT6T7_auxiliary_condExp
      μ Z V hZ hV hIndV FV g hFV hgV hFi hgi hmean
    have hHceV : μ[H | E.vectorSigma π] =ᵐ[μ] (fun ω => gC (E.X i ω)) := by
      rw [hHrep] at hce
      simpa only [SAP.P006a.Experiment.vectorSigma, g, V] using hce
    have htV : StronglyMeasurable[E.vectorSigma π] t := by
      have htMeasV : Measurable[E.vectorSigma π] (fun ω => E.T π i ω) := by
        change Measurable[MeasurableSpace.comap V
          (inferInstance : MeasurableSpace Dsgn)] (fun ω => E.T π i ω)
        convert ((measurable_pi_apply i).comp measurable_snd).comp
          (comap_measurable V) using 1 <;> funext ω <;> rfl
      dsimp [t]
      exact ((measurable_of_countable bit).comp htMeasV).stronglyMeasurable
    have hpX : StronglyMeasurable[E.covariateSigma i] p := by
      dsimp [p, SAP.P006a.Experiment.covariateSigma]
      exact (hpa.1.comp (comap_measurable (E.X i))).stronglyMeasurable
    have hHceX : μ[H | E.covariateSigma i] =ᵐ[μ] (fun ω => gC (E.X i ω)) := by
      have htower := condExp_condExp_of_le (μ := μ) (f := H) hsmall hVle
      have hXle : E.covariateSigma i ≤ (inferInstance : MeasurableSpace Ω) :=
        hsmall.trans hVle
      calc
        μ[H | E.covariateSigma i] =ᵐ[μ]
            μ[μ[H | E.vectorSigma π] | E.covariateSigma i] := htower.symm
        _ =ᵐ[μ] μ[(fun ω => gC (E.X i ω)) | E.covariateSigma i] :=
          condExp_congr_ae hHceV
        _ =ᵐ[μ] (fun ω => gC (E.X i ω)) := by
          have h := condExp_of_stronglyMeasurable (μ := μ) hXle hgCi (by
            simpa [g, V] using hgi)
          exact Eventually.of_forall fun ω => congrFun h ω
    have ht : Measurable (fun ω => E.T π i ω) := (S.measurable_units i).2.2.2
    have htH : Integrable (fun ω => t ω * H ω) μ := by
      exact AronowAudit.P006.Wave1.T7_bit_mul ht hHint
    have hpH : Integrable (fun ω => p ω * H ω) μ := by
      have hpub : Measurable (fun ω => π (E.X i ω)) := hpa.1.comp (S.measurable_units i).1
      have hpBound : ∀ ω, ‖p ω‖ ≤ 1 := by
        intro ω
        dsimp [p]
        rw [abs_of_nonneg (hpa.2 (E.X i ω)).1]
        exact (hpa.2 (E.X i ω)).2
      exact hHint.bdd_mul hpub.aestronglyMeasurable
        (ae_of_all _ hpBound)
    have htInt : Integrable t μ := by
      have h := AronowAudit.P006.Wave1.T7_bit_mul ht
        (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
      simpa [t, SAP.P006a.bit, AronowAudit.P006.bit] using h
    have hcoin : μ[t | E.covariateSigma i] =ᵐ[μ] p := by
      simpa [t, p, SAP.P006a.Experiment.covariateSigma] using S.bernoulli i
    have hTHceV : μ[(fun ω => t ω * H ω) | E.vectorSigma π] =ᵐ[μ]
        (fun ω => t ω * gC (E.X i ω)) := by
      have h := condExp_mul_of_stronglyMeasurable_left htV htH hHint
      filter_upwards [h, hHceV] with ω h₁ h₂
      have h₁' : μ[(fun η => t η * H η) | E.vectorSigma π] ω =
          t ω * μ[H | E.vectorSigma π] ω := by
        change μ[(fun η => bit (E.T π i η) * H η) | E.vectorSigma π] ω =
          bit (E.T π i ω) * μ[H | E.vectorSigma π] ω at h₁
        simpa [t] using h₁
      exact h₁'.trans (congrArg (fun x => t ω * x) h₂)
    have hTHceX : μ[(fun ω => t ω * H ω) | E.covariateSigma i] =ᵐ[μ]
        (fun ω => p ω * gC (E.X i ω)) := by
      have htower := condExp_condExp_of_le (μ := μ)
        (f := fun ω => t ω * H ω) hsmall hVle
      have hgCiInt : Integrable (fun ω => gC (E.X i ω)) μ := by
        simpa [g, V] using hgi
      have htG : Integrable (fun ω => t ω * gC (E.X i ω)) μ := by
        exact AronowAudit.P006.Wave1.T7_bit_mul ht hgCiInt
      have hpull := condExp_mul_of_stronglyMeasurable_right hgCi htG htInt
      calc
        μ[(fun ω => t ω * H ω) | E.covariateSigma i] =ᵐ[μ]
            μ[μ[(fun ω => t ω * H ω) | E.vectorSigma π] | E.covariateSigma i] := htower.symm
        _ =ᵐ[μ] μ[(fun ω => t ω * gC (E.X i ω)) | E.covariateSigma i] :=
          condExp_congr_ae hTHceV
        _ =ᵐ[μ] (fun ω => μ[t | E.covariateSigma i] ω * gC (E.X i ω)) := hpull
        _ =ᵐ[μ] (fun ω => p ω * gC (E.X i ω)) := by
          filter_upwards [hcoin] with ω hω
          exact congrArg (fun x => x * gC (E.X i ω)) hω
    have hPHceX : μ[(fun ω => p ω * H ω) | E.covariateSigma i] =ᵐ[μ]
        (fun ω => p ω * gC (E.X i ω)) := by
      have hpull := condExp_mul_of_stronglyMeasurable_left hpX hpH hHint
      filter_upwards [hpull, hHceX] with ω h₁ h₂
      exact h₁.trans (congrArg (fun x => p ω * x) h₂)
    have hdiff : (fun ω => (t ω - p ω) * H ω) =
        (fun ω => t ω * H ω - p ω * H ω) := by
      funext ω
      ring
    refine ⟨?_, ?_, ?_⟩
    · simpa [t, H, μ] using htH
    · simpa [p, H, μ] using hpH
    · change μ[(fun ω => (t ω - p ω) * H ω) | E.covariateSigma i] =ᵐ[μ]
        (fun _ => (0 : ℝ))
      rw [hdiff]
      have hsub := condExp_sub htH hpH (E.covariateSigma i)
      filter_upwards [hsub, hTHceX, hPHceX] with ω hs h₁ h₂
      simp only [Pi.sub_apply] at hs
      rw [h₁, h₂] at hs
      simp at hs
      exact hs

