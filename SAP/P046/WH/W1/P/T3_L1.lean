import SAP.P046.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

theorem SAP.P046.WH.W1.T3_L1_proof : SAP.P046.WH.W1.T3_L1 := by
  classical
  intro M hM n hn
  letI := hM.probability
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  let Q := SAP.P046.Bridge.toStudy M
  have hQ : AronowAudit.P046.ValidStudy Q := SAP.P046.Bridge.valid_to hM
  have hunitSigma : AronowAudit.P046.covariateSigma = SAP.P046.covariateSigma := rfl
  have hsampleSigma : AronowAudit.P046.sampleCovariateSigma n =
      SAP.P046.sampleCovariateSigma n := rfl
  have hhtFun : AronowAudit.P046.ht (n := n) Q = SAP.P046.ht (n := n) M := by
    funext a
    exact SAP.P046.Bridge.ht_agrees (M := M) (n := n) a
  have hmuWFun : AronowAudit.P046.muW (n := n) Q = SAP.P046.muW (n := n) M := by
    funext a
    rfl
  have hmuEq : AronowAudit.P046.mu Q = SAP.P046.mu M := rfl
  have hsum (a : SAP.P046.Sample n) :
      SAP.P046.ht M a = ∑ i, SAP.P046.wholeSummand M i a := by
    unfold SAP.P046.ht SAP.P046.wholeSummand SAP.P046.htTerm
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [div_div]
    congr 1
    ring
  have hcentreP := AronowAudit.P046.Wave1.ht_conditional_centre_proof Q hQ n hn
  have hcentre : condExp (SAP.P046.sampleCovariateSigma n) (SAP.P046.sampleLaw M n)
      (SAP.P046.ht M) =ᵐ[SAP.P046.sampleLaw M n] SAP.P046.muW M := by
    rw [← hsampleSigma]
    rw [← hhtFun, ← hmuWFun]
    exact hcentreP
  have hhtP := AronowAudit.P046.ht_unbiased Q hQ n hn
  have hht : (∫ a, SAP.P046.ht M a ∂SAP.P046.sampleLaw M n) = SAP.P046.mu M := by
    rw [← hhtFun]
    exact hhtP.trans hmuEq
  have hmuWP := AronowAudit.P046.muW_unbiased Q hQ n hn
  have hmuW : (∫ a, SAP.P046.muW M a ∂SAP.P046.sampleLaw M n) = SAP.P046.mu M := by
    rw [← hmuWFun]
    exact hmuWP.trans hmuEq
  refine ⟨hsum, ?_,
    hcentre, hht, hmuW, ?_⟩
  · intro i
    let hp := measurePreserving_eval (fun _ : Fin n => M.law) i
    have hpos := hp.quasiMeasurePreserving.ae hM.positivity
    have hxyP := AronowAudit.P046.conditional_xy_factorization Q hQ
    have hxyFun : (fun o : SAP.P046.Unit => SAP.P046.X o * SAP.P046.Y1 o) =
        (fun o : AronowAudit.P046.Unit => AronowAudit.P046.X o * AronowAudit.P046.Y1 o) := by
      funext o
      rfl
    have hxyOut : (fun o : SAP.P046.Unit => M.pi (SAP.P046.W o) * M.m (SAP.P046.W o)) =
        (fun o : AronowAudit.P046.Unit => Q.pi (AronowAudit.P046.W o) * Q.m (AronowAudit.P046.W o)) := by
      funext o
      rfl
    have hxy : condExp (SAP.P046.covariateSigma) M.law
        (fun o => SAP.P046.X o * SAP.P046.Y1 o) =ᵐ[M.law]
          fun o => M.pi (SAP.P046.W o) * M.m (SAP.P046.W o) := by
      rw [← hunitSigma, hxyFun, hxyOut]
      exact hxyP
    have hxyi := hp.quasiMeasurePreserving.ae hxy
    have hprop := hp.quasiMeasurePreserving.ae hM.propensity
    have hreg := hp.quasiMeasurePreserving.ae hM.regression
    have hfun :
        (fun a : SAP.P046.Sample n => SAP.P046.wholeSummand M i a) =ᵐ[sampleLaw M n]
          (fun a => (n : ℝ)⁻¹ *
            SAP.P046.htTerm (M.pi (SAP.P046.W (a i)))
              (SAP.P046.X (a i)) (SAP.P046.Y (a i))) := by
      filter_upwards [hpos] with a ha
      have hpi : M.pi (SAP.P046.W (a i)) ≠ 0 :=
        ne_of_gt (lt_trans hM.delta_pos ha.1)
      change SAP.P046.X (a i) * SAP.P046.Y (a i) /
        ((n : ℝ) * M.pi (SAP.P046.W (a i))) =
          (n : ℝ)⁻¹ *
            (SAP.P046.X (a i) * SAP.P046.Y (a i) /
              M.pi (SAP.P046.W (a i)))
      field_simp [hnR, hpi]
    have hscaled :
        condExp (sampleCovariateSigma n) (sampleLaw M n)
          (fun a => SAP.P046.wholeSummand M i a) =ᵐ[sampleLaw M n]
        fun a => (n : ℝ)⁻¹ * condExp (sampleCovariateSigma n) (sampleLaw M n)
          (fun b => SAP.P046.htTerm (M.pi (SAP.P046.W (b i)))
            (SAP.P046.X (b i)) (SAP.P046.Y (b i))) a := by
      calc
        _ =ᵐ[sampleLaw M n] condExp (sampleCovariateSigma n) (sampleLaw M n)
            (fun a => (n : ℝ)⁻¹ *
              SAP.P046.htTerm (M.pi (SAP.P046.W (a i)))
                (SAP.P046.X (a i)) (SAP.P046.Y (a i))) :=
          condExp_congr_ae hfun
        _ =ᵐ[sampleLaw M n] _ := by
          let f := fun a : SAP.P046.Sample n => SAP.P046.htTerm
            (M.pi (SAP.P046.W (a i))) (SAP.P046.X (a i)) (SAP.P046.Y (a i))
          have hc := condExp_smul (μ := sampleLaw M n) ((n : ℝ)⁻¹) f
              (sampleCovariateSigma n)
          have hfscal : (fun a : SAP.P046.Sample n => (n : ℝ)⁻¹ * f a) =
              (n : ℝ)⁻¹ • f := by
            funext a
            simp [smul_eq_mul]
          filter_upwards [hc] with a ha
          rw [hfscal]
          change condExp (sampleCovariateSigma n) (sampleLaw M n) ((n : ℝ)⁻¹ • f) a =
            ((n : ℝ)⁻¹ • condExp (sampleCovariateSigma n) (sampleLaw M n) f) a
          simpa [smul_eq_mul] using ha
    have hcoordP := AronowAudit.P046.Wave1.htcentre_coordinate Q hQ n i
    have hcoordFun :
        (fun a : SAP.P046.Sample n => SAP.P046.htTerm (M.pi (SAP.P046.W (a i)))
          (SAP.P046.X (a i)) (SAP.P046.Y (a i))) =
        (fun a : AronowAudit.P046.Sample n => AronowAudit.P046.htTerm
          (Q.pi (AronowAudit.P046.W (a i))) (AronowAudit.P046.X (a i))
          (AronowAudit.P046.Y (a i))) := by
      funext a
      rfl
    have hmFun : (fun a : SAP.P046.Sample n => M.m (SAP.P046.W (a i))) =
        (fun a : AronowAudit.P046.Sample n => Q.m (AronowAudit.P046.W (a i))) := by
      funext a
      rfl
    have hcoord : condExp (sampleCovariateSigma n) (sampleLaw M n)
        (fun a => SAP.P046.htTerm (M.pi (SAP.P046.W (a i)))
          (SAP.P046.X (a i)) (SAP.P046.Y (a i))) =ᵐ[sampleLaw M n]
        fun a => M.m (SAP.P046.W (a i)) := by
      rw [← hsampleSigma]
      rw [hcoordFun, hmFun]
      exact hcoordP
    have hmean :
        condExp (sampleCovariateSigma n) (sampleLaw M n)
          (fun a => SAP.P046.wholeSummand M i a) =ᵐ[sampleLaw M n]
        fun a => M.m (SAP.P046.W (a i)) / n := by
      filter_upwards [hscaled, hcoord] with a hs hc
      rw [hs, hc]
      simp [div_eq_mul_inv, mul_comm]
    filter_upwards [hmean, hxyi, hprop, hreg, hpos] with a hm hxy hprop hreg hpos
    have hpi : M.pi (SAP.P046.W (a i)) ≠ 0 :=
      ne_of_gt (lt_trans hM.delta_pos hpos.1)
    have hden : (n : ℝ) * M.pi (SAP.P046.W (a i)) ≠ 0 := mul_ne_zero hnR hpi
    refine ⟨AronowAudit.P046.consistency_treated (a i), ?_, ?_, ?_⟩
    · rw [hm, hxy]
      field_simp [hnR, hpi]
    · rw [hxy, hprop, hreg]
    · rw [hprop, hreg]
      field_simp [hnR, hpi]
  · intro i
    let hp := measurePreserving_eval (fun _ : Fin n => M.law) i
    have hf : AEStronglyMeasurable (fun o : SAP.P046.Unit => M.m (SAP.P046.W o)) M.law :=
      (hM.measurable_m.comp measurable_fst).aestronglyMeasurable
    have hmap := hp.map_eq
    have hfmap : AEStronglyMeasurable (fun o : SAP.P046.Unit => M.m (SAP.P046.W o))
        (Measure.map (fun a : SAP.P046.Sample n => a i) (SAP.P046.sampleLaw M n)) := by
      change AEStronglyMeasurable (fun o : SAP.P046.Unit => M.m (SAP.P046.W o))
        (Measure.map (Function.eval i) (Measure.pi (fun _ : Fin n => M.law)))
      rw [hmap]
      exact hf
    calc
      (∫ a : SAP.P046.Sample n, M.m (SAP.P046.W (a i)) ∂SAP.P046.sampleLaw M n) =
          ∫ o : SAP.P046.Unit, M.m (SAP.P046.W o) ∂
            Measure.map (fun a : SAP.P046.Sample n => a i) (SAP.P046.sampleLaw M n) := by
        change (∫ a : Fin n → SAP.P046.Unit,
          M.m (SAP.P046.W (a i)) ∂Measure.pi (fun _ : Fin n => M.law)) =
          ∫ o : SAP.P046.Unit, M.m (SAP.P046.W o) ∂
            Measure.map (Function.eval i) (Measure.pi (fun _ : Fin n => M.law))
        exact (integral_map hp.measurable.aemeasurable hfmap).symm
      _ = ∫ o : SAP.P046.Unit, M.m (SAP.P046.W o) ∂M.law := by
        change (∫ o : SAP.P046.Unit, M.m (SAP.P046.W o) ∂
          Measure.map (Function.eval i) (Measure.pi (fun _ : Fin n => M.law))) = _
        rw [hmap]
      _ = SAP.P046.mu M := by
        have hmeanP := AronowAudit.P046.regression_mean Q hQ
        have hmFun : (fun o : SAP.P046.Unit => M.m (SAP.P046.W o)) =
            (fun o : AronowAudit.P046.Unit => Q.m (AronowAudit.P046.W o)) := by
          funext o
          rfl
        rw [hmFun, ← hmuEq, show M.law = Q.law by rfl]
        exact hmeanP
