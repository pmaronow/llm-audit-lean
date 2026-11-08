import SAP.P018a.WH.W2.Leaves
import AronowAudit.P018.Wave1.Gap.TailBSignInference
import AronowAudit.Shared.MapTailB.PairLimitTools
import AronowAudit.Shared.MapTailB.RowLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P018a.WH.W2.P.T7_L5

open AronowAudit.P018 AronowAudit.P018.Wave1.TailBSign

local instance t7_leaf_unit_probability :
    MeasureTheory.IsProbabilityMeasure AronowAudit.P018.signPairKernel.μ := tb05_standing.1

theorem vector_approximation_inProbability
    (hSlope : SAP.P018a.T7SlopeApproximation) :
    AronowAudit.P018.inProbability
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signPairKernel)
      (fun N ω => SAP.P018a.wholeSecondOrderMap (tb05_pairStatistic N ω) -
        SAP.P018a.wholeSecondOrderStatistic N ω) := by
  letI : ∀ N, MeasureTheory.IsProbabilityMeasure
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signPairKernel N) := fun N =>
    AronowAudit.P018.Wave1.printed_unit_probability _
  let e₁ : ∀ N : ℕ, (Fin N → Bool × Bool) → ℝ := fun N ω =>
    (N : ℝ) * SAP.P018a.sampleOLS (SAP.P018a.design SAP.P018a.signPairKernel ω)
      (SAP.P018a.response SAP.P018a.signPairKernel ω) 1 -
      2 * ((∑ i, SAP.P018a.wholePairZ ω i) / Real.sqrt N) *
        ((∑ i, SAP.P018a.wholePairZ ω i * SAP.P018a.wholePairW ω i) / Real.sqrt N)
  let e₂ : ∀ N : ℕ, (Fin N → Bool × Bool) → ℝ := fun N ω => tb05_secondOrderError N ω
  let f : ∀ N : ℕ, (Fin N → Bool × Bool) → SAP.P018a.Vec 2 := fun N ω =>
    SAP.P018a.wholeSecondOrderMap (tb05_pairStatistic N ω) -
    SAP.P018a.wholeSecondOrderStatistic N ω
  have hP : SAP.P018a.unitSampleLaw SAP.P018a.signPairKernel =
      AronowAudit.P018.unitSampleLaw AronowAudit.P018.signPairKernel := by
      funext N
      exact (SAP.P018a.Bridge.kernel_sample_agrees SAP.P018a.signPairKernel
        (fun _ : Fin N => (false, false))).1.trans (by rfl)
  have h₁ : AronowAudit.P018.inProbability
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signPairKernel) e₁ := by
    rw [← hP]
    exact hSlope
  have h₂ : AronowAudit.P018.inProbability
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signPairKernel)
      (fun N ω => tb05_secondOrderError N ω) := tb05_second_order_in_probability
  have hfirst : ∀ N ω, f N ω 0 = -e₁ N ω := by
    intro N ω
    simp [f, e₁, SAP.P018a.wholeSecondOrderMap, SAP.P018a.wholeSecondOrderStatistic,
      tb05_pairStatistic, SAP.P018a.wholePairZ, SAP.P018a.wholePairW, tb05_z, tb05_w,
      SAP.P018a.signValue, AronowAudit.P018.signValue]
  have hvar (N : ℕ) (ω : Fin N → Bool × Bool) :
      SAP.P018a.sampleVariance SAP.P018a.members
          (SAP.P018a.design SAP.P018a.signPairKernel ω)
          (SAP.P018a.response SAP.P018a.signPairKernel ω) 1 1 =
        AronowAudit.P018.sampleVariance AronowAudit.P018.members
          (AronowAudit.P018.design AronowAudit.P018.signPairKernel ω)
          (AronowAudit.P018.response AronowAudit.P018.signPairKernel ω) 1 1 := rfl
  have hsecond : ∀ N ω, f N ω 1 = -e₂ N ω := by
    intro N ω
    dsimp [f, SAP.P018a.wholeSecondOrderMap, SAP.P018a.wholeSecondOrderStatistic]
    rw [hvar]
    simp [f, e₂, SAP.P018a.wholeSecondOrderMap, SAP.P018a.wholeSecondOrderStatistic,
      tb05_pairStatistic, SAP.P018a.wholePairZ, SAP.P018a.wholePairW, tb05_z, tb05_w,
      tb05_secondOrderError, SAP.P018a.signValue, AronowAudit.P018.signValue]
  have hc₁ : AronowAudit.P018.inProbability
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signPairKernel)
      (fun N ω => f N ω 0) := by
    have hfun : (fun N ω => f N ω 0) = (fun N ω => -e₁ N ω) := by
      funext N ω
      exact hfirst N ω
    rw [hfun]
    unfold AronowAudit.P018.inProbability at h₁ ⊢
    simpa only [norm_neg] using h₁
  have hc₂ : AronowAudit.P018.inProbability
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signPairKernel)
      (fun N ω => f N ω 1) := by
    have hfun : (fun N ω => f N ω 1) = (fun N ω => -e₂ N ω) := by
      funext N ω
      exact hsecond N ω
    rw [hfun]
    unfold AronowAudit.P018.inProbability at h₂ ⊢
    simpa only [norm_neg] using h₂
  exact
    (AronowAudit.Shared.MapTailB.tb09_inProbability_pi
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signPairKernel) f (by
      intro j
      fin_cases j
      · exact hc₁
      · exact hc₂))

end SAP.P018a.WH.W2.P.T7_L5

theorem SAP.P018a.WH.W2.T7_L5_proof : SAP.P018a.WH.W2.T7_L5 := by
  intro hSlope
  letI : MeasureTheory.IsProbabilityMeasure AronowAudit.P018.signPairKernel.μ :=
    AronowAudit.P018.Wave1.TailBSign.tb05_standing.1
  letI : ∀ N, MeasureTheory.IsProbabilityMeasure
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signPairKernel N) := fun N =>
    AronowAudit.P018.Wave1.printed_unit_probability _
  have hmap := AronowAudit.Shared.MapTailB.TailB_weakLimit_continuous_map
    (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signPairKernel)
    AronowAudit.P018.Wave1.TailBSign.tb05_pairStatistic _
    AronowAudit.P018.Wave1.TailBSign.tb05_joint_sign_clt
    SAP.P018a.wholeSecondOrderMap (by
      unfold SAP.P018a.wholeSecondOrderMap
      fun_prop)
  exact AronowAudit.Shared.MapTailB.TailB_weakLimit_perturbation
    (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signPairKernel)
    (fun N ω => SAP.P018a.wholeSecondOrderMap
      (AronowAudit.P018.Wave1.TailBSign.tb05_pairStatistic N ω))
    SAP.P018a.wholeSecondOrderStatistic SAP.P018a.wholeSecondOrderLaw hmap
    (fun N => (measurable_of_countable _).aemeasurable)
    (SAP.P018a.WH.W2.P.T7_L5.vector_approximation_inProbability hSlope)
