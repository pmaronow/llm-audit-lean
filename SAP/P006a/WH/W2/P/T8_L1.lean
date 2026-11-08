import SAP.P006a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace SAP.P006a.WH.W2.P.T8_L1

noncomputable section

open SAP.P006a.WH.W2

lemma weighted_coin_integrals_eq {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (π : C → ℝ) (i : Fin n)
    (hbi : Integrable (fun ω => bit (E.T π i ω) * E.μhat π ω (E.X i ω)) (E.law π))
    (hpi : Integrable (fun ω => π (E.X i ω) * E.μhat π ω (E.X i ω)) (E.law π))
    (hzero : (E.law π)[(fun ω => (bit (E.T π i ω) - π (E.X i ω)) *
      E.μhat π ω (E.X i ω)) | E.covariateSigma i]
        =ᵐ[E.law π] (fun _ => (0 : ℝ)))
    (hG : E.covariateSigma i ≤ ‹MeasurableSpace Ω›)
    (htrim : SigmaFinite ((E.law π).trim hG)) :
    (∫ ω, bit (E.T π i ω) * E.μhat π ω (E.X i ω) ∂E.law π) =
      ∫ ω, π (E.X i ω) * E.μhat π ω (E.X i ω) ∂E.law π := by
  let f : Ω → ℝ := fun ω =>
    (bit (E.T π i ω) - π (E.X i ω)) * E.μhat π ω (E.X i ω)
  have hsplit : f = (fun ω => bit (E.T π i ω) * E.μhat π ω (E.X i ω)) -
      (fun ω => π (E.X i ω) * E.μhat π ω (E.X i ω)) := by
    funext ω
    dsimp [f]
    ring
  have hf : Integrable f (E.law π) := by
    rw [hsplit]
    exact hbi.sub hpi
  have hcezero :
      ∫ ω, (E.law π)[f | E.covariateSigma i] ω ∂E.law π = 0 := by
    calc
      ∫ ω, (E.law π)[f | E.covariateSigma i] ω ∂E.law π =
          ∫ _ω, (0 : ℝ) ∂E.law π := integral_congr_ae hzero
      _ = 0 := by simp
  have hfintegral : ∫ ω, f ω ∂E.law π = 0 := by
    calc
      ∫ ω, f ω ∂E.law π =
          ∫ ω, (E.law π)[f | E.covariateSigma i] ω ∂E.law π :=
        (integral_condExp (μ := E.law π) (m := E.covariateSigma i)
          (f := f) (hμm := htrim) hG).symm
      _ = 0 := hcezero
  have hdiff :
      (∫ ω, bit (E.T π i ω) * E.μhat π ω (E.X i ω) ∂E.law π) -
        ∫ ω, π (E.X i ω) * E.μhat π ω (E.X i ω) ∂E.law π = 0 := by
    calc
      _ = ∫ ω, f ω ∂E.law π := by
        rw [← integral_sub hbi hpi]
        apply integral_congr_ae
        exact ae_of_all _ (fun ω => (congrFun hsplit ω).symm)
      _ = 0 := hfintegral
  linarith

end
end SAP.P006a.WH.W2.P.T8_L1

open SAP.P006a.WH.W2 SAP.P006a.WH.W2.P.T8_L1

theorem SAP.P006a.WH.W2.T8_L1_proof : SAP.P006a.WH.W2.T8_L1 := by
  intro Ω C _ _ n E π hπ hS hI
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability
  letI : IsProbabilityMeasure E.PX := hS.px_probability
  have houtcome (i : Fin n) :
      ∫ ω, bit (E.T π i ω) * E.Y1 i ω ∂E.law π =
        OutcomeMeanW2 E π := by
    obtain ⟨hX, hY0, hY1, hT⟩ := hS.measurable_units i
    have hb : Measurable (fun ω => bit (E.T π i ω)) :=
      (measurable_of_countable bit).comp hT
    have hbi : Integrable (fun ω => bit (E.T π i ω) * E.Y1 i ω) (E.law π) :=
      AronowAudit.P006.Wave1.RepairT6T7_mul_integrable hb
        (fun ω => AronowAudit.P006.Wave1.RepairT6T7_bit_norm (E.T π i ω))
        (hS.integrable_units i).2
    have hG : E.covariateSigma i ≤ ‹MeasurableSpace Ω› := hX.comap_le
    have htrim : SigmaFinite ((E.law π).trim hG) := inferInstance
    have hm := (AronowAudit.P006.Wave1.RepairT6T7_unit_outcome_moments
      (SAP.P006a.Bridge.experiment E) (SAP.P006a.Bridge.policyDesign hS) hπ i).2
    have hlocal :
        ∫ ω, bit (E.T π i ω) * E.Y1 i ω ∂E.law π =
          ∫ ω, π (E.X i ω) * E.μ1 (E.X i ω) ∂E.law π := by
      calc
        _ = ∫ ω, (E.law π)[(fun η => bit (E.T π i η) * E.Y1 i η) |
              E.covariateSigma i] ω ∂E.law π :=
          (integral_condExp (μ := E.law π) (m := E.covariateSigma i)
            (f := fun ω => bit (E.T π i ω) * E.Y1 i ω)
            (hμm := htrim) hG).symm
        _ = ∫ ω, π (E.X i ω) * E.μ1 (E.X i ω) ∂E.law π :=
          integral_congr_ae hm
    have htransport := AronowAudit.P006.Wave1.RepairT6T7_law_transport
      (SAP.P006a.Bridge.experiment E) (SAP.P006a.Bridge.policyDesign hS) hπ i
      (hπ.1.mul hS.means_measurable.2)
      (AronowAudit.P006.Wave1.RepairT6T7_mul_integrable hπ.1
        (AronowAudit.P006.Wave1.RepairT6T7_admissible_norm hπ) hS.means_integrable.2)
    change ∫ ω, bit (E.T π i ω) * E.Y1 i ω ∂E.law π =
      ∫ c, π c * E.μ1 c ∂E.PX
    exact hlocal.trans htransport.2
  have hcoin (i : Fin n) :
      ∫ ω, bit (E.T π i ω) * E.μhat π ω (E.X i ω) ∂E.law π =
        EvaluationMeanW2 E π i := by
    rcases hI i with ⟨hbi, hpi, hzero⟩
    have hG : E.covariateSigma i ≤ ‹MeasurableSpace Ω› :=
      (hS.measurable_units i).1.comap_le
    have htrim : SigmaFinite ((E.law π).trim hG) := inferInstance
    change (∫ ω, bit (E.T π i ω) * E.μhat π ω (E.X i ω) ∂E.law π) =
      ∫ ω, π (E.X i ω) * E.μhat π ω (E.X i ω) ∂E.law π
    · exact weighted_coin_integrals_eq E π i hbi hpi hzero hG htrim
  have hterm (i : Fin n) :
      Integrable (fun ω => bit (E.T π i ω) * E.Y1 i ω -
        bit (E.T π i ω) * E.μhat π ω (E.X i ω)) (E.law π) ∧
      (∫ ω, bit (E.T π i ω) * E.Y1 i ω -
        bit (E.T π i ω) * E.μhat π ω (E.X i ω) ∂E.law π) =
          OutcomeMeanW2 E π - EvaluationMeanW2 E π i := by
    rcases hI i with ⟨hbi, hpi, hzero⟩
    have hYint : Integrable (fun ω => bit (E.T π i ω) * E.Y1 i ω) (E.law π) :=
      AronowAudit.P006.Wave1.RepairT6T7_mul_integrable
        ((measurable_of_countable bit).comp (hS.measurable_units i).2.2.2)
        (fun ω => AronowAudit.P006.Wave1.RepairT6T7_bit_norm (E.T π i ω))
        (hS.integrable_units i).2
    refine ⟨hYint.sub hbi, ?_⟩
    rw [integral_sub hYint hbi, houtcome i]
    exact congrArg (fun x => OutcomeMeanW2 E π - x) (hcoin i)
  have hrealized :
      (fun ω => ∑ i : Fin n,
        (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω)) =
      (fun ω => ∑ i : Fin n,
        (bit (E.T π i ω) * E.Y1 i ω -
          bit (E.T π i ω) * E.μhat π ω (E.X i ω))) := by
    funext ω
    apply Finset.sum_congr rfl
    intro i hi
    cases ht : E.T π i ω <;>
      simp [Experiment.observed, ht, bit] <;> ring
  change (∫ ω, ∑ i : Fin n,
      (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) * 1 ∂E.law π) = _
  simp only [mul_one]
  rw [integral_congr_ae (ae_of_all _ (fun ω => congrFun hrealized ω))]
  rw [integral_finsetSum Finset.univ (fun i hi => (hterm i).1)]
  simp_rw [fun i => (hterm i).2]
