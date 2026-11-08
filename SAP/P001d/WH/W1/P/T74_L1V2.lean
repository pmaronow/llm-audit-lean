import SAP.P001d.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace SAP.P001d.WH.W1.P.T74_L1V2

lemma covariance_zero_of_integrable_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F R : Ω → ℝ)
    (hR : Integrable R μ)
    (hprod : Integrable (fun ω => F ω * R ω) μ)
    (hRmean : (∫ ω, R ω ∂μ) = 0)
    (hprodmean : (∫ ω, F ω * R ω ∂μ) = 0) :
    covariance F R μ = 0 := by
  change (∫ ω, (F ω - μ[F]) * (R ω - μ[R]) ∂μ) = 0
  rw [hRmean]
  simp only [sub_zero]
  calc
    (∫ ω, (F ω - μ[F]) * R ω ∂μ)
        = ∫ ω, (F ω * R ω - μ[F] * R ω) ∂μ := by
          congr 1
          funext ω
          ring
    _ = (∫ ω, F ω * R ω ∂μ) - ∫ ω, μ[F] * R ω ∂μ :=
          integral_sub hprod (hR.const_mul (μ[F]))
    _ = 0 := by rw [hprodmean, integral_const_mul, hRmean]; simp

end SAP.P001d.WH.W1.P.T74_L1V2

theorem SAP.P001d.WH.W1.T74_L1V2_proof : SAP.P001d.WH.W1.T74_L1V2 := by
  intro Ω E _ _ μ hμ X hX Y hY m hm g hg hgi hprod
  let R : Ω → ℝ := fun ω => Y ω - m (X ω)
  let F : Ω → ℝ := g ∘ X
  have hres := SAP.P001d.WH.W1.residual_means μ X hX Y m hm
  have hRi : Integrable R μ := by simpa [R] using hres.1
  have hRcef : IsCEF μ X R (fun _ => 0) := by simpa [R] using hres.2.1
  have hRmean : (∫ ω, R ω ∂μ) = 0 := by simpa [R] using hres.2.2.1
  have hRcond : (fun _ : Ω => (0 : ℝ)) =ᵐ[μ]
      μ[R | MeasurableSpace.comap X inferInstance] := by
    simpa [R] using hres.2.2.2
  have hFi : Integrable F μ := by simpa [F] using hgi
  have hprod' : Integrable (fun ω => F ω * R ω) μ := by
    simpa [F, R, Function.comp_apply] using hprod
  have hFstrong : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] F μ := by
    exact (hg.comp (comap_measurable X)).aestronglyMeasurable
  have hpull := condExp_mul_of_aestronglyMeasurable_left
    (m := MeasurableSpace.comap X inferInstance) hFstrong hprod' hRi
  have hcondprod := hpull
  have hcondzero : μ[(fun ω => F ω * R ω) |
      MeasurableSpace.comap X inferInstance] =ᵐ[μ] 0 := by
    filter_upwards [hcondprod, hRcond] with ω hω hRω
    calc
      μ[(fun ω => F ω * R ω) | MeasurableSpace.comap X inferInstance] ω =
          F ω * μ[R | MeasurableSpace.comap X inferInstance] ω := hω
      _ = 0 := by rw [← hRω]; simp
  have hprodmean : (∫ ω, F ω * R ω ∂μ) = 0 := by
    have hIC :
        (∫ ω, MeasureTheory.condExp (MeasurableSpace.comap X inferInstance) μ
          (fun ω => F ω * R ω) ω ∂μ) = ∫ ω, F ω * R ω ∂μ :=
      MeasureTheory.integral_condExp (m := MeasurableSpace.comap X inferInstance)
        (m₀ := inferInstance) (μ := μ) (f := fun ω : Ω => F ω * R ω) hX.comap_le
    calc
      (∫ ω, F ω * R ω ∂μ) =
          ∫ ω, MeasureTheory.condExp (MeasurableSpace.comap X inferInstance) μ
            (fun ω => F ω * R ω) ω ∂μ := hIC.symm
      _ = 0 := by
        rw [integral_congr_ae hcondzero]
        simp
  exact SAP.P001d.WH.W1.P.T74_L1V2.covariance_zero_of_integrable_product
    μ F R hRi hprod' hRmean hprodmean
