import SAP.P010.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

universe u

theorem SAP.P010.WH.W1.T12_L1_proof : SAP.P010.WH.W1.T12_L1.{u} := by
  intro Ω mΩ ν π fR fO hπ hπ1 hR hO
  have hc : 0 < π / (1 - π) := div_pos hπ (sub_pos.mpr hπ1)
  have hprinted :
      (fun x => fR x * SAP.P010.odds (SAP.P010.propensity π (fR x) (fO x))) =ᵐ[ν]
        (fun x => (π / (1 - π)) * ((fR x)^2 / fO x)) := by
    filter_upwards [hR, hO] with x hx hy
    have hm := AronowAudit.P010.transport_mass_factors π (fR x) (fO x)
      hπ hπ1 hx hy
    simpa [SAP.P010.odds, SAP.P010.propensity,
      AronowAudit.P010.printedOdds, AronowAudit.P010.studyPropensity] using hm.2
  have hconverted :
      (fun x => ENNReal.ofReal
        (fR x * SAP.P010.odds (SAP.P010.propensity π (fR x) (fO x)))) =ᵐ[ν]
      (fun x => ENNReal.ofReal (π / (1 - π)) *
        ENNReal.ofReal ((fR x)^2 / fO x)) := by
    filter_upwards [hprinted] with x hx
    rw [hx, ENNReal.ofReal_mul hc.le]
  change (∫⁻ x, ENNReal.ofReal
      (fR x * SAP.P010.odds (SAP.P010.propensity π (fR x) (fO x))) ∂ν) =
    ENNReal.ofReal (π / (1 - π)) *
      (∫⁻ x, ENNReal.ofReal ((fR x)^2 / fO x) ∂ν)
  calc
    _ = ∫⁻ x, ENNReal.ofReal (π / (1 - π)) *
        ENNReal.ofReal ((fR x)^2 / fO x) ∂ν := lintegral_congr_ae hconverted
    _ = ENNReal.ofReal (π / (1 - π)) *
        (∫⁻ x, ENNReal.ofReal ((fR x)^2 / fO x) ∂ν) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
