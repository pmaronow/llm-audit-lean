import SAP.P027b.Bridge.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b.Bridge
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

theorem periodicRowCertificates_proof : PeriodicRowCertificates := by
  intro row
  have hc := AronowAudit.P027.Wave1.GP027P016P031B1b_a3_floor_ceil_certificates row
  dsimp only
  refine ⟨hc.1,hc.2.1,?_,?_,?_⟩
  · fin_cases row <;> norm_num [contrastR,a3HighR]
  · exact (congrArg₂ (fun a b : ℤ => a-b) hc.2.2.2.1 hc.2.2.2.2.1).trans hc.2.2.2.2.2.2
  · intro H C hH hC
    have hR : 0 ≤ contrastR (2*a3HighR row) := hc.2.2.1
    have hround := AronowAudit.P027.Wave1.GP027P016P031B1b_a3_rounding_implies_contrast_tail
      H C (a3HighH row) (a3HighC row) (contrastR (2*a3HighR row)) 0.005
      (by linarith) hH hC
    have hcontrast : a3HighC row-(1+contrastR (2*a3HighR row))*a3HighH row =
      a3HighContrast row := (AronowAudit.P027.a3_high_contrast_arithmetic row).1
    rw [hcontrast] at hround
    linarith

theorem T19_proof : T19Statement := by
  exact ⟨periodicFixed_proof,periodicModel_proof,periodicDiagonalization_proof,
    periodicGaussian_proof,periodicTail_proof,periodicRows_proof,periodicNumerics_proof,
    periodicRowCertificates_proof⟩

end
end SAP.P027b.Bridge
