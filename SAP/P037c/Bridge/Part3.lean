import SAP.P037c.Defs
import AronowAudit.P037.Wave1.Gap.GLP037B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c.Bridge
open SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Both variance definitions use the actual refitted contrast and the same design mass. -/
theorem controlVariance_eq (f : (Fin 6 × (Fin 4 → Bool)) → ℝ) :
    controlVariance f = AronowAudit.P037.controlVariance f := rfl

theorem collapsed_certificate : CollapsedControlCertificate :=
  AronowAudit.P037.Wave1.collapsed_controls_variance_counterexample_proof

theorem variance_certificates_differ :
    controlCollapsedVarianceCertificate ≠ controlFullVarianceCertificate :=
  AronowAudit.P037.collapsed_controls_certificate_inequalities.2.2.2.2

theorem control_weights_positive (D : (Fin 4 × Fin 2) → Fin 4) (i : Fin 4 × Fin 2) :
    0<controlWeight D i := AronowAudit.P037.Wave1.collapsedControls_weight_positive D i

theorem observed_rank : Function.Injective (controlFullRow controlObserved).mulVec :=
  AronowAudit.P037.Wave1.collapsedControls_observed_rank

theorem collapsed_rank (z : Fin 6 × (Fin 4 → Bool)) :
    Function.Injective (Matrix.mulVec
      (fun i k => if controlExposure z i=k then (1:ℝ) else 0 :
        Matrix (Fin 4 × Fin 2) (Fin 4) ℝ)) :=
  AronowAudit.P037.Wave1.collapsedControls_collapsed_rank z

theorem control_prediction (D : (Fin 4 × Fin 2) → Fin 4)
    (v : Fin 5 → ℝ) (i : Fin 4 × Fin 2) :
    (controlFullRow D).mulVec v i = v (D i).castSucc + controlPiI i*v 4 :=
  AronowAudit.P037.Wave1.collapsedControls_prediction D v i

end SAP.P037c.Bridge
