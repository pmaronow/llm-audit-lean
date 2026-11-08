import SAP.P027b.Bridge.Part2
import AronowAudit.P027.Wave1.Gap.GLP027P016P031B2
import AronowAudit.P027.Wave1.Gap.GP027P016P031B1b

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027b.Bridge
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

theorem phaseOriginal_eq (r m : ℕ) (hr : 0 < r) :
    toProject (phaseOriginal r m hr) = AronowAudit.P027.phaseOriginal r m hr := rfl

/-- Component data and all its certificates are transported without alteration. -/
def decompositionToProject {r m : ℕ} {z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ}
    (d : PhaseDecomposition r m z) : AronowAudit.P027.PhaseDecomposition r m z where
  within := d.within
  signal := d.signal
  low := d.low
  high := d.high
  within_zero := d.within_zero
  signal_multiple := d.signal_multiple
  low_constant := d.low_constant
  high_constant := d.high_constant
  reconstruct := d.reconstruct

def decompositionFromProject {r m : ℕ} {z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ}
    (d : AronowAudit.P027.PhaseDecomposition r m z) : PhaseDecomposition r m z where
  within := d.within
  signal := d.signal
  low := d.low
  high := d.high
  within_zero := d.within_zero
  signal_multiple := d.signal_multiple
  low_constant := d.low_constant
  high_constant := d.high_constant
  reconstruct := d.reconstruct

theorem periodicFixed_proof : PeriodicFixed := by
  exact AronowAudit.P027.periodic_mean_identities

theorem periodicDiagonalization_proof : PeriodicDiagonalization := by
  intro r m hr hm z hz
  have h := AronowAudit.P027.Wave1.contrast_deterministic_correction_proof r m hr hm z hz
  rcases h with ⟨hcen,hw,hp,hl,hg,ho,he,hu,hf,hcancel⟩
  refine ⟨hcen,hw,hp,hl,hg,ho,?_,?_,?_,hcancel⟩
  · obtain ⟨d⟩ := he
    exact ⟨decompositionFromProject d⟩
  · intro d₁ d₂
    exact hu (decompositionToProject d₁) (decompositionToProject d₂)
  · intro d
    exact hf (decompositionToProject d)

theorem periodicGaussian_proof : PeriodicGaussian := by
  exact @AronowAudit.P027.Wave1.contrast_gaussian_law_proof

theorem periodicTail_proof : PeriodicTail := by
  exact @AronowAudit.P027.Wave1.contrast_gaussian_tail_proof

theorem periodicRows_proof : PeriodicRows := by
  exact @AronowAudit.P027.Wave1.a3_high_rows_probability_bound_proof

theorem periodicNumerics_proof : PeriodicNumerics := by
  have h := AronowAudit.P027.periodic_model_prediction_values
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,by norm_num,by norm_num,?_⟩
  exact AronowAudit.P027.a3_high_contrast_arithmetic

end
end SAP.P027b.Bridge
