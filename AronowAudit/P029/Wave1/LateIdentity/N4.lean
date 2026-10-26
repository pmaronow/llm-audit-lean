import AronowAudit.P029.Wave1.LateIdentityBlueprint

namespace AronowAudit.P029.Wave1.LateIdentity

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

universe u v

noncomputable section

/-- Integrate the pointwise ITT identities outside the null defier event. -/
theorem n4_proof : N4.{u, v} := by
  intro h2 Ω X _ _ μ _ U Z hiv
  have hreg := h2 μ U Z hiv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hdef, -⟩ := hiv
  have hnodef : ∀ᵐ ω ∂μ, ¬ (U ω).defier :=
    measure_eq_zero_iff_ae_notMem.mp hdef
  have hDae :
      (fun ω => bit ((U ω).receipt true) - bit ((U ω).receipt false)) =ᵐ[μ]
        (fun ω => if (U ω).complier then (1 : ℝ) else 0) := by
    filter_upwards [hnodef] with ω hω
    exact (unit_itt_identities (U ω) hω).1
  have hYae :
      (fun ω => (U ω).outcome true - (U ω).outcome false) =ᵐ[μ]
        (fun ω => if (U ω).complier then (U ω).tau else 0) := by
    filter_upwards [hnodef] with ω hω
    exact (unit_itt_identities (U ω) hω).2
  constructor
  · calc
      (∫ ω, bit ((U ω).receipt true) ∂μ) - (∫ ω, bit ((U ω).receipt false) ∂μ) =
          ∫ ω, bit ((U ω).receipt true) - bit ((U ω).receipt false) ∂μ :=
        (integral_sub (hreg.1 true).1 (hreg.1 false).1).symm
      _ = ∫ ω, (if (U ω).complier then (1 : ℝ) else 0) ∂μ :=
        integral_congr_ae hDae
      _ = mP μ {ω | (U ω).complier} := by
        simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, mP, measureReal_def] using
          (integral_indicator_one (μ := μ) hreg.2.2)
  · calc
      (∫ ω, (U ω).outcome true ∂μ) - (∫ ω, (U ω).outcome false ∂μ) =
          ∫ ω, (U ω).outcome true - (U ω).outcome false ∂μ :=
        (integral_sub (hreg.1 true).2.1 (hreg.1 false).2.1).symm
      _ = ∫ ω, (if (U ω).complier then (U ω).tau else 0) ∂μ :=
        integral_congr_ae hYae

end

end AronowAudit.P029.Wave1.LateIdentity
