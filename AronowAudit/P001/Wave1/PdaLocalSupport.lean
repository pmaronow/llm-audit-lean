import AronowAudit.P001.Wave1.PdaLocalSupportBlueprint
import AronowAudit.P001.Wave1.GapLaw.N1
import AronowAudit.P001.Wave1.GapLaw.N2
import AronowAudit.P001.Wave1.GapLaw.N3
import AronowAudit.P001.Wave1.GapLaw.N4
import AronowAudit.P001.Wave1.GapLaw.N5

set_option autoImplicit false

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 AronowAudit.P001.Wave1.GapLaw MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

theorem printed_pda_local_support_contract_refuted :
    ¬ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {K : ℕ}
      (X : Ω → Fin K → ℝ) (Y : Ω → ℝ), Measurable X →
      (∀ j, Integrable (fun ω => X ω j) μ) → Integrable Y μ →
      ∀ (f : (Fin K → ℝ) → ℝ), HasVectorPDF (μ.map X) f →
      ∀ (m m' : (Fin K → ℝ) → ℝ), IsCEF μ X Y m → IsCEF μ X Y m' →
      ∀ (k : Fin K),
      (∀ x, 0 < f x → DifferentiableAt ℝ (fun t => m (Function.update x k (x k + t))) 0) →
      (∀ x, 0 < f x → DifferentiableAt ℝ (fun t => m' (Function.update x k (x k + t))) 0) →
      ∃ a : ℝ,
        HasDerivAt (fun t => m (Function.update (fun j => mean μ (fun ω => X ω j)) k
          (mean μ (fun ω => X ω k) + t))) a 0 ∧
        HasDerivAt (fun t => m' (Function.update (fun j => mean μ (fun ω => X ω j)) k
          (mean μ (fun ω => X ω k) + t))) a 0 :=
  AronowAudit.P001.Wave1.PdaLocalSupport.assemble
    n1_proof n2_proof n3_proof n4_proof n5_proof

end

end AronowAudit.P001.Wave1
