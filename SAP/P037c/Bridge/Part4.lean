import SAP.P037c.Defs
import AronowAudit.P037.P037_Review

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c.Bridge
open SAP.P037c
open scoped BigOperators

/-- Preserve the finite design's weights, nonnegativity, and normalization. -/
def toFiniteDesign {Ω : Type*} [Fintype Ω] (d : FiniteDesign Ω) :
    AronowAudit.P037.FiniteDesign Ω := ⟨d.weight, d.nonneg, d.total⟩

theorem designMean_eq {Ω : Type*} [Fintype Ω] (d : FiniteDesign Ω) (f : Ω → ℝ) :
    designMean d f = AronowAudit.P037.designMean (toFiniteDesign d) f := rfl

theorem cross_eq {Ω I : Type*} [Fintype Ω] [Fintype I]
    (d : FiniteDesign Ω) (x y : Ω → I → ℝ) :
    cross d x y = AronowAudit.P037.ExpectedProjection.cross (toFiniteDesign d) x y := rfl

theorem blockDemean_eq {B : ℕ} (x : (Fin B × Fin 4) → ℝ) :
    blockDemean x = AronowAudit.P037.ExpectedProjection.blockDemean x := rfl

theorem block_bias {Ω K : Type*} [Fintype Ω] [Fintype K] : BlockModelBiasStatement Ω K := by
  intro B d T C Y X a η μ lam p τ₀ β τ b g hT hTC hspan hY htt hK hN
  exact AronowAudit.P037.ExpectedProjection.block_model_bias_identity
    (toFiniteDesign d) T C Y X a η μ lam p τ₀ β τ b g hT hTC hspan hY htt hK hN

theorem common_intercept {Ω K : Type*} [Fintype Ω] [Fintype K] : CommonInterceptStatement Ω K := by
  intro B d T C Y X a μ lam p τ₀ β τ b g hT hTC hspan hY htt hK hN
  exact AronowAudit.P037.ExpectedProjection.common_intercept_identifies_slope
    (toFiniteDesign d) T C Y X a μ lam p τ₀ β τ b g hT hTC hspan hY htt hK hN

end SAP.P037c.Bridge
