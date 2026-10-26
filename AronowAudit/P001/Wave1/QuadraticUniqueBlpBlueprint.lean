import AronowAudit.P001.P001_Foundations

/-!
# Uniform/Gaussian quadratic CEF and its unique BLP (P001-T46)

Example 2.2.24 (BLP under Nonlinearity), p. 82 (PDF p. 100), with corrected
CEF factor `10X²`; Example 2.2.23, pp. 79–81; and mean-square minimization
in Theorem 2.2.21, p. 76.

For `X ~ U(0,1)`, independent `W ~ N(0,1)`, and `Y = 10X² + W`, the CEF is `10x²`.
The BLP has slope `10` and intercept `-5/3`, and `-5/3 + 10X` uniquely minimizes
the affine mean-square risk. The proof combines the CEF and coefficient identities,
`Var X = 1/12`, and square integrability of `X`, `X²`, and `W`.
-/

namespace AronowAudit.P001.Wave1.QuadraticUniqueBlp

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u


def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X W : Ω → ℝ), Measurable X → Measurable W → IndepFun X W μ →
    μ.map X = uniformLaw 0 1 → μ.map W = gaussianReal 0 1 →
    let Y : Ω → ℝ := fun ω => 10 * (X ω) ^ 2 + W ω
    IsCEF μ X Y (fun x => 10 * x ^ 2) ∧
    blpSlope μ X Y = 10 ∧ blpIntercept μ X Y = -5 / 3 ∧
    (∀ a b : ℝ,
      linearRisk μ X Y (-5 / 3) 10 ≤ linearRisk μ X Y a b ∧
      (linearRisk μ X Y a b = linearRisk μ X Y (-5 / 3) 10 ↔
        a = -5 / 3 ∧ b = 10))

/-- N1 (proof step "the bounded uniform `X` has all moments and the Gaussian `W` has
finite second moment; hence `X, X², W` (and so `Y = 10X² + W`) are square-integrable"). -/
def N1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X W : Ω → ℝ), Measurable X → Measurable W →
    μ.map X = uniformLaw 0 1 → μ.map W = gaussianReal 0 1 →
    MemLp X 2 μ ∧ MemLp (fun ω => (X ω) ^ 2) 2 μ ∧ MemLp W 2 μ

/-- The node suffices: the CEF, `Var X = 1/12` and the coefficients come from the proved
`uniform_quadratic_cef_and_blp`; with `N1` and `Var X > 0`, the proved
`blp_corrected_derivatives_and_minimum` gives the unique minimum at
`(blpIntercept, blpSlope) = (-5/3, 10)`. -/
theorem assemble (h1 : N1.{u}) : Target.{u} := by
  intro Ω _ μ _ X W hX hW hi hx hw Y
  obtain ⟨hcef, -, -, -, hvar, -, -, hslope, hint⟩ :=
    uniform_quadratic_cef_and_blp μ X W hX hW hi hx hw
  have hslope' : blpSlope μ X Y = 10 := hslope
  have hint' : blpIntercept μ X Y = -5 / 3 := hint
  obtain ⟨hX2, hXX2, hW2⟩ := h1 μ X W hX hW hx hw
  have hY2 : MemLp Y 2 μ := (hXX2.const_mul 10).add hW2
  have hv : 0 < var μ X := by rw [hvar]; norm_num
  obtain ⟨-, -, hmin⟩ := blp_corrected_derivatives_and_minimum μ X Y hX2 hY2 hv
  refine ⟨hcef, hslope', hint', fun a b => ?_⟩
  have h := hmin a b
  rw [hslope', hint'] at h
  exact h

/- Satisfiable instance of the hypotheses: `Ω = ℝ × ℝ`,
`μ = (uniformLaw 0 1).prod (gaussianReal 0 1)`, `X = Prod.fst`, `W = Prod.snd`. -/

end
end AronowAudit.P001.Wave1.QuadraticUniqueBlp
