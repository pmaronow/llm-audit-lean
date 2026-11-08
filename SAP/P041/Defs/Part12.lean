import SAP.P041.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041
open Matrix
open scoped BigOperators

/-- Mathematical content packaged for P041-T10. -/
def T10Statement : Prop :=
  (∀ (h₀ a b g C L T w : ℝ),
    b*(C-L)+a*T+g*T*(C-L)+w =
      C*b+(-b)*L+(a+C*g)*T+(-g)*T*L+w ∧
    tenureHazard h₀ b a g C L T w = yearHazard h₀ b a g (C-L) T w) ∧
  (∀ (a g C L : ℝ),
    Real.exp (-g) = 1 / Real.exp g ∧
    Real.exp ((a+C*g)+(-g)*(L+1)) =
      Real.exp ((a+C*g)+(-g)*L) * (1/Real.exp g) ∧
    (∀ r : ℝ, 0 < r →
      ((r < 1 ↔ 1 < 1/r) ∧ (1 < r ↔ 1/r < 1)))) ∧
  ((∀ r : ℝ, 0.989-0.0005 ≤ r → r ≤ 0.989+0.0005 →
      1.0106 < 1/r ∧ 1/r < 1.0117 ∧ 1 < 1/r) ∧
    (∀ r : ℝ, 0.981-0.0005 ≤ r → r ≤ 0.981+0.0005 →
      1.0188 < 1/r ∧ 1/r < 1.0199 ∧ 1 < 1/r) ∧
    (∀ r : ℝ, 1.056-0.0005 ≤ r → r ≤ 1.056+0.0005 →
      0.9465 < 1/r ∧ 1/r < 0.9475 ∧ 1/r < 1) ∧
    (∀ r : ℝ, 1.004-0.0005 ≤ r → r ≤ 1.004+0.0005 →
      0.9955 < 1/r ∧ 1/r < 0.9966 ∧ 1/r < 1)) ∧
  (∀ (g V s : ℝ), 0 < V → s = Real.exp g * Real.sqrt V →
      (1/Real.exp g) * Real.sqrt V = s/(Real.exp g)^2 ∧ (-g)^2/V = g^2/V) ∧
  (tenureFromYear 2014 2009 = 5 ∧ tenureFromYear 2014 2008 = 6 ∧
    illustrativeYearRelativeHazard 0 2009 = 1 ∧
    illustrativeYearRelativeHazard 0 2008 = 1 ∧
    illustrativeYearRelativeHazard 1 2009 = 1 ∧
    illustrativeYearRelativeHazard 1 2008 = 125/132 ∧
    (1:ℝ) < 132/125 ∧ (125/132:ℝ) < 1 ∧
    (132/125:ℝ)*(125/132) = 1)

end SAP.P041
