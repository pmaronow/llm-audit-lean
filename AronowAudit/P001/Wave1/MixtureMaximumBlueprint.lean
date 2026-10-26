import AronowAudit.P001.P001_Foundations

/-!
# Unbounded mixture likelihood (P001-T103)

The unrestricted mixture likelihood in Example 5.2.11 need not have a maximizer,
even for a nonempty sample of positive observations. `Target` negates the assertion
that every such sample has a maximizer over `MixtureAdmissible`.

For the sample `y = (1,2,3)` and `σ > 0`, the parameter
`θ_σ = (1/2, 1/4, 1, σ, 0, 1, 1)` (coordinate order
`p_N, p_LN, μ_N, σ_N, μ_LN, σ_LN, λ_E`) is admissible and satisfies
`L(θ_σ) ≥ C/σ`, where `C = e⁻⁵/(32√(2π)) > 0`.
The normal contribution at `y = 1` is `1/(2σ√(2π))`; the exponential contributions
at `y = 2, 3` are `e⁻²/4`, `e⁻³/4`; all other contributions are nonnegative.
Thus the likelihood is unbounded. For a proposed maximizer with value `B`, taking
`σ = C/(|B|+1)` gives a larger likelihood.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.MixtureMaximum

open AronowAudit.P001
open scoped BigOperators

noncomputable section

/-- Negation of the universal assertion. -/
def Target : Prop :=
  ¬ ∀ {n : ℕ}, 0 < n → ∀ (y : Fin n → ℝ), (∀ i, 0 < y i) →
    ∃ θ : Fin 7 → ℝ, MixtureAdmissible θ ∧ ∀ θ', MixtureAdmissible θ' →
      mixtureLikelihood y θ' ≤ mixtureLikelihood y θ

/-- The witness sample `y = (1, 2, 3)`. -/
def sample : Fin 3 → ℝ := ![1, 2, 3]

/-- The collapsing parameter path `θ_σ = (1/2, 1/4, 1, σ, 0, 1, 1)`: the normal component
is centred at the observation `1` with scale `σ`. -/
def collapse (σ : ℝ) : Fin 7 → ℝ := ![1/2, 1/4, 1, σ, 0, 1, 1]

/-- The positive constant `C = e⁻⁵ / (32 √(2π))`. -/
def lowerConst : ℝ := Real.exp (-5) / (32 * Real.sqrt (2 * Real.pi))

/-- For every `σ > 0`, `collapse σ` is admissible and its likelihood at `sample`
is at least `lowerConst / σ`. -/
def N1 : Prop :=
  ∀ σ : ℝ, 0 < σ → MixtureAdmissible (collapse σ) ∧
    lowerConst / σ ≤ mixtureLikelihood sample (collapse σ)

theorem lowerConst_pos : 0 < lowerConst := by
  unfold lowerConst
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- A proposed maximizer with likelihood `B` is exceeded by the collapsing path
at `σ = lowerConst / (|B| + 1)`. -/
theorem assemble (h1 : N1) : Target := by
  intro H
  obtain ⟨θ, -, hmax⟩ := H (n := 3) (by norm_num) sample (by
    intro i; fin_cases i <;> simp [sample])
  set B := mixtureLikelihood sample θ
  have hC := lowerConst_pos
  have hB : 0 < |B| + 1 := by positivity
  set σ := lowerConst / (|B| + 1) with hσdef
  have hσ : 0 < σ := div_pos hC hB
  obtain ⟨hadm, hlow⟩ := h1 σ hσ
  have hq : lowerConst / σ = |B| + 1 := by
    rw [hσdef, div_div_cancel₀ hC.ne']
  have hle := hmax (collapse σ) hadm
  have : |B| + 1 ≤ B := by linarith
  linarith [le_abs_self B]

end

end AronowAudit.P001.Wave1.MixtureMaximum
