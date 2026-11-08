import AronowAudit.P001.P001_Foundations

/-!
# Blueprint: refutation of `AronowAudit.P001.printed_unrestricted_mixture_maximum` (P001-T103)

Record 3 of group P001a: P001-T103 / `AronowAudit.P001.printed_unrestricted_mixture_maximum`;
resolution `refute`. Frozen contract (P001_Foundations.lean:5091): for every nonempty
sample `y` of positive observations, the Example 5.2.11 mixture likelihood has a maximizer
over the unrestricted admissible parameter set `MixtureAdmissible`.

`Target` is the negation of exactly that contract; the `example` checks by `Iff.rfl` that
it is the negation of the frozen declaration's type.

Witness (paper proof, record 3): `n = 3`, `y = (1,2,3)`. For `σ > 0` the parameter
`θ_σ = (1/2, 1/4, 1, σ, 0, 1, 1)` (coordinate order `p_N, p_LN, μ_N, σ_N, μ_LN, σ_LN, λ_E`)
is admissible and `L(θ_σ) ≥ C/σ` with `C = e⁻⁵/(32√(2π)) > 0`: the normal term at `y = 1`
gives `1/(2σ√(2π))`, the exponential terms at `y = 2, 3` give `e⁻²/4`, `e⁻³/4`, and every
other contribution is nonnegative. So the likelihood is unbounded on the admissible set and
no maximizer exists; the assembly (fully proved below) takes `σ = C/(|B|+1)` with
`B = L(θ*)`.

Nodes: `N1` (lower bound). The old drafts `mixture_three_point_unbounded` and
`mixture_unbounded_positive_sample` depend on `sorryAx` and must not be used.
Writers prove `theorem n1_proof : N1` in `AronowAudit/P001/Wave1/MixtureMaximum/N1.lean`.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.MixtureMaximum

open AronowAudit.P001
open scoped BigOperators

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded contract
`printed_unrestricted_mixture_maximum`. -/
def Target : Prop :=
  ¬ ∀ {n : ℕ}, 0 < n → ∀ (y : Fin n → ℝ), (∀ i, 0 < y i) →
    ∃ θ : Fin 7 → ℝ, MixtureAdmissible θ ∧ ∀ θ', MixtureAdmissible θ' →
      mixtureLikelihood y θ' ≤ mixtureLikelihood y θ

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration). Only the
frozen theorem's *type* is read; its `sorry` proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P001.printed_unrestricted_mixture_maximum) :=
  Iff.rfl

/-- The witness sample `y = (1, 2, 3)`. -/
def sample : Fin 3 → ℝ := ![1, 2, 3]

/-- The collapsing parameter path `θ_σ = (1/2, 1/4, 1, σ, 0, 1, 1)`: the normal component
is centred at the observation `1` with scale `σ`. -/
def collapse (σ : ℝ) : Fin 7 → ℝ := ![1/2, 1/4, 1, σ, 0, 1, 1]

/-- The positive constant `C = e⁻⁵ / (32 √(2π))`. -/
def lowerConst : ℝ := Real.exp (-5) / (32 * Real.sqrt (2 * Real.pi))

/-- **Node N1** (paper proof, record 3, first paragraph: "every θ_σ is MixtureAdmissible
... At y=1 the normal contribution is 1/(2σc) ... At y=2 and y=3 the exponential
contribution alone is respectively e^{-2}/4 and e^{-3}/4. Multiplication of these
nonnegative lower bounds gives L(θ_σ)≥C/σ, where C=e^{-5}/(32c)"). For every `σ > 0`,
`θ_σ` is admissible and `C/σ ≤ L(θ_σ)` at the sample `(1,2,3)`.
Suggested route: `Fin.prod_univ_three`, `Matrix.cons_val_*` simp lemmas to evaluate the
coordinates; `normalDensity 1 σ 1 = 1/(σ √(2π))` (`sub_self`, `Real.exp_zero`); each of
`normalDensity`, `lognormalDensity`, `exponentialDensity` is `≥ 0` for positive scale
(`Real.exp_pos`, `Real.sqrt_pos`, `Real.pi_pos`, `div_nonneg`); `exponentialDensity 1 y =
exp (-y)` for `y ≥ 0`; `Real.exp_add` for `e⁻² e⁻³ = e⁻⁵`; `mul_le_mul` of three
nonnegative lower bounds. -/
def N1 : Prop :=
  ∀ σ : ℝ, 0 < σ → MixtureAdmissible (collapse σ) ∧
    lowerConst / σ ≤ mixtureLikelihood sample (collapse σ)

theorem lowerConst_pos : 0 < lowerConst := by
  unfold lowerConst
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- The nodes suffice: an admissible maximizer `θ*` with value `B` is beaten by `θ_σ` at
`σ = C/(|B|+1)`, whose likelihood is at least `|B| + 1 > B`. -/
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

/-- Nonvacuity record: the witness sample satisfies the contract's hypotheses
(`0 < 3`, all observations positive), and `θ_σ` is a genuine admissible parameter for
every `σ > 0` (given `N1`). -/
example (h1 : N1) : 0 < 3 ∧ (∀ i, 0 < sample i) ∧ ∀ σ : ℝ, 0 < σ →
    MixtureAdmissible (collapse σ) :=
  ⟨by norm_num, by intro i; fin_cases i <;> simp [sample], fun σ hσ => (h1 σ hσ).1⟩

end

end AronowAudit.P001.Wave1.MixtureMaximum
