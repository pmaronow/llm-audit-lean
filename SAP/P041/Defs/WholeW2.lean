import Mathlib
import SAP.P041.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041

open Matrix MeasureTheory

/-- Change from first-election-year coefficients `(b,a,g)` to tenure coefficients.
The centering year `C` is fixed, rather than estimated. -/
def tenureCoreW2 (C : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, 0, 0; 0, 1, C; 0, 0, -1]

/-- The complete coefficient change, with the identity on all `n` other fitted
coefficients. The baseline is rescaled separately by `exp (C*b)`. -/
def tenureChangeW2 (n : ℕ) (C : ℝ) :
    Matrix (Fin 3 ⊕ Fin n) (Fin 3 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (tenureCoreW2 C) 0 0 1

/-- Explicit tenure coefficients, including every unchanged nuisance coordinate. -/
def tenureCoefficientsW2 (n : ℕ) (C : ℝ)
    (β : Fin 3 ⊕ Fin n → ℝ) : Fin 3 ⊕ Fin n → ℝ :=
  Sum.elim ![-β (Sum.inl 0),
    β (Sum.inl 1) + C * β (Sum.inl 2), -β (Sum.inl 2)]
    (fun j => β (Sum.inr j))

/-- Actual covariance matrix of a finite random coefficient vector. Uses of this
definition below explicitly assume square integrability of every coordinate. -/
def covarianceMatrixW2 {Ω ι : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ProbabilityTheory.covariance (fun ω => X ω i) (fun ω => X ω j) μ

/-- P041-T10; S9 File, Table A (rendered p. 1) and Table B (rendered p. 2);
S10 File (rendered p. 1); the same covariate label occurs in the notes to S6,
S9 and S11 and on p. 4/8 (PDF p. 4).
The fitted covariate is first-election year. Replacing it by tenure preserves
the predictor and fitted hazards after transforming the year, treatment and
interaction coefficients and baseline. The complete coefficient covariance
transforms by congruence, with every other coefficient retained. The five
printed ratios reverse direction through reciprocals, with the stated uniform
enclosures; the two 1.056 reciprocals round to 0.947. Reciprocal delta-method
standard errors obey s/r^2 even at zero variance. Where a Wald test is defined,
its squared statistic, two-sided normal p value and cutoff decisions are
preserved; both S9 Table B rounding rectangles retain three stars under this
Wald reading. The exact 132/125 illustration has the stated hazards and tenure
values. The usual measure-theoretic conditions are assumed; finite second
moments are explicit for covariance, and positive variance is required only
for the Wald test. Hazard ratios formed by division require a nonzero baseline.
-/
def T10WholeStatement : Prop :=
  -- (i) Pointwise equality allows any time-dependent baseline by specialization.
  (∀ (h₀ a b g C L T w : ℝ),
    b * (C - L) + a * T + g * T * (C - L) + w =
      C * b + (-b) * L + (a + C * g) * T + (-g) * T * L + w ∧
    tenureHazard h₀ b a g C L T w = yearHazard h₀ b a g (C - L) T w) ∧
  -- (ii) The actual treatment hazard ratio, its increment, and the S10 increment.
  (∀ (h₀ a b g C L w : ℝ), h₀ ≠ 0 →
    tenureHazard h₀ b a g C L 1 w / tenureHazard h₀ b a g C L 0 w =
      Real.exp ((a + C * g) + (-g) * L)) ∧
  (∀ (a g C L : ℝ),
    Real.exp (-g) = 1 / Real.exp g ∧
    Real.exp ((a + C * g) + (-g) * (L + 1)) =
      Real.exp ((a + C * g) + (-g) * L) * (1 / Real.exp g) ∧
    (∀ r : ℝ, 0 < r →
      ((r < 1 ↔ 1 < 1 / r) ∧ (1 < r ↔ 1 / r < 1)))) ∧
  (∀ (h₀ b C L w : ℝ),
    Real.exp (-b) = 1 / Real.exp b ∧
    tenureHazard h₀ b 0 0 C (L + 1) 0 w =
      tenureHazard h₀ b 0 0 C L 0 w * (1 / Real.exp b)) ∧
  -- (iii) The third universal clause applies to both identically printed rows.
  ((∀ r : ℝ, printedInterval 0.989 r →
      1.0106 < 1 / r ∧ 1 / r < 1.0117 ∧ 1 < 1 / r) ∧
    (∀ r : ℝ, printedInterval 0.981 r →
      1.0188 < 1 / r ∧ 1 / r < 1.0199 ∧ 1 < 1 / r) ∧
    (∀ r : ℝ, printedInterval 1.056 r →
      0.9465 < 1 / r ∧ 1 / r < 0.9475 ∧ 1 / r < 1 ∧
      roundsWhole (1000 * (1 / r)) 947) ∧
    (∀ r : ℝ, printedInterval 1.004 r →
      0.9955 < 1 / r ∧ 1 / r < 0.9966 ∧ 1 / r < 1)) ∧
  -- The conditional repair retaining tenure labels: all coefficient coordinates.
  (∀ (n : ℕ) (C : ℝ) (β : Fin 3 ⊕ Fin n → ℝ),
    tenureCoefficientsW2 n C β = tenureChangeW2 n C *ᵥ β ∧
    tenureCoefficientsW2 n C (tenureCoefficientsW2 n C β) = β) ∧
  (∀ (n : ℕ) (C : ℝ) (V : Matrix (Fin 3 ⊕ Fin n) (Fin 3 ⊕ Fin n) ℝ),
    (tenureChangeW2 n C * V * (tenureChangeW2 n C).transpose)
      (Sum.inl 2) (Sum.inl 2) = V (Sum.inl 2) (Sum.inl 2)) ∧
  (∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (C : ℝ)
      (X : Ω → Fin 3 ⊕ Fin n → ℝ),
    (∀ i, MemLp (fun ω => X ω i) 2 μ) →
    (∀ i, MemLp (fun ω => tenureCoefficientsW2 n C (X ω) i) 2 μ) ∧
    covarianceMatrixW2 μ (fun ω => tenureCoefficientsW2 n C (X ω)) =
      tenureChangeW2 n C * covarianceMatrixW2 μ X * (tenureChangeW2 n C).transpose) ∧
  -- (iv) Existence of the SE does not require a positive variance.
  (∀ (g V s : ℝ), 0 ≤ V → s = Real.exp g * Real.sqrt V →
    Real.exp (-g) * Real.sqrt V = s / (Real.exp g) ^ 2) ∧
  (∀ (g V : ℝ), 0 < V →
    (-g) ^ 2 / V = g ^ 2 / V ∧
    |(-g) / Real.sqrt V| = |g / Real.sqrt V| ∧
    normalTwoSided ((-g) / Real.sqrt V) = normalTwoSided (g / Real.sqrt V) ∧
    (∀ α : ℝ,
      (normalTwoSided ((-g) / Real.sqrt V) < α ↔
        normalTwoSided (g / Real.sqrt V) < α))) ∧
  (∀ (r s : ℝ), printedInterval 1.056 r →
    (printedInterval 0.020 s ∨ printedInterval 0.019 s) →
    normalTwoSided (hazardWald r s) < 0.01 ∧
    normalTwoSided (hazardWald (1 / r) (s / r ^ 2)) =
      normalTwoSided (hazardWald r s) ∧
    significanceTier (hazardWald r s) = 3 ∧
    significanceTier (hazardWald (1 / r) (s / r ^ 2)) = 3) ∧
  -- (v) Exact illustrative law, rather than a claim to have performed new refits.
  (tenureFromYear 2014 2009 = 5 ∧ tenureFromYear 2014 2008 = 6 ∧
    illustrativeYearRelativeHazard 0 2009 = 1 ∧
    illustrativeYearRelativeHazard 0 2008 = 1 ∧
    illustrativeYearRelativeHazard 1 2009 = 1 ∧
    illustrativeYearRelativeHazard 1 2008 = 125 / 132 ∧
    (1 : ℝ) < 132 / 125 ∧ (125 / 132 : ℝ) < 1 ∧
    (132 / 125 : ℝ) * (125 / 132) = 1) ∧
  ((132 / 125 : ℝ) = 1.056 ∧
    tenureFromYear 2014 1993 = 21 ∧ tenureFromYear 2014 2013 = 1)

end SAP.P041
