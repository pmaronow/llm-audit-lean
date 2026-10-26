import AronowAudit.P001.P001_Foundations

/-!
# Polynomial BLP approximation of the CEF on full interval support (P001-T109)

Theorems 4.3.2–4.3.3 (p. 158, proof pp. 158–159). The support condition
`Supp[X] = [a,b]` is expressed in the book's PMF/PDF sense: a PDF with
`paperSupport f = [a,b]`, or a countable-range PMF whose positive-mass set is `[a,b]`.
The latter includes the degenerate interval `a = b`. Containment in `[a,b]` holds a.e.

Population least-squares polynomials of every degree exist, including for singular
Gram matrices. The Weierstrass tail bound holds for every degree-bounded minimizing
family. The full-support hypothesis restricts the domain to that of the paper;
the proof uses only a.e. containment. Finite second moments are the standing MSE
convention (`MemLp Y 2 μ`). `Target` is universe polymorphic in `Ω`.

The intermediate statements establish L² integrability of `m(X)` and polynomials,
the risk decomposition, abstract finite-dimensional least squares, existence of
least-squares polynomials in L², and the Weierstrass tail bound.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.PolynomialBlp

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section


def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → MemLp Y 2 μ →
    ∀ (a b : ℝ), (∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) →
    ((∃ f : ℝ → ℝ, HasPDF (μ.map X) f ∧ paperSupport f = Set.Icc a b) ∨
      (Set.Countable (Set.range X) ∧
        ∀ x : ℝ, 0 < prob μ {ω | X ω = x} ↔ x ∈ Set.Icc a b)) →
    ∀ (m : ℝ → ℝ), IsCEF μ X Y m → ContinuousOn m (Set.Icc a b) →
    (∃ p : ℕ → Polynomial ℝ, (∀ J, (p J).natDegree ≤ J) ∧
      (∀ (J : ℕ) (q : Polynomial ℝ), q.natDegree ≤ J →
        mean μ (fun ω => (Y ω - (p J).eval (X ω)) ^ 2) ≤
          mean μ (fun ω => (Y ω - q.eval (X ω)) ^ 2))) ∧
    (∀ p : ℕ → Polynomial ℝ, (∀ J, (p J).natDegree ≤ J) →
      (∀ (J : ℕ) (q : Polynomial ℝ), q.natDegree ≤ J →
        mean μ (fun ω => (Y ω - (p J).eval (X ω)) ^ 2) ≤
          mean μ (fun ω => (Y ω - q.eval (X ω)) ^ 2)) →
      ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ J', J ≤ J' →
        mean μ (fun ω => (m (X ω) - (p J').eval (X ω)) ^ 2) < ε)

/-- With `X` a.e. in `[a,b]` and `m` continuous there, `m(X)` and every polynomial
of `X` belong to L². -/
def N1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (a b : ℝ) (m : ℝ → ℝ), Measurable X →
    (∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) → IsCEF μ X Y m → ContinuousOn m (Set.Icc a b) →
    MemLp (fun ω => m (X ω)) 2 μ ∧ ∀ q : Polynomial ℝ, MemLp (fun ω => q.eval (X ω)) 2 μ

/-- The squared risk of any measurable L² function `g(X)` decomposes into the CEF
residual risk and its squared distance from `m(X)`. -/
def N2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (m : ℝ → ℝ), Measurable X → MemLp Y 2 μ → IsCEF μ X Y m →
    MemLp (fun ω => m (X ω)) 2 μ → ∀ g : ℝ → ℝ, Measurable g →
    MemLp (fun ω => g (X ω)) 2 μ →
    mean μ (fun ω => (Y ω - g (X ω)) ^ 2) =
      mean μ (fun ω => (Y ω - m (X ω)) ^ 2) + mean μ (fun ω => (m (X ω) - g (X ω)) ^ 2)

/-- In a real inner-product space, distance to the span of finitely many vectors
is attained by a coefficient vector; linear independence is not required. -/
def N3 : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (d : ℕ) (v : Fin d → H)
    (y : H), ∃ b : Fin d → ℝ, ∀ c : Fin d → ℝ,
      ‖y - ∑ i, b i • v i‖ ≤ ‖y - ∑ i, c i • v i‖

/-- Under `N3`, square-integrability of `Y` and all polynomials of `X` gives a
least-squares polynomial of every degree bound. -/
def N4 : Prop :=
  N3.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → MemLp Y 2 μ →
    (∀ q : Polynomial ℝ, MemLp (fun ω => q.eval (X ω)) 2 μ) →
    ∀ J : ℕ, ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ ∀ q : Polynomial ℝ, q.natDegree ≤ J →
      mean μ (fun ω => (Y ω - p.eval (X ω)) ^ 2) ≤ mean μ (fun ω => (Y ω - q.eval (X ω)) ^ 2)

/-- Under `N1` and `N2`, every degree-bounded minimizing family converges to the
continuous CEF in squared mean on the compact covariate interval. -/
def N5 : Prop :=
  N1.{u} → N2.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (a b : ℝ) (m : ℝ → ℝ), Measurable X → MemLp Y 2 μ →
    (∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) → IsCEF μ X Y m → ContinuousOn m (Set.Icc a b) →
    ∀ p : ℕ → Polynomial ℝ, (∀ J, (p J).natDegree ≤ J) →
      (∀ (J : ℕ) (q : Polynomial ℝ), q.natDegree ≤ J →
        mean μ (fun ω => (Y ω - (p J).eval (X ω)) ^ 2) ≤
          mean μ (fun ω => (Y ω - q.eval (X ω)) ^ 2)) →
      ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ J', J ≤ J' →
        mean μ (fun ω => (m (X ω) - (p J').eval (X ω)) ^ 2) < ε

/-- The intermediate hypotheses give a minimizing polynomial family and squared-mean
convergence for every such family. -/
theorem assemble (h1 : N1.{u}) (h2 : N2.{u}) (h3 : N3.{u}) (h4 : N4.{u}) (h5 : N5.{u}) :
    Target.{u} := by
  intro Ω _ μ _ X Y hX hY a b hsupp _ m hm hc
  obtain ⟨-, hq2⟩ := h1 μ X Y a b m hX hsupp hm hc
  have hex := h4 h3 μ X Y hX hY hq2
  refine ⟨⟨fun J => (hex J).choose, fun J => (hex J).choose_spec.1,
    fun J q hq => (hex J).choose_spec.2 q hq⟩, ?_⟩
  exact h5 h1 h2 μ X Y a b m hX hY hsupp hm hc

end

end AronowAudit.P001.Wave1.PolynomialBlp
