import AronowAudit.P001.P001_Foundations

/-!
# Blueprint: polynomial BLP approximation of the CEF on full interval support (P001-T109)

Record 6 of group P001a: P001-T109 / held `AronowAudit.P001.polynomial_blp_cef_approximation`;
resolution `repair_and_prove`. Theorems 4.3.2-4.3.3 (p. 158, proof pp. 158-159). The held
draft (P001_Foundations.lean:4138) bounds `X` pointwise in `[a,b]` (allowing gapped or finite
support) and assumes a minimizing family. The repair (mapper's
`polynomial_blp_paper_support_approximation`):

* restores `Supp[X] = [a,b]` in the book's PMF/PDF sense (`hfull`: a PDF with
  `paperSupport f = [a,b]`, or a countable-range PMF whose positive-mass set is `[a,b]`,
  which keeps the degenerate interval `a = b`), and uses a.e. containment `hsupp`;
* proves (first conjunct) that population least-squares polynomials of every degree exist,
  allowing a singular Gram matrix;
* proves (second conjunct) the Weierstrass tail bound for *every* degree-bounded minimizing
  family.

`hfull` is a fidelity restriction only; the proof uses `hsupp`. Finite second moments are
the standing MSE convention (`MemLp Y 2 μ`). `Target` is universe polymorphic in `Ω`.

Nodes: `N1` (L² of `m(X)` and polynomials), `N2` (risk decomposition), `N3` (abstract
finite-dimensional least squares in an inner-product space), `N4` (least-squares
polynomials exist in L²), `N5` (Weierstrass tail). The frozen draft
`polynomial_blp_cef_approximation` (sorry) must not be used.
Writers prove `theorem nk_proof : Nk` in `AronowAudit/P001/Wave1/PolynomialBlp/Nk.lean`.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.PolynomialBlp

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The frozen statement the record is resolved by (mapper's
`AronowAudit.P001.Wave1.polynomial_blp_paper_support_approximation`). -/
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

/-- **Node N1** (paper proof, record 6, first paragraph: "Every polynomial q and the
continuous restriction of m to I are bounded on I. Their compositions with X are therefore
in L²(μ), since they are measurable and bounded almost surely"). Under a.e. containment in
`[a,b]`, `m(X)` and every polynomial of `X` are in L².
Suggested route: `IsCompact.exists_bound_of_continuousOn` (`isCompact_Icc`, also for
`q.continuous.continuousOn`), `MemLp.of_bound` with the a.e. bound, measurability from
`hm.1.comp hX` and `q.continuous.measurable.comp hX` (`aestronglyMeasurable`). -/
def N1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (a b : ℝ) (m : ℝ → ℝ), Measurable X →
    (∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) → IsCEF μ X Y m → ContinuousOn m (Set.Icc a b) →
    MemLp (fun ω => m (X ω)) 2 μ ∧ ∀ q : Polynomial ℝ, MemLp (fun ω => q.eval (X ω)) 2 μ

/-- **Node N2** (paper proof, record 6, first paragraph: "Conditional-expectation pullout
... gives E[e(m(X)-q(X))]=0. Expanding the square and integrating yields the exact finite
identity E[(Y-q(X))²]=E[e²]+E[(m(X)-q(X))²]"). Squared-risk decomposition for every L²
function `g(X)` of the covariate.
Suggested route: the proved `cef_residual_orthogonality_correction` (:3353; axiom-clean)
gives `mean (Y - m X) = 0` and `covariance (g ∘ X) (Y - m ∘ X) = 0`, hence
`∫ (m X - g X)(Y - m X) = 0` (`covariance_eq_sub`/definition of covariance); expand
`(Y - g)² = (Y - m)² + 2 (m - g)(Y - m) + (m - g)²` and use `integral_add`,
`integral_mul_left`, with integrability from `MemLp.integrable_sq`/`MemLp.integrable_mul`. -/
def N2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (m : ℝ → ℝ), Measurable X → MemLp Y 2 μ → IsCEF μ X Y m →
    MemLp (fun ω => m (X ω)) 2 μ → ∀ g : ℝ → ℝ, Measurable g →
    MemLp (fun ω => g (X ω)) 2 μ →
    mean μ (fun ω => (Y ω - g (X ω)) ^ 2) =
      mean μ (fun ω => (Y ω - m (X ω)) ^ 2) + mean μ (fun ω => (m (X ω) - g (X ω)) ^ 2)

/-- **Node N3** (paper proof, record 6, second paragraph: "Its image V_J is finite
dimensional, hence closed. Orthogonal projection of Y onto V_J exists in the Hilbert space
... Choose coefficients representing that projection"). Abstract finite-dimensional least
squares: in any real inner-product space, the distance from `y` to the span of finitely
many vectors is attained by some coefficient vector (no linear independence needed).
Suggested route: `K := Submodule.span ℝ (Set.range v)` is finite-dimensional, hence complete
(`FiniteDimensional.complete`, instance `Submodule.HasOrthogonalProjection.ofCompleteSpace`);
`Submodule.starProjection_minimal` (`‖y - K.starProjection y‖ = ⨅ x : K, ‖y - x‖`),
`ciInf_le` with `OrderBot`-free bound `0 ≤ ‖·‖`; represent `K.starProjection y ∈ K` by
`Submodule.mem_span_range_iff_exists_fun`. -/
def N3 : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (d : ℕ) (v : Fin d → H)
    (y : H), ∃ b : Fin d → ℝ, ∀ c : Fin d → ℝ,
      ‖y - ∑ i, b i • v i‖ ≤ ‖y - ∑ i, c i • v i‖

/-- **Node N4** (paper proof, record 6, second paragraph: "It has natDegree≤J, including when
it is zero, and minimizes E[(Y-q(X))²] over every q with natDegree≤J ... This construction
also works when a=b"). Least-squares polynomials of every degree exist, given the abstract
node `N3` instantiated in `L²(μ)`.
Suggested route: apply `N3` in `Lp ℝ 2 μ` to `y = hY.toLp Y` and
`v k = (hq (X^k)).toLp _` for `k : Fin (J+1)`; set `p = ∑ k, C (b k) * X^k`
(`Polynomial.natDegree_sum_le_of_forall_le`, `natDegree_C_mul_X_pow_le`); any `q` with
`natDegree ≤ J` is `∑ k : Fin (J+1), C (q.coeff k) * X^k`
(`Polynomial.as_sum_range'`, `Fin.sum_univ_eq_sum_range`); `MemLp.toLp_sub`,
`Lp.norm_toLp`/`MeasureTheory.L2.integral_inner_eq_sq_eLpNorm`/`L2.inner_def` to identify
`‖toLp (Y - q X)‖² = ∫ (Y - q X)²`, then `sq_le_sq'`/`pow_le_pow_left` from the norm bound. -/
def N4 : Prop :=
  N3.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → MemLp Y 2 μ →
    (∀ q : Polynomial ℝ, MemLp (fun ω => q.eval (X ω)) 2 μ) →
    ∀ J : ℕ, ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ ∀ q : Polynomial ℝ, q.natDegree ≤ J →
      mean μ (fun ω => (Y ω - p.eval (X ω)) ^ 2) ≤ mean μ (fun ω => (Y ω - q.eval (X ω)) ^ 2)

/-- **Node N5** (paper proof, record 6, third paragraph: "Fix ε>0 and set δ=√ε/2>0.
Weierstrass on I supplies a polynomial q with |m(x)-q(x)|<δ ... E[(m(X)-q(X))²]≤δ²=ε/4<ε.
Put J=natDegree(q). For any J′≥J ... cancel E[e²] to obtain the required error <ε").
The Weierstrass tail for every degree-bounded minimizing family, under `N1` and `N2`.
Suggested route: `a ≤ b` from the a.e. containment (a probability measure is nonzero);
`weierstrass_approximation` (:4127, axiom-clean) with `ε' = √ε/2`; `integral_mono_ae`
against the constant `ε/4` (`Real.sq_sqrt`); minimality at `J'` against `q`
(`q.natDegree ≤ J'`), `N2` for both polynomials (`Polynomial.continuous.measurable`),
then `linarith`. -/
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

/-- The nodes suffice: `N4` (through `N1`'s polynomial L² facts and `N3`) yields a
minimizing family by choice over `J`; `N5` gives the tail for every minimizing family. -/
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
