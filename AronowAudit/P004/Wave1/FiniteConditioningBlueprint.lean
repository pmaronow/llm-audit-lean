import AronowAudit.P004.P004_FiniteGraphCompletion

/-! # Shared blueprint module: finite conditional expectation on the product design (P004)

Shared by the T29 (`NedFarCovariance`) and T44 (`NedHeadline`) blueprints. All nodes concern
the existing project definitions `conditionOn p J U` (the conditional expectation of `U` given
the coordinates in `J`, under the independent-coin product design `designWeight p`) and
`l2Norm p U = sqrt (E[U²])`, for coin probabilities strictly inside `(0,1)`.

Paper-proof source: map-P004 REPORT, record 2, paragraph "Write E_J for the conditional
expectation defined by conditionOn on assignment coordinates J. On the finite product design
its conditioning denominator is positive. Summing over the coordinates outside J proves: E_J
preserves constants and expectations, is positive, is an L² contraction, and E_J E_I=E_I when
I⊆J. Its value depends only on z restricted to J. Functions of disjoint coordinate sets are
independent by factoring the product design weights. Orthogonal projection also gives
||U−E_J U||₂≤||U−E_I U||₂ for I⊆J", and record 7 (projected dependency graphs).

Independence of functions of disjoint coordinate sets is NOT a node: it is the proved
`AronowAudit.P004.GraphCompletion.expect_mul_of_disjoint_depends`
(`P004_FiniteGraphCompletion.lean`, with `DependsOn F S`, `DependsOn G Sᶜ`).
Useful existing lemmas: `expect_split` (two versions), `design_normalized`, `expect_mono`,
`design_weight_nonneg`, `cov_centered`, `variance_le_second`, `variance_sum`,
`ComponentCompletion.expect_abs_le`, `CLTCompletion.designMeasure_integral`.
All nodes are leaves except where a docstring says "uses".
-/

namespace AronowAudit.P004.Wave1.FiniteConditioning

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Coin probabilities strictly inside `(0,1)`. -/
abbrev Admissible {N : ℕ} (p : Fin N → ℝ) : Prop := ∀ i, 0 < p i ∧ p i < 1

/-- FC1 (paper proof: "Its value depends only on z restricted to J"). No positivity needed. -/
def FC1 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ) (J : Finset (Fin N)) (U : Assignment N → ℝ) (z z' : Assignment N),
    (∀ j ∈ J, z j = z' j) → conditionOn p J U z = conditionOn p J U z'

/-- FC2 (paper proof: "E_J preserves constants ... the coefficient can be pulled through the
conditional expectation"): constants, additivity, subtractivity and pulling out a factor that
depends only on the conditioning coordinates. The cylinder `{z' : z'|_J = z|_J}` has design
probability `∏_{j∈J} coin (p j) (z j) > 0` (factor the product weights over `J` and `Jᶜ`). -/
def FC2 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ J : Finset (Fin N),
    (∀ (c : ℝ) (z : Assignment N), conditionOn p J (fun _ => c) z = c) ∧
    (∀ (U V : Assignment N → ℝ) (z : Assignment N),
      conditionOn p J (fun z => U z + V z) z = conditionOn p J U z + conditionOn p J V z) ∧
    (∀ (U V : Assignment N → ℝ) (z : Assignment N),
      conditionOn p J (fun z => U z - V z) z = conditionOn p J U z - conditionOn p J V z) ∧
    (∀ F U : Assignment N → ℝ, (∀ z z', (∀ j ∈ J, z j = z' j) → F z = F z') →
      ∀ z, conditionOn p J (fun z => F z * U z) z = F z * conditionOn p J U z)

/-- FC3 (paper proof: "E_J preserves ... expectations"). -/
def FC3 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (J : Finset (Fin N)) (U : Assignment N → ℝ),
    expect p (conditionOn p J U) = expect p U

/-- FC4 (paper proof: "E_J E_I=E_I when I⊆J"), both orders of the tower property. -/
def FC4 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (I J : Finset (Fin N)), I ⊆ J →
    ∀ U : Assignment N → ℝ,
      conditionOn p J (conditionOn p I U) = conditionOn p I U ∧
      conditionOn p I (conditionOn p J U) = conditionOn p I U

/-- FC5 (paper proof: "is positive"): conditional expectation preserves absolute bounds. -/
def FC5 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (J : Finset (Fin N)) (U : Assignment N → ℝ)
    (M : ℝ), (∀ z, |U z| ≤ M) → ∀ z, |conditionOn p J U z| ≤ M

/-- FC6 (paper proof: "is an L² contraction ... Orthogonal projection also gives
||U−E_J U||₂≤||U−E_I U||₂ for I⊆J; expand the square and note that U−E_J U is orthogonal to
every J-measurable function"). -/
def FC6 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (J : Finset (Fin N)) (U : Assignment N → ℝ),
    l2Norm p (conditionOn p J U) ≤ l2Norm p U ∧
    ∀ I : Finset (Fin N), I ⊆ J →
      l2Norm p (fun z => U z - conditionOn p J U z) ≤ l2Norm p (fun z => U z - conditionOn p I U z)

/-- FC7 (paper proof: "the L² triangle inequality, and the absolute bounds"; "For any X,Y,
|Cov(X,Y)|≤||X||₂||Y||₂: center both variables, apply Cauchy–Schwarz, and use Var(X)≤E[X²]"):
the finite L² algebra of `l2Norm`. Transport to `CLTCompletion.designMeasure` and Mathlib's
`L²` norm, or use the weighted Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq` with `Real.sqrt` directly. -/
def FC7 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p →
    (∀ U : Assignment N → ℝ, 0 ≤ l2Norm p U) ∧
    (∀ U V : Assignment N → ℝ, l2Norm p (fun z => U z + V z) ≤ l2Norm p U + l2Norm p V) ∧
    (∀ U V : Assignment N → ℝ, l2Norm p (fun z => U z - V z) ≤ l2Norm p U + l2Norm p V) ∧
    (∀ {ι : Type} (S : Finset ι) (U : ι → Assignment N → ℝ),
      l2Norm p (fun z => ∑ k ∈ S, U k z) ≤ ∑ k ∈ S, l2Norm p (U k)) ∧
    (∀ (c : ℝ) (U : Assignment N → ℝ), l2Norm p (fun z => c * U z) = |c| * l2Norm p U) ∧
    (∀ (U : Assignment N → ℝ) (M : ℝ), (∀ z, |U z| ≤ M) → l2Norm p U ≤ M) ∧
    (∀ U V : Assignment N → ℝ, (∀ z, |U z| ≤ |V z|) → l2Norm p U ≤ l2Norm p V) ∧
    (∀ U V : Assignment N → ℝ, |expect p (fun z => U z * V z)| ≤ l2Norm p U * l2Norm p V) ∧
    (∀ U V : Assignment N → ℝ, |cov p U V| ≤ l2Norm p U * l2Norm p V) ∧
    (∀ U : Assignment N → ℝ, expect p U = 0 → variance p U = (l2Norm p U)^2)

/-- FC8 (paper proof: "Because Z_i belongs to every nonnegative-radius ball about i, its
coefficient can be pulled through the conditional expectation ... Constants and the arm fits
cancel in this projection error"): for a score that is an own-coin affine function of `U`,
the projection error is at most the coefficient bound times that of `U`, when `i ∈ J`.
Uses FC2 and FC7. -/
def FC8 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (J : Finset (Fin N)) (i : Fin N), i ∈ J →
    ∀ (U : Assignment N → ℝ) (α β : Bool → ℝ) (A : ℝ), (∀ a, |α a| ≤ A) →
      l2Norm p (fun z => α (z i) * U z + β (z i) -
          conditionOn p J (fun z => α (z i) * U z + β (z i)) z) ≤
        A * l2Norm p (fun z => U z - conditionOn p J U z)

/-- FC9 (paper proof, record 7: "If two finite groups have no such cross-edge, the unions of
their r-balls are disjoint by the metric triangle inequality, so the full two families of
projected scores are independent by product assignment"): a family whose members depend on
coordinate sets that are disjoint across non-neighbours has a genuine finite dependency graph.
Pattern: `design_dependency_graph` (`P004_FiniteGraphCompletion.lean`), with
`GraphCompletion.expect_mul_of_disjoint_depends` applied to the unions of the sets. -/
def FC9 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (V : CircleTable N)
    (S : Fin N → Set (Fin N)) (B : Fin N → Finset (Fin N)),
    (∀ i, i ∈ B i) → (∀ i j, j ∈ B i ↔ i ∈ B j) → (∀ i, DependsOn (V i) (S i)) →
    (∀ i j, j ∉ B i → Disjoint (S i) (S j)) → FiniteDependencyGraph p V B

end
end AronowAudit.P004.Wave1.FiniteConditioning
