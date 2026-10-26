import AronowAudit.P004.P004_FiniteGraphCompletion

/-! # Finite conditional expectation on the product design (P004)

The statements concern conditional expectation given assignment coordinates J
and the L² norm sqrt(E[U²]), for coin probabilities strictly inside `(0,1)`.
The conditioning denominator is positive. Summing over complementary
coordinates shows preservation of constants and expectations, positivity,
L² contraction, and the tower identities when I⊆J. The conditional expectation
depends only on the coordinates in J.

Functions of disjoint coordinate sets are independent by factorization of
the product weights. Orthogonal projection also gives
||U−E_J U||₂≤||U−E_I U||₂ for I⊆J.
-/

namespace AronowAudit.P004.Wave1.FiniteConditioning

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Coin probabilities strictly inside `(0,1)`. -/
abbrev Admissible {N : ℕ} (p : Fin N → ℝ) : Prop := ∀ i, 0 < p i ∧ p i < 1

/-- Conditioning depends only on the coordinates in J; no positivity is needed. -/
def FC1 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ) (J : Finset (Fin N)) (U : Assignment N → ℝ) (z z' : Assignment N),
    (∀ j ∈ J, z j = z' j) → conditionOn p J U z = conditionOn p J U z'

/-- Constants, additivity, subtraction, and pulling out a factor that
depends only on the conditioning coordinates. The cylinder `{z' : z'|_J = z|_J}`
has design probability `∏_{j∈J} coin (p j) (z j) > 0`, by factoring the product
weights over J and its complement. -/
def FC2 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ J : Finset (Fin N),
    (∀ (c : ℝ) (z : Assignment N), conditionOn p J (fun _ => c) z = c) ∧
    (∀ (U V : Assignment N → ℝ) (z : Assignment N),
      conditionOn p J (fun z => U z + V z) z = conditionOn p J U z + conditionOn p J V z) ∧
    (∀ (U V : Assignment N → ℝ) (z : Assignment N),
      conditionOn p J (fun z => U z - V z) z = conditionOn p J U z - conditionOn p J V z) ∧
    (∀ F U : Assignment N → ℝ, (∀ z z', (∀ j ∈ J, z j = z' j) → F z = F z') →
      ∀ z, conditionOn p J (fun z => F z * U z) z = F z * conditionOn p J U z)

/-- Conditional expectation preserves expectation. -/
def FC3 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (J : Finset (Fin N)) (U : Assignment N → ℝ),
    expect p (conditionOn p J U) = expect p U

/-- Both tower identities for nested coordinate sets I⊆J. -/
def FC4 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (I J : Finset (Fin N)), I ⊆ J →
    ∀ U : Assignment N → ℝ,
      conditionOn p J (conditionOn p I U) = conditionOn p I U ∧
      conditionOn p I (conditionOn p J U) = conditionOn p I U

/-- Conditional expectation preserves absolute bounds. -/
def FC5 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (J : Finset (Fin N)) (U : Assignment N → ℝ)
    (M : ℝ), (∀ z, |U z| ≤ M) → ∀ z, |conditionOn p J U z| ≤ M

/-- L² contraction and monotonicity of the projection error:
||U−E_J U||₂≤||U−E_I U||₂ for I⊆J. Expand the square and use orthogonality
of U−E_J U to every J-measurable function. -/
def FC6 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (J : Finset (Fin N)) (U : Assignment N → ℝ),
    l2Norm p (conditionOn p J U) ≤ l2Norm p U ∧
    ∀ I : Finset (Fin N), I ⊆ J →
      l2Norm p (fun z => U z - conditionOn p J U z) ≤ l2Norm p (fun z => U z - conditionOn p I U z)

/-- Finite L² algebra: the triangle inequality, absolute bounds, and
|Cov(X,Y)|≤||X||₂||Y||₂. For the covariance bound, center both variables,
apply Cauchy–Schwarz, and use Var(X)≤E[X²]. The finite weighted
Cauchy–Schwarz inequality also proves the product bound directly. -/
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

/-- For a score that is an own-coin affine function of U, the projection
error is at most the coefficient bound times that of U, when i∈J.
The own-coin coefficient can be pulled through conditioning; constants and
the arm fits cancel in the projection error. -/
def FC8 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (J : Finset (Fin N)) (i : Fin N), i ∈ J →
    ∀ (U : Assignment N → ℝ) (α β : Bool → ℝ) (A : ℝ), (∀ a, |α a| ≤ A) →
      l2Norm p (fun z => α (z i) * U z + β (z i) -
          conditionOn p J (fun z => α (z i) * U z + β (z i)) z) ≤
        A * l2Norm p (fun z => U z - conditionOn p J U z)

/-- A family whose members depend on coordinate sets disjoint across
non-neighbours has a finite dependency graph. For two groups with no cross-edge,
the unions of their coordinate sets are disjoint, so product assignment gives
independence of the entire two families. -/
def FC9 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ), Admissible p → ∀ (V : CircleTable N)
    (S : Fin N → Set (Fin N)) (B : Fin N → Finset (Fin N)),
    (∀ i, i ∈ B i) → (∀ i j, j ∈ B i ↔ i ∈ B j) → (∀ i, DependsOn (V i) (S i)) →
    (∀ i j, j ∉ B i → Disjoint (S i) (S j)) → FiniteDependencyGraph p V B

end
end AronowAudit.P004.Wave1.FiniteConditioning
