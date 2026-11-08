import Mathlib
import SAP.P015b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015b

universe u v w z

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

/-- Conditional independence given X, expressed by factorization of conditional
probabilities of measurable events. This works on arbitrary probability spaces;
regular conditional laws are needed only after passage to a real vector's law. -/
def ConditionalIndependentW3 {Ω : Type u} {E : Type v} {F : Type w} {B : Type z}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace B]
    (P : Measure Ω) (X : Ω → E) (Y : Ω → F) (D : Ω → B) : Prop :=
  ∀ (C : Set F) (J : Set B), MeasurableSet C → MeasurableSet J →
    P[(Y ⁻¹' C ∩ D ⁻¹' J).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap X inferInstance] =ᵐ[P]
    fun s => P[(Y ⁻¹' C).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap X inferInstance] s *
      P[(D ⁻¹' J).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap X inferInstance] s

/-- All covariance matrices used by the finite GLS formulas are positive
definite. Thus their inverses are actual inverses, including the precision sum.
The assumptions are exactly the full-rank and covariance assumptions of T10. -/
def PoolingCovariancesW3 : Prop :=
  ∀ (G q : ℕ) (_hG : 1 ≤ G) (_hq : 1 ≤ q)
    (n : Fin G → ℕ) (Z : ∀ g, Matrix (Fin (n g)) (Fin q) ℝ)
    (S : Matrix (Fin q) (Fin q) ℝ) (σ₂ : Fin G → ℝ)
    (_hS : S.PosSemidef) (_hσ : ∀ g, 0 < σ₂ g)
    (_hQ : ∀ g, ((Z g).transpose * Z g).det ≠ 0),
    let P := fun g => precisionMatrix S ((Z g).transpose * Z g) (σ₂ g)
    (∀ g, (S + σ₂ g • ((Z g).transpose * Z g)⁻¹).PosDef ∧
      (P g).PosDef ∧
      (Z g * S * (Z g).transpose + σ₂ g • 1).PosDef) ∧
    (∑ g, P g).PosDef

/-- For prescribed weights, scalar pooling for every coefficient family is
equivalent to the full treatment-row identity. This is equivalent to BOTH
off-treatment zeros and equality of the diagonal to the prescribed weight.
The algebra holds for arbitrary finite matrix families, hence for the GLS maps. -/
def ScalarRowCriterionW3 : Prop :=
  ∀ (G q : ℕ) (A : Fin G → Matrix (Fin q) (Fin q) ℝ)
    (a : Fin G → ℝ) (b : Fin q),
    ((∀ t : Fin G → Fin q → ℝ,
        (∑ g, (A g).mulVec (t g)) b = ∑ g, a g * t g b) ↔
      ∀ g, (A g) b = fun j => if j = b then a g else 0) ∧
    ((∀ g, (A g) b = fun j => if j = b then a g else 0) ↔
      (∀ g j, j ≠ b → A g b j = 0) ∧ ∀ g, A g b b = a g)

/-- A common bound on every coordinate is equivalent to a common bound on the
finite-dimensional sup norms. An explicit bound avoids suprema of empty sets. -/
def UniformlyBoundedCoefficientsW3 {G q : ℕ}
    (t : ℕ → Fin G → Fin q → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ k g j, |t k g j| ≤ M

/-- Vanishing off-treatment entries imply vanishing treatment-pooling error
for every uniformly bounded, possibly varying, coefficient family. The scalar
weights are the treatment DIAGONAL entries at the same index. This stronger
matrix-only formulation applies in particular to every sequence of GLS models. -/
def BoundedInputApproximationW3 : Prop :=
  ∀ (G q : ℕ) (A : ℕ → Fin G → Matrix (Fin q) (Fin q) ℝ) (b : Fin q)
    (_hvanish : ∀ g j, j ≠ b → Tendsto (fun k => A k g b j) atTop (𝓝 0))
    (t : ℕ → Fin G → Fin q → ℝ) (_hbounded : UniformlyBoundedCoefficientsW3 t),
    Tendsto (fun k => (∑ g, (A k g).mulVec (t k g)) b -
      ∑ g, A k g b b * t k g b) atTop (𝓝 0)

/-- Expression (7) applied within ANY group satisfying its own assumptions.
Potential outcomes are Y(d)=Y0+tau*d, as in `treatmentEstimate`. The existing
eight-family `RegressionRegularity` states the sufficient moment/LLN and rank
reading of A.1(4), and includes a positive finite mean residual weight.
No independence or identical distribution ACROSS groups is asserted or needed. -/
def WithinGroupExpression7W3 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℕ) (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (_hD : ∀ i, Measurable (D i)) (_hY : ∀ i, Measurable (Y₀ i))
    (_hτ : ∀ i, Measurable (τ i)) (_hX : ∀ i, Measurable (X i))
    (_hiid : iIndepFun (fun i s => (D i s, Y₀ i s, τ i s, X i s)) P)
    (_hident : ∀ i, IdentDistrib (fun s => (D i s, Y₀ i s, τ i s, X i s))
      (fun s => (D 0 s, Y₀ 0 s, τ 0 s, X 0 s)) P P)
    (_hunconf : ConditionalIndependentW3 P (X 0) (fun s => (Y₀ 0 s, τ 0 s)) (D 0))
    (ω : Fin (K+1) → ℝ)
    (_hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlVector (X 0 s)) ω)
    (_hreg : RegressionRegularity P D Y₀ τ X),
    Integrable (fun s => squaredPopulationResidual P (D 0) (X 0) s * τ 0 s) P ∧
    TendstoInMeasure P (treatmentEstimate D Y₀ τ X) atTop
      (fun _ => (∫ s, squaredPopulationResidual P (D 0) (X 0) s * τ 0 s ∂P) /
        (∫ s, squaredPopulationResidual P (D 0) (X 0) s ∂P))

/-- P015-T10; p. 257 (PDF p. 8), corrected random-coefficient aggregation
description; expression (7), p. 254 (PDF p. 5), under its assumptions within
each group. Usual measure-theoretic conditions are assumed.
For nonempty finite groups and coordinates, full-rank group designs, positive
error variances and a symmetric positive semidefinite coefficient covariance,
all covariance inverses exist. Precision pooling uniquely minimizes the GLS
loss, equals raw-observation GLS and the sum of the matrix-weighted group OLS
vectors, and its matrix weights sum to the identity. Its treatment coordinate
can include other coefficients. For prescribed scalar weights, pooling all
coefficient vectors is equivalent to the full treatment-row identity, hence
to off-treatment zeros AND the prescribed diagonal entries. Treatment-block
diagonal precisions suffice, with weights p_g/sum_h p_h. Along any sequence
with fixed finite dimensions, vanishing off-treatment entries give a vanishing
error for uniformly bounded coefficient inputs, using the treatment diagonal
entries as weights. Expression (7) applies separately in each group satisfying
its causal and regularity assumptions. This qualification is compatible with
consistency under correctly specified random-coefficient and exogeneity
assumptions; it makes no additional consistency assertion. -/
def T10WholeStatement_W3 : Prop :=
  MatrixPooling ∧ PoolingCovariancesW3 ∧ ScalarRowCriterionW3 ∧
    BoundedInputApproximationW3 ∧ WithinGroupExpression7W3.{u} ∧ RawPoolingCounterexample

end
end SAP.P015b
