import SAP.P015a.Defs.WholeW1
import SAP.P015a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a.WH.W1

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-- Finite-dimensional chain and sum rules for scalar functions of row predictors.
Prove each row map has differential `scoreDifferential (W i)` using the coordinate
projections, compose `HasDerivAt.hasFDerivAt` with that map, and sum. Interchange the
two finite sums to identify the transposed-design gradient. Empty samples and empty
coordinate types give zero maps by the same calculation. About 60 lines. -/
def T8_L1 : Prop :=
  ∀ (n q : ℕ) (W : Matrix (Fin n) (Fin q) ℝ) (f : Fin n → ℝ → ℝ)
    (d : Fin n → ℝ) (θ : Fin q → ℝ),
    (∀ i, HasDerivAt (f i) (d i) (W.mulVec θ i)) →
    HasFDerivAt (fun t => ∑ i, f i (W.mulVec t i))
      (scoreDifferential (W.transpose.mulVec d)) θ

/-- Normalization and exponential tilting for a common-support canonical family.
The density is finite, positive and a.e. measurable by the integrability in
`ValidCanonicalFamily`. Transfer integrability and integrals through `withDensity`.
For η+s*t in I, the density times exp(t*y) is the density at η+s*t times
exp((κ(η+s*t)-κ(η))/s). Nearby normalizations give the MGF formula and an open
neighborhood of zero in `integrableExpSet`. This needs no assumed response moment
or differentiation under an integral. Use the a.e.-measurable density-transfer
lemmas, which do not require a sigma-finite reference measure. About 150 lines. -/
def T8_L2 : Prop :=
  ∀ (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ) (carrier : ℝ → ℝ) (I support : Set ℝ),
    ValidCanonicalFamily ν κ s carrier I support → ∀ η ∈ I,
      IsProbabilityMeasure (canonicalResponseLaw ν κ s carrier η) ∧
      (0 : ℝ) ∈ interior (integrableExpSet (fun y : ℝ => y)
        (canonicalResponseLaw ν κ s carrier η)) ∧
      (∀ t : ℝ, η + s * t ∈ I →
        Integrable (fun y : ℝ => Real.exp (t * y)) (canonicalResponseLaw ν κ s carrier η) ∧
        mgf (fun y : ℝ => y) (canonicalResponseLaw ν κ s carrier η) t =
          Real.exp ((κ (η + s * t) - κ η) / s))

/-- Mean-only Taylor residuals and the Appendix C affine OLS reparameterization,
for every differentiable scalar mean, including Poisson's exp mean. Expand the
intercept predictor using W_i0=1; use `Matrix.mulVec_mulVec` to write Aδ as W'(Wδ).
The two residual vectors equal r-f0*Aδ. Coordinate field algebra proves both
directions of the affine inverse when f0 is nonzero. No full-rank assumption is
needed. About 100 lines; the donors `affine_predictor` give the predictor identity. -/
def T8_L3 : Prop := wholeResidualLinearization

/-- The finite Cox score has risk-set softmax terms. Each risk set contains its
event subject, so its exponential sum is strictly positive. Differentiate the row
predictors, finite exponential sums and their logarithms, then sum the event
contributions and collect coordinates. Zero events or zero coordinates cause no
problem; no event can exist with an empty risk set. About 120 lines. -/
def T8_L4 : Prop :=
  ∀ (n q e : ℕ) (Z : Matrix (Fin n) (Fin q) ℝ) (event : Fin e → Fin n)
    (risk : Fin e → Finset (Fin n)), (∀ k, event k ∈ risk k) →
    ∀ θ : Fin q → ℝ,
      (∀ k, 0 < ∑ j ∈ risk k, Real.exp (Z.mulVec θ j)) ∧
      HasFDerivAt (finiteCoxLikelihood Z event risk)
        (scoreDifferential (finiteCoxScore Z event risk θ)) θ


end
end SAP.P015a.WH.W1
