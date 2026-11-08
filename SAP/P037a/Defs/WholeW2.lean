import Mathlib
import SAP.P037a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical Topology

/-- The positive orthant, including all coordinates of the multiplier vector. -/
def positiveOrthantW2 (n : ℕ) : Set (Fin n → ℝ) := {e | ∀ i, 0 < e i}

/-- The first `m` coordinates; the last coordinate of a chart vector is the total. -/
def headCoordinatesW2 (m : ℕ) (z : Fin (m+1) → ℝ) : Fin m → ℝ :=
  fun i => z i.castSucc

/-- Coordinate order is `(q₁,…,qₘ,t)`, in ordinary `(m+1)`-dimensional volume. -/
def normalizationDomainW2 (m : ℕ) : Set (Fin (m+1) → ℝ) :=
  {z | headCoordinatesW2 m z ∈ openSimplex m ∧ 0 < z (Fin.last m)}

/-- The displayed forward map, with `m=n-1` free probability coordinates. -/
noncomputable def forwardNormalizationW2 (m : ℕ) (e : Fin (m+1) → ℝ) :
    Fin (m+1) → ℝ :=
  Fin.snoc (headCoordinatesW2 m (normalizedWeights e)) (∑ i, e i)

/-- The inverse map `(q,t) ↦ (tq₁,…,tqₘ,t(1-∑qᵢ))`. -/
noncomputable def inverseNormalizationW2 (m : ℕ) (z : Fin (m+1) → ℝ) :
    Fin (m+1) → ℝ :=
  fun i => z (Fin.last m) * appendSimplex m (headCoordinatesW2 m z) i

/-- Independent Exp(1) multipliers. -/
noncomputable def exponentialInputW2 (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => expMeasure 1)

/-- Independent U(0,1) multipliers, with the package's open-interval convention. -/
noncomputable def uniformInputW2 (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => uniformDraw)

/-- The exponential product density, zero outside the positive orthant. -/
noncomputable def exponentialDensityW2 (n : ℕ) (e : Fin n → ℝ) : ℝ≥0∞ :=
  (positiveOrthantW2 n).indicator (fun x => ENNReal.ofReal (Real.exp (-∑ i, x i))) e

/-- Joint density in the displayed `(q₁,…,qₘ,t)` coordinate order, zero elsewhere. -/
noncomputable def normalizationJointDensityW2 (m : ℕ) (z : Fin (m+1) → ℝ) : ℝ≥0∞ :=
  (normalizationDomainW2 m).indicator
    (fun x => ENNReal.ofReal (x (Fin.last m)^m * Real.exp (-x (Fin.last m)))) z

noncomputable def normalizationJointLawW2 (m : ℕ) : Measure (Fin (m+1) → ℝ) :=
  volume.withDensity (normalizationJointDensityW2 m)

/-- The closed coordinate simplex used to connect the existing spacing theorem. -/
def closedSimplexW2 (m : ℕ) : Set (Fin m → ℝ) :=
  {q | (∀ i, 0 ≤ q i) ∧ ∑ i, q i ≤ 1}

/-- Order statistics of `m` draws, in increasing index order. -/
noncomputable def sortedSampleW2 (m : ℕ) (x : Fin m → ℝ) : Fin m → ℝ :=
  x ∘ Tuple.sort x

/-- The first `m` spacings, starting with the gap from zero. -/
noncomputable def firstSpacingsW2 (m : ℕ) (x : Fin m → ℝ) (i : Fin m) : ℝ :=
  if i.val = 0 then sortedSampleW2 m x i
  else sortedSampleW2 m x i - sortedSampleW2 m x ⟨i.val - 1, by omega⟩

/-- All `m+1` spacings; the last is the gap from the largest order statistic to one. -/
noncomputable def allSpacingsW2 (m : ℕ) (x : Fin m → ℝ) : Fin (m+1) → ℝ :=
  appendSimplex m (firstSpacingsW2 m x)

/-- Boundary faces have zero coordinate volume; the open simplex has volume `1/m!`. -/
def simplexVolumeFactsW2 : Prop :=
  ∀ m : ℕ,
    volume.restrict (closedSimplexW2 m) = volume.restrict (openSimplex m) ∧
    volume (openSimplex m) = (m.factorial : ℝ≥0∞)⁻¹

/-- Both maps preserve the indicated domains and are inverse on those domains. -/
def normalizationGeometryW2 : Prop :=
  ∀ m : ℕ,
    (∀ e ∈ positiveOrthantW2 (m+1),
      forwardNormalizationW2 m e ∈ normalizationDomainW2 m ∧
      inverseNormalizationW2 m (forwardNormalizationW2 m e) = e) ∧
    (∀ z ∈ normalizationDomainW2 m,
      inverseNormalizationW2 m z ∈ positiveOrthantW2 (m+1) ∧
      forwardNormalizationW2 m (inverseNormalizationW2 m z) = z)

def inverseJacobianW2 : Prop :=
  ∀ (m : ℕ) (z : Fin (m+1) → ℝ), z ∈ normalizationDomainW2 m →
    DifferentiableAt ℝ (inverseNormalizationW2 m) z ∧
    |(fderiv ℝ (inverseNormalizationW2 m) z).det| = z (Fin.last m)^m

def forwardJacobianW2 : Prop :=
  ∀ (m : ℕ) (e : Fin (m+1) → ℝ), e ∈ positiveOrthantW2 (m+1) →
    DifferentiableAt ℝ (forwardNormalizationW2 m) e ∧
    |(fderiv ℝ (forwardNormalizationW2 m) e).det| = ((∑ i, e i) ^ m)⁻¹

def exponentialProductDensityW2 : Prop :=
  ∀ m : ℕ,
    exponentialInputW2 (m+1) = volume.withDensity (exponentialDensityW2 (m+1)) ∧
    ∀ᵐ e ∂exponentialInputW2 (m+1), e ∈ positiveOrthantW2 (m+1)

def exponentialJointDensityW2 : Prop :=
  ∀ m : ℕ,
    Measure.map (forwardNormalizationW2 m) (exponentialInputW2 (m+1)) =
      normalizationJointLawW2 m

def jointMarginalW2 : Prop :=
  ∀ m : ℕ,
    Measure.map (headCoordinatesW2 m) (normalizationJointLawW2 m) =
      (m.factorial : ℝ≥0∞) • volume.restrict (openSimplex m)

/-- The explicitly defined simplex law is a probability on positive unit-sum weights. -/
def simplexCertificationW2 : Prop :=
  ∀ k : ℕ,
    IsProbabilityMeasure (simplexLaw (k+1)) ∧
    ∀ᵐ p ∂simplexLaw (k+1), (∀ i, 0 < p i) ∧ ∑ i, p i = 1

/-- Arbitrary independent exponential inputs, not just the canonical product sample space. -/
def exponentialConstructionW2 : Prop :=
  ∀ (k : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Fin (k+2) → Ω → ℝ),
    (∀ i, Measurable (E i)) → iIndepFun E μ →
    (∀ i, Measure.map (E i) μ = expMeasure 1) →
    Measure.map (fun ω => normalizedWeights (fun i => E i ω)) μ = simplexLaw (k+1) ∧
    Measure.map (fun ω => forwardNormalizationW2 (k+1) (fun i => E i ω)) μ =
      normalizationJointLawW2 (k+1) ∧
    ∀ᵐ ω ∂μ, 0 < ∑ i, E i ω ∧
      (∀ i, 0 < normalizedWeights (fun j => E j ω) i) ∧
      ∑ i, normalizedWeights (fun j => E j ω) i = 1

/-- Coordinatewise minus-log preserves independence and gives the full exponential construction. -/
def logUniformConstructionW2 : Prop :=
  ∀ (k : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Fin (k+2) → Ω → ℝ),
    (∀ i, Measurable (V i)) → iIndepFun V μ →
    (∀ i, Measure.map (V i) μ = uniformDraw) →
    iIndepFun (fun i ω => -Real.log (V i ω)) μ ∧
    (∀ i, Measure.map (fun ω => -Real.log (V i ω)) μ = expMeasure 1) ∧
    Measure.map (fun ω i => -Real.log (V i ω)) μ = exponentialInputW2 (k+2) ∧
    Measure.map (fun ω => normalizedWeights (fun i => -Real.log (V i ω))) μ =
      simplexLaw (k+1) ∧
    Measure.map (fun ω => forwardNormalizationW2 (k+1) (fun i => -Real.log (V i ω))) μ =
      normalizationJointLawW2 (k+1) ∧
    ∀ᵐ ω ∂μ, 0 < ∑ i, -Real.log (V i ω) ∧
      (∀ i, 0 < normalizedWeights (fun j => -Real.log (V j ω)) i) ∧
      ∑ i, normalizedWeights (fun j => -Real.log (V j ω)) i = 1

/-- All endpoint gaps, strict order almost surely, and the completed simplex law. -/
def spacingConstructionW2 : Prop :=
  ∀ k : ℕ,
    Measure.map (allSpacingsW2 (k+1)) (uniformInputW2 (k+1)) = simplexLaw (k+1) ∧
    ∀ᵐ x ∂uniformInputW2 (k+1),
      StrictMono (sortedSampleW2 (k+1) x) ∧
      (∀ i, sortedSampleW2 (k+1) x i ∈ Ioo 0 1) ∧
      allSpacingsW2 (k+1) x (Fin.last (k+1)) =
        1 - sortedSampleW2 (k+1) x (Fin.last k) ∧
      (∀ i, 0 < allSpacingsW2 (k+1) x i) ∧ ∑ i, allSpacingsW2 (k+1) x i = 1

/-- Full column rank and positive weights justify the inverse and unique WLS refit. -/
def wlsUniquenessW2 : Prop :=
  ∀ {I K : Type} [Fintype I] [Fintype K] [DecidableEq K]
    (w : I → ℝ) (X : Matrix I K ℝ) (y : I → ℝ),
    (∀ i, 0 < w i) → Function.Injective X.mulVec →
    IsUnit (gramWeighted w X).det ∧
    WLS w X y (wlsCoefficient w X y) ∧
    ∀ b : K → ℝ, WLS w X y b → b = wlsCoefficient w X y

/-- Direct independent uniforms remain a different law, including on an arbitrary sample space. -/
def directUniformConstructionW2 : Prop :=
  ∀ (k : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Fin (k+2) → Ω → ℝ),
    (∀ i, Measurable (U i)) → iIndepFun U μ →
    (∀ i, Measure.map (U i) μ = uniformDraw) →
    Measure.map (fun ω => normalizedWeights (fun i => U i ω)) μ = uniformWeightLaw k ∧
    Measure.map (fun ω => normalizedWeights (fun i => U i ω)) μ ≠ simplexLaw (k+1) ∧
    ∀ᵐ ω ∂μ, (∀ i, 0 < U i ω) ∧
      ∀ (d : ℕ) (X : Matrix (Fin (k+2)) (Fin d) ℝ) (y : Fin (k+2) → ℝ),
        Function.Injective X.mulVec →
        wlsCoefficient (normalizedWeights (fun i => U i ω)) X y =
          wlsCoefficient (fun i => U i ω) X y

/-- P037-T5; SI Appendix, Table S6, p. 41, and Table S7, p. 42
(supplement PDF pp. 41–42).
The Bayesian bootstrap uses the probability law with constant density (n-1)!
in the first n-1 open-simplex coordinates, supported on positive unit-sum weights.
For every n≥2, independent Exp(1) multipliers normalized by their sum have this
law; independent U(0,1) draws transformed by minus-log give independent Exp(1)
inputs and the same construction. The forward normalization map in coordinate
order (p₁,…,pₙ₋₁,t) and its inverse have absolute Jacobian determinants
t^{-(n-1)} and t^{n-1}, respectively. The joint density is t^{n-1} exp(-t)
on the open simplex times t>0 and zero elsewhere; its t-integral is (n-1)!.
The n spacings of n-1 ordered independent uniforms, including both endpoint
gaps, have the same simplex law. Direct independent uniform multipliers,
even after normalization, have a different law (ratio-event probabilities
1/6 versus 1/4). Positive common scaling preserves the unique full-rank WLS
coefficient, so raw and normalized uniform replicates agree. The usual
measure-theoretic conditions are assumed. These facts justify the conditional
relabel/recompute correction, without identifying the rule actually used or
supplying replacement standard errors. -/
def T5WholeStatement_W2 : Prop :=
  simplexCertificationW2 ∧ normalizationGeometryW2 ∧
  inverseJacobianW2 ∧ forwardJacobianW2 ∧ exponentialJointDensityW2 ∧
  exponentialConstructionW2 ∧ logUniformExponential ∧ logUniformConstructionW2 ∧
  gammaNormalization ∧ spacingConstructionW2 ∧ uniformWeightsDiffer ∧
  directUniformConstructionW2 ∧ weightScaling ∧ normalizationRefit ∧ wlsUniquenessW2

end SAP.P037a
