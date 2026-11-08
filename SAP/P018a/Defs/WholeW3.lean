import Mathlib
import SAP.P018a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section
namespace SAP.P018a
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ENNReal

/-- Conditional expectation of the total score, taken coordinate by coordinate. -/
def conditionalScoreSumW3 {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) : (Fin N → U) → Vec k :=
  fun ω a => (unitSampleLaw K N)[(fun z => scoreSum K z a) | designSigma K] ω

/-- The score sum with each residual replaced by its conditional mean. -/
def residualMeanScoreSumW3 {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) : (Fin N → U) → Vec k :=
  fun ω => ∑ d : Dyad N, score (design K ω d) (conditionalResidualMean K d ω)

/-- Conditional covariance matrix of the total score given the entire design. -/
def conditionalScoreVarianceW3 {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) : (Fin N → U) → Mat k :=
  fun ω a b => (unitSampleLaw K N)[(fun z =>
    (scoreSum K z a - conditionalScoreSumW3 K z a) *
    (scoreSum K z b - conditionalScoreSumW3 K z b)) | designSigma K] ω

/-- The omitted between-design variance. -/
def omittedVarianceW3 {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) : Mat k :=
  varMat (unitSampleLaw K N) (residualMeanScoreSumW3 K)

/-- Ordered diagonal-plus-neighbor sum; each diagonal occurs once. -/
def diagonalNeighborsW3 {k N : ℕ} (A : Dyad N → Dyad N → Mat k) : Mat k :=
  ∑ d, (A d d + ∑ f ∈ neighbors d, A d f)

/-- Raw second moment of two single-record scores. -/
def scoreMomentW3 {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d f : Dyad N) : Mat k :=
  meanMat (unitSampleLaw K N) (fun ω =>
    (epsilon K ω d * epsilon K ω f) • outer (design K ω d) (design K ω f))

/-- The same score moment written using a conditional residual second moment. -/
def conditionalSecondMomentW3 {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d f : Dyad N) : Mat k :=
  meanMat (unitSampleLaw K N) (fun ω =>
    ((unitSampleLaw K N)[(fun z => epsilon K z d * epsilon K z f) |
      designSigma K] ω) • outer (design K ω d) (design K ω f))

/-- All raw score cross-moments, including ordered disjoint pairs. -/
def fullRawW3 {Ω : Type*} [MeasurableSpace Ω] {k N : ℕ}
    (P : Measure Ω) (q : Ω → Dyad N → Vec k) : Mat k :=
  ∑ d, ∑ f, meanMat P (fun ω => outer (q ω d) (q ω f))

/-- Raw score cross-moments over all ordered overlapping pairs. -/
def sparseRawW3 {Ω : Type*} [MeasurableSpace Ω] {k N : ℕ}
    (P : Measure Ω) (q : Ω → Dyad N → Vec k) : Mat k :=
  ∑ d, ∑ f, if overlap d f then meanMat P (fun ω => outer (q ω d) (q ω f)) else 0

/-- Unconditional covariances over all ordered overlapping pairs. -/
def sparseCovW3 {Ω : Type*} [MeasurableSpace Ω] {k N : ℕ}
    (P : Measure Ω) (q : Ω → Dyad N → Vec k) : Mat k :=
  ∑ d, ∑ f, if overlap d f then covMat P (fun ω => q ω d) (fun ω => q ω f) else 0

/-- The centering products which a sparse raw-moment replacement must retain. -/
def sparseMeansW3 {Ω : Type*} [MeasurableSpace Ω] {k N : ℕ}
    (P : Measure Ω) (q : Ω → Dyad N → Vec k) : Mat k :=
  ∑ d, ∑ f, if overlap d f then
    outer (meanVec P (fun ω => q ω d)) (meanVec P (fun ω => q ω f)) else 0

/-- Centered sparse covariance identity and its exact raw-moment criterion. -/
def blockCovarianceConclusionsW3 {Ω : Type*} [MeasurableSpace Ω] {k N : ℕ}
    (P : Measure Ω) (q : Ω → Dyad N → Vec k) : Prop :=
  let S := fun ω => ∑ d, q ω d
  meanVec P S = 0 ∧
  varMat P S = fullRawW3 P q ∧
  varMat P S = sparseCovW3 P q ∧
  varMat P S = sparseRawW3 P q - sparseMeansW3 P q ∧
  sparseRawW3 P q = varMat P S + sparseMeansW3 P q ∧
  (sparseRawW3 P q = varMat P S ↔ sparseMeansW3 P q = 0) ∧
  ((∀ d, meanVec P (fun ω => q ω d) = 0) → sparseRawW3 P q = varMat P S) ∧
  (∑ d, meanVec P (fun ω => q ω d)) = 0

/-- The unweighted repeated prescription, with its literal record normalization. -/
def repeatedConclusionsW3 {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) : Prop :=
  let q := repeatedBlockScore R (repeatedBeta R N)
  let S := fun ω => ∑ d : Dyad N, q ω d
  0 < repeatedL R N ∧
  (∀ d a, MemLp (fun ω => q ω d a) 2 (repeatedLaw R N)) ∧
  (∀ d f, ¬overlap d f → IndepFun (fun ω => q ω d) (fun ω => q ω f) (repeatedLaw R N)) ∧
  blockCovarianceConclusionsW3 (repeatedLaw R N) q ∧
  meanMat (repeatedLaw R N) (fun ω => (repeatedL R N)⁻¹ • repeatedGram R ω) = repeatedH R N ∧
  repeatedTarget R N = ((N : ℝ)/(repeatedL R N)^2) •
    sandwich (repeatedH R N)⁻¹ (sparseCovW3 (repeatedLaw R N) q) ∧
  repeatedTarget R N = varMat (repeatedLaw R N) (fun ω =>
    (repeatedH R N)⁻¹.mulVec ((Real.sqrt N / repeatedL R N) • S ω))

/-- The record-weighted prescription; weights may be any fixed real numbers. -/
def weightedConclusionsW3 {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (w : (d : Dyad N) → Fin (R.T N d) → ℝ) : Prop :=
  let q := recordWeightedBlockScore R w (recordWeightedBeta R w)
  let S := fun ω => ∑ d : Dyad N, q ω d
  (∀ d a, MemLp (fun ω => q ω d a) 2 (repeatedLaw R N)) ∧
  (∀ d f, ¬overlap d f → IndepFun (fun ω => q ω d) (fun ω => q ω f) (repeatedLaw R N)) ∧
  blockCovarianceConclusionsW3 (repeatedLaw R N) q ∧
  meanMat (repeatedLaw R N) (fun ω => (Dreal N)⁻¹ • recordWeightedGram R w ω) = recordWeightedH R w ∧
  recordWeightedTarget R w = ((N : ℝ)/(Dreal N)^2) •
    sandwich (recordWeightedH R w)⁻¹ (sparseCovW3 (repeatedLaw R N) q) ∧
  recordWeightedTarget R w = varMat (repeatedLaw R N) (fun ω =>
    (recordWeightedH R w)⁻¹.mulVec ((Real.sqrt N / Dreal N) • S ω))

/-- p. 566 (PDF p. 3), equation (2); p. 573 (PDF p. 10), equation (6) and
Appendix B; p. 568 and p. 576, repeated and weighted covariance targets.
Under the usual measure-theoretic conditions, the symmetric iid single-record
model has centered scores, zero disjoint raw moments, the corrected sparse
second-moment meat, the full law of total covariance and its omitted positive
semidefinite term, the disjoint conditional remainder, the overlap representation
of Gamma, and the exact finite-N and limiting sandwiches. Projection orthogonality
alone need not remove the omitted term. For bounded finite repeated records and
fixed real weights with nonsingular population Gram, the total score is centered;
its covariance equals the full raw double sum and the sparse unconditional
covariance sum. The sparse raw sum is valid exactly when the sparse block-mean
products cancel, in particular if every block is centered. Global centering alone
is insufficient. The repeated and weighted targets use N/L^2 and N/D^2,
respectively. No fitted-residual consistency is asserted here. -/
def T2WholeStatement_W3 : Prop :=
  T2Statement.{u} ∧
  (∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (K : Kernel U k), Standing K →
    (∀ N : ℕ, 2 ≤ N →
      conditionalScoreSumW3 (N := N) K =ᵐ[unitSampleLaw K N] residualMeanScoreSumW3 K ∧
      omittedVarianceW3 (N := N) K = varMat (unitSampleLaw K N) (conditionalScoreSumW3 K) ∧
      (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) =
        meanMat (unitSampleLaw K N) (conditionalScoreVarianceW3 K) ∧
      varMat (unitSampleLaw K N) (scoreSum K) =
        meanMat (unitSampleLaw K N) (conditionalScoreVarianceW3 K) +
          varMat (unitSampleLaw K N) (conditionalScoreSumW3 K) ∧
      correctedSigma K N = diagonalNeighborsW3 (N := N) (scoreMomentW3 K) ∧
      correctedSigma K N = diagonalNeighborsW3 (N := N) (conditionalSecondMomentW3 K) ∧
      (∀ d : Dyad N, meanMat (unitSampleLaw K N) (fun ω =>
        outer (score (design K ω d) (epsilon K ω d))
          (score (design K ω d) (epsilon K ω d))) = scoreH K) ∧
      (∀ d f : Dyad N, d ≠ f → overlap d f →
        meanMat (unitSampleLaw K N) (fun ω =>
          outer (score (design K ω d) (epsilon K ω d))
            (score (design K ω f) (epsilon K ω f))) = projectionGamma K) ∧
      trueTarget K N = sandwich (populationGram K)⁻¹
        ((2/((N : ℝ)-1)) • scoreH K +
          (4*((N : ℝ)-2)/((N : ℝ)-1)) • projectionGamma K) ∧
      ((N : ℝ)/(Dreal N)^2) • sandwich (populationGram K)⁻¹
        (meanMat (unitSampleLaw K N) (fun ω =>
          meat members (fun d => score (design K ω d) (epsilon K ω d)))) = trueTarget K N) ∧
    (projectionGamma K).transpose = projectionGamma K) ∧
  (∃ (K : Kernel ℝ 2) (N : ℕ), Standing K ∧ 2 ≤ N ∧
    (∀ d : Dyad N, meanVec (unitSampleLaw K N) (fun ω =>
      score (design K ω d) (epsilon K ω d)) = 0) ∧ omittedVarianceW3 (N := N) K ≠ 0) ∧
  (∀ {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k),
    1 ≤ k → 2 ≤ N → RepeatedAtSize R N →
    ((repeatedH R N).det ≠ 0 → repeatedConclusionsW3 (N := N) R) ∧
    (∀ w : (d : Dyad N) → Fin (R.T N d) → ℝ,
      (recordWeightedH R w).det ≠ 0 → weightedConclusionsW3 R w)) ∧
  (∃ R : RepeatedKernel Unit 1, RepeatedAtSize R 4 ∧ (repeatedH R 4).det ≠ 0 ∧
    let q := repeatedBlockScore R (repeatedBeta R 4)
    meanVec (repeatedLaw R 4) (fun ω => ∑ d : Dyad 4, q ω d) = 0 ∧
    varMat (repeatedLaw R 4) (fun ω => ∑ d : Dyad 4, q ω d) = 0 ∧
    sparseRawW3 (repeatedLaw R 4) q = !![(2 : ℝ)] ∧
    sparseMeansW3 (repeatedLaw R 4) q = !![(2 : ℝ)])

end SAP.P018a
