import Mathlib
import SAP.P022.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022
open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
noncomputable section

-- SAP version of AronowAudit/P022/P022_Variance.lean:Design
structure Design where
  N : ℕ
  m : ℕ
  k : ℕ
  population_min : 4 ≤ N
  treatment_min : 2 ≤ m
  control_min : 2 ≤ k
  sample_le : m + k ≤ N

-- SAP version of AronowAudit/P022/P022_Variance.lean:Assignment
abbrev Assignment (d : Design) := Equiv.Perm (Fin d.N)

-- SAP version of AronowAudit/P022/P022_Variance.lean:finiteMean
def finiteMean {N : ℕ} (v : Fin N → ℝ) : ℝ := 𝔼 i, v i

-- SAP version of AronowAudit/P022/P022_Variance.lean:finiteVariance
def finiteVariance {N : ℕ} (v : Fin N → ℝ) : ℝ :=
  finiteMean (fun i => (v i - finiteMean v) ^ 2)

-- SAP version of AronowAudit/P022/P022_Variance.lean:finiteCovariance
def finiteCovariance {N : ℕ} (v w : Fin N → ℝ) : ℝ :=
  finiteMean (fun i => (v i - finiteMean v) * (w i - finiteMean w))

-- SAP version of AronowAudit/P022/P022_Variance.lean:designExpectation
def designExpectation (d : Design) (f : Assignment d → ℝ) : ℝ := 𝔼 π, f π

-- SAP version of AronowAudit/P022/P022_Variance.lean:designProbability
def designProbability (d : Design) (event : Assignment d → Prop) : ℝ :=
  by
    classical
    exact designExpectation d (fun π => if event π then 1 else 0)

-- SAP version of AronowAudit/P022/P022_Variance.lean:designVariance
def designVariance (d : Design) (f : Assignment d → ℝ) : ℝ :=
  designExpectation d (fun π => (f π - designExpectation d f) ^ 2)

-- SAP version of AronowAudit/P022/P022_Variance.lean:observedTreatment
def observedTreatment (d : Design) (y : Fin d.N → ℝ) (π : Assignment d) :
    Fin d.m → ℝ := fun i => y (π ⟨i.val, by have := d.sample_le; omega⟩)

-- SAP version of AronowAudit/P022/P022_Variance.lean:observedControl
def observedControl (d : Design) (y : Fin d.N → ℝ) (π : Assignment d) :
    Fin d.k → ℝ := fun i => y (π ⟨d.m + i.val, by have := d.sample_le; omega⟩)

-- SAP version of AronowAudit/P022/P022_Variance.lean:averageEffect
def averageEffect (d : Design) (y1 y0 : Fin d.N → ℝ) : ℝ :=
  finiteMean y1 - finiteMean y0

-- SAP version of AronowAudit/P022/P022_Variance.lean:estimatedEffect
def estimatedEffect (d : Design) (y1 y0 : Fin d.N → ℝ) (π : Assignment d) : ℝ :=
  finiteMean (observedTreatment d y1 π) - finiteMean (observedControl d y0 π)

-- SAP version of AronowAudit/P022/P022_Variance.lean:trueVariance
def trueVariance (d : Design) (y1 y0 : Fin d.N → ℝ) : ℝ :=
  designVariance d (estimatedEffect d y1 y0)

-- SAP version of AronowAudit/P022/P022_Variance.lean:varianceExpression
def varianceExpression (N m k : ℕ) (v1 v0 cov : ℝ) : ℝ :=
  (((N : ℝ) - m) / m * v1 + ((N : ℝ) - k) / k * v0 + 2 * cov) /
    ((N : ℝ) - 1)

-- SAP version of AronowAudit/P022/P022_Variance.lean:empiricalCDF
def empiricalCDF {N : ℕ} (y : Fin N → ℝ) (x : ℝ) : ℝ :=
  finiteMean (fun i => if y i ≤ x then 1 else 0)

-- SAP version of AronowAudit/P022/P022_Variance.lean:empiricalLeftCDF
def empiricalLeftCDF {N : ℕ} (y : Fin N → ℝ) (x : ℝ) : ℝ :=
  finiteMean (fun i => if y i < x then 1 else 0)

-- SAP version of AronowAudit/P022/P022_Variance.lean:sortedOutcomes
def sortedOutcomes {N : ℕ} (y : Fin N → ℝ) : List ℝ :=
  (List.ofFn y).mergeSort (fun a b => decide (a ≤ b))

-- SAP version of AronowAudit/P022/P022_Variance.lean:orderStatistic
def orderStatistic {N : ℕ} (y : Fin N → ℝ) (r : ℕ) : ℝ :=
  (sortedOutcomes y).getD (r - 1) 0

-- SAP version of AronowAudit/P022/P022_Variance.lean:empiricalQuantile
def empiricalQuantile {N : ℕ} (y : Fin N → ℝ) (u : ℝ) : ℝ :=
  orderStatistic y (Nat.ceil ((N : ℝ) * u))

-- SAP version of AronowAudit/P022/P022_Variance.lean:BoundSide
inductive BoundSide | H | L
  deriving DecidableEq

-- SAP version of AronowAudit/P022/P022_Variance.lean:sharpCovariance
def sharpCovariance {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (B : BoundSide) : ℝ :=
  (∫ u in (0 : ℝ)..1, empiricalQuantile a u *
    empiricalQuantile b (if B = .H then u else 1 - u)) -
      finiteMean a * finiteMean b

-- SAP version of AronowAudit/P022/P022_Variance.lean:populationBound
def populationBound (d : Design) (y1 y0 : Fin d.N → ℝ) (B : BoundSide) : ℝ :=
  varianceExpression d.N d.m d.k (finiteVariance y1) (finiteVariance y0)
    (sharpCovariance y1 y0 B)

-- SAP version of AronowAudit/P022/P022_Variance.lean:sampleVariance
def sampleVariance {s : ℕ} (y : Fin s → ℝ) : ℝ :=
  (∑ i, (y i - finiteMean y) ^ 2) / ((s : ℝ) - 1)

-- SAP version of AronowAudit/P022/P022_Variance.lean:marginalVarianceEstimate
def marginalVarianceEstimate {s : ℕ} (N : ℕ) (y : Fin s → ℝ) : ℝ :=
  ((N : ℝ) - 1) / N * sampleVariance y

-- SAP version of AronowAudit/P022/P022_Variance.lean:estimateBound
def estimateBound {m k : ℕ} (N : ℕ) (a : Fin m → ℝ) (b : Fin k → ℝ)
    (B : BoundSide) : ℝ :=
  varianceExpression N m k (marginalVarianceEstimate N a)
    (marginalVarianceEstimate N b) (sharpCovariance a b B)

-- SAP version of AronowAudit/P022/P022_Variance.lean:estimatedVariance
def estimatedVariance (d : Design) (y1 y0 : Fin d.N → ℝ) (B : BoundSide)
    (π : Assignment d) : ℝ :=
  estimateBound d.N (observedTreatment d y1 π) (observedControl d y0 π) B

-- SAP version of AronowAudit/P022/P022_Variance.lean:conventionalEstimate
def conventionalEstimate (d : Design) (y1 y0 : Fin d.N → ℝ)
    (π : Assignment d) : ℝ :=
  (d.N : ℝ) / ((d.N : ℝ) - 1) *
    (marginalVarianceEstimate d.N (observedTreatment d y1 π) / d.m +
     marginalVarianceEstimate d.N (observedControl d y0 π) / d.k)

-- SAP version of AronowAudit/P022/P022_Variance.lean:neymanEstimate
def neymanEstimate (d : Design) (y1 y0 : Fin d.N → ℝ) (B : BoundSide)
    (π : Assignment d) : ℝ :=
  let A := marginalVarianceEstimate d.N (observedTreatment d y1 π)
  let C := marginalVarianceEstimate d.N (observedControl d y0 π)
  varianceExpression d.N d.m d.k A C
    (if B = .H then Real.sqrt (A * C) else -Real.sqrt (A * C))

-- SAP version of AronowAudit/P022/P022_Variance.lean:ExperimentSequence
structure ExperimentSequence where
  design : ℕ → Design
  size : ∀ q, (design q).N = q + 4
  y1 : ℕ → ℝ
  y0 : ℕ → ℝ

-- SAP version of AronowAudit/P022/P022_Variance.lean:rowOutcomes
def rowOutcomes (S : ExperimentSequence) (treatment : Bool) (q : ℕ) :
    Fin (S.design q).N → ℝ :=
  fun i => (if treatment then S.y1 else S.y0) i.val

-- SAP version of AronowAudit/P022/P022_Variance.lean:JointLaw
abbrev JointLaw := ProbabilityMeasure (ℝ × ℝ)

-- SAP version of AronowAudit/P022/P022_Variance.lean:lawCDF
def lawCDF (H : JointLaw) (treatment : Bool) (x : ℝ) : ℝ :=
  ((H : Measure (ℝ × ℝ)) {p | (if treatment then p.1 else p.2) ≤ x}).toReal

-- SAP version of AronowAudit/P022/P022_Variance.lean:lawLeftCDF
def lawLeftCDF (H : JointLaw) (treatment : Bool) (x : ℝ) : ℝ :=
  ((H : Measure (ℝ × ℝ)) {p | (if treatment then p.1 else p.2) < x}).toReal

-- SAP version of AronowAudit/P022/P022_Variance.lean:weakPopulationConvergence
def weakPopulationConvergence (S : ExperimentSequence) (H : JointLaw) : Prop :=
  ∀ f : BoundedContinuousFunction (ℝ × ℝ) ℝ,
    Tendsto (fun q => finiteMean (fun i : Fin (S.design q).N =>
      f (S.y1 i.val, S.y0 i.val))) atTop
        (𝓝 (∫ p, f p ∂(H : Measure (ℝ × ℝ))))

-- SAP version of AronowAudit/P022/P022_Variance.lean:Conditions123
def Conditions123 (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ) : Prop :=
  0 < θ ∧ θ ≤ 1 ∧ 0 < ρ ∧ ρ < 1 ∧
  Tendsto (fun q => ((S.design q).m : ℝ) / (S.design q).N) atTop (𝓝 (θ * ρ)) ∧
  Tendsto (fun q => (((S.design q).m : ℝ) + (S.design q).k) / (S.design q).N)
    atTop (𝓝 θ) ∧
  weakPopulationConvergence S H ∧
  (∀ t x, ¬ContinuousAt (lawCDF H t) x →
    Tendsto (fun q => empiricalCDF (rowOutcomes S t q) x) atTop (𝓝 (lawCDF H t x)))

-- SAP version of AronowAudit/P022/P022_Variance.lean:UniformSquareIntegrability
def UniformSquareIntegrability (S : ExperimentSequence) : Prop :=
  ∀ t : Bool, Tendsto (fun β : ℝ => sSup (Set.range (fun q =>
    finiteMean (fun i : Fin (S.design q).N =>
      let y := (if t then S.y1 else S.y0) i.val
      if β ≤ y ^ 2 then y ^ 2 else 0)))) atTop (𝓝 0) ∧
    (∀ β : ℝ, BddAbove (Set.range (fun q =>
      finiteMean (fun i : Fin (S.design q).N =>
        let y := (if t then S.y1 else S.y0) i.val
        if β ≤ y ^ 2 then y ^ 2 else 0))))

-- SAP version of AronowAudit/P022/P022_Variance.lean:AtomLeftConvergence
def AtomLeftConvergence (S : ExperimentSequence) (H : JointLaw) : Prop :=
  ∀ t x, ¬ContinuousAt (lawCDF H t) x →
    Tendsto (fun q => empiricalLeftCDF (rowOutcomes S t q) x)
      atTop (𝓝 (lawLeftCDF H t x))

-- SAP version of AronowAudit/P022/P022_Variance.lean:cdfDistance
def cdfDistance (A B : ℝ → ℝ) : ℝ := sSup (Set.range (fun x => |A x - B x|))

-- SAP version of AronowAudit/P022/P022_Variance.lean:sampledCDF
def sampledCDF (S : ExperimentSequence) (t : Bool) (q : ℕ)
    (π : Assignment (S.design q)) : ℝ → ℝ :=
  if t then empiricalCDF (observedTreatment (S.design q) (rowOutcomes S true q) π)
  else empiricalCDF (observedControl (S.design q) (rowOutcomes S false q) π)

-- SAP version of AronowAudit/P022/P022_Variance.lean:scaledProbabilityLimsup
def scaledProbabilityLimsup (S : ExperimentSequence)
    (events : (q : ℕ) → Assignment (S.design q) → Prop) : ℝ≥0∞ :=
  Filter.limsup (fun q => ENNReal.ofReal
    ((S.design q).N * designProbability (S.design q) (events q))) atTop

end
end SAP.P022
