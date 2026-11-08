import Mathlib
import SAP.P018a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section
namespace SAP.P018a
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

/-- A pivot extended by zero where its estimated variance is nonpositive.
`Real.sqrt` and real division give exactly this extension. -/
def W1Pivot {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (c : Vec k) (ω : Fin N → U) : ℝ :=
  dot c (coefficientError K ω) /
    Real.sqrt (dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c))

/-- The ordered shared-endpoint score moment under three independent units. -/
def W1SharedScoreMoment {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) : Mat k :=
  meanMat ((K.μ.prod K.μ).prod K.μ) (fun z =>
    outer (populationScore K z.1.1 z.1.2) (populationScore K z.1.1 z.2))

/-- P018-T13; p. 576 (PDF p. 13), Appendix E, display for the logistic variance estimator.
The six specified binary dyads have a globally strictly concave log-likelihood uniquely
maximized at zero, and the stated exact bread, meats, distinct positive definite
covariances, difference, and unit-incidence identity. -/
def T13WholeStatement : Prop :=
  T13Statement ∧ StrictConcaveOn ℝ Set.univ
    (fun β : Vec 2 => ∑ d, logLikelihood (logitX d) (logitY d) β)

/-- P018-T8; p. 567 (PDF p. 4), after Proposition 1; p. 565 (PDF p. 2);
p. 573 (PDF p. 10), Appendix A.
Under the standing bounded symmetric unit-kernel model, the projection CLT (allowing
singular limits), target limit, and sandwich consistency hold. Every contrast of positive
limiting variance has a standard normal zero-extended pivot, vanishing probability of
nonpositive estimated variance, and nominal confidence coverage. The shared-endpoint
moment equals the projection covariance. The specified zero-variance slope supplies a
failure of normal inference. -/
def T8WholeStatement : Prop :=
  (∀ {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k), Standing K →
    projectionGamma K = W1SharedScoreMoment K ∧
    (∃ ν : Measure (Vec k), centeredNormalLaw ν (limitingTarget K) ∧
      weakLimit (unitSampleLaw K) (fun N ω => Real.sqrt N • coefficientError K ω) ν) ∧
    Tendsto (trueTarget K) atTop (𝓝 (limitingTarget K)) ∧
    inProbability (unitSampleLaw K) (fun N ω =>
      (N : ℝ) • sampleVariance members (design K ω) (response K ω) - limitingTarget K) ∧
    ∀ c : Vec k, 0 < dot c ((limitingTarget K).mulVec c) →
      weakLimit (unitSampleLaw K) (fun _ ω => W1Pivot K c ω) (gaussianReal 0 1) ∧
      Tendsto (fun N : ℕ => (unitSampleLaw K N {ω |
        dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c) ≤ 0}).toReal)
        atTop (𝓝 0) ∧
      ∀ α : ℝ, 0 < α ∧ α < 1 →
        Tendsto (fun N : ℕ => (unitSampleLaw K N {ω |
          0 ≤ dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c) ∧
          |dot c (coefficientError K ω)| ≤ normalQuantile (1-α/2) *
            Real.sqrt (dot c ((sampleVariance members (design K ω) (response K ω)).mulVec c))}).toReal)
          atTop (𝓝 (1-α))) ∧
  (Standing signPairKernel ∧ populationBeta signPairKernel = 0 ∧
    limitingTarget signPairKernel = !![4,0;0,0] ∧
    Tendsto (fun N : ℕ => (unitSampleLaw signPairKernel N {ω |
      (sampleVariance members (design signPairKernel ω) (response signPairKernel ω)) 1 1 < 0}).toReal)
      atTop (𝓝 (1-Real.exp (-1/2))) ∧
    ¬weakLimit (unitSampleLaw signPairKernel) (fun _ ω =>
      coefficientError signPairKernel ω 1 /
        Real.sqrt ((sampleVariance members (design signPairKernel ω) (response signPairKernel ω)) 1 1))
      (gaussianReal 0 1))

/-- One-based geometric unit weights, geometric sum, total dyad weight, and coefficients. -/
def W1q {N : ℕ} (i : Fin N) : ℝ := (1/2 : ℝ)^(i.val+1)
def W1x (N : ℕ) : ℝ := (1/2 : ℝ)^N
def W1S (N : ℕ) : ℝ := ∑ i : Fin N, W1q i
def W1W (N : ℕ) : ℝ := ∑ d : Dyad N, concentratedWeight d
def W1c {N : ℕ} (i : Fin N) : ℝ := W1q i * (W1S N - W1q i) / W1W N

def W1WeightEvent (N : ℕ) : Set (Fin N → Bool) :=
  {ω | ∀ i : Fin N, i.val < 8 → ω i = true}
def W1TailWeight (N : ℕ) : ℝ :=
  ∑ d : Dyad N, if 8 ≤ (secondUnit d).val then concentratedWeight d else 0

def W1WeightScore {N : ℕ} (ω : Fin N → Bool) (d : Dyad N) : ℝ :=
  concentratedWeight d * (response signKernel ω d - weightedOLS signKernel concentratedWeight ω 0)

def W1WeightVariance (N : ℕ) : ℝ := ProbabilityTheory.variance
  (fun ω => weightedOLS signKernel concentratedWeight ω 0) (unitSampleLaw signKernel N)

/-- Two identical directed copies of each sign dyad, grouped into one overlap block. -/
def W1TwoSignRecords : RepeatedKernel Bool 1 :=
  ⟨fairLaw,fun _ _ => 2,fun _ _ _ _ _ => ![1],
    fun _ _ _ u v => signValue u+signValue v⟩

def W1T9Setup : Prop :=
  Standing signKernel ∧ SampleRank signKernel ∧ populationBeta signKernel = 0 ∧
  (∀ N : ℕ, 2 ≤ N → weightedPopulationBeta signKernel (@concentratedWeight N) = 0 ∧
    ∀ ω : Fin N → Bool,
      (Dreal N)⁻¹ • sampleGram (design signKernel ω) = (1 : Mat 1) ∧
      ∀ d : Dyad N, |epsilon signKernel ω d| ≤ 2 ∧
        |response signKernel ω d - dot (design signKernel ω d)
          (weightedOLS signKernel concentratedWeight ω)| ≤ 4) ∧
  (∀ N M : ℕ, ∀ d : Dyad N, ∀ f : Dyad M,
    (firstUnit d).val = (firstUnit f).val → (secondUnit d).val = (secondUnit f).val →
    concentratedWeight d = concentratedWeight f) ∧
  (∀ N : ℕ, 2 ≤ N → ∀ ω : Fin N → Bool,
    recordWeightedOLS W1TwoSignRecords (fun d _ => concentratedWeight d) ω =
      weightedOLS signKernel concentratedWeight ω ∧
    recordWeightedVariance W1TwoSignRecords (fun d _ => concentratedWeight d) ω =
      weightedVariance signKernel concentratedWeight ω)

def W1T9Coefficients : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N),
    (∑ i : Fin N, W1c i) = 2 ∧
    W1c (⟨0, by omega⟩ : Fin N) = 3 / (4 * (1-W1x N)) ∧
    (3/4 : ℝ) ≤ W1c (⟨0, by omega⟩ : Fin N)

def W1T9Tail : Prop :=
  ∀ N : ℕ, 8 ≤ N → 0 ≤ W1TailWeight N ∧ W1TailWeight N ≤ 1/256 ∧
    ∀ ω ∈ W1WeightEvent N,
      0 ≤ 2-weightedOLS signKernel concentratedWeight ω 0 ∧
      2-weightedOLS signKernel concentratedWeight ω 0 ≤ 4*W1TailWeight N/W1W N ∧
      (∑ d : Dyad N, |W1WeightScore ω d|) ≤ 8*W1TailWeight N ∧
      |(weightedVariance signKernel concentratedWeight ω) 0 0| ≤
        64*(W1TailWeight N/W1W N)^2

def W1T9Limits : Prop :=
  ¬inProbability (unitSampleLaw signKernel)
      (fun _ ω => weightedOLS signKernel concentratedWeight ω 0) ∧
  Tendsto (fun N : ℕ => (N : ℝ)*W1WeightVariance N) atTop atTop ∧
  Tendsto (fun N : ℕ => W1W N / Dreal N) atTop (𝓝 0) ∧
  Tendsto (fun N : ℕ => 3 / (4*(1-W1x N))) atTop (𝓝 (3/4))

/-- Reversal is one-based i ↦ N+1-i. -/
def W1Reverse {N : ℕ} (ω : Fin N → Bool) : Fin N → Bool := fun i => ω i.rev

def W1T9Repetitions : Prop :=
  (∀ N : ℕ, 2 ≤ N → ∀ ω : Fin N → Bool,
    (repeatedOLS concentratedRepeated ω, repeatedVariance concentratedRepeated ω) =
      (weightedOLS signKernel concentratedWeight (W1Reverse ω),
       weightedVariance signKernel concentratedWeight (W1Reverse ω))) ∧
  (∀ B : ℕ, ∃ N : ℕ, 2 ≤ N ∧ ∃ d : Dyad N, B < concentratedRepeated.T N d)

/-- P018-T9; p. 575 (PDF p. 12), Appendix D and Corollary 2;
pp. 567–568 (PDF pp. 4–5), fixed finite repetitions and Corollary 1.
The bounded fair-sign intercept model with fixed weights 2^(-i-j) has the stated geometric
sums, linear fit, variance bounded below by 9/16 and tending to 36/35, inconsistent
coefficients and divergent scaled variance. Its first-eight-positive event has probability
1/256 and forces the stated sandwich separation, ruling out a common deterministic
target. The normalized weighted design vanishes and the first coefficient tends to 3/4.
Identical repetitions 2^(i+j) transfer the joint law by label reversal and have no uniform
count bound. Duplicating both directions preserves the weighted fit and sandwich.
The all-N linear-fit and variance identities include the zero completion when N<2. -/
def T9WholeStatement : Prop :=
  T9Statement ∧ W1T9Setup ∧
  (∀ N : ℕ, W1S N = 1-W1x N ∧ W1W N = (1-W1x N)*(1-2*W1x N)/3 ∧
    W1WeightVariance N = ∑ i : Fin N, (W1c i)^2 ∧
    ∀ ω : Fin N → Bool, weightedOLS signKernel concentratedWeight ω 0 =
      ∑ i : Fin N, W1c i * signValue (ω i)) ∧
  W1T9Coefficients ∧ W1T9Tail ∧
  (∀ N : ℕ, 8 ≤ N →
    (unitSampleLaw signKernel N (W1WeightEvent N)).toReal = 1/256 ∧
    (1/8 : ℝ) ≤ W1W N ∧
    ∀ ω ∈ W1WeightEvent N,
      |(weightedVariance signKernel concentratedWeight ω) 0 0| ≤ 1/16 ∧
      (1/2 : ℝ) ≤ |(weightedVariance signKernel concentratedWeight ω) 0 0-W1WeightVariance N|) ∧
  (∀ N : ℕ, 2 ≤ N → ∀ ω : Fin N → Bool,
    (weightedVariance signKernel concentratedWeight ω) 0 0 =
      (W1W N)^(-2 : ℤ) * ∑ d : Dyad N, ∑ f : Dyad N,
        if overlap d f then W1WeightScore ω d * W1WeightScore ω f else 0) ∧
  W1T9Limits ∧ W1T9Repetitions

/-- Bounded measurable ordered data kernel with an intercept; symmetry is not assumed. -/
def W1OrderedStanding {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Prop :=
  IsProbabilityMeasure K.μ ∧
  Measurable (fun uv : U × U => K.X uv.1 uv.2) ∧
  Measurable (fun uv : U × U => K.Y uv.1 uv.2) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ uv ∂K.μ.prod K.μ,
    ‖K.X uv.1 uv.2‖ ≤ C ∧ |K.Y uv.1 uv.2| ≤ C) ∧
  (∃ j : Fin k, ∀ u v, K.X u v j = 1)

/-- Deterministic inclusion of at most one record per direction, including empty blocks. -/
def W1DirectedRecords {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (K : Kernel U k)
    (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool) : Prop :=
  R.μ = K.μ ∧ (∀ N d, Function.Injective (dir N d)) ∧
  ∀ N d (t : Fin (R.T N d)) u v,
    R.X N d t u v = (if dir N d t then K.X v u else K.X u v) ∧
    R.Y N d t u v = (if dir N d t then K.Y v u else K.Y u v)

/-- Normalized directed-record problem, with no positivity requirement on block counts. -/
def W1DirectedSetting {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (K : Kernel U k)
    (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k) : Prop :=
  W1OrderedStanding K ∧ W1DirectedRecords R K dir ∧
  (∀ N d t, 0 < v N d t ∧ v N d t ≤ C) ∧ H.PosDef ∧
  Tendsto (fun N : ℕ => recordWeightedH R (v N)) atTop (𝓝 H)

/-- A deterministic bounded common-record witness: first record is +1, second is -1. -/
def W1MeanWitness : RepeatedKernel Unit 1 :=
  ⟨Measure.dirac (), fun N d =>
    if (secondUnit d).val < N/2 then 1 else 2,
    fun _ _ _ _ _ => ![1], fun _ _ t _ _ => if t.val = 0 then 1 else -1⟩

def W1MeanOverlap (N : ℕ) : Mat 1 :=
  ((N : ℝ)/(repeatedL W1MeanWitness N)^2) • meat members
    (fun d : Dyad N => meanVec (repeatedLaw W1MeanWitness N)
      (fun ω => repeatedBlockScore W1MeanWitness (repeatedBeta W1MeanWitness N) ω d))

/-- Common-record repeated consistency, with exactly the canonical overlap-mean condition. -/
def W1RepeatedConsistency : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k),
    RepeatedStanding R →
    (∃ fX : ℕ → U → U → Vec k, ∃ fY : ℕ → U → U → ℝ,
      ∀ N d (t : Fin (R.T N d)) u v,
        R.X N d t u v = fX t.val u v ∧ R.Y N d t u v = fY t.val u v) →
    (∃ T0 : ℕ, ∀ N d, R.T N d ≤ T0) →
    ∀ H : Mat k, H.PosDef → Tendsto (repeatedH R) atTop (𝓝 H) →
    Tendsto (fun N : ℕ => ((N : ℝ)/(repeatedL R N)^2) • meat members
      (fun d : Dyad N => meanVec (repeatedLaw R N)
        (fun ω => repeatedBlockScore R (repeatedBeta R N) ω d))) atTop (𝓝 0) →
    inProbability (repeatedLaw R) (fun N ω =>
      (N : ℝ) • repeatedVariance R ω-repeatedTarget R N)

/-- The bounded-data standing assumptions at a fixed size; empty blocks are permitted. -/
def W1BoundedRecordsAtSize {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) : Prop :=
  IsProbabilityMeasure R.μ ∧
  (∀ d t, Measurable (fun uv : U × U => R.X N d t uv.1 uv.2) ∧
    Measurable (fun uv : U × U => R.Y N d t uv.1 uv.2)) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ d t, ∀ᵐ uv ∂ R.μ.prod R.μ,
    ‖R.X N d t uv.1 uv.2‖ ≤ C ∧ |R.Y N d t uv.1 uv.2| ≤ C)

/-- Ordinary-inverse scale identities in the standing bounded-data domain. -/
def W1ScaleInvariance : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k),
    W1BoundedRecordsAtSize R N →
    ∀ (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (a : ℝ), 0 < a → 2 ≤ N →
    ∀ ω : Fin N → U, (recordWeightedGram R w ω).det ≠ 0 → (recordWeightedH R w).det ≠ 0 →
    recordWeightedOLS R (fun d t => a*w d t) ω = recordWeightedOLS R w ω ∧
    recordWeightedVariance R (fun d t => a*w d t) ω = recordWeightedVariance R w ω ∧
    recordWeightedTarget R (fun d t => a*w d t) = recordWeightedTarget R w

/-- Bounded positive fixed weights and unweighted rank alone are insufficient. -/
def W1WeightObstruction : Prop :=
  (∀ N : ℕ, 2 ≤ N → ∀ d : Dyad N, 0 < concentratedWeight d ∧ concentratedWeight d ≤ 1/8) ∧
  Standing signKernel ∧ SampleRank signKernel ∧
  ¬(∃ V : ℕ → ℝ,
    Tendsto (fun N : ℕ => (N : ℝ)*W1WeightVariance N-V N) atTop (𝓝 0) ∧
    inProbability (unitSampleLaw signKernel) (fun N ω =>
      (N : ℝ)*(weightedVariance signKernel concentratedWeight ω) 0 0-V N))

/-- P018-T10; pp. 567–568 (PDF pp. 4–5), Corollary 1;
p. 575 (PDF p. 12), Appendix D and Corollary 2.
Uniformly bounded common record kernels and counts, a positive limiting normalized design,
and vanishing scaled overlap products of block means imply repeated sandwich consistency.
The stacked normal equations alone need not give overlap control or consistency. A common ordered
kernel, at most one record per direction, bounded positive normalized weights, and a
positive limiting normalized weighted design imply weighted consistency, permitting empty
blocks. Positive common weight rescaling leaves all three weighted quantities unchanged
where the ordinary inverses exist. Bounded positive fixed weights and unweighted rank
alone are insufficient. -/
def T10WholeStatement : Prop :=
  W1RepeatedConsistency.{u} ∧
  (∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (K : Kernel U k), W1OrderedStanding K →
    ∀ dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool,
    W1DirectedRecords R K dir →
    ∀ (w : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (a : ℕ → ℝ),
    (∀ N, 0 < a N) →
    (∃ C : ℝ, ∀ N d t, 0 < w N d t/a N ∧ w N d t/a N ≤ C) →
    ∀ H : Mat k, H.PosDef →
    Tendsto (fun N : ℕ => recordWeightedH R (fun d t => w N d t/a N)) atTop (𝓝 H) →
    inProbability (repeatedLaw R) (fun N ω =>
      (N : ℝ) • recordWeightedVariance R (w N) ω - recordWeightedTarget R (w N))) ∧
  W1ScaleInvariance.{u} ∧ W1WeightObstruction ∧
  (RepeatedStanding W1MeanWitness ∧
    (∀ N d, W1MeanWitness.T N d ≤ 2) ∧
    (∃ fX : ℕ → Unit → Unit → Vec 1, ∃ fY : ℕ → Unit → Unit → ℝ,
      ∀ N d (t : Fin (W1MeanWitness.T N d)) u v,
        W1MeanWitness.X N d t u v = fX t.val u v ∧
        W1MeanWitness.Y N d t u v = fY t.val u v) ∧
    (∀ N : ℕ, 2 ≤ N → repeatedH W1MeanWitness N = (1 : Mat 1) ∧
      (∑ d : Dyad N, meanVec (repeatedLaw W1MeanWitness N)
        (fun ω => repeatedBlockScore W1MeanWitness (repeatedBeta W1MeanWitness N) ω d)) = 0) ∧
    ¬Tendsto W1MeanOverlap atTop (𝓝 0) ∧
    ¬inProbability (repeatedLaw W1MeanWitness) (fun N ω =>
      (N : ℝ) • repeatedVariance W1MeanWitness ω-repeatedTarget W1MeanWitness N))

/-- T identical fair-sign records per unordered dyad. -/
def W1IdenticalSign (T : ℕ) : RepeatedKernel Bool 1 :=
  ⟨fairLaw, fun _ _ => T, fun _ _ _ _ _ => ![1],
    fun _ _ _ u v => signValue u+signValue v⟩

def W1BlockX {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (d : Dyad N) (u v : U) :
    Matrix (Fin (R.T N d)) (Fin k) ℝ := fun t a => R.X N d t u v a

def W1WrongBlockGram {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (d : Dyad N) : Mat (R.T N d) :=
  meanMat (R.μ.prod R.μ) (fun uv => W1BlockX R d uv.1 uv.2 * (W1BlockX R d uv.1 uv.2).transpose)

def W1CoefficientBlockGram {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (d : Dyad N) : Mat k :=
  meanMat (R.μ.prod R.μ) (fun uv => (W1BlockX R d uv.1 uv.2).transpose * W1BlockX R d uv.1 uv.2)

/-- The mixed uniform/sign model in T11(f), with independence built into the product law. -/
def W1MixedKernel : Kernel (ℝ × Bool) 2 :=
  ⟨uniformUnitLaw.prod fairLaw, fun u v => ![1,u.1+v.1],
    fun u v => signValue u.2+signValue v.2⟩

def W1CrossGram {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  meanMat ((K.μ.prod K.μ).prod K.μ) (fun z => outer (K.X z.1.1 z.1.2) (K.X z.1.1 z.2))

def W1ConditionalRow {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d : Dyad N) : Mat k :=
  conditionalTerm K d d + ∑ f ∈ neighbors d, conditionalTerm K d f

def W1ScoreCovRow {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k) (d : Dyad N) : Mat k :=
  covMat (unitSampleLaw K N) (fun ω => score (design K ω d) (epsilon K ω d))
    (fun ω => score (design K ω d) (epsilon K ω d)) +
  ∑ f ∈ neighbors d, covMat (unitSampleLaw K N)
    (fun ω => score (design K ω d) (epsilon K ω d))
    (fun ω => score (design K ω f) (epsilon K ω f))

def W1SignMean {N : ℕ} (ω : Fin N → Bool) : ℝ := (N : ℝ)⁻¹ * ∑ i, signValue (ω i)
def W1ScaledSignSandwich {N : ℕ} (ω : Fin N → Bool) : ℝ :=
  (N : ℝ)*(sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0

def W1T11ScalarMoments : Prop :=
  Standing signKernel ∧ populationBeta signKernel = 0 ∧
  ∀ N : ℕ, 3 ≤ N →
    (∀ ω : Fin N → Bool, sampleOLS (design signKernel ω) (response signKernel ω) 0 =
      (2/(N : ℝ))*∑ i, signValue (ω i)) ∧
    (∀ d : Dyad N,
      (∀ᵐ ω ∂unitSampleLaw signKernel N, conditionalResidualMean signKernel d ω = 0) ∧
      W1ConditionalRow signKernel d = !![2*(N : ℝ)-2] ∧
      ∀ f : Dyad N,
        ProbabilityTheory.covariance (fun ω => epsilon signKernel ω d)
          (fun ω => epsilon signKernel ω f) (unitSampleLaw signKernel N) =
            ((members d ∩ members f).card : ℝ) ∧
        (∀ᵐ ω ∂unitSampleLaw signKernel N,
          conditionalResidualCov signKernel d f ω = ((members d ∩ members f).card : ℝ))) ∧
    populationGram signKernel = 1 ∧ repeatedL (singleRecord signKernel) N = Dreal N ∧
    (∀ ω : Fin N → Bool,
      repeatedOLS (singleRecord signKernel) ω = sampleOLS (design signKernel ω) (response signKernel ω) ∧
      repeatedVariance (singleRecord signKernel) ω = sampleVariance members (design signKernel ω) (response signKernel ω) ∧
      weightedOLS signKernel (fun _ => 1) ω = sampleOLS (design signKernel ω) (response signKernel ω) ∧
      weightedVariance signKernel (fun _ => 1) ω = sampleVariance members (design signKernel ω) (response signKernel ω))

def W1T11SampleFormula : Prop :=
  ∀ N : ℕ, 3 ≤ N →
    (∀ ω : Fin N → Bool, W1ScaledSignSandwich ω =
      (4*((N : ℝ)-2)*((N : ℝ)-3)/((N : ℝ)-1)^2)*(1-(W1SignMean ω)^2)) ∧
    (∫ ω, W1ScaledSignSandwich ω ∂unitSampleLaw signKernel N) =
      4*((N : ℝ)-2)*((N : ℝ)-3)/((N : ℝ)*((N : ℝ)-1))

def W1T11Repeated : Prop :=
  ∀ T N : ℕ, 1 ≤ T → 3 ≤ N →
    repeatedL (W1IdenticalSign T) N = (T : ℝ)*Dreal N ∧
    repeatedBeta (W1IdenticalSign T) N = 0 ∧
    repeatedH (W1IdenticalSign T) N = 1 ∧
    varMat (repeatedLaw (W1IdenticalSign T) N)
      (fun ω => ∑ d : Dyad N, repeatedBlockScore (W1IdenticalSign T) 0 ω d) =
      !![(T : ℝ)^2*(N : ℝ)*((N : ℝ)-1)^2] ∧
    (∀ d : Dyad N,
      W1CoefficientBlockGram (W1IdenticalSign T) d = !![(T : ℝ)] ∧
      W1WrongBlockGram (W1IdenticalSign T) d = (fun _ _ => 1)) ∧
    ((N : ℝ)/(repeatedL (W1IdenticalSign T) N)^2) •
      sandwich (!![(T : ℝ)] : Mat 1)⁻¹
        !![(T : ℝ)^2*(N : ℝ)*((N : ℝ)-1)^2] = !![4/(T : ℝ)^2] ∧
    repeatedTarget (W1IdenticalSign T) N = !![4]

def W1T11MixedMoments : Prop :=
  Standing W1MixedKernel ∧ populationBeta W1MixedKernel = 0 ∧
  populationGram W1MixedKernel = !![1,0;0,2/3] ∧
  W1CrossGram W1MixedKernel = !![1,0;0,1/3] ∧
  (∫ uv, dot (W1MixedKernel.X uv.1 uv.2) (W1MixedKernel.X uv.1 uv.2)
    ∂W1MixedKernel.μ.prod W1MixedKernel.μ) = 5/3 ∧
  scoreH W1MixedKernel = !![2,0;0,4/3] ∧ projectionGamma W1MixedKernel = !![1,0;0,1/3]

def W1T11MixedRows : Prop :=
  ∀ N : ℕ, 3 ≤ N → ∀ d : Dyad N,
    W1ConditionalRow W1MixedKernel d = !![2*(N : ℝ)-2,0;0,2*(N : ℝ)/3] ∧
    W1ScoreCovRow W1MixedKernel d = !![2*(N : ℝ)-2,0;0,2*(N : ℝ)/3]

/-- P018-T11; p. 568 (PDF p. 5), display for the repeated target;
p. 576 (PDF p. 13), display for the weighted target.
In the fair-sign intercept model the exact fit has scaled variance 4, while each literal
unsummed target equals 4/D and tends to zero. The exact sample and expectation sandwich
formulas, their probability limit and both discrepancy limits hold. Restoring the dyad
sum gives the actual score variance and target 4. With T identical records the printed
block bread has the wrong dimension (and is singular for T=2); its unnormalized coefficient
bread gives 4/T^2, whereas the normalized bread gives 4. In the independent uniform/sign
two-regressor model the stated Gram, cross-Gram, scalar norm and dyad covariance yield
the distinct coefficient-bread and scalar-left-bread matrices. -/
def T11WholeStatement : Prop :=
  T11Statement ∧ W1T11ScalarMoments ∧ W1T11SampleFormula ∧
  (∀ N : ℕ, 3 ≤ N →
    varMat (unitSampleLaw signKernel N) (scoreSum signKernel) = !![(N : ℝ)*((N : ℝ)-1)^2] ∧
    (N : ℝ)*((N : ℝ)-1)^2 = Dreal N*(2*(N : ℝ)-2) ∧
    (N : ℝ)*(2*(N : ℝ)-2)/(Dreal N)^2 = 8/((N : ℝ)*((N : ℝ)-1))) ∧
  Tendsto (fun N : ℕ => (N : ℝ)*ProbabilityTheory.variance
      (fun ω => sampleOLS (design signKernel ω) (response signKernel ω) 0)
      (unitSampleLaw signKernel N)-4/Dreal N) atTop (𝓝 4) ∧
  inProbability (unitSampleLaw signKernel)
    (fun N ω => W1ScaledSignSandwich ω-4/Dreal N-4) ∧
  W1T11Repeated ∧
  (∀ N : ℕ, 3 ≤ N → ∀ d : Dyad N,
    (W1WrongBlockGram (W1IdenticalSign 2) d).det = 0 ∧
    W1CoefficientBlockGram (W1IdenticalSign 2) d = !![2]) ∧
  W1T11MixedMoments ∧ W1T11MixedRows ∧
  (∀ N : ℕ, 3 ≤ N → ∀ d : Dyad N,
    ((N : ℝ)/(Dreal N)^2) • sandwich (populationGram W1MixedKernel)⁻¹
      (Dreal N • W1ConditionalRow W1MixedKernel d) = !![4,0;0,3*(N : ℝ)/((N : ℝ)-1)] ∧
    ((N : ℝ)/(Dreal N)^2) • ((5/3 : ℝ)⁻¹ •
      ((Dreal N • W1ConditionalRow W1MixedKernel d)*(populationGram W1MixedKernel)⁻¹)) =
        !![12/5,0;0,6*(N : ℝ)/(5*((N : ℝ)-1))])

end SAP.P018a
