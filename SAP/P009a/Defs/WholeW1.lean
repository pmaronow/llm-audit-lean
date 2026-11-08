import Mathlib
import SAP.P009a.Defs
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P009a
open Filter MeasureTheory
open scoped BigOperators Topology Classical
noncomputable section
/-- The joint assignment probability minus the product of its two marginals. -/
def assignmentGap {n : ℕ} (E : FiniteExperiment n) (b : Bool) (i j : Fin n) : ℝ :=
  probability E.design (fun z => z i = b ∧ z j = b) -
    armProbability E i b * armProbability E j b
/-- The diagonal-inclusive coordinate mixing coefficient. -/
def assignmentMixing {n : ℕ} (E : FiniteExperiment n) (i j : Fin n) : ℝ :=
  mixingCoefficient E.design (fun z => z i) (fun z => z j)
/-- The off-diagonal mixing sum with the diagonal Bernoulli variances restored. -/
def restoredMixingSum {n : ℕ} (E : FiniteExperiment n) (b : Bool) : ℝ :=
  (∑ i, ∑ j, if j = i then 0 else assignmentMixing E i j) +
    ∑ i, armProbability E i b * (1 - armProbability E i b)
/-- P009-T16. Supplement A, p. 23, proof of Lemma A23, first display, corrected. For every design, arm and positive k, every joint assignment probability difference is bounded term by term by alpha, including the diagonal. Alpha lies in [0,1/4]. The full-pair mixing sum bounds the covariance sum and is bounded by k² d_AVG/n plus the nondependent mixing remainder. Self-dependence, the sum defining d_AVG, and the equivalent off-diagonal formula with the diagonal Bernoulli variances restored are included. The sample size is positive. -/
def T16WholeStatement : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (E : FiniteExperiment n) (b : Bool) (k : ℝ) (_hk : 0 < k),
    (∀ i j,
      covariance E.design (fun z => if z i = b then 1 else 0)
        (fun z => if z j = b then 1 else 0) = assignmentGap E b i j ∧
      |assignmentGap E b i j| ≤ assignmentMixing E i j ∧
      0 ≤ assignmentMixing E i j ∧ assignmentMixing E i j ≤ 1/4 ∧
      dependenceIndicator E i j + (1 - dependenceIndicator E i j) = 1) ∧
    (∀ i, dependenceIndicator E i i = 1 ∧
      assignmentGap E b i i = armProbability E i b * (1 - armProbability E i b) ∧
      assignmentMixing E i i = armProbability E i b * (1 - armProbability E i b)) ∧
    (∑ i, ∑ j, dependenceIndicator E i j) = (n : ℝ) * averageDependence E ∧
    k^2/(n:ℝ)^2 * (∑ i, ∑ j, assignmentGap E b i j) ≤
      k^2/(n:ℝ)^2 * (∑ i, ∑ j, assignmentMixing E i j) ∧
    k^2/(n:ℝ)^2 * (∑ i, ∑ j, assignmentMixing E i j) ≤
      k^2*averageDependence E/(n:ℝ) + k^2/(n:ℝ)^2 *
        (∑ i, ∑ j, (1-dependenceIndicator E i j)*assignmentMixing E i j) ∧
    (∑ i, ∑ j, assignmentMixing E i j) = restoredMixingSum E b ∧
    k^2/(n:ℝ)^2 * (∑ i, ∑ j, assignmentGap E b i j) ≤
      k^2/(n:ℝ)^2 * restoredMixingSum E b ∧
    k^2/(n:ℝ)^2 * restoredMixingSum E b ≤
      k^2*averageDependence E/(n:ℝ) + k^2/(n:ℝ)^2 *
        (∑ i, ∑ j, (1-dependenceIndicator E i j)*assignmentMixing E i j)
/-- All four variance estimates in their printed order: BER, AVG, MAX, SR. -/
def wholeVarianceEstimate {n : ℕ} (E : FiniteExperiment n) (a : Fin 4)
    (z : TreatmentVector n) : ℝ :=
  if a = 0 then bernoulliVarianceEstimate E z
  else if a = 1 then averageVarianceEstimate E z
  else if a = 2 then maximumVarianceEstimate E z else spectralVarianceEstimate E z
def sparseScaledError (a : Fin 4) (t : ℕ) (z : TreatmentVector (t+1)) : ℝ :=
  let E := sparseSequence.experiment t
  sampleSize sparseSequence t / averageDependence E *
    (wholeVarianceEstimate E a z - variance E.design (htEstimate E))
def sparseCenteredError (t : ℕ) (z : TreatmentVector (t+1)) : ℝ :=
  let E := sparseSequence.experiment t
  sampleSize sparseSequence t *
    (bernoulliVarianceEstimate E z - variance E.design (htEstimate E)) - meanSquaredEffect E
def sparseNormalizedBias (t : ℕ) : ℝ :=
  let E := sparseSequence.experiment t
  sampleSize sparseSequence t *
    (expectation E.design (bernoulliVarianceEstimate E) - variance E.design (htEstimate E))
def sparseNormalizedVariance (t : ℕ) : ℝ :=
  let E := sparseSequence.experiment t
  sampleSize sparseSequence t / averageDependence E * variance E.design (htEstimate E)
/-- Exact finite errors and their fair two-point laws, including the finite lower-tail cutoff. -/
def W1SparseErrors : Prop :=
  ∀ t, let E := sparseSequence.experiment t
    let n := sampleSize sparseSequence t
    (∀ a z, sparseScaledError a t z = (4*treatmentValue (z 0)-1)/n ∧
      sparseScaledError a t z = if z 0 then 3/n else -1/n) ∧
    (∀ a (b : Bool), probability E.design (fun z =>
      sparseScaledError a t z = if b then 3/n else -1/n) = 1/2) ∧
    (∀ ε > 0, 1/ε < n → ∀ a,
      probability E.design (fun z => sparseScaledError a t z ≤ -ε) = 0) ∧
    (∀ z, sparseCenteredError t z = (4*treatmentValue (z 0)-2)/n ∧
      sparseCenteredError t z = if z 0 then 2/n else -2/n) ∧
    (∀ b : Bool, probability E.design (fun z =>
      sparseCenteredError t z = if b then 2/n else -2/n) = 1/2)
/-- The dispersion and graph-rate checks in Propositions 8, 9A and 10A, and failure of Part B. -/
def W1SparseRates : Prop :=
  Tendsto (fun t => dispersionOfVariances (sparseSequence.experiment t)^2) atTop (nhds 0) ∧
  Tendsto (fun t => dispersionOfVariances (sparseSequence.experiment t)) atTop (nhds 0) ∧
  (∀ t, let E := sparseSequence.experiment t
    averageDependence E / rmsDependence E = 1 ∧
    maximumDependence E / (Real.sqrt (sampleSize sparseSequence t) *
      Real.sqrt (averageDependence E)) = 1 / Real.sqrt (sampleSize sparseSequence t) ∧
    spectralRadius E / (Real.sqrt (sampleSize sparseSequence t) *
      Real.sqrt (averageDependence E)) = 1 / Real.sqrt (sampleSize sparseSequence t)) ∧
  vanishingRelativeTo (fun t => dispersionOfVariances (sparseSequence.experiment t))
    (fun t => averageDependence (sparseSequence.experiment t) /
      rmsDependence (sparseSequence.experiment t)) ∧
  Tendsto (fun t => maximumDependence (sparseSequence.experiment t) /
    (Real.sqrt (sampleSize sparseSequence t) * Real.sqrt (averageDependence (sparseSequence.experiment t))))
    atTop (nhds 0) ∧
  Tendsto (fun t => spectralRadius (sparseSequence.experiment t) /
    (Real.sqrt (sampleSize sparseSequence t) * Real.sqrt (averageDependence (sparseSequence.experiment t))))
    atTop (nhds 0) ∧
  ¬ EventuallyPositiveLowerBound (fun t => meanSquaredEffect (sparseSequence.experiment t))
/-- Pointwise interval cases, exact coverage for every level, and exact relative lower tails. -/
def W1SparseIntervals : Prop :=
  ∀ t, let E := sparseSequence.experiment t
    let n := sampleSize sparseSequence t
    (∀ α, 0 < α → α < 1 → ∀ a,
      (∀ z : TreatmentVector (t+1),
        (z 0 = false → htEstimate E z = 0 ∧ wholeVarianceEstimate E a z = 0 ∧
          htEstimate E z - Real.sqrt (wholeVarianceEstimate E a z/α) = 0 ∧
          htEstimate E z + Real.sqrt (wholeVarianceEstimate E a z/α) = 0 ∧
          ¬ IntervalCovers (htEstimate E z) (expectedATE E) (wholeVarianceEstimate E a z) α) ∧
        (z 0 = true → (htEstimate E z - expectedATE E)^2 = 1/n^2 ∧
          (htEstimate E z - expectedATE E)^2 ≤ wholeVarianceEstimate E a z/α ∧
          IntervalCovers (htEstimate E z) (expectedATE E) (wholeVarianceEstimate E a z) α)) ∧
      probability E.design (fun z => IntervalCovers (htEstimate E z) (expectedATE E)
        (wholeVarianceEstimate E a z) α) = 1/2) ∧
    (∀ η, 0 < η → η < 1 → ∀ a,
      probability E.design (fun z => wholeVarianceEstimate E a z <
        (1-η)*variance E.design (htEstimate E)) = 1/2)
/-- P009-T1. Section 6.1, p. 689, equation (1); Definition 10, p. 691; Propositions 8–10, pp. 692–693. The fair Bernoulli family y₁(z)=z₁, yᵢ(z)=0 for i>1 satisfies every clause (a)–(h) of the counterexample: all real moment orders, full-cube bounds and diagonal interference, the exact estimands, estimator moments, four coincident variance estimates, finite two-point scaled errors and lower-tail cutoff, equation (1), vanishing scaled expected bias, contribution variances and all dispersion and graph-rate conditions. Part B's positive mean-square lower bound fails. For every alpha in (0,1), each of the four plug-in intervals has coverage exactly 1/2, with the stated pointwise interval cases; every relative underestimation probability is 1/2 and the normalized true variance tends to zero. Thus the printed conservative-inference implication fails. -/
def T1WholeStatement : Prop :=
  T1Statement ∧
  (∀ q s : ℝ, 2 ≤ q → 1 ≤ s → SequenceRegularity sparseSequence 2 q s) ∧
  (∀ t i z, 0 ≤ (sparseSequence.experiment t).outcome i z ∧
    (sparseSequence.experiment t).outcome i z ≤ 1) ∧
  (∀ t i b, armProbability (sparseSequence.experiment t) i b = 1/2) ∧
  (∀ t i j, interferenceIndicator (sparseSequence.experiment t) i j = (if i = j then 1 else 0) ∧
    dependenceIndicator (sparseSequence.experiment t) i j = (if i = j then 1 else 0)) ∧
  (∀ t i, contributionVariance (sparseSequence.experiment t) i = if i.val = 0 then 1 else 0) ∧
  W1SparseErrors ∧ W1SparseRates ∧ W1SparseIntervals ∧
  (∀ t, sparseNormalizedBias t = 1/sampleSize sparseSequence t ∧
    sparseNormalizedVariance t = 1/sampleSize sparseSequence t) ∧
  Tendsto sparseNormalizedBias atTop (nhds 0) ∧ Tendsto sparseNormalizedVariance atTop (nhds 0)
/-- Definition 10's literal iterated limit implies every fixed positive-cutoff limit. -/
def W1IteratedTails : Prop :=
  ∀ (Ω : ℕ → Type) [∀ t, MeasurableSpace (Ω t)]
    (P : (t : ℕ) → Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (error : (t : ℕ) → Ω t → ℝ) (L : ℝ → ℝ),
    (∀ ε > 0, Tendsto (fun t => ((P t) {ω | error t ω ≤ -ε}).toReal)
      atTop (nhds (L ε))) →
    Tendsto L (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
    ∀ ε > 0, Tendsto (fun t => ((P t) {ω | error t ω ≤ -ε}).toReal) atTop (nhds 0)
/-- The sparse family witnesses vanishing scaled bias and failure of coverage without a variance floor. -/
def W1CoverageCounterexample : Prop :=
  SequenceRegularity sparseSequence 2 4 1 ∧
  (∀ t, let E := sparseSequence.experiment t
    ProductDesign E ∧ NoSpillovers E ∧ 0 < variance E.design (htEstimate E) ∧
    (∀ z, 0 ≤ bernoulliVarianceEstimate E z) ∧
    expectation E.design (htEstimate E) = expectedATE E ∧
    variance E.design (htEstimate E) < expectation E.design (bernoulliVarianceEstimate E) ∧
    probability E.design (fun z => IntervalCovers (htEstimate E z) (expectedATE E)
      (bernoulliVarianceEstimate E z) (1/20)) = 1/2) ∧
  VarianceConservative sparseSequence (fun t => bernoulliVarianceEstimate (sparseSequence.experiment t)) ∧
  ConvergesInProbability sparseSequence sparseCenteredError ∧
  (∀ t, sparseNormalizedBias t = 1/sampleSize sparseSequence t ∧
    sparseNormalizedVariance t = 1/sampleSize sparseSequence t) ∧
  Tendsto sparseNormalizedBias atTop (nhds 0) ∧ Tendsto sparseNormalizedVariance atTop (nhds 0) ∧
  (1/2 : ℝ) < 1-1/20
/-- P009-T2. Section 6.1, p. 689, corrected sentence; Definition 10, p. 691. For unbiased square-integrable statistics with positive finite variance and nonnegative measurable variance estimates, plug-in noncoverage is at most the relative underestimation probability plus alpha/(1-eta). Vanishing relative tails give liminf coverage at least 1-alpha. Additive scaled lower-tail control and an eventual positive normalized-variance floor give relative control, including the finite event inclusion. The literal iterated Definition-10 condition gives all fixed-cutoff limits. Bernoulli HT is unbiased and has the stated coverage under this variance floor. Scaled bias may vanish and coverage may fail without the floor, as the sparse family shows. -/
def T2WholeStatement : Prop :=
  T2Statement ∧ W1IteratedTails ∧ W1CoverageCounterexample
/-- The common data and strict weighting violations retained in the original T3 package. -/
def W1SignedBase (E F G : FiniteExperiment 2) : Prop :=
  (∀ z, E.design.mass z =
    (if z 0 then 1/4 else 3/4) * (if z 1 then 3/4 else 1/4)) ∧
  (∀ i z, E.outcome i z = if i = 0 then treatmentValue (z 1) else -treatmentValue (z 0)) ∧
  (∀ z, F.design.mass z =
    if z 0 ∧ ¬ z 1 then 1/4 else if ¬ z 0 ∧ z 1 then 3/4 else 0) ∧
  (∀ i z, F.outcome i z = 1) ∧
  (∀ z, G.design.mass z =
    (if z 0 then 1/4 else 3/4) * (if z 1 then 3/4 else 1/4)) ∧
  (∀ i z, G.outcome i z = if i = 0 then 1 else 1-treatmentValue (z 0)) ∧
  Regularity E 4 4 1 ∧ ProductDesign E ∧ Regularity F 4 4 1 ∧
  Regularity G 4 4 1 ∧ ProductDesign G ∧
  variance E.design (estimatedArmMean E true) = 13/48 ∧
  (∑ i, ∑ j, covariance E.design (armResponse E true 1 i) (armResponse E true 1 j)) = 0 ∧
  variance F.design (fun z => estimatedArmSize F true z / 2) = 1/3 ∧
  (∑ i, ∑ j, covariance F.design
    (fun z => treatmentValue (z i)) (fun z => treatmentValue (z j))) = 0 ∧
  variance G.design (fun z => ∑ i,
    armResponse G true 2 i z / armProbability G i true ^ 2) = 367/9 ∧
  (4:ℝ)^4 * (∑ i, ∑ j, covariance G.design
    (armResponse G true 2 i) (armResponse G true 2 j)) = 39 ∧
  (0:ℝ) < 13/48 ∧ (0:ℝ) < 1/3 ∧ (39:ℝ) < 367/9
def twoUnitProduct (z : TreatmentVector 2) : ℝ := treatmentValue (z 0) * treatmentValue (z 1)
/-- All omitted finite facts for the signed-outcome Bernoulli example. -/
def W1SignedTable (E : FiniteExperiment 2) : Prop :=
  (∀ z, armResponse E true 1 0 z = twoUnitProduct z ∧
    armResponse E true 1 1 z = -twoUnitProduct z ∧
    estimatedArmMean E true z = (4/3)*twoUnitProduct z) ∧
  probability E.design (fun z => twoUnitProduct z = 1) = 3/16 ∧
  probability E.design (fun z => twoUnitProduct z = 0) = 13/16 ∧
  variance E.design twoUnitProduct = 39/256 ∧
  (∀ i j, covariance E.design (armResponse E true 1 i) (armResponse E true 1 j) =
    if i = j then 39/256 else -39/256) ∧
  variance E.design (estimatedArmMean E true) > (4:ℝ)^2/2^2 *
    (∑ i, ∑ j, covariance E.design (armResponse E true 1 i) (armResponse E true 1 j))
/-- The count example's support is an almost-sure claim; zero-mass cube points are unrestricted. -/
def W1CountTable (F : FiniteExperiment 2) : Prop :=
  probability F.design (fun z => treatmentValue (z 0)+treatmentValue (z 1) = 1) = 1 ∧
  probability F.design (fun z => estimatedArmSize F true z/2 = 2) = 1/4 ∧
  probability F.design (fun z => estimatedArmSize F true z/2 = 2/3) = 3/4 ∧
  variance F.design (fun z => estimatedArmSize F true z/2) > (4:ℝ)^2/2^2 *
    (∑ i, ∑ j, covariance F.design
      (fun z => treatmentValue (z i)) (fun z => treatmentValue (z j)))
def squareWeightedSum (G : FiniteExperiment 2) (z : TreatmentVector 2) : ℝ :=
  ∑ i, armResponse G true 2 i z / armProbability G i true ^ 2
/-- The square example's full variable identities, law, raw moments and strict violation. -/
def W1SquareTable (G : FiniteExperiment 2) : Prop :=
  (∀ z, armResponse G true 2 0 z = treatmentValue (z 0) ∧
    armResponse G true 2 1 z = treatmentValue (z 1)*(1-treatmentValue (z 0)) ∧
    squareWeightedSum G z = 16*armResponse G true 2 0 z + (16/9)*armResponse G true 2 1 z) ∧
  probability G.design (fun z => squareWeightedSum G z = 0) = 3/16 ∧
  probability G.design (fun z => squareWeightedSum G z = 16/9) = 9/16 ∧
  probability G.design (fun z => squareWeightedSum G z = 16) = 1/4 ∧
  expectation G.design (squareWeightedSum G) = 5 ∧
  expectation G.design (fun z => squareWeightedSum G z ^ 2) = 592/9 ∧
  (∑ i, ∑ j, covariance G.design (armResponse G true 2 i) (armResponse G true 2 j)) = 39/256 ∧
  variance G.design (fun z => armResponse G true 2 0 z + armResponse G true 2 1 z) = 39/256 ∧
  variance G.design (squareWeightedSum G) > (4:ℝ)^4 *
    (∑ i, ∑ j, covariance G.design (armResponse G true 2 i) (armResponse G true 2 j))
/-- P009-T3. Supplement A, pp. 8, 22, 23, 25, proofs of Lemmas A9, A22, A23, A25. The three specified two-unit experiments refute each printed replacement of unequal positive weights by a common upper bound inside a signed covariance sum. The full-cube outcome bounds and Assumption 1 at every real q≥2 and s≥1 are included. The signed example has B~Bernoulli(3/16), variance 39/256, the stated covariance matrix and muHat=(4/3)B. The count example has arm-size ratio 2 or 2/3 with probabilities 1/4 and 3/4. The square example has W=0,16/9,16 with probabilities 3/16,9/16,1/4, mean 5, second moment 592/9 and variance 367/9>39. The final lemma rates stand. -/
def T3WholeStatement : Prop :=
  ∃ E F G : FiniteExperiment 2, W1SignedBase E F G ∧
    (∀ i z, |E.outcome i z| ≤ 1 ∧ |F.outcome i z| ≤ 1 ∧ |G.outcome i z| ≤ 1) ∧
    (∀ q s : ℝ, 2 ≤ q → 1 ≤ s →
      Regularity E 4 q s ∧ Regularity F 4 q s ∧ Regularity G 4 q s) ∧
    W1SignedTable E ∧ W1CountTable F ∧ W1SquareTable G
/-- A true probability or conditional probability of the incoming treated count. -/
def incomingMass {n : ℕ} (E : FiniteExperiment n) (i : Fin n) (t : ℕ) : ℝ :=
  probability E.design (fun z => treatedIncomingCount E i z = t)
def incomingConditionalMass {n : ℕ} (E : FiniteExperiment n) (i : Fin n)
    (b : Bool) (t : ℕ) : ℝ :=
  conditionalMean E.design (fun z => z i = b)
    (fun z => if treatedIncomingCount E i z = t then 1 else 0)
/-- The printed ratio-minus-one right side, used only at positive denominators in T17. -/
def printedIncomingRatio (n c : ℕ) (p : ℝ) (b : Bool) (t : ℕ) : ℝ :=
  (c:ℝ)/(p*((n:ℝ)-c)) *
    (p-treatmentValue b*(t:ℝ)/(c:ℝ)-(1-treatmentValue b)*((c:ℝ)-t)/(c:ℝ))
/-- Three complete tables, indexed only by t=0,1,2, so no truncated-subtraction artifacts occur. -/
def W1HypergeomTables (E : FiniteExperiment 4) : Prop :=
  ∀ t : Fin 3,
    incomingMass E 0 t = (![1/2,1/2,0] : Fin 3 → ℝ) t ∧
    printedHypergeomMass 4 2 2 t = (![1/6,2/3,1/6] : Fin 3 → ℝ) t ∧
    incomingConditionalMass E 0 true t = (![2/3,1/3,0] : Fin 3 → ℝ) t ∧
    printedHypergeomMass 3 1 2 t = (![1/3,2/3,0] : Fin 3 → ℝ) t ∧
    incomingConditionalMass E 0 false t = (![1/3,2/3,0] : Fin 3 → ℝ) t ∧
    printedHypergeomMass 3 2 2 t = (![0,2/3,1/3] : Fin 3 → ℝ) t
/-- The second, no-interference, complete-randomization counterexample. -/
def W1HypergeomSecond (F : FiniteExperiment 4) : Prop :=
  (∀ z, F.design.mass z = if (∑ i, if z i then (1:ℕ) else 0) = 2 then 1/6 else 0) ∧
  (∀ i z, F.outcome i z = treatmentValue (z i)) ∧
  FixedSizeDesign F 2 ∧ Regularity F 2 4 1 ∧ NoSpillovers F ∧
  (∀ i b, armProbability F i b = 1/2) ∧
  (∀ i j, Affects F j i ↔ j = i) ∧
  (∀ i, incomingCount F i = 1 ∧ (∀ z, treatedIncomingCount F i z = 0) ∧
    incomingMass F i 0 = 1) ∧ printedHypergeomMass 4 2 1 0 = 1/2 ∧
  (1 : ℝ) ≠ 1/2
/-- P009-T17. Supplement A, p. 10, proof of Lemma A12; Definition A3, p. 9. The two printed hypergeometric laws and the printed likelihood-ratio identity are false: T_i counts only other interfering units, whose number is incoming(i)-1. Under complete randomization of two of four units, y₁(v)=v₁+v₂ and yⱼ(v)=vⱼ otherwise give incoming(1)=2, T₁=Z₂, the full true and printed probability tables at t=0,1,2 for both conditioning arms, true ratio 4/3 versus printed ratio 2, and true ratio-minus-one 1/3 versus printed right side 1. The second instance has yⱼ(v)=vⱼ, incoming(i)=1 and T_i=0 surely, but printed zero-count probability 1/2. Both designs, all marginals, regularity and positive ratio denominators are certified. The inequality of Lemma A12 is not refuted. -/
def T17WholeStatement : Prop :=
  (∀ {n : ℕ} (E : FiniteExperiment n) (i : Fin n),
    (Finset.univ.filter (fun j => j ≠ i ∧ Affects E j i)).card = incomingCount E i - 1) ∧
  ∃ E F : FiniteExperiment 4,
    (∀ z, E.design.mass z = if (∑ i, if z i then (1:ℕ) else 0) = 2 then 1/6 else 0) ∧
    (∀ i z, E.outcome i z = treatmentValue (z i) + if i = 0 then treatmentValue (z 1) else 0) ∧
    FixedSizeDesign E 2 ∧ Regularity E 2 4 1 ∧
    (∀ i b, armProbability E i b = 1/2) ∧
    (∀ j, Affects E j 0 ↔ j = 0 ∨ j = 1) ∧
    incomingCount E 0 = 2 ∧ incomingCount E 0 = min 2 (4-2) ∧
    (∀ z, treatedIncomingCount E 0 z = if z 1 then 1 else 0) ∧
    W1HypergeomTables E ∧
    0 < incomingMass E 0 0 ∧ 0 < armProbability E 0 true ∧
    0 < (4:ℝ)-(incomingCount E 0:ℝ) ∧
    incomingConditionalMass E 0 true 0 / incomingMass E 0 0 = 4/3 ∧
    printedHypergeomMass 3 1 2 0 / printedHypergeomMass 4 2 2 0 = 2 ∧
    incomingConditionalMass E 0 true 0 / incomingMass E 0 0 - 1 = 1/3 ∧
    printedIncomingRatio 4 (incomingCount E 0) (armProbability E 0 true) true 0 = 1 ∧
    incomingConditionalMass E 0 true 0 / incomingMass E 0 0 - 1 ≠
      printedIncomingRatio 4 (incomingCount E 0) (armProbability E 0 true) true 0 ∧
    W1HypergeomSecond F
end
end SAP.P009a
