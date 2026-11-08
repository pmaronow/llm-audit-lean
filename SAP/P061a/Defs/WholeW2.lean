import Mathlib
import SAP.P061a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

/-- The actual other-unit coordinates selected by a neighborhood. -/
def neighborhoodVectorW2 {N : ℕ} {S : Set (Fin N → ℝ)}
    (H : Finset (Fin N)) (z : S) : Neighborhood ℝ H := fun j => z.val j.val

/-- Unconditional neighborhood masses on an arbitrary feasible assignment set. -/
noncomputable def neighborhoodMassW2 {N : ℕ} {S : Set (Fin N → ℝ)}
    (D : AtomicDesign S) (H : Finset (Fin N)) (x : Neighborhood ℝ H) : ℝ :=
  eventProbability D (fun z => neighborhoodVectorW2 H z = x)

/-- Conditional neighborhood masses; the theorems require a positive conditioning cell. -/
noncomputable def conditionalNeighborhoodMassW2 {N : ℕ} {S : Set (Fin N → ℝ)}
    (D : AtomicDesign S) (i : Fin N) (H : Finset (Fin N))
    (e : ℝ) (x : Neighborhood ℝ H) : ℝ :=
  eventProbability D (fun z => z.val i = e ∧ neighborhoodVectorW2 H z = x) /
    exposureProbability D (coordinateExposure S) i e

/-- Existence of the printed minimum and maximum, on the stated function domain. -/
def HasExtremaW2 {B : Type} (f : B → ℝ) (C : Set B) : Prop :=
  (∃ a : ℝ, IsLeast (f '' C) a) ∧ (∃ b : ℝ, IsGreatest (f '' C) b)

/-- The printed range, evaluated only when its two finite attained extrema exist. -/
noncomputable def responseRangeOnW2 {B : Type} (f : B → ℝ) (C : Set B) : ℝ :=
  sSup (f '' C) - sInf (f '' C)

/-- The local TV envelope. Only neighborhood configurations have finite support;
the assignment design, feasible set, and coordinate alphabets may be infinite.
The set C may be larger than K, and supplies the printed response range. -/
noncomputable def localTVEnvelopeW2 {N : ℕ} {S : Set (Fin N → ℝ)}
    (D : AtomicDesign S) (H : Fin N → Finset (Fin N))
    (K : ∀ i, Finset (Neighborhood ℝ (H i)))
    (C : ∀ i, Set (Neighborhood ℝ (H i)))
    (f : ∀ i, ℝ → Neighborhood ℝ (H i) → ℝ) (d d' : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i,
    (responseRangeOnW2 (f i d) (C i) *
      variationDistance
        (fun x : K i => conditionalNeighborhoodMassW2 D i (H i) d x.val)
        (fun x : K i => neighborhoodMassW2 D (H i) x.val) +
     responseRangeOnW2 (f i d') (C i) *
      variationDistance
        (fun x : K i => conditionalNeighborhoodMassW2 D i (H i) d' x.val)
        (fun x : K i => neighborhoodMassW2 D (H i) x.val))

/-- Existence conditions for the actual AEED and hybrid-difference ADE.
Index n denotes population size n+1, so there is no empty population.
Separate first moments of the two hybrid responses are not assumed. -/
def PopulationDomainW2
    (S : ∀ n : ℕ, Set (Fin (n+1) → ℝ)) (D : ∀ n, AtomicDesign (S n))
    (y : ∀ n, Responses (S n) (n+1)) (d d' : ℝ) : Prop :=
  (∀ n i, 0 < exposureProbability (D n) (coordinateExposure (S n)) i d ∧
    0 < exposureProbability (D n) (coordinateExposure (S n)) i d') ∧
  (∀ n, targetMoment (D n) (coordinateExposure (S n)) (y n) d ∧
    targetMoment (D n) (coordinateExposure (S n)) (y n) d') ∧
  (∀ n i z, supported (D n) z →
    insertCoordinate i d (otherCoordinates z.val i) ∈ S n ∧
    insertCoordinate i d' (otherCoordinates z.val i) ∈ S n) ∧
  (∀ n i, HasMean (D n) (fun z =>
    hybridResponse (S n) (y n) i d z - hybridResponse (S n) (y n) i d' z))

/-- Statistical conclusions for common centers and a common scale. Real division
sets the studentized statistic to zero on a zero estimated scale. Consistency
makes all nonpositive estimated scales negligible. Coverage is the actual
unstandardized event and is asserted for both centers at continuity endpoints. -/
def InferenceConclusionsW2 {Ω : ℕ → Type} (D : ∀ n, AtomicDesign (Ω n))
    (estimate estimatedScale : ∀ n, Ω n → ℝ) (T A s : ℕ → ℝ)
    (L : MeasureTheory.Measure ℝ) : Prop :=
  Tendsto (fun n => eventProbability (D n) (fun z => estimatedScale n z ≤ 0))
    atTop (𝓝 0) ∧
  (Tendsto (fun n => |T n - A n| / s n) atTop (𝓝 0) →
    weakLimit D (fun n z => (estimate n z - A n) / estimatedScale n z) L ∧
    weakLimit D (fun n z => (estimate n z - T n) / estimatedScale n z) L ∧
    ∀ q : ℝ, 0 < q → L {-q} = 0 → L {q} = 0 →
      (Tendsto (fun n => eventProbability (D n) (fun z =>
        |estimate n z - A n| ≤ q * estimatedScale n z))
        atTop (𝓝 (L (Set.Icc (-q) q)).toReal) ∧
       Tendsto (fun n => eventProbability (D n) (fun z =>
        |estimate n z - T n| ≤ q * estimatedScale n z))
        atTop (𝓝 (L (Set.Icc (-q) q)).toReal))) ∧
  (∀ c : ℝ, c ≠ 0 →
    Tendsto (fun n => (T n - A n) / s n) atTop (𝓝 c) →
    weakLimit D (fun n z => (estimate n z - A n) / estimatedScale n z)
      (translatedLaw L c))

/-- The corrected transfer and shifted-law alternative for the paper's actual
individualistic AEED and feasible raw-hybrid ADE, on all positive population sizes. -/
def T5PopulationInferenceW2 : Prop :=
  ∀ (S : ∀ n : ℕ, Set (Fin (n+1) → ℝ)) (D : ∀ n, AtomicDesign (S n))
    (y : ∀ n, Responses (S n) (n+1)) (d d' : ℝ)
    (estimate estimatedScale : ∀ n, S n → ℝ) (s : ℕ → ℝ)
    (L : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure L],
    PopulationDomainW2 S D y d d' → (∀ n, 0 < s n) →
    weakLimit D (fun n z =>
      (estimate n z - populationContrast (D n) (coordinateExposure (S n)) (y n) d d') /
        s n) L →
    probabilityLimit D (fun n z => estimatedScale n z / s n) 1 →
    InferenceConclusionsW2 D estimate estimatedScale
      (fun n => populationContrast (D n) (coordinateExposure (S n)) (y n) d d')
      (fun n => averageDirectContrast (S n) (D n) (y n) d d') s L

/-- General local bound with the paper's discrete assignment law. K contains
every supported neighborhood configuration, and C is the domain used for the
printed extrema. The response identity and hybrid feasibility are needed only
on positive-mass assignments. No finite global alphabet or full feasible cube
is required; even separate hybrid moments follow from the local hypotheses. -/
def T5NeighborhoodBoundW2 : Prop :=
  ∀ (N : ℕ) (S : Set (Fin N → ℝ)) (D : AtomicDesign S) (y : Responses S N)
    (d d' : ℝ) (H : Fin N → Finset (Fin N))
    (K : ∀ i, Finset (Neighborhood ℝ (H i)))
    (C : ∀ i, Set (Neighborhood ℝ (H i)))
    (f : ∀ i, ℝ → Neighborhood ℝ (H i) → ℝ),
    0 < N → (∀ i, i ∉ H i) → (∀ i, (K i).Nonempty) →
    (∀ i x, x ∈ K i → x ∈ C i) →
    (∀ i z, supported D z → neighborhoodVectorW2 (H i) z ∈ K i) →
    (∀ i e, e = d ∨ e = d' → HasExtremaW2 (f i e) (C i)) →
    (∀ i, 0 < exposureProbability D (coordinateExposure S) i d ∧
      0 < exposureProbability D (coordinateExposure S) i d') →
    (∀ i z, supported D z →
      insertCoordinate i d (otherCoordinates z.val i) ∈ S ∧
      insertCoordinate i d' (otherCoordinates z.val i) ∈ S) →
    (∀ i e, e = d ∨ e = d' → ∀ z, supported D z →
      hybridResponse S y i e z = f i e (neighborhoodVectorW2 (H i) z)) →
    |populationContrast D (coordinateExposure S) y d d' -
      averageDirectContrast S D y d d'| ≤ localTVEnvelopeW2 D H K C f d d'

/-- A local-envelope bound that is little-o of the positive scale suffices. -/
def T5RateSufficesW2 : Prop :=
  ∀ (T A bound s : ℕ → ℝ), (∀ n, 0 < s n) →
    (∀ n, |T n - A n| ≤ bound n) →
    Tendsto (fun n => bound n / s n) atTop (𝓝 0) →
    Tendsto (fun n => |T n - A n| / s n) atTop (𝓝 0)

/-- The concrete T4 design, along population sizes 2(m+2)^8, has a vanishing
raw gap, a diverging absolute standardized gap, and direct-effect coverage
tending to zero. The scale is the exact standard deviation, and all finite
design, positivity, moment, and local-dependence facts are retained. -/
def T5RateExampleW2 : Prop :=
  ∃ D : ∀ m, AtomicDesign (Fin (m^8) → BitPair),
    (∀ m z, (D m).mass z = ∏ k : Fin (m^8),
      if (z k).1 = (z k).2 then (1+pairParameter m)/4 else (1-pairParameter m)/4) ∧
    (∀ m, 2 ≤ m → PairInferenceFacts D m) ∧
    Tendsto (fun n : ℕ =>
      populationContrast (D (n+2)) (pairedOwnBit ((n+2)^8)) (pairResponses (n+2)) 1 0 -
        pairDirectContrast (n+2) (D (n+2))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ =>
      |populationContrast (D (n+2)) (pairedOwnBit ((n+2)^8)) (pairResponses (n+2)) 1 0 -
        pairDirectContrast (n+2) (D (n+2))| / pairStandardError (n+2) (D (n+2)))
      atTop atTop ∧
    Tendsto (fun n : ℕ => eventProbability (D (n+2)) (fun z =>
      |pairEstimator (n+2) (D (n+2)) z - pairDirectContrast (n+2) (D (n+2))| ≤
        5 * pairStandardError (n+2) (D (n+2)))) atTop (𝓝 0)

/-- P061-T5; main p. 14, Equation (8) and footnote 8, p. 7, and supplement p. 5.
For individualistic assignments, a negligible AEED--ADE gap in positive
standard-error units transfers the limiting law under consistent scale estimation.
Both Wald coverages tend to L([-q,q]) for each fixed q>0 with zero limiting mass
at both endpoints; a continuous limiting law automatically satisfies this condition.
A nonzero limiting standardized drift shifts the law. The T4 design has a vanishing
raw gap but a diverging absolute standardized gap and failing direct-effect coverage.
For arbitrary discrete feasible designs with finite neighborhood support, the
range-times-TV envelope bounds the target gap, and an envelope o(s) suffices.
The usual measure-theoretic conditions are assumed. Only the hybrid differences
need finite means for transfer, and estimated scales may be nonpositive on
asymptotically negligible events. -/
def T5WholeStatement_W2 : Prop :=
  T5PopulationInferenceW2 ∧ T5NeighborhoodBoundW2 ∧ T5RateSufficesW2 ∧
  T5RateExampleW2 ∧
  (∀ (L : MeasureTheory.Measure ℝ) [MeasureTheory.NullSingletonClass L] (q : ℝ),
    L {-q} = 0 ∧ L {q} = 0)

end SAP.P061a
