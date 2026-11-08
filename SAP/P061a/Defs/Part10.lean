import SAP.P061a.Defs.Part9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

/-- Transfer on the stronger moment domain and at continuity boundaries only. -/
def InferenceTransfer : Prop :=
  ∀ (S : ∀ N : ℕ, Set (Fin N → ℝ)) (D : ∀ N, AtomicDesign (S N))
    (y : ∀ N, Responses (S N) N) (d d' : ℝ)
    (estimate estimatedScale : ∀ N, S N → ℝ) (s : ℕ → ℝ)
    (L : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure L],
    (∀ N, 0 < s N) → (∀ N z, 0 < estimatedScale N z) →
    (∀ N i, 0 < exposureProbability (D N) (coordinateExposure (S N)) i d ∧
      0 < exposureProbability (D N) (coordinateExposure (S N)) i d') →
    (∀ N, targetMoment (D N) (coordinateExposure (S N)) (y N) d ∧
      targetMoment (D N) (coordinateExposure (S N)) (y N) d') →
    (∀ N i z, supported (D N) z →
      insertCoordinate i d (otherCoordinates z.val i) ∈ S N ∧
      insertCoordinate i d' (otherCoordinates z.val i) ∈ S N) →
    (∀ N i, HasMean (D N) (hybridResponse (S N) (y N) i d) ∧
      HasMean (D N) (hybridResponse (S N) (y N) i d')) →
    weakLimit D (fun N z =>
      (estimate N z-populationContrast (D N) (coordinateExposure (S N)) (y N) d d')/s N) L →
    probabilityLimit D (fun N z => estimatedScale N z/s N) 1 →
    Tendsto (fun N =>
      (populationContrast (D N) (coordinateExposure (S N)) (y N) d d' -
        averageDirectContrast (S N) (D N) (y N) d d')/s N) atTop (𝓝 0) →
    weakLimit D (fun N z =>
      (estimate N z-averageDirectContrast (S N) (D N) (y N) d d')/estimatedScale N z) L ∧
    (∀ q : ℝ, 0 < q → L {q} = 0 → L {-q} = 0 →
      Tendsto (fun N => eventProbability (D N) (fun z =>
        |estimate N z-averageDirectContrast (S N) (D N) (y N) d d'| ≤ q*estimatedScale N z))
        atTop (𝓝 ((L (Set.Icc (-q) q)).toReal)))

/-- Finite common alphabets ensure the response ranges are genuine finite extrema. -/
def FiniteNeighborhoodBound : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A] (N : ℕ)
    (label : A → ℝ), Function.Injective label →
    ∀ (D : AtomicDesign (Fin N → A)) (y : Responses (Fin N → A) N)
      (H : Fin N → Finset (Fin N)) (f : ∀ i, A → Neighborhood A (H i) → ℝ) (d d' : A),
    0 < N → (∀ i, i ∉ H i) →
    (∀ i, 0 < exposureProbability D (fun i z => label (z i)) i (label d) ∧
      0 < exposureProbability D (fun i z => label (z i)) i (label d')) →
    (∀ i e, e=d ∨ e=d' → ∀ z, y i (Function.update z i e) = f i e (fun j => z j.val)) →
    |populationContrast D (fun i z => label (z i)) y (label d) (label d') -
      (N : ℝ)⁻¹ * ∑ i, mean D (fun z =>
        y i (Function.update z i d)-y i (Function.update z i d'))| ≤
      (N : ℝ)⁻¹ * ∑ i,
        (responseRange (f i d) * variationDistance (conditionalNeighborhoodLaw D i (H i) d) (neighborhoodLaw D (H i)) +
         responseRange (f i d') * variationDistance (conditionalNeighborhoodLaw D i (H i) d') (neighborhoodLaw D (H i)))

def T5Statement : Prop :=
  InferenceTransfer ∧ FiniteNeighborhoodBound ∧
  (∀ (T A L s : ℕ → ℝ), (∀ N, 0 < s N) → (∀ N, |T N-A N| ≤ L N) →
    Tendsto (fun N => L N/s N) atTop (𝓝 0) →
    Tendsto (fun N => (T N-A N)/s N) atTop (𝓝 0)) ∧
  (∀ (Ω : ℕ → Type) (D : ∀ N, AtomicDesign (Ω N))
      (estimate estimatedScale : ∀ N, Ω N → ℝ) (T A s : ℕ → ℝ)
      (L : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure L] (c : ℝ),
    c ≠ 0 → (∀ N, 0 < s N) → (∀ N z, 0 < estimatedScale N z) →
    weakLimit D (fun N z => (estimate N z-T N)/s N) L →
    probabilityLimit D (fun N z => estimatedScale N z/s N) 1 →
    Tendsto (fun N => (T N-A N)/s N) atTop (𝓝 c) →
    weakLimit D (fun N z => (estimate N z-A N)/estimatedScale N z) (translatedLaw L c))


end SAP.P061a
