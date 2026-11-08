import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

/-- Normalized nonnegative atomic masses on every feasible assignment.
All events are predicates; finite ordinary means require HasMean. -/
structure AtomicDesign (Ω : Type) where
  mass : Ω → ℝ
  mass_nonnegative : ∀ z, 0 ≤ mass z
  mass_summable : Summable mass
  mass_total : (∑' z, mass z) = 1


abbrev Responses (Ω : Type) (N : ℕ) := Fin N → Ω → ℝ

abbrev Exposures (Ω : Type) (N : ℕ) := Fin N → Ω → ℝ

def supported {Ω : Type} (D : AtomicDesign Ω) (z : Ω) : Prop := 0 < D.mass z

noncomputable def eventProbability {Ω : Type} (D : AtomicDesign Ω) (A : Ω → Prop) : ℝ :=
  ∑' z, if A z then D.mass z else 0

noncomputable def mean {Ω : Type} (D : AtomicDesign Ω) (f : Ω → ℝ) : ℝ :=
  ∑' z, D.mass z * f z

def HasMean {Ω : Type} (D : AtomicDesign Ω) (f : Ω → ℝ) : Prop :=
  Summable (fun z => D.mass z * |f z|)

noncomputable def exposureProbability {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (i : Fin N) (d : ℝ) : ℝ :=
  eventProbability D (fun z => g i z = d)

def positiveExposure {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (d : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ exposureProbability D g i d

def targetMoment {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) (d : ℝ) : Prop :=
  ∀ i, HasMean D (fun z => if g i z = d then y i z else 0)

noncomputable def exposureMean {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) (i : Fin N) (d : ℝ) : ℝ :=
  mean D (fun z => if g i z = d then y i z else 0) / exposureProbability D g i d

noncomputable def conditionalExposureMean {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) (i : Fin N) (d : ℝ) : ℝ :=
  ∑' z, if g i z = d then (D.mass z / exposureProbability D g i d) * y i z else 0

noncomputable def populationExposureMean {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) (d : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, exposureMean D g y i d

noncomputable def unitContrast {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) (i : Fin N) (d d' : ℝ) : ℝ :=
  exposureMean D g y i d - exposureMean D g y i d'

noncomputable def populationContrast {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) (d d' : ℝ) : ℝ :=
  populationExposureMean D g y d - populationExposureMean D g y d'

noncomputable def estimateExposureMean {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) (d : ℝ) (z : Ω) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (if g i z = d then y i z else 0) / exposureProbability D g i d

noncomputable def estimateContrast {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) (d d' : ℝ) (z : Ω) : ℝ :=
  estimateExposureMean D g y d z - estimateExposureMean D g y d' z

def supportStability {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) (y : Responses Ω N) : Prop :=
  ∀ i z z', supported D z → supported D z' → g i z = g i z' → y i z = y i z'

def globalStability {Ω : Type} {N : ℕ} (g : Exposures Ω N)
    (y : Responses Ω N) : Prop :=
  ∀ i z z', g i z = g i z' → y i z = y i z'

noncomputable def designVariance {Ω : Type} (D : AtomicDesign Ω) (X : Ω → ℝ) : ℝ :=
  mean D (fun z => (X z - mean D X)^2)

noncomputable def designCovariance {Ω : Type} (D : AtomicDesign Ω) (X Y : Ω → ℝ) : ℝ :=
  mean D (fun z => (X z - mean D X) * (Y z - mean D Y))

def independent {Ω A B : Type} (D : AtomicDesign Ω) (X : Ω → A) (Y : Ω → B) : Prop :=
  ∀ E : A → Prop, ∀ F : B → Prop,
    eventProbability D (fun z => E (X z) ∧ F (Y z)) =
      eventProbability D (fun z => E (X z)) * eventProbability D (fun z => F (Y z))

def mutuallyIndependent {Ω : Type} {N : ℕ} (D : AtomicDesign Ω)
    (g : Exposures Ω N) : Prop :=
  ∀ E : Fin N → ℝ → Prop,
    eventProbability D (fun z => ∀ i, E i (g i z)) =
      ∏ i, eventProbability D (fun z => E i (g i z))

def otherCoordinates {N : ℕ} (v : Fin N → ℝ) (i : Fin N) : {j : Fin N // j ≠ i} → ℝ :=
  fun j => v j.val

def insertCoordinate {N : ℕ} (i : Fin N) (e : ℝ)
    (w : {j : Fin N // j ≠ i} → ℝ) : Fin N → ℝ :=
  fun j => if h : j = i then e else w ⟨j,h⟩

def coordinateExposure {N : ℕ} (S : Set (Fin N → ℝ)) : Exposures S N :=
  fun i z => z.val i

noncomputable def hybridResponse {N : ℕ} (S : Set (Fin N → ℝ))
    (y : Responses S N) (i : Fin N) (e : ℝ) (z : S) : ℝ :=
  if h : insertCoordinate i e (otherCoordinates z.val i) ∈ S then
    y i ⟨insertCoordinate i e (otherCoordinates z.val i),h⟩ else 0

noncomputable def averageDirectContrast {N : ℕ} (S : Set (Fin N → ℝ))
    (D : AtomicDesign S) (y : Responses S N) (d d' : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, mean D (fun z => hybridResponse S y i d z - hybridResponse S y i d' z)

def probabilityLimit {Ω : ℕ → Type} (D : ∀ N, AtomicDesign (Ω N))
    (X : ∀ N, Ω N → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun N => eventProbability (D N) (fun z => |X N z - a| > ε)) atTop (𝓝 0)

def weakLimit {Ω : ℕ → Type} (D : ∀ N, AtomicDesign (Ω N))
    (X : ∀ N, Ω N → ℝ) (L : MeasureTheory.Measure ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ, Tendsto (fun N => mean (D N) (fun z => f (X N z)))
    atTop (𝓝 (∫ x, f x ∂L))

noncomputable def translatedLaw (L : MeasureTheory.Measure ℝ) (c : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.map (fun x : ℝ => x+c) L

end SAP.P061a
