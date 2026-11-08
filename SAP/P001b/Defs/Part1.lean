import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Event probability, used only with finite probability measures. -/
def probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) : ℝ :=
  (μ A).toReal

/-- A nonnegative integrable density of a real-valued law. -/
def Density (ν : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
    ν = volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- A nonnegative integrable density with respect to planar Lebesgue measure. -/
def JointDensity (ν : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ z, 0 ≤ f z) ∧ Integrable f volume ∧
    ν = volume.withDensity (fun z => ENNReal.ofReal (f z))

def distributionFunction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  probability μ {ω | X ω ≤ x}

/-- Finite probabilities from atom weights; normalization is stated where needed. -/
def finiteProbability {n : ℕ} (w : Fin n → ℝ) (A : Fin n → Prop) : ℝ :=
  ∑ i, if A i then w i else 0

def finiteMean {n : ℕ} (w : Fin n → ℝ) (Y : Fin n → ℝ) : ℝ :=
  ∑ i, w i * Y i

/-- A conditional mean on a positive-mass cell. The voting theorem gives both masses. -/
def finiteConditionalMean {n : ℕ} (w : Fin n → ℝ)
    (Y X : Fin n → ℝ) (x : ℝ) : ℝ :=
  (∑ i, if X i = x then w i * Y i else 0) /
    finiteProbability w (fun i => X i = x)

/-- Conditional independence as factorization on every positive-mass cell. -/
def FiniteConditionalIndependence {n : ℕ} {E F G : Type*} (w : Fin n → ℝ)
    (Y : Fin n → E) (Z : Fin n → F) (X : Fin n → G) : Prop :=
  ∀ (x : G) (y : E) (z : F), 0 < finiteProbability w (fun i => X i = x) →
    finiteProbability w (fun i => X i = x ∧ Y i = y ∧ Z i = z) *
      finiteProbability w (fun i => X i = x) =
    finiteProbability w (fun i => X i = x ∧ Y i = y) *
      finiteProbability w (fun i => X i = x ∧ Z i = z)

def voterMass : Fin 4 → ℝ := ![3/8, 1/8, 1/8, 3/8]
def electorateType : Fin 4 → ℝ := ![0, 0, 1, 1]
def displayedGender : Fin 4 → ℝ := ![0, 1, 0, 1]
def potentialVoteShare (d : ℝ) (i : Fin 4) : ℝ := 20 + 40 * electorateType i + 5 * d

def displayedLeaflet (d : Bool) : ℝ × Bool × Bool := (0, d, false)

/-- The voter uses only the displayed gender and the electorate's preference type. -/
def votesNo (u : ℝ) (k : Fin 100) (d : Bool) : Prop :=
  (k.val + 1 : ℝ) ≤ 20 + 40 * u + 5 * (if d then 1 else 0)

def countedVoteShare (i : Fin 4) (d : Bool) : ℝ :=
  ((Finset.univ.filter (fun k : Fin 100 => votesNo (electorateType i) k d)).card : ℝ)

def observedVoteShare (i : Fin 4) : ℝ := potentialVoteShare (displayedGender i) i

def zeroMass : Fin 1 → ℝ := fun _ => 1

def integerCDF (q : ℤ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℤ, if (k : ℝ) ≤ x then q k else 0

def dieMass : Fin 6 → ℝ := fun _ => 1/6
def dieValue (i : Fin 6) : ℝ := (i : ℝ) + 1

/-- The nonempty members of the event/complement family. -/
def complementFamily {Ω : Type*} (A : Set Ω) : Set (Set Ω) :=
  {C | C.Nonempty ∧ (C = A ∨ C = Aᶜ)}

end
end SAP.P001b
