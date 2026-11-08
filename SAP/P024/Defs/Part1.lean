import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024
open scoped BigOperators
noncomputable section

/-- A finite assignment law; all expectations below average only over assignment. -/
structure Design (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

def expectation {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, d.mass ω * X ω

def probability {Ω : Type*} [Fintype Ω] (d : Design Ω) (P : Ω → Prop) : ℝ :=
  by classical exact expectation d (fun ω => if P ω then 1 else 0)

def variance {Ω : Type*} [Fintype Ω] (d : Design Ω) (X : Ω → ℝ) : ℝ :=
  expectation d (fun ω => (X ω - expectation d X)^2)

def uniformDesign (Ω : Type*) [Fintype Ω] [Nonempty Ω] : Design Ω where
  mass := fun _ => 1 / (Fintype.card Ω : ℝ)
  nonneg := fun _ => by positivity
  total := by simp [Fintype.card_ne_zero]

def indicator (z : Bool) : ℝ := if z then 1 else 0

/-- Fixed potential outcomes, observed through current exposure only. -/
def observed {I Ω : Type*} (z : Ω → I → Bool) (y0 y1 : I → ℝ)
    (ω : Ω) (i : I) : ℝ := if z ω i then y1 i else y0 i

def averageEffect {I : Type*} (E : Finset I) (y0 y1 : I → ℝ) : ℝ :=
  (∑ i ∈ E, (y1 i - y0 i)) / E.card

/-- Current-exposure inverse-probability contrast; used only on nonempty overlap sets. -/
def htEstimate {I Ω : Type*} (E : Finset I) (z : Ω → I → Bool)
    (y0 y1 π : I → ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ E, if z ω i then y1 i / π i else -(y0 i / (1 - π i))) / E.card

def exposureProbability {I Ω : Type*} [Fintype Ω] (d : Design Ω)
    (z : Ω → I → Bool) (i : I) : ℝ := expectation d (fun ω => indicator (z ω i))

def overlap {I Ω : Type*} [Fintype I] [Fintype Ω] (d : Design Ω)
    (z : Ω → I → Bool) : Finset I :=
  Finset.univ.filter (fun i => 0 < exposureProbability d z i ∧ exposureProbability d z i < 1)

/-- Uniform upper-tail randomization value, counting ties. -/
def randomizationP {Ω : Type*} [Fintype Ω] (D : Ω → ℝ) (ω : Ω) : ℝ :=
  ((Finset.univ.filter (fun υ => D ω ≤ D υ)).card : ℝ) / Fintype.card Ω

/-- Indices 0,1,2 encode onsets 2,3,4; period indices encode dates 1,2,3,4. -/
def onsetExposure (s : Fin 3) (t : Fin 4) : Bool := decide (s.val+2 ≤ t.val+1)

def calendarBaseline (t : Fin 4) : ℝ := (t.val+1 : ℝ)^2
def calendarTreated (t : Fin 4) : ℝ := calendarBaseline t + 2
def calendarEligible : Finset (Fin 4) := {1,2}

def calendarHT (s : Fin 3) : ℝ :=
  htEstimate calendarEligible onsetExposure calendarBaseline calendarTreated
    (exposureProbability (uniformDesign (Fin 3)) onsetExposure) s

/-- The before-after contrast under the sharp null, using all four dates. -/
def calendarBeforeAfter (s : Fin 3) : ℝ :=
  (∑ t : Fin 4, if onsetExposure s t then calendarBaseline t else 0) / (3-s.val : ℝ) -
  (∑ t : Fin 4, if onsetExposure s t then 0 else calendarBaseline t) / (s.val+1 : ℝ)

def calendarObservedBeforeAfter (s : Fin 3) : ℝ :=
  (∑ t : Fin 4, if onsetExposure s t then
    observed onsetExposure calendarBaseline calendarTreated s t else 0) / (3-s.val : ℝ) -
  (∑ t : Fin 4, if onsetExposure s t then 0 else
    observed onsetExposure calendarBaseline calendarTreated s t) / (s.val+1 : ℝ)

/-- Individual group means, with unit weight equal to cluster size. -/
def clusterDIM {J : Type*} [Fintype J] (n y0 y1 : J → ℝ) (z : J → Bool) : ℝ :=
  (∑ j, if z j then n j * y1 j else 0) / (∑ j, if z j then n j else 0) -
  (∑ j, if z j then 0 else n j * y0 j) / (∑ j, if z j then 0 else n j)

def clusterEffect {J : Type*} [Fintype J] (n y0 y1 : J → ℝ) : ℝ :=
  (∑ j, n j * (y1 j-y0 j)) / (∑ j, n j)

def treatedCount {J : Type*} [Fintype J] (z : J → Bool) : ℕ :=
  (Finset.univ.filter (fun j => z j = true)).card

/-- Fixed divisors represent observed group sizes only under the stated count condition. -/
def fixedDIM {J : Type*} [Fintype J] (m : ℕ) (y0 y1 : J → ℝ) (z : J → Bool) : ℝ :=
  (∑ j, if z j then y1 j else 0) / (m : ℝ) -
  (∑ j, if z j then 0 else y0 j) / ((Fintype.card J : ℝ)-m)

end
end SAP.P024
