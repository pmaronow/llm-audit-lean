import SAP.P024.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024
open scoped BigOperators
noncomputable section

/-- Unnormalized probability of the conditioning event, as a finite sum. -/
def bernoulliNonemptyMass (k : ℕ) (p : ℝ) : ℝ :=
  ∑ s : NonemptyAllocations k, bernoulliMass p s.val

/-- Normalized conditional masses; used below only for 0<p<1 with positive event mass. -/
def bernoulliConditionalMass (k : ℕ) (p : ℝ) (s : NonemptyAllocations k) : ℝ :=
  bernoulliMass p s.val / bernoulliNonemptyMass k p

def bernoulliConditionalExpectation (k : ℕ) (p : ℝ)
    (X : NonemptyAllocations k → ℝ) : ℝ :=
  ∑ s, bernoulliConditionalMass k p s * X s

def blockPopulation {B : Type*} [Fintype B] (I : B → Type*) [∀ b, Fintype (I b)] : ℝ :=
  ∑ b, (Fintype.card (I b) : ℝ)

/-- Block HT contrast with stipulated fractions, identified with actual propensities in T8. -/
def blockedHT {B Ω : Type*} [Fintype B] (I : B → Type*) [∀ b, Fintype (I b)]
    (m : B → ℕ) (z : Ω → (b : B) → I b → Bool)
    (y0 y1 : (b : B) → I b → ℝ) (ω : Ω) : ℝ :=
  (∑ b, ∑ i, if z ω b i then y1 b i / ((m b : ℝ)/Fintype.card (I b))
    else -(y0 b i/(1-(m b : ℝ)/Fintype.card (I b)))) / blockPopulation I

def blockedEstimate {B Ω : Type*} [Fintype B] (I : B → Type*) [∀ b, Fintype (I b)]
    (m : B → ℕ) (z : Ω → (b : B) → I b → Bool)
    (y0 y1 : (b : B) → I b → ℝ) (ω : Ω) : ℝ :=
  ∑ b, (Fintype.card (I b) : ℝ)/blockPopulation I *
    fixedDIM (m b) (y0 b) (y1 b) (z ω b)

end
end SAP.P024
