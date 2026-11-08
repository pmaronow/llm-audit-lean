import SAP.P003a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Unit tables use zero-based labels and Boolean binary outcomes. An integer-indexed
mass g represents physical points j/k on the lattice with denominator k; latticeMean
uses those physical coordinates. IsMass requires an absolutely summable first moment,
whereas IsPMF requires only nonnegative, summable masses with total one. SDShape uses
twice the center, allowing half-integer centers. Fair convolutions encode independence. -/

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

abbrev PotentialTable (n : ℕ) := Fin n → Bool × Bool

def bit (b : Bool) : ℝ := if b then 1 else 0

def tableCounts {n : ℕ} (w : PotentialTable n) : Counts :=
  ⟨(Finset.univ.filter fun i => w i = (true,true)).card,
   (Finset.univ.filter fun i => w i = (true,false)).card,
   (Finset.univ.filter fun i => w i = (false,true)).card,
   (Finset.univ.filter fun i => w i = (false,false)).card⟩

noncomputable def tableTau {n : ℕ} (w : PotentialTable n) : ℝ :=
  (∑ i, (bit (w i).1 - bit (w i).2)) / n

def SDShape (f : ℤ → ℝ) (c₂ : ℤ) : Prop :=
  (∀ i, f (c₂-i) = f i) ∧ (∀ i j, c₂ ≤ 2*i → i ≤ j → f j ≤ f i)

def IsPMF (f : ℤ → ℝ) : Prop :=
  (∀ i, 0 ≤ f i) ∧ Summable f ∧ (∑' i, f i) = 1

def IsMass (f : ℤ → ℝ) : Prop :=
  (∀ i, 0 ≤ f i) ∧ Summable f ∧ (∑' i, f i) = 1 ∧
    Summable (fun i : ℤ => (i : ℝ) * f i)

/-- A normalized finite-first-moment law symmetric and decreasing away from its mean. -/
def IsSD (f : ℤ → ℝ) : Prop :=
  IsMass f ∧ ∃ c₂ : ℤ, (∑' i : ℤ, (i : ℝ) * f i) = (c₂ : ℝ)/2 ∧ SDShape f c₂

noncomputable def fairMass (i : ℤ) : ℝ :=
  (if i = 0 then 1/2 else 0) + (if i = 1 then 1/2 else 0)

noncomputable def dependentSumMass (i : ℤ) : ℝ :=
  (if i = 0 then 1/2 else 0) + (if i = 2 then 1/2 else 0)

/-- Independent convolution with the uniform mass on zero and one. -/
noncomputable def smoothMass (f : ℤ → ℝ) (i : ℤ) : ℝ := (f i + f (i-1))/2

/-- Independent fair smoothing of a law supported on the parity lattice p+2Z. -/
noncomputable def paritySmooth (f : ℤ → ℝ) (p : ℤ) (i : ℤ) : ℝ := f ((i-p)/2)/2

def PrintedDecrease (f : ℤ → ℝ) : Prop := ∀ i j, i < j → f j ≤ f i

def zeroMass (i : ℤ) : ℝ := if i = 0 then 1 else 0

noncomputable def latticeMean (k : ℕ) (g : ℤ → ℝ) : ℝ :=
  ∑' j : ℤ, ((j : ℝ)/(k : ℝ))*g j

/-- The complete-randomization probability that m times the estimator equals j. -/
noncomputable def scaledEstimatorMass (v : Counts) (m : ℕ) (j : ℤ) : ℝ :=
  designProb v m (fun q => (m : ℚ)*estimateQ (observed v q) = (j : ℚ))

def pairContribution (w₁ w₂ : Bool × Bool) (z : Bool) : ℤ :=
  if z then (if w₁.1 then 1 else 0) - (if w₂.2 then 1 else 0)
  else (if w₂.1 then 1 else 0) - (if w₁.2 then 1 else 0)

noncomputable def tableEstimator {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) : ℝ :=
  (∑ i, if i ∈ z then bit (w i).1 else 0) / z.card -
    (∑ i, if i ∈ z then 0 else bit (w i).2) / (n-z.card)

noncomputable def finiteTail {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (D : Ω → ℝ)
    (x : ℝ) : ℝ := ∑ i, if x ≤ D i then w i else 0

end SAP.P003a
