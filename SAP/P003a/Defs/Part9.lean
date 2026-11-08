import SAP.P003a.Defs.Part8

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

/-- Packaged content for P003-T14; see the Challenge docstring for scope. -/
def T14Statement : Prop :=
  ((∀ f, IsPMF f → ¬ PrintedDecrease f) ∧ IsSD zeroMass ∧ IsSD fairMass ∧
      ¬ PrintedDecrease zeroMass) ∧
  (IsSD fairMass ∧ (∑' i : ℤ, (i : ℝ)*fairMass i) = 1/2) ∧
  (∀ (k : ℕ) (hk : 0 < k) (g : ℤ → ℝ)
    (hg : IsMass g),
    (∑' j, g j) = 1 ∧ latticeMean k g = (∑' j : ℤ, (j : ℝ)*g j)/(k : ℝ) ∧
    (∀ j : ℤ, (if (2 : ℚ)*j = 1/2 then (1 : ℝ) else 0) = 0))

/-- Packaged content for P003-T9; see the Challenge docstring for scope. -/
def T9Statement : Prop :=
  (IsSD fairMass ∧ (∑' i : ℤ, (i : ℝ)*fairMass i) = 1/2 ∧
    IsMass dependentSumMass ∧ (∑' i : ℤ, (i : ℝ)*dependentSumMass i) = 1 ∧
    dependentSumMass 1 = 0 ∧ dependentSumMass 2 = 1/2 ∧
    ¬ IsSD dependentSumMass) ∧
  (∀ (i : ℤ),
    (∑ b : Bool, if (if b then (1 : ℤ) else 0) = i then (1/2 : ℝ) else 0) =
      fairMass i ∧
    (∑ b : Bool, if (if b then (1 : ℤ) else 0)+(if b then (1 : ℤ) else 0) = i
      then (1/2 : ℝ) else 0) = dependentSumMass i)

/-- Packaged content for P003-T10; see the Challenge docstring for scope. -/
def T10Statement : Prop :=
  (∀ (f : ℤ → ℝ) (hf : IsSD f),
    IsSD (smoothMass f)) ∧
  (∀ (f : ℤ → ℝ) (c : ℤ) (hf : SDShape f c),
    SDShape (smoothMass f) (c+1)) ∧
  (∀ (f : ℤ → ℝ) (hf : IsSD f) (p : ℤ)
    (hp : p = 0 ∨ p = 1),
    IsSD (paritySmooth f p) ∧
    ∀ k, paritySmooth f p (p+2*k) = f k/2 ∧
      paritySmooth f p (p+2*k+1) = f k/2)

/-- Packaged content for P003-T15; see the Challenge docstring for scope. -/
def T15Statement : Prop :=
  (∀ (v : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) (hd : 1 ≤ v.b+v.c),
    IsSD (scaledEstimatorMass v m))

/-- Packaged content for P003-T16; see the Challenge docstring for scope. -/
def T16Statement : Prop :=
  (∀ {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n))
    (m : ℕ) (hm : 0 < m) (hn : n = 2*m) (hz : z.card = m),
    tableEstimator w z = (∑ i, if i ∈ z then bit (w i).1 else -bit (w i).2)/(m : ℝ)) ∧
  ((pairContribution (true,false) (true,true) true,
      pairContribution (true,false) (true,true) false) = (0,1) ∧
    (pairContribution (true,false) (true,false) true,
      pairContribution (true,false) (true,false) false) = (1,1) ∧
    (pairContribution (true,false) (false,true) true,
      pairContribution (true,false) (false,true) false) = (0,0) ∧
    (pairContribution (true,false) (false,false) true,
      pairContribution (true,false) (false,false) false) = (1,0) ∧
    (pairContribution (true,true) (true,true) true,
      pairContribution (true,true) (true,true) false) = (0,0) ∧
    (pairContribution (true,true) (false,false) true,
      pairContribution (true,true) (false,false) false) = (1,-1))

end SAP.P003a
