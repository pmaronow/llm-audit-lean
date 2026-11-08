import Mathlib
import SAP.P025b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

/-! Finite populations compatible with absolute totals or with shares alone.
Positive integer class sizes are required in every compatibility predicate. -/

def absoluteCompatible {J : ℕ} (α β : ℝ) (mass : Fin J → ℝ) (m : Fin J → ℕ) : Prop :=
  ∀ j, 0 < m j ∧ α*(m j : ℝ) ≤ mass j ∧ mass j ≤ β*(m j : ℝ)

def classMean {J : ℕ} (y : Fin J → ℝ) (m : Fin J → ℕ) : ℝ :=
  (∑ j, (m j : ℝ)*y j)/(∑ j, (m j : ℝ))

def sharesCompatible {J : ℕ} (α β : ℝ) (q : Fin J → ℝ) (m : Fin J → ℕ) : Prop :=
  ∃ T : ℝ, 0 < T ∧ absoluteCompatible α β (fun j => T*q j) m

def compatibleMeans {J : ℕ} (y q : Fin J → ℝ) (α β : ℝ) : Set ℝ :=
  {v | ∃ m : Fin J → ℕ, sharesCompatible α β q m ∧ classMean y m = v}

def absoluteCompatibleMeans {J : ℕ} (y mass : Fin J → ℝ) (α β : ℝ) : Set ℝ :=
  {v | ∃ m : Fin J → ℕ, absoluteCompatible α β mass m ∧ classMean y m = v}

def knownSizeCompatibleMeans {J : ℕ} (y mass : Fin J → ℝ) (α β : ℝ) (N : ℕ) : Set ℝ :=
  {v | ∃ m : Fin J → ℕ,absoluteCompatible α β mass m ∧ (∑ j,m j)=N ∧ classMean y m=v}

def proportionRegion {J : ℕ} (q : Fin J → ℝ) (γ : ℝ) (r : Fin J → ℝ) : Prop :=
  (∀ j, 0 ≤ r j) ∧ (∑ j,r j)=1 ∧ ∀ j k, r j*q k ≤ γ*r k*q j

def classProportions {J : ℕ} (m : Fin J → ℕ) (j : Fin J) : ℝ :=
  (m j : ℝ)/(∑ k,(m k : ℝ))

def weightProportions {J : ℕ} (q W : Fin J → ℝ) (j : Fin J) : ℝ :=
  W j*q j/(∑ k,W k*q k)

def rationalVector {J : ℕ} (r : Fin J → ℝ) : Prop := ∀ j, ∃ x : ℚ, (x:ℝ)=r j

end
end SAP.P025b
