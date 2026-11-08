import Mathlib.Tactic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace AronowAudit.P015
noncomputable section
open Matrix Finset
open scoped BigOperators

noncomputable def ols {N Q : Type*} [Fintype N] [Fintype Q] [DecidableEq Q]
    (W : Matrix N Q ℝ) (Y : N → ℝ) : Q → ℝ :=
  (W.transpose * W)⁻¹.mulVec (W.transpose.mulVec Y)

def groupPrecision {Q : Type*} [Fintype Q] [DecidableEq Q]
    (S Qg : Matrix Q Q ℝ) (σ₂ : ℝ) : Matrix Q Q ℝ := (S+σ₂ • Qg⁻¹)⁻¹

def pooledGLS {G Q : Type*} [Fintype G] [Fintype Q] [DecidableEq Q]
    (P : G → Matrix Q Q ℝ) (t : G → Q → ℝ) : Q → ℝ :=
  (∑ g, P g)⁻¹.mulVec (∑ g, (P g).mulVec (t g))

def poolingLoss {G Q : Type*} [Fintype G] [Fintype Q]
    (P : G → Matrix Q Q ℝ) (t : G → Q → ℝ) (m : Q → ℝ) : ℝ :=
  ∑ g, dotProduct (t g-m) ((P g).mulVec (t g-m))

end
end AronowAudit.P015
