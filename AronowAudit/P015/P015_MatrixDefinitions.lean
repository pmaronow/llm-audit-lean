import Mathlib.Tactic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace AronowAudit.P015
noncomputable section
open Matrix Finset
open scoped BigOperators

/-- Appendix A's inverse-Gram formula (W′W)⁻¹W′Y, p. 262. It gives the OLS
coefficients when W has full column rank; the definition uses Lean's totalized
matrix inverse for other inputs. -/
noncomputable def ols {N Q : Type*} [Fintype N] [Fintype Q] [DecidableEq Q]
    (W : Matrix N Q ℝ) (Y : N → ℝ) : Q → ℝ :=
  (W.transpose * W)⁻¹.mulVec (W.transpose.mulVec Y)

/-- Full-vector random-coefficient GLS precision: Ω_g=S+σ_g²Q_g⁻¹
and P_g=Ω_g⁻¹, p. 257, correction P015-T10. -/
def groupPrecision {Q : Type*} [Fintype Q] [DecidableEq Q]
    (S Qg : Matrix Q Q ℝ) (σ₂ : ℝ) : Matrix Q Q ℝ := (S+σ₂ • Qg⁻¹)⁻¹

/-- GLS pools all coordinates using matrix precision, as corrected in T10. -/
def pooledGLS {G Q : Type*} [Fintype G] [Fintype Q] [DecidableEq Q]
    (P : G → Matrix Q Q ℝ) (t : G → Q → ℝ) : Q → ℝ :=
  (∑ g, P g)⁻¹.mulVec (∑ g, (P g).mulVec (t g))

/-- The quadratic sum ∑_g (θhat_g−m)′P_g(θhat_g−m). Under the design and
covariance hypotheses of corrected_matrix_pooling (P015-T10, p. 257), its
unique minimizer is pooledGLS P t. No minimization claim is made here for
arbitrary matrices P. -/
def poolingLoss {G Q : Type*} [Fintype G] [Fintype Q]
    (P : G → Matrix Q Q ℝ) (t : G → Q → ℝ) (m : Q → ℝ) : ℝ :=
  ∑ g, dotProduct (t g-m) ((P g).mulVec (t g-m))

end
end AronowAudit.P015
