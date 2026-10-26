import AronowAudit.P023.P023_Audit
import Mathlib.Algebra.Polynomial.Derivative

/-!
The Rodrigues-normalized Legendre polynomials and the proposition expressing
their orthogonality and squared norms from Folland. The polynomial is defined
explicitly; orthogonality is a proposition definition, not a theorem proved here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace AronowAudit.Literature

/-- The Legendre polynomial defined by Rodrigues' formula. G. B. Folland,
Fourier Analysis and Its Applications (Wadsworth & Brooks/Cole, 1992),
section 6.2, equation (6.2), p. 166. -/
def legendreRodrigues (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((2 ^ n * (Nat.factorial n : ℝ))⁻¹) *
    (Polynomial.derivative^[n]) ((Polynomial.X ^ 2 - 1) ^ n)

/-- G. B. Folland, Fourier Analysis and Its Applications (1992),
Theorem 6.1, equation (6.4), p. 167 (proof continues on p. 168).
Full orthogonality and squared norms of the Rodrigues-normalized real
Legendre polynomials, for every pair of nonnegative integer degrees.
The source uses L2(-1,1); endpoints are Lebesgue-null, so the displayed
ordinary integral over Icc is the same inner product. -/
def FollandLegendreOrthogonality : Prop :=
  ∀ m n : ℕ,
    (∫ x in Set.Icc (-1 : ℝ) 1,
      (legendreRodrigues m).eval x * (legendreRodrigues n).eval x) =
      if m = n then 2 / (2 * (n : ℝ) + 1) else 0


end AronowAudit.Literature

namespace AronowAudit.P023

universe u


end AronowAudit.P023
