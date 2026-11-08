import AronowAudit.P023.P023_Audit
import Mathlib.Algebra.Polynomial.Derivative

/-!
Conditional assessment statements for cond-P023. No target is proved here.
The literature propositions are independent of the P023 objects. See the run
report for source checks, application premises, and unproved bridging work.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace AronowAudit.Literature

/-- The Rodrigues normalization P_n(1)=1. G. B. Folland, Fourier Analysis
and Its Applications (Wadsworth & Brooks/Cole, 1992), section 6.2,
equation (6.2), p. 166. This auxiliary definition contains no P023 objects. -/
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

/-- G. B. Folland, Fourier Analysis and Its Applications (1992),
Theorem 6.6, p. 172: P'_(n+1)-P'_(n-1)=(2n+1)P_n for every n >= 1.
All real arguments are quantified. Polynomial differentiation realizes the
ordinary derivatives in the source. No half-interval or P023 moment is assumed. -/
def FollandLegendreDerivativeIdentity : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
    (legendreRodrigues (n + 1)).derivative.eval x -
      (legendreRodrigues (n - 1)).derivative.eval x =
      (2 * (n : ℝ) + 1) * (legendreRodrigues n).eval x

/-- A real trigonometric polynomial of order at most n, with arbitrary
real cosine and sine coefficients (including its constant coefficient).
This is Powell's space Q_n from chapters 13 and 16. -/
def realTrigValue (n : ℕ) (a b : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin (n + 1),
    (a j * Real.cos ((j.val : ℝ) * x) + b j * Real.sin ((j.val : ℝ) * x))

/-- The best uniform trigonometric approximation error, Powell (1981),
equation (16.1), p. 189. For a continuous periodic function, this is the
minimum of the sup norms: the infimum of all uniform upper bounds is an
equivalent definition. The set is nonempty and bounded below in every use.
It is independent of the audit's supError and of all its estimators. -/
def trigBestUniformError (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ a b : Fin (n + 1) → ℝ,
    ∀ x : ℝ, |f x - realTrigValue n a b x| ≤ e}

/-- M. J. D. Powell, Approximation Theory and Methods (Cambridge University
Press, 1981; 1991 reprint), Theorem 16.1 (Jackson II), equation (16.6), p. 190.
For every continuous 2*pi-periodic real function with global Lipschitz
constant M, the best uniform order-n trigonometric error is at most
pi*M/(2*(n+1)). All orders n >= 0, functions and constants are quantified.
A separate M >= 0 assumption is unnecessary: the displayed Lipschitz
premise implies it by testing two distinct arguments, as in the source. -/
def PowellJacksonII : Prop :=
  ∀ (f : ℝ → ℝ) (M : ℝ), Continuous f →
    Function.Periodic f (2 * Real.pi) →
    (∀ x y : ℝ, |f x - f y| ≤ M * |x - y|) →
    ∀ n : ℕ, trigBestUniformError f n ≤ Real.pi * M / (2 * ((n : ℝ) + 1))

#print FollandLegendreOrthogonality
#check @FollandLegendreOrthogonality
#print FollandLegendreDerivativeIdentity
#check @FollandLegendreDerivativeIdentity
#print PowellJacksonII
#check @PowellJacksonII

end AronowAudit.Literature

namespace AronowAudit.P023

universe u

/-- The complete held proposition, with only independent published-result
hypotheses prefixed. Statement only; no held theorem proof is referenced. -/
def uniform_residual_constants_conditional_statement : Prop :=
  AronowAudit.Literature.FollandLegendreOrthogonality →
  AronowAudit.Literature.FollandLegendreDerivativeIdentity →
    ProbabilityLaw uniformMargins ∧ MarginSupport uniformMargins ∧
    (∀ J, 1 ≤ J → residualVariance uniformMargins J = centralBinomial ((J + 1) / 2)^2 / 4) ∧
    (∀ x, (projection uniformMargins 1).eval x = projection1 x) ∧
    (∀ x, (projection uniformMargins 7).eval x = projection7 x) ∧
    residualVariance uniformMargins 1 = 1 / 16 ∧
    residualVariance uniformMargins 7 = 1225 / 65536 ∧
    expectation uniformMargins (fun x => |popResidual uniformMargins 1 x|) = 5 / 24 ∧
    amplification uniformMargins 1 = 10 / 3 ∧
    1 / Real.sqrt (residualVariance uniformMargins 1) = 4 ∧
    1 / Real.sqrt (residualVariance uniformMargins 7) = 256 / 35 ∧
    (47642006857252250 / 10000000000000000 : ℝ) < amplification uniformMargins 7 ∧
    amplification uniformMargins 7 < (47642006857252260 / 10000000000000000 : ℝ)

#check @uniform_residual_constants_conditional_statement

/-- The complete held proposition, with only independent published-result
hypotheses prefixed. Statement only; no held theorem proof is referenced. -/
def corrected_proposition2_conditional_statement : Prop :=
  AronowAudit.Literature.FollandLegendreOrthogonality →
  AronowAudit.Literature.FollandLegendreDerivativeIdentity →
  AronowAudit.Literature.PowellJacksonII →
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (α β : ℝ) (h : ℝ → ℝ) (c δ L σ2 : ℝ)
    (hr : RepairedRegularity ν α β h c δ L σ2) (hiid : IIDSample P ν sample)
    (k : ℕ → ℝ) (hkpos : ∀ N, 0 < k N)
    (hk0 : Tendsto k atTop (nhds 0))
    (hnk : Tendsto (fun N : ℕ => (N : ℝ) * k N) atTop atTop),
    let μ := marginLaw ν
    let m := fun x => α + β*party x + h x
    (∀ J, 1 ≤ J → MomentPositiveDefinite μ J ∧
      residualVariance μ J ≥ c*δ/(4*((J:ℝ)+1))) ∧
    (∀ J, 1 ≤ J → ∃ p : Polynomial ℝ, p.natDegree ≤ J ∧ p.eval 0 = 0 ∧
      supError h p ≤ 4*jacksonK*L/((J:ℝ)+1)) ∧
    (∀ J, 1 ≤ J → |populationCoefficient μ J m - β| ≤
      8*jacksonK*L / Real.sqrt (c*δ*((J:ℝ)+1))) ∧
    Tendsto (fun J => populationCoefficient μ J m) atTop (nhds β) ∧
    (∀ J, 1 ≤ J → ConvergesInProbability P (fun N => samplePolynomial sample N J) (populationCoefficient μ J m)) ∧
    (∀ k', 0 < k' → k' ≤ δ → |populationRD μ m k' - β| ≤ 2*L*k') ∧
    ConvergesInProbability P (sampleRD sample k) β ∧
    (∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, 1 ≤ J →
      ConvergesInProbability P (fun N ω => samplePolynomial sample N J ω - sampleRD sample k N ω)
        (populationCoefficient μ J m - β) ∧ |populationCoefficient μ J m - β| < ε) ∧
    (∀ degrees : ℕ → ℕ, Tendsto degrees atTop atTop →
      Tendsto (fun N => ((degrees N : ℝ)+2)^2 /
        ((N:ℝ) * (smallestMomentEigenvalue μ (degrees N))^3)) atTop (nhds 0) →
      ConvergesInProbability P (fun N ω => samplePolynomial sample N (degrees N) ω -
        populationCoefficient μ (degrees N) m) 0 ∧
      ConvergesInProbability P (fun N ω => samplePolynomial sample N (degrees N) ω - sampleRD sample k N ω) 0) ∧
    (∃ degrees : ℕ → ℕ, (∀ N, 1 ≤ degrees N) ∧ Tendsto degrees atTop atTop ∧
      Tendsto (fun N => ((degrees N : ℝ)+2)^2 /
        ((N:ℝ) * (smallestMomentEigenvalue μ (degrees N))^3)) atTop (nhds 0))

set_option pp.universes true in
#check @corrected_proposition2_conditional_statement

/-- The complete held proposition, with only independent published-result
hypotheses prefixed. Statement only; no held theorem proof is referenced. -/
def density_residual_comparison_conditional_statement : Prop :=
  AronowAudit.Literature.FollandLegendreOrthogonality →
  AronowAudit.Literature.FollandLegendreDerivativeIdentity →
  ∀ (ν : Measure (ℝ × ℝ)) (α β : ℝ)
    (h : ℝ → ℝ) (c δ L σ2 : ℝ) (hr : RepairedRegularity ν α β h c δ L σ2)
    (J : ℕ) (hJ : 1 ≤ J),
    let μ := marginLaw ν
    let n := (J+1)/2
    (∀ p : Polynomial ℝ, p.natDegree ≤ J →
      expectation μ (fun x => (party x-p.eval x)^2) ≥
        c*(∫ x in Set.Icc (-δ) δ, (party x-p.eval x)^2)) ∧
    residualVariance μ J ≥ 2*c*δ*residualVariance uniformMargins J ∧
    2*c*δ*residualVariance uniformMargins J = c*δ*centralBinomial n^2/2 ∧
    c*δ*centralBinomial n^2/2 ≥ c*δ/(8*(n:ℝ)) ∧
    c*δ/(8*(n:ℝ)) ≥ c*δ/(4*((J:ℝ)+1))

#check @density_residual_comparison_conditional_statement

#print axioms uniform_residual_constants_conditional_statement
#print axioms corrected_proposition2_conditional_statement
#print axioms density_residual_comparison_conditional_statement

end AronowAudit.P023
