import SAP.P041.WH.W1.Helpers
import SAP.P041.WH.W1.Refutations
import SAP.P041.WH.W1.GaussianCertificates
import SAP.P041.WH.W1.StudentCertificates

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P041.WH.W1
open Matrix
open scoped BigOperators

/-- Individual binary observations give the four-cell sufficient statistics,
full rank, inverse, coefficients and fitted values. Partition the finite sums
by cell and response; use citation_ols_exact_fit and
citation_gram_inverse_is_inverse. No supplied normal equations are assumed. -/
def T7_L1 : Prop :=
  ∀ (n : ℕ) (cell : Fin n → Fin 4) (y : Fin n → Bool),
    CitationInputsW1 n cell y → CitationFitW1 cell y

/-- Transport the cell residual sums and HC1 calculation to the individual
observations. The preceding fit certificate is an explicit premise. On each
cell, sum (Y-f)^2 as a(1-f)^2+(50-a)f^2. Expand the covariance's (1,1) entry,
use the symmetric inverse and citation_hc1_exact_variance. About 200 lines. -/
def T7_L2 : Prop :=
  T7_L1 → ∀ (n : ℕ) (cell : Fin n → Fin 4) (y : Fin n → Bool),
    CitationInputsW1 n cell y → CitationResidualFactsW1 cell y

/-- Identify the genuine Gamma density with its integer-power form. Adapt
student21_density_identity with Gamma_nat_eq_factorial 98 and
Gamma_nat_add_half 98; cancel positive square roots and factorials. -/
def T7_L3 : Prop :=
  ∀ t : ℝ, Student197DensityW1 t = Student197ConstantW1 / (1+t^2/197)^99

/-- Global alternating polynomial bounds for the t(197) kernel. Multiply by
(1+u)^99. The remainder after degree 24, and the negative remainder after
degree 25, have nonnegative coefficients for u≥0. Generate the 99 rational
coefficients, prove the polynomial identities with ring, and use positivity.
This needs no convergence or interchange of an infinite series and integral. -/
def T7_L4 : Prop :=
  ∀ u : ℝ, 0 ≤ u →
    Student197TaylorW1 25 u ≤ 1/(1+u)^99 ∧
    1/(1+u)^99 ≤ Student197TaylorW1 24 u

/-- Rational normalization enclosure. Square the positive bounds, using
Real.pi_gt_d20, Real.pi_lt_d20 and Real.sq_sqrt at 197. All remaining
obligations concern a single exact binomial coefficient and rational powers. -/
def T7_L5 : Prop :=
  (0.39843633174605 : ℝ) ≤ Student197ConstantW1 ∧
    Student197ConstantW1 ≤ 0.39843633174607

/-- Finite Student tail certificates, with the density, kernel and constant
certificates supplied as premises. Integrate the degree-24/25 brackets on
[0,x], using the proved student197_polynomial_integral to obtain
Student197IntegratedW1 n x. Bound the positive integral and normalization,
then discharge the four rational endpoints with norm_num. The two critical
endpoints have margins exceeding 0.000013; the degree-25 remainder is below
10^(-12) there. This is the integration/certificate step, not a new assumption
that the reference probability has a particular value. -/
def T7_L6 : Prop :=
  T7_L3 → T7_L4 → T7_L5 → Student197EndpointsW1

/-- Continuity and strict decrease of the actual Student tail on [0,∞).
Use student_density_regular (ν=197), Gamma_pos_of_pos for strict positivity,
continuity of the interval integral, and positivity of its increment on a
nondegenerate interval. The absolute value makes the tail continuous on ℝ. -/
def T7_L7 : Prop :=
  Continuous Student197TailW1 ∧ StrictAntiOn Student197TailW1 (Set.Ici 0)

/-- Normal-reference numerical facts for the erroneous statistic and the 1%
critical point. Use Wave1.normal_tail_bound and normal_tail_antitone at
64/129, 1, 2.5755 and 2.5765. Obtain the genuine critical point from
NormalCompletion.normalCritical_cdf/normalCritical_pos and bracket it by
strictMono_normal_cdf. This is a finite tail-certificate refinement. -/
def T7_L8 : Prop := CitationNormalFactsW1

/-- First Cox rectangle: refine the endpoint logarithms using
neg_log_certificate and wald_numerator_above; then apply a sharpened Gaussian
integral enclosure. Derive 0<h<1 and s>0 from the printed intervals. The
normalizer 1/sqrt(2π) can be bounded using pi_gt_d20/pi_lt_d20, and the
degree-28/29 normal_intPoly brackets suffice for these nine-decimal bounds. -/
def T8_L1 : Prop :=
  CoxRectangleW1 0.670 0.095 2.8064 2.8426 0.004416378 0.005073862

/-- Second Cox rectangle. Use neg_log_certificate at 0.4795 and 0.4805,
wald_numerator_above and positive s endpoints, then normal_integral_bracket
with a sharpened normalizing constant. Keep endpoint log bounds rational. -/
def T8_L2 : Prop :=
  CoxRectangleW1 0.480 0.174 2.0181 2.0314 0.041792640 0.044011941

/-- Third Cox rectangle. The numerator is increasing on this interval, so use
wald_numerator_below rather than the decreasing-numerator lemma. Certify
endpoint logs, divide by the positive s endpoints, and enclose the actual
normal CDF with normal_integral_bracket and normal_cdf_integral. -/
def T8_L3 : Prop :=
  CoxRectangleW1 0.274 0.162 2.1820 2.1974 0.027554610 0.029563591

/-- Fourth Cox rectangle. As in the third, wald_numerator_below supplies the
correct numerator direction. Refine rational endpoint logs and Gaussian
tails, including the lower p bound strictly above 0.0139. -/
def T8_L4 : Prop :=
  CoxRectangleW1 0.316 0.149 2.4345 2.4520 0.013945057 0.015189259

/-- First central approximation. Bound log(0.670) by the finite atanh series,
then use the Gaussian integral bracket with a sharp normalizing constant.
Errors express decimal ellipses, not nearest-last-digit rounding. -/
def T8_L5 : Prop := CoxCentreW1 0.670 0.095 (-2.82442) 0.0047366

/-- Second central approximation; the same finite log and normal-integral
certificates at (0.480,0.174) prove the two explicit errors and negative sign. -/
def T8_L6 : Prop := CoxCentreW1 0.480 0.174 (-2.02474) 0.0428938

/-- Third central approximation. Its actual p is about 0.028547593538, so
retain error <10^(-7) about 0.0285475, not a nearest-digit rounding assertion.
Use the refined log and normal integral certificates. -/
def T8_L7 : Prop := CoxCentreW1 0.274 0.162 (-2.18967) 0.0285475

/-- Fourth central approximation, with explicit errors for the logarithmic
Wald statistic and actual Gaussian p value. The degree-28/29 bracket and
pi_d20 bounds give ample precision. -/
def T8_L8 : Prop := CoxCentreW1 0.316 0.149 (-2.44319) 0.0145578

/-- Genuine 1% normal critical point and its approximation. Choose the donor
normalCritical 0.01, use its exact CDF equation and positivity, and bracket
the tail at 2.5758292 and 2.5758294 using sharp finite Gaussian certificates.
StrictMono_normal_cdf gives the strict bracket and uniqueness. -/
def T8_L9 : Prop :=
  ∃ c : ℝ, NormalCriticalW1 0.01 c ∧ |c-2.5758293| < 0.0000001

/-- Genuine 5% normal critical point. Bracket at 1.9599639 and 1.9599641,
using the donor exact quantile equation and refined normal-tail certificates;
strict CDF monotonicity proves uniqueness. -/
def T8_L10 : Prop :=
  ∃ c : ℝ, NormalCriticalW1 0.05 c ∧ |c-1.9599640| < 0.0000001

/-- Genuine 10% normal critical point. Bracket at 1.6448535 and 1.6448537
with the same exact CDF and finite-integral route. No empty infimum is used
in the exported proposition: existence, positivity and uniqueness are explicit. -/
def T8_L11 : Prop :=
  ∃ c : ℝ, NormalCriticalW1 0.10 c ∧ |c-1.6448536| < 0.0000001

/-- Derive the P design's size, Gram matrix, full rank and cross products
from the three studies' six cells of 50. Partition finite sums by study and
treatment. Certify positiveStudyGram's invertibility by a rational inverse;
ols_normal_equations and positive_balanced_slope finish the treatment slope.
The outcome is arbitrary real, so the result includes all binary horizons. -/
def T9_L1 : Prop := PositiveDesignFactsW1

/-- Derive the C design's size and sufficient statistics from four cells of
50. Use the explicit citationGramInverse for full rank and the donor
cited_balanced_slope after ols_normal_equations. No Gram or nonsingularity
hypothesis is allowed: both follow from the cell counts. -/
def T9_L2 : Prop := CitedDesignFactsW1

/-- Derive the F design's size, Gram matrix, invertibility and cross products
from the 75/76 arm cardinalities. An explicit 2×2 inverse or determinant
calculation proves full rank; former_two_group_slope gives the result. -/
def T9_L3 : Prop := FormerDesignFactsW1

theorem T8_assembly (h1 : T8_L1) (h2 : T8_L2) (h3 : T8_L3) (h4 : T8_L4)
    (h5 : T8_L5) (h6 : T8_L6) (h7 : T8_L7) (h8 : T8_L8)
    (h9 : T8_L9) (h10 : T8_L10) (h11 : T8_L11) : T8WholeStatement := by
  refine ⟨t8_existing, h1, h2, h3, h4, ?_, ?_, ?_, ?_, h5, h6, h7, h8, ?_⟩
  · intro h s hh hs
    have hc := h1 h s hh hs
    exact ⟨by linarith [hc.2.2.2.2.2.1], by linarith [hc.2.2.2.2.2.2]⟩
  · intro h s hh hs
    have hc := h2 h s hh hs
    exact ⟨by linarith [hc.2.2.2.2.2.1], by linarith [hc.2.2.2.2.2.2]⟩
  · intro h s hh hs
    have hc := h3 h s hh hs
    exact ⟨by linarith [hc.2.2.2.2.2.1], by linarith [hc.2.2.2.2.2.2]⟩
  · intro h s hh hs
    have hc := h4 h s hh hs
    exact ⟨by linarith [hc.2.2.2.2.2.1], by linarith [hc.2.2.2.2.2.2]⟩
  · obtain ⟨c₁,hc₁,he₁⟩ := h9
    obtain ⟨c₅,hc₅,he₅⟩ := h10
    obtain ⟨c₁₀,hc₁₀,he₁₀⟩ := h11
    refine ⟨c₁,c₅,c₁₀,hc₁,he₁,hc₅,he₅,hc₁₀,he₁₀,
      normal_tier_equivalences c₁ c₅ c₁₀ hc₁ hc₅ hc₁₀, ?_⟩
    have a := (abs_lt.mp he₁)
    have b := (abs_lt.mp he₅)
    exact ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith⟩

theorem T7_assembly (h1 : T7_L1) (h2 : T7_L2) (h3 : T7_L3) (h4 : T7_L4)
    (h5 : T7_L5) (h6 : T7_L6) (h7 : T7_L7) (h8 : T7_L8) : T7WholeStatement := by
  have hEnds := h6 h3 h4 h5
  have hEndsCopy := hEnds
  obtain ⟨pLo,pHi,pOne,pA,pB⟩ := hEndsCopy
  have hBelow : ∀ x : ℝ, |x| < 1 → 0.10 < Student197TailW1 x := by
    intro x hx
    have he : Student197TailW1 |x| = Student197TailW1 x := by
      simp only [Student197TailW1, abs_abs]
    have hh := h7.2 (show (0 : ℝ) ≤ |x| from abs_nonneg x)
      (show (0 : ℝ) ≤ 1 by norm_num) hx
    rw [he] at hh
    exact pOne.trans hh
  obtain ⟨cT,hcT,heT⟩ := intermediate_value_Icc' (by norm_num : (2.6005 : ℝ) ≤ 2.6015)
    h7.1.continuousOn (show Student197TailW1 2.6015 ≤ 0.01 ∧
      0.01 ≤ Student197TailW1 2.6005 from ⟨pB.le,pA.le⟩)
  have hcTa : (2.6005 : ℝ) < cT := by
    by_contra h
    have heq : cT = 2.6005 := le_antisymm (le_of_not_gt h) hcT.1
    rw [heq] at heT
    linarith
  have hcTb : cT < (2.6015 : ℝ) := by
    by_contra h
    have heq : cT = 2.6015 := le_antisymm hcT.2 (le_of_not_gt h)
    rw [heq] at heT
    linarith
  have hcT0 : 0 < cT := by linarith
  have hUnique : ∀ d : ℝ, 0 ≤ d → Student197TailW1 d = 0.01 → d = cT := by
    intro d hd he
    exact h7.2.injOn hd hcT0.le (he.trans heT.symm)
  have hNormalCopy := h8
  obtain ⟨_,_,_,cN,hcN,hcNa,hcNb⟩ := hNormalCopy
  have hSElo : (0.06446 : ℝ) < Real.sqrt (2047/492500 : ℝ) := by
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 0.06446)).mpr
    norm_num
  have hSEhi : Real.sqrt (2047/492500 : ℝ) < 0.06447 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 0.06447)).mpr
    norm_num
  refine ⟨t7_existing, (fun n c y hi => ⟨h1 n c y hi, h2 h1 n c y hi⟩),
    hSElo,hSEhi,h8,hEnds,hBelow,cN,cT,hcN,hcNa,hcNb,hcT0,heT,hUnique,
    hcTa,hcTb,by linarith,by linarith,?_⟩
  let t : ℝ := (8/25) / Real.sqrt (2047/492500)
  have ht : (4.89 : ℝ) < t := Bridge.corrected_citation_standard_error.2.2.2.2.2.2.2.2.2.2.2.1
  have ht0 : 0 < t := by linarith
  have htAbs : |t| = t := abs_of_pos ht0
  have hN : cN < |t| := by rw [htAbs]; linarith
  have hT : cT < |t| := by rw [htAbs]; linarith
  have hpT := h7.2 hcT0.le (abs_nonneg t) hT
  have heAbs : Student197TailW1 |t| = Student197TailW1 t := by
    simp only [Student197TailW1, abs_abs]
  rw [heAbs,heT] at hpT
  refine ⟨?_, by rwa [htAbs], hN,hT,(normal_lt_critical 0.01 cN t hcN).mpr hN,hpT⟩
  change ((8/25 : ℝ) / Real.sqrt (2047/492500))^2 = 50432/2047
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2047/492500)]
  norm_num

theorem T9_assembly (h1 : T9_L1) (h2 : T9_L2) (h3 : T9_L3) : T9WholeStatement := by
  exact ⟨complement_all,h1,h2,h3,s11_regressions h1 h2 h3,s11_table,six_hour_vectors h1,indicator_updates⟩

theorem T11_assembly : T11WholeStatement := t11_complete

theorem T12_assembly : T12WholeStatement := t12_complete

end SAP.P041.WH.W1
