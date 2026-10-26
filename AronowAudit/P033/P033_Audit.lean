import Mathlib.Tactic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.CDF
import Mathlib.Probability.Moments.Variance
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# P033: mathematical models and corrections

Exact numerical data values below are premises, not conclusions inferred
from a dataset. The models M1 and M2 and the explicit counterexamples
are distinguished from the published claims.
-/
namespace AronowAudit.P033

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section

/-- "The difference between the expected treated and control potential outcomes at a
cutoff" (main p. 3, identification). The arguments are the two conditional mean functions. -/
def rdEffect (μ₁ μ₀ : ℝ → ℝ) (c : ℝ) : ℝ := μ₁ c - μ₀ c


/-- Normal CDF Φ of N(0,1), notation used here, not notation printed in the paper.
This is a genuine probability measure, not an uninterpreted function. -/
def normalCDF (x : ℝ) : ℝ := (gaussianReal 0 1).real (Iic x)

/-- Φ⁻¹(p), the infimum quantile of the actual standard Gaussian, notation used here.
At the levels used below, the Gaussian CDF is strictly increasing and continuous. -/
def normalQuantile (p : ℝ) : ℝ := sInf {x : ℝ | p ≤ normalCDF x}

/-- "A two-tailed test at the 5% significance level" (main p. 9).
Its unrounded normal critical value is Φ⁻¹(39/40), as read from replication code. -/
def normalCritical : ℝ := normalQuantile (39/40)

/-- φ, the standard-normal density. -/
def normalDensity (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The normal-approximation power described on main p. 9:
"based on a central limit approximation for the sampling distribution". -/
def normalPower (a : ℝ) : ℝ := normalCDF (a - normalCritical) +
  normalCDF (-a - normalCritical)

/-- Expectation under a finite, equally likely randomization distribution.
Used for the 1024 equally likely cluster shocks (T3), not as an
assumption that the original paper is a finite-population analysis. -/
def finiteMean {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ) : ℝ :=
  (∑ ω, Y ω) / (Fintype.card Ω : ℝ)

/-- Sampling variance about the finite expectation under the same uniform law (T3). -/
def finiteVariance {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ) : ℝ :=
  finiteMean (fun ω => (Y ω - finiteMean Y)^2)

/-- The sample mean is the arithmetic mean of n records. -/
def sampleMean {n : ℕ} (Y : Fin n → ℝ) : ℝ := (∑ i, Y i) / n

/-- Sample variance with divisor n-1; the paper's p. 7 wording says "sample variance"
although the code uses its square root (T10-T11). -/
def sampleVariance {n : ℕ} (Y : Fin n → ℝ) : ℝ :=
  (∑ i, (Y i - sampleMean Y)^2) / ((n : ℝ) - 1)

/-- Sample standard deviation, the corrected divisor for main p. 7, Figure 4. -/
def sampleSD {n : ℕ} (Y : Fin n → ℝ) : ℝ := Real.sqrt (sampleVariance Y)

/-- "Standardized point estimates and standardized estimated standard errors on the two
axes" (main p. 7). The horizontal estimate is absolute, as in the plotting code. -/
def funnelPoint (β se s₀ : ℝ) : ℝ × ℝ := (|β| / s₀, se / s₀)

/-- The S4-described upper-endpoint SE: "using the upper bound of a 95% CI and the
point estimate ... critical value" (supplement S4, pp. 9-10). -/
def upperSE (β U q : ℝ) : ℝ := (U - β) / q

/-- Corrected S4 description of the released rule: full interval width divided by
 twice the normal critical value (T15; main p. 4 and supplement S4). -/
def widthSE (L U q : ℝ) : ℝ := (U - L) / (2 * q)

/-- "Reconstruct t-statistics using the ratio of coefficients and standard errors"
(main p. 4); the replication uses their absolute values. -/
def absoluteT (β se : ℝ) : ℝ := |β| / se

/-- Missing p-values in the released cleaning workflow are normal-tail transforms
2 Φ(-|t|), as specified in corrected T15 (supplement S4). -/
def reconstructedP (β L U q : ℝ) : ℝ :=
  2 * normalCDF (-absoluteT β (widthSE L U q))

/-- T11(i), main p. 7 corrected: standardizing both coordinates by one nonzero
divisor preserves the signed t-ratio. This is a supporting algebra lemma. -/
theorem standardized_ratio (β se s : ℝ) (hs : s ≠ 0) (hse : se ≠ 0) :
    (β / s) / (se / s) = β / se := by
  field_simp

/-- T11(ii), main p. 7 corrected: the boundary t = ζ has y-on-x slope 1/ζ. -/
theorem significance_boundary (x y ζ : ℝ) (hy : y ≠ 0) (hζ : ζ ≠ 0) :
    x / y = ζ ↔ y = x / ζ := by
  rw [div_eq_iff hy, eq_div_iff hζ]
  constructor <;> intro h <;> nlinarith

/-- T11(iii), main p. 7 corrected: significance is on or below the reciprocal line,
equivalently on or to the right at a fixed height. -/
theorem significance_side (x y ζ : ℝ) (hy : 0 < y) (hζ : 0 < ζ) :
    (ζ ≤ x / y ↔ y ≤ x / ζ) ∧ (y ≤ x / ζ ↔ ζ * y ≤ x) := by
  rw [le_div_iff₀ hy, le_div_iff₀ hζ]
  constructor <;> constructor <;> intro h <;> nlinarith

/-- T11(v), corrected p. 7: nonnegative variance equals its standard deviation
exactly at variance zero or one. -/
theorem sqrt_eq_variance (v : ℝ) (hv : 0 ≤ v) :
    Real.sqrt v = v ↔ v = 0 ∨ v = 1 := by
  constructor
  · intro h
    have hsq := Real.sq_sqrt hv
    rw [h] at hsq
    have : v * (v - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- Binary sample-variance formula in terms of n records and k ones, as in
T11(v), p. 7 corrected. For natural counts n≥2 and k≤n this describes an
actual binary multiset; the definition extends the expression to arbitrary reals. -/
def binarySampleVariance (n k : ℝ) : ℝ :=
  (k * (1 - k/n)^2 + (n-k) * (k/n)^2) / (n-1)

/-- T11(v): algebraic identity for arbitrary real n≠0,1 and k; for natural
counts n≥2 and k≤n, it is the variance formula for k ones and n-k zeros. -/
theorem binary_sample_variance_formula (n k : ℝ) (hn : n ≠ 0) (hn1 : n ≠ 1) :
    binarySampleVariance n k = k*(n-k)/(n*(n-1)) := by
  unfold binarySampleVariance
  field_simp
  <;> ring


/-- T6(i)/T11(v): actual sample variance of any finite vector of binary outcomes
with k ones. This bridges the binary multiset formula to the reusable sample
variance definition instead of assuming that formula as a model of variance. -/
theorem binary_sample_variance_actual {n : ℕ} (hn : 2 ≤ n)
    (y : Fin n → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (k : ℕ) (hk : (∑ i, y i) = (k:ℝ)) :
    sampleVariance y = (k:ℝ)*((n:ℝ)-k)/((n:ℝ)*((n:ℝ)-1)) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have hn1 : (n:ℝ)-1 ≠ 0 := by linarith
  have hy2 : (∑ i, y i^2) = ∑ i, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    rcases hy i with h | h <;> norm_num [h]
  have hexpand : (∑ i, (y i-sampleMean y)^2) =
      (∑ i, y i^2)-2*sampleMean y*(∑ i, y i)+(n:ℝ)*sampleMean y^2 := by
    calc
      (∑ i, (y i-sampleMean y)^2) =
        ∑ i, (y i^2-2*sampleMean y*y i+sampleMean y^2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
          Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold sampleVariance
  rw [hexpand,hy2,hk]
  simp only [sampleMean,hk]
  field_simp
  <;> ring

/-- T10, exact witnesses for main p. 7 and Figure 4 p. 8: the printed
slope misclassifies (1/2,1/2); sample variance and sample SD give different points.
This does not assert that the actual figure or its code uses the wrong line. -/
theorem funnel_counterexample :
    (0 ≤ (1/2 : ℝ) ∧ (1/2 : ℝ) ≤ 2 ∧ (1/2 : ℝ) ≤ 4/5) ∧
    ((1/2 : ℝ)/(1/2) = 1 ∧ (1 : ℝ) < 49/25) ∧
    ((1/2 : ℝ)/(49/25) = 25/98 ∧ (25/98 : ℝ) < 1/2) ∧
    sampleMean ![(0:ℝ),2,4] = 2 ∧
    sampleVariance ![(0:ℝ),2,4] = 4 ∧
    sampleSD ![(0:ℝ),2,4] = 2 ∧
    funnelPoint 1 (1/2) 2 = (1/2,1/4) ∧
    funnelPoint 1 (1/2) 4 = (1/4,1/8) ∧
    funnelPoint 1 (1/2) 2 ≠ funnelPoint 1 (1/2) 4 ∧
    ((1/2 : ℝ)/(1/4) = 2 ∧ (1/4 : ℝ)/(1/8) = 2) := by
  norm_num [sampleMean, sampleVariance, sampleSD, funnelPoint, Fin.sum_univ_succ]

/-- T11, the complete formal content of the corrected funnel-plot description
(main p. 7, Fig. 4 p. 8), including all nonzero and positive hypotheses and the
Boas-Hidalgo 82/568 binary variance and decimal enclosure. The stored decimal
is a premise and is not asserted to be exactly an irrational square root. -/
theorem funnel_correction :
    (∀ β se s : ℝ, s ≠ 0 → se ≠ 0 → (β/s)/(se/s) = β/se) ∧
    (∀ x y ζ : ℝ, y ≠ 0 → ζ ≠ 0 → (x/y = ζ ↔ y = x/ζ)) ∧
    (∀ x y ζ : ℝ, 0 < y → 0 < ζ →
      (ζ ≤ x/y ↔ y ≤ x/ζ) ∧ (y ≤ x/ζ ↔ ζ*y ≤ x)) ∧
    ((1 : ℝ)/(49/25) = 25/49 ∧ (25/49 : ℝ) < 1 ∧ (1 : ℝ) < 49/25) ∧
    (∀ v : ℝ, 0 ≤ v → (Real.sqrt v = v ↔ v = 0 ∨ v = 1)) ∧
    (∀ n k : ℕ, 2 ≤ n → k ≤ n →
      binarySampleVariance n k = (k:ℝ)*((n:ℝ)-k)/((n:ℝ)*((n:ℝ)-1))) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ y : Fin n → ℝ,
      (∀ i, y i = 0 ∨ y i = 1) → ∀ k : ℕ, (∑ i, y i) = (k:ℝ) →
      sampleVariance y = (k:ℝ)*((n:ℝ)-k)/((n:ℝ)*((n:ℝ)-1))) ∧
    binarySampleVariance 568 82 = 123/994 ∧
    ((351770457441169/10^15 - 1/10^14 : ℝ)^2 < 123/994 ∧
      (123/994 : ℝ) < (351770457441169/10^15 + 1/10^14)^2) := by
  refine ⟨standardized_ratio, significance_boundary, significance_side, ?_,
    sqrt_eq_variance, ?_, ?_, ?_, ?_⟩
  · norm_num
  · intro n k hn hk
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    apply binary_sample_variance_formula <;> linarith
  · intro n hn y hy k hk
    exact binary_sample_variance_actual hn y hy k hk
  · norm_num [binarySampleVariance]
  · norm_num

/-- T14, exact Klašnja-Titiunik and Holbein witnesses for the two interval
SE functions (supplement S4; the numbers and code rule are
premises). The two rules put Holbein b on opposite sides of the 27q/18 bin edge. -/
theorem interval_rule_counterexample :
    (∀ q : ℝ, 0 < q →
      upperSE (-3/20) (-101/1000) q = 49/(1000*q) ∧
      widthSE (-213/1000) (-101/1000) q = 7/(125*q) ∧
      widthSE (-213/1000) (-101/1000) q /
        upperSE (-3/20) (-101/1000) q = 8/7) ∧
    ((-101/1000 : ℝ) - (-3/20) = 49/1000 ∧
      (-101/1000 : ℝ) - (-213/1000) = 14/125) ∧
    upperSE (-3/20) (-101/1000) (49/25) = 1/40 ∧
    absoluteT (-3/20) (upperSE (-3/20) (-101/1000) (49/25)) = 6 ∧
    widthSE (-213/1000) (-101/1000) (49/25) = 1/35 ∧
    absoluteT (-3/20) (widthSE (-213/1000) (-101/1000) (49/25)) = 21/4 ∧
    (((-213/1000 : ℝ) + (-101/1000))/2 - (-3/20) = -7/1000) ∧
    (∀ q : ℝ, 0 < q →
      absoluteT (79/1000) (widthSE (27/1000) (132/1000) q) / q = 158/105 ∧
      absoluteT (79/1000) (upperSE (79/1000) (132/1000) q) / q = 79/53) ∧
    ((27/18 : ℝ) < 158/105 ∧ (158/105 : ℝ) < 28/18 ∧
      (26/18 : ℝ) < 79/53 ∧ (79/53 : ℝ) < 27/18) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hq0 := ne_of_gt hq
    dsimp [upperSE, widthSE]
    constructor
    · field_simp <;> norm_num <;> ring
    constructor
    · field_simp <;> norm_num <;> ring
    · field_simp <;> norm_num <;> ring
  · norm_num
  · norm_num [upperSE]
  · norm_num [upperSE, absoluteT]
  · norm_num [widthSE]
  · norm_num [widthSE, absoluteT]
  · norm_num
  · intro q hq
    have hq0 := ne_of_gt hq
    norm_num [absoluteT, upperSE, widthSE]
    constructor <;> field_simp <;> ring
  · norm_num

/-- T15(ii), corrected S4: exact difference between the width and upper rules. -/
theorem interval_rule_difference (β L U q : ℝ) (hq : q ≠ 0) :
    2*q*(widthSE L U q - upperSE β U q) = 2*β - (L+U) := by
  unfold widthSE upperSE
  field_simp
  <;> ring

/-- T15, the complete corrected interval-imputation formula (main p. 4,
supplement S4 pp. 9-10). The quantile choices and the normal-tail
p-value are definitions of a reconstruction, not claims of exact inference for
arbitrary reported confidence intervals. -/
theorem interval_rule_correction :
    (∀ α β L U : ℝ, L < U → 0 < normalQuantile (1-α/2) →
      let q := normalQuantile (1-α/2)
      widthSE L U q = (U-L)/(2*q) ∧
      absoluteT β (widthSE L U q) = |β|/widthSE L U q ∧
      reconstructedP β L U q = 2*normalCDF (-absoluteT β (widthSE L U q))) ∧
    normalQuantile (1-(1/10 : ℝ)/2) = normalQuantile (19/20) ∧
    normalQuantile (1-(1/20 : ℝ)/2) = normalCritical ∧
    (∀ β L U q : ℝ, L < U → 0 < q →
      2*q*(widthSE L U q - upperSE β U q) = 2*β-(L+U) ∧
      (widthSE L U q = upperSE β U q ↔ β = (L+U)/2) ∧
      (upperSE β U q < widthSE L U q ↔ (L+U)/2 < β) ∧
      (widthSE L U q < upperSE β U q ↔ β < (L+U)/2)) ∧
    (∀ β q s : ℝ, 0 < q → 0 < s →
      widthSE (β-q*s) (β+q*s) q = s ∧ upperSE β (β+q*s) q = s) ∧
    (∀ q : ℝ, 0 < q →
      widthSE (-213/1000) (-101/1000) q = 7/(125*q) ∧
      absoluteT (-3/20) (widthSE (-213/1000) (-101/1000) q) = 75*q/28) ∧
    (widthSE (-213/1000) (-101/1000) (49/25) = 1/35 ∧
      absoluteT (-3/20) (widthSE (-213/1000) (-101/1000) (49/25)) = 21/4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β L U hLU hq
    exact ⟨rfl, rfl, rfl⟩
  · congr 1 <;> norm_num
  · unfold normalCritical
    congr 1 <;> norm_num
  · intro β L U q hLU hq
    have hd := interval_rule_difference β L U q (ne_of_gt hq)
    refine ⟨hd, ?_, ?_, ?_⟩
    · constructor <;> intro h <;> nlinarith
    · constructor <;> intro h <;> nlinarith
    · constructor <;> intro h <;> nlinarith
  · intro β q s hq hs
    have hq0 := ne_of_gt hq
    unfold widthSE upperSE
    constructor <;> field_simp <;> ring
  · intro q hq
    have hq0 := ne_of_gt hq
    norm_num [widthSE, absoluteT]
    constructor <;> field_simp <;> ring
  · norm_num [widthSE, absoluteT]

/-! ## The diagnostic comparison (T1-T2) -/

/-- Model M1 (T1), illustrating main p. 3's continuity assumption:
the control conditional mean is 2+x. This model is not in the paper. -/
def m1Control (x : ℝ) : ℝ := 2+x

/-- Model M1's treated conditional mean 6+x (T1). -/
def m1Treated (x : ℝ) : ℝ := 6+x

/-- The eight fixed scores ±j/5, j=1,...,4, used for a regular conditional
Gaussian outcome law, not conditioning by division on a probability-zero event. -/
def m1Distance : Fin 4 → ℝ := ![1/5,2/5,3/5,4/5]


/-- Original local linear intercept weights a (T1(i)). -/
def m1Linear : Fin 4 → ℝ := ![6/5,3/10,-1/5,-3/10]

/-- Quadratic curvature coefficient weights c (T1(ii)). -/
def m1Curvature : Fin 4 → ℝ := ![50/7,-125/14,-25/7,75/14]

/-- Original intercept's second moment m=-21/125, estimated-bias multiplier
at h=b=1 (T1(ii)). -/
def m1BiasMoment : ℝ := -21/125

/-- Estimated-bias weights d=m c (T1(ii)). -/
def m1Bias (i : Fin 4) : ℝ := m1BiasMoment * m1Curvature i

/-- Bias-corrected intercept weights b=a-d (T1(ii)). -/
def m1Corrected (i : Fin 4) : ℝ := m1Linear i - m1Bias i

/-- A or B is a weighted right-minus-left intercept on the same eight outcomes.
Side index 0 is left and 1 is right; T1(iii). -/
def rdEstimator (w : Fin 4 → ℝ) (Y : (Fin 2 × Fin 4) → ℝ) : ℝ :=
  ∑ i, w i * (Y (1,i) - Y (0,i))


/-- Independent conditional outcomes at the eight scores in T1 and T2:
left mean μ₀(-u), right mean μ₁(u), unit variance one known. -/
def rdConditionalLaw (μ₁ μ₀ : ℝ → ℝ) : Measure ((Fin 2 × Fin 4) → ℝ) :=
  Measure.pi (fun si => gaussianReal
    (if si.1 = 0 then μ₀ (-m1Distance si.2) else μ₁ (m1Distance si.2)) 1)

/-- S_A=√83/5, the reported exact SD in Model M1 (T1(iv)). -/
def m1SELinear : ℝ := Real.sqrt 83 / 5

/-- S_B=√410/5, the reported exact SD in Model M1 (T1(iv)). -/
def m1SECorrected : ℝ := Real.sqrt 410 / 5

/-- Probability that a symmetric interval about an estimator contains its target;
main pp. 3-4's inference discussion, specialized to the explicit models. -/
def intervalCoverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℝ) (θ halfLength : ℝ) : ℝ :=
  μ.real {ω | θ ∈ Icc (T ω-halfLength) (T ω+halfLength)}

/-- The numerical realization of eight outcomes in T1(vi). -/
def m1Observed (si : Fin 2 × Fin 4) : ℝ :=
  if si.1 = 0 then ![19/10,3/2,8/5,1] si.2 else ![63/10,63/10,34/5,33/5] si.2


/-- M2's smooth polynomial perturbation q(x), T2(b). It vanishes
at every observed treated score but changes the cutoff mean by twenty. -/
def m2Perturbation (x : ℝ) : ℝ :=
  20*(1-5*x)*(1-(5/2)*x)*(1-(5/3)*x)*(1-(5/4)*x)

/-- Treated conditional mean 6+x+q(x) in M2; control mean and error law are M1's,
T2(b). -/
def m2Treated (x : ℝ) : ℝ := m1Treated x + m2Perturbation x


/-- T2(f), general square-integrable variance identity behind main pp. 4 and 8's
"added imprecision ... bias adjustment". No independence is assumed between the
estimate L and its estimated bias β̂. -/
theorem bias_adjustment_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L βhat : Ω → ℝ)
    (hL : MemLp L 2 μ) (hβ : MemLp βhat 2 μ) :
    variance (fun ω => L ω-βhat ω) μ = variance L μ + variance βhat μ -
      2*covariance L βhat μ := by
  rw [variance_fun_sub hL hβ]
  ring

/-- Independent studies, M2 on S and M1 elsewhere, conditional on the eight
scores for each study. Target T2(e); independence is represented by product
measures and S is an arbitrary subset of all N studies, not an empirical count. -/
def studyDataLaw (N : ℕ) (S : Finset (Fin N)) :
    Measure (Fin N → (Fin 2 × Fin 4) → ℝ) :=
  Measure.pi (fun j => if j ∈ S then rdConditionalLaw m2Treated m1Control
    else rdConditionalLaw m1Treated m1Control)

/-- The true study-specific cutoff effect is 24 in M2 and 4 in M1 (T2(e)). -/
def studyEffect {N : ℕ} (S : Finset (Fin N)) (j : Fin N) : ℝ := if j ∈ S then 24 else 4


/-! ## Clustered nearest-neighbour variance (T3-T4) -/

/-- Nearest-neighbour residual within a tied running-variable cell of m records,
T3/T4, as specified by rdrobust's default nnmatch=3. The paper (p. 7)
only says "default settings". When m≥4 all other records are the neighbours. -/
def nnResidual {m : ℕ} (y : Fin m → ℝ) (i : Fin m) : ℝ :=
  Real.sqrt (((m:ℝ)-1)/m) * (y i - ((∑ j, y j)-y i)/((m:ℝ)-1))

/-- Cluster-robust score variance f∑g score_g², T3/T4.
Finite-sample f cannot restore a cluster score erased by cell residualization. -/
def clusterScoreVariance {G : ℕ} (f : ℝ) (score : Fin G → ℝ) : ℝ :=
  f * ∑ g, score g ^ 2

/-- T4(i), exact cancellation of within-cell nearest-neighbour residuals for
arbitrary outcomes. The identity holds for m≥2; application to default
nnmatch=3 requires m≥4. -/
theorem nn_residual_sum {m : ℕ} (hm : 2 ≤ m) (y : Fin m → ℝ) :
    (∑ i, nnResidual y i) = 0 := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (m:ℝ)-1 ≠ 0 := by linarith
  unfold nnResidual
  rw [← Finset.mul_sum]
  have hz : (∑ i, (y i-((∑ j, y j)-y i)/((m:ℝ)-1))) = 0 := by
    simp only [div_eq_mul_inv, sub_mul, Finset.sum_sub_distrib,
      Finset.sum_const, ← Finset.sum_mul, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring
  rw [hz, mul_zero]

/-- A cluster g contains complete cells c with assignment owner c=g. Record
weights depend only on the cell's common running-variable value, so they are
constant within c. This models the nested-cell hypothesis in T4(ii). -/
def nestedClusterScore {C G : ℕ} (m : Fin C → ℕ) (owner : Fin C → Fin G)
    (ell : Fin C → ℝ) (y : (c : Fin C) → Fin (m c) → ℝ) (g : Fin G) : ℝ :=
  ∑ c, if owner c = g then ell c * ∑ i, nnResidual (y c) i else 0

/-- T4(ii), exact zero scores for nested cells of at least four records,
and hence a zero clustered variance for every outcome vector and every factor. -/
theorem nested_cells_zero_variance {C G : ℕ} (m : Fin C → ℕ)
    (hm : ∀ c, 4 ≤ m c) (owner : Fin C → Fin G) (ell : Fin C → ℝ)
    (y : (c : Fin C) → Fin (m c) → ℝ) (f : ℝ) :
    (∀ g, nestedClusterScore m owner ell y g = 0) ∧
    clusterScoreVariance f (nestedClusterScore m owner ell y) = 0 := by
  have hg : ∀ g, nestedClusterScore m owner ell y g = 0 := by
    intro g
    unfold nestedClusterScore
    apply Finset.sum_eq_zero
    intro c hc
    rw [nn_residual_sum (by have := hm c; omega)]
    simp
  exact ⟨hg, by simp [clusterScoreVariance, hg]⟩

/-- Independent uniform {-1,+1} shocks are functions on a uniform finite
Boolean cube. False maps to -1 and true to +1 (T3's 1024 outcomes). -/
def signShock (u : Bool) : ℝ := if u then 1 else -1


/-- Conventional right-minus-left cluster weights in T3(i). -/
def clusterLinear : Fin 10 → ℝ := ![1/5,1/5,0,-2/5,-1,1,2/5,0,-1/5,-1/5]

/-- Bias-corrected cluster weights in T3(ii), with h=b so the intercept is
that of the quadratic fit. -/
def clusterCorrected : Fin 10 → ℝ := ![-2/5,1/5,4/5,2/5,-2,2,-2/5,-4/5,-1/5,2/5]

/-- T3 estimator as a linear combination of the ten independent cluster signs. -/
def clusterEstimator (a : Fin 10 → ℝ) (ω : Fin 10 → Bool) : ℝ :=
  ∑ g, a g * signShock (ω g)

/-- Every record in cluster g has both potential outcomes equal to U_g;
T3's clustered sharp design has zero conditional means and zero RD effect. -/
def clusterOutcome (ω : Fin 10 → Bool) (g : Fin 10) (_i : Fin 5) : ℝ := signShock (ω g)

/-- Noisy extension Y_gi=U_g+e_gi of T3(v). The 60 coordinates are independent
uniform signs: ten cluster shocks and fifty independent record shocks. -/
def noisyClusterOutcome (ω : (Fin 10 ⊕ (Fin 10 × Fin 5)) → Bool)
    (g : Fin 10) (i : Fin 5) : ℝ := signShock (ω (.inl g)) + signShock (ω (.inr (g,i)))

/-- The cluster means in the noisy example, T3(v). -/
def noisyClusterMean (ω : (Fin 10 ⊕ (Fin 10 × Fin 5)) → Bool) (g : Fin 10) : ℝ :=
  (∑ i, noisyClusterOutcome ω g i)/5

/-- The noisy conventional/bias-corrected estimator ∑g a_g barY_g, T3(v). -/
def noisyClusterEstimator (a : Fin 10 → ℝ)
    (ω : (Fin 10 ⊕ (Fin 10 × Fin 5)) → Bool) : ℝ := ∑ g, a g * noisyClusterMean ω g

/-- Covariance under the same finite uniform law, for T3(v)'s I₅+11ᵀ. -/
def finiteCovariance {Ω : Type*} [Fintype Ω] (X Y : Ω → ℝ) : ℝ :=
  finiteMean (fun ω => (X ω-finiteMean X)*(Y ω-finiteMean Y))


/-- Shrinking-bandwidth design of T4(iii): n(n+1) clusters per
side, five records each, at ±j/[n(n+1)], h=b=1/n; local normalized distances
j/(n+1) and triangular weights for j=1,...,n. -/
def shrinkingDistance (n : ℕ) (j : Fin n) : ℝ := ((j:ℝ)+1)/((n:ℝ)+1)

/-- Local triangular weight in T4(iii)'s shrinking-bandwidth design. -/
def shrinkingKernel (n : ℕ) (j : Fin n) : ℝ := 1-shrinkingDistance n j

/-- Three kernel moments S₀,S₁,S₂ in T4(iii). -/
def shrinkingMoment (n power : ℕ) : ℝ :=
  ∑ j : Fin n, shrinkingKernel n j * shrinkingDistance n j ^ power

/-- Cluster intercept coefficient from the WLS moment inverse, T4(iii). -/
def shrinkingIntercept (n : ℕ) (j : Fin n) : ℝ :=
  shrinkingKernel n j * (shrinkingMoment n 2-shrinkingMoment n 1*shrinkingDistance n j) /
    (shrinkingMoment n 0*shrinkingMoment n 2-shrinkingMoment n 1^2)

/-- True conventional two-side variance V_n in the independent-sign model,
T4(iii). This definition is the sum of squared actual WLS weights. -/
def shrinkingVariance (n : ℕ) : ℝ := 2 * ∑ j : Fin n, shrinkingIntercept n j ^ 2

/-- Actual right-minus-left conventional estimator in T4(iii)'s active
shrinking-bandwidth design. The independent signs are uniform over the finite
Boolean cube; the omitted n(n+1)-n clusters per side have zero kernel weight. -/
def shrinkingEstimator (n : ℕ) (ω : (Fin 2 × Fin n) → Bool) : ℝ :=
  ∑ j, shrinkingIntercept n j*(signShock (ω (1,j))-signShock (ω (0,j)))

/-- T4(iii) with T3(v)'s record noise: five independent record shocks added
to each independent cluster shock, and the same WLS weights on cluster means. -/
def shrinkingNoisyEstimator (n : ℕ)
    (ω : ((Fin 2 × Fin n) ⊕ ((Fin 2 × Fin n) × Fin 5)) → Bool) : ℝ :=
  ∑ j, shrinkingIntercept n j *
    ((∑ i : Fin 5, (signShock (ω (.inl (1,j)))+signShock (ω (.inr ((1,j),i)))))/5 -
     (∑ i : Fin 5, (signShock (ω (.inl (0,j)))+signShock (ω (.inr ((0,j),i)))))/5)

/-- Corrected cluster-component estimator G/(G-1)∑ a_g²(Z_g-barZ)² in T4(iv).
It is a statement for independent cluster means, not a general RD sandwich theorem. -/
def clusterPlugin {G : ℕ} (a Z : Fin G → ℝ) : ℝ :=
  (G:ℝ)/((G:ℝ)-1) * ∑ g, a g^2 * (Z g-sampleMean Z)^2

/-- T4(v), exact one-study corrections conditional on the stored weights,
shares, and the repaired power being below 60%. This is not a full regenerated
table or an independent proof of the benchmark power. -/
theorem clustered_table_arithmetic :
    ((1/6 : ℝ)-1/36 = 5/36) ∧ ((11/72 : ℝ)-1/36 = 1/8) ∧
    ((5/48 : ℝ)-1/36 = 11/144) ∧ ((1/13 : ℝ)-1/26 = 1/26) ∧
    ((1/26 : ℝ)-1/26 = 0) := by
  norm_num

/-! ## Individual outcomes versus cell counts (T5-T6) -/

/-- Wald ratio of the outcome and treatment discontinuities, the fuzzy-RD
estimand read from the reanalysis of Coppock-Green (T5; main p. 9 defines
Cohen's d but does not print a Wald formula). -/
def waldRatio (yE yI dE dI : ℝ) : ℝ := (yE-yI)/(dE-dI)

/-- Explicit binary individuals in the T5 construction: k of n records are ones.
The population law on two cell types is uniform and each cell has 100 people. -/
def binaryIndicator {n : ℕ} (k : ℕ) (i : Fin n) : ℝ := if i.val < k then 1 else 0

/-- Eligible cells' untreated future-voter counts 5 and 45 (T5).
The first 50 individuals are compliers; the next five untreated nonvoters in
this ordering are induced by treatment, yielding observed counts 10 and 50. -/
def eligibleBaseline : Fin 2 → ℕ := ![5,45]

/-- Ineligible cells' observed future-voter counts 10 and 40 (T5). -/
def ineligibleBaseline : Fin 2 → ℕ := ![10,40]

/-- Individual potential outcomes in T5's fuzzy example. The first 50 people
comply with eligibility, treatment moves exactly five of them from 0 to 1.
Treatment is monotone and the untreated side averages agree at 1/4. -/
def countToyPotential (eligible treated : Bool) (cell : Fin 2) (i : Fin 100) : ℝ :=
  binaryIndicator ((if eligible then eligibleBaseline cell else ineligibleBaseline cell) +
    (if treated then 5 else 0)) i

/-- Observed treatment in the fuzzy count toy: 50 on the eligible side and
zero on the ineligible side, T5. -/
def countToyTreatment (eligible : Bool) (i : Fin 100) : ℝ :=
  if eligible then binaryIndicator 50 i else 0

/-- The observed individual outcomes under the treatment assignment, T5.
This makes the binary potential-outcome construction explicit. -/
def countToyObserved (eligible : Bool) (cell : Fin 2) (i : Fin 100) : ℝ :=
  if countToyTreatment eligible i = 1 then countToyPotential eligible true cell i
  else countToyPotential eligible false cell i

/-- Bernoulli population variance p(1-p), p. 9 corrected standardization (T6).
This formula is also used for the untreated population in T5. -/
def binaryPopulationVariance (p : ℝ) : ℝ := p*(1-p)

/-- Count of the explicit k-one binary sample, computed by a cardinality lemma
rather than enumerating hundreds of individuals (support for T5/T6/T11). -/
theorem sum_binary_indicator {n : ℕ} (k : ℕ) :
    (∑ i : Fin n, binaryIndicator k i) = (min n k : ℝ) := by
  classical
  unfold binaryIndicator
  rw [← Finset.sum_filter]
  simp [Fin.card_filter_val_lt]

/-- Scaling every count scales the sample variance by scale², T5(v). -/
theorem sample_variance_scale {n : ℕ} (y : Fin n → ℝ) (scale : ℝ) :
    sampleVariance (fun i => scale*y i) = scale^2*sampleVariance y := by
  have hm : sampleMean (fun i => scale*y i) = scale*sampleMean y := by
    simp only [sampleMean, ← Finset.mul_sum]
    ring
  unfold sampleVariance
  rw [hm]
  have hs : (∑ i, (scale*y i-scale*sampleMean y)^2) = scale^2*∑ i, (y i-sampleMean y)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hs]
  ring

/-- Scaling counts by positive scale scales their sample SD by scale, T5(v). -/
theorem sample_sd_scale {n : ℕ} (hn : 2 ≤ n) (y : Fin n → ℝ) (scale : ℝ) (hscale : 0 < scale) :
    sampleSD (fun i => scale*y i) = scale*sampleSD y := by
  unfold sampleSD
  rw [sample_variance_scale, Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq_eq_abs,
    abs_of_pos hscale]

/-- T5(v): multiplying outcome and treatment counts by one positive scale leaves
the Wald effect unchanged and multiplies the count-standardized effect by 1/scale. -/
theorem wald_count_scale (yE yI dE dI sd scale : ℝ) (hscale : 0 < scale) :
    waldRatio (scale*yE) (scale*yI) (scale*dE) (scale*dI) = waldRatio yE yI dE dI ∧
    waldRatio (scale*yE) (scale*yI) (scale*dE) (scale*dI)/(scale*sd) =
      (waldRatio yE yI dE dI/sd)/scale := by
  have hscale0 := ne_of_gt hscale
  have hw : waldRatio (scale*yE) (scale*yI) (scale*dE) (scale*dI) = waldRatio yE yI dE dI := by
    unfold waldRatio
    rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ hscale0]
  refine ⟨hw, ?_⟩
  rw [hw]
  simp [div_div, mul_comm]

/-- T5 complete count-standardization counterexample using a toy model.
Explicit binary individual potentials, monotone compliance, actual observed
counts, both count variances, doubling and arbitrary positive scaling are
included. Squared Cohen d avoids unnecessary square-root arithmetic while
specifying the same nonnegative standardized effect. -/
theorem count_standardization_counterexample :
    (∀ eligible treated cell i,
      countToyPotential eligible treated cell i = 0 ∨ countToyPotential eligible treated cell i = 1) ∧
    (∀ eligible i, countToyTreatment eligible i = 0 ∨ countToyTreatment eligible i = 1) ∧
    (∀ i, countToyTreatment false i ≤ countToyTreatment true i) ∧
    (∑ i, countToyTreatment true i) = 50 ∧ (∑ i, countToyTreatment false i) = 0 ∧
    (∀ cell, (∑ i, countToyPotential true false cell i) = (eligibleBaseline cell:ℝ) ∧
      (∑ i, (countToyPotential true true cell i - countToyPotential true false cell i)) = 5) ∧
    (∀ cell, (∑ i, countToyObserved true cell i) = ![(10:ℝ),50] cell ∧
      (∑ i, countToyObserved false cell i) = ![(10:ℝ),40] cell) ∧
    ((5+45 : ℝ)/200 = (10+40)/200) ∧
    waldRatio 30 25 50 0 = 1/10 ∧
    ((10+40 : ℝ)/200 = 1/4) ∧ binaryPopulationVariance (1/4) = 3/16 ∧
    ((1/10 : ℝ)^2/binaryPopulationVariance (1/4) = 4/75) ∧
    sampleVariance ![(10:ℝ),50] = 800 ∧ sampleVariance ![(10:ℝ),40] = 450 ∧
    ((1/10 : ℝ)^2/sampleVariance ![(10:ℝ),50] = 1/80000) ∧
    ((1/80000 : ℝ) ≠ 4/75) ∧
    waldRatio 60 50 100 0 = 1/10 ∧ ((20+80 : ℝ)/400 = 1/4) ∧
    sampleVariance ![(20:ℝ),100] = 3200 ∧
    ((1/10 : ℝ)^2/sampleVariance ![(20:ℝ),100] = 1/320000) ∧
    ((1/320000 : ℝ) = (1/80000)/4) ∧
    (∀ yE yI dE dI sd scale : ℝ, 0 < scale →
      waldRatio (scale*yE) (scale*yI) (scale*dE) (scale*dI) = waldRatio yE yI dE dI ∧
      waldRatio (scale*yE) (scale*yI) (scale*dE) (scale*dI)/(scale*sd) = (waldRatio yE yI dE dI/sd)/scale) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ y : Fin n → ℝ, ∀ scale : ℝ, 0 < scale →
      sampleSD (fun i => scale*y i) = scale*sampleSD y) := by
  have hp : ∀ eligible treated cell i,
      countToyPotential eligible treated cell i = 0 ∨ countToyPotential eligible treated cell i = 1 := by
    intro eligible treated cell i
    unfold countToyPotential binaryIndicator
    split_ifs <;> simp
  have ht : ∀ eligible i, countToyTreatment eligible i = 0 ∨ countToyTreatment eligible i = 1 := by
    intro eligible i
    cases eligible
    · exact Or.inl rfl
    · unfold countToyTreatment binaryIndicator
      split_ifs <;> simp
  have hm : ∀ i, countToyTreatment false i ≤ countToyTreatment true i := by
    intro i; simp [countToyTreatment, binaryIndicator]; split_ifs <;> norm_num
  have hobs : ∀ cell, (∑ i, countToyObserved true cell i) = ![(10:ℝ),50] cell ∧
      (∑ i, countToyObserved false cell i) = ![(10:ℝ),40] cell := by
    intro cell
    have he : countToyObserved true cell = binaryIndicator (eligibleBaseline cell+5) := by
      funext i
      fin_cases cell
      · by_cases h50 : i.val < 50
        · simp [countToyObserved, countToyTreatment, countToyPotential, eligibleBaseline, binaryIndicator, h50] <;> rfl
        · have h10 : ¬ i.val < 10 := by omega
          have h5 : ¬ i.val < 5 := by omega
          simp [countToyObserved, countToyTreatment, countToyPotential, eligibleBaseline, binaryIndicator, h50, h10, h5]
      · by_cases h50 : i.val < 50
        · simp [countToyObserved, countToyTreatment, countToyPotential, eligibleBaseline, binaryIndicator, h50] <;> rfl
        · have h45 : ¬ i.val < 45 := by omega
          simp [countToyObserved, countToyTreatment, countToyPotential, eligibleBaseline, binaryIndicator, h50, h45]
    have hi : countToyObserved false cell = binaryIndicator (ineligibleBaseline cell) := by
      funext i
      simp [countToyObserved,countToyTreatment,countToyPotential]
    rw [he,hi,sum_binary_indicator,sum_binary_indicator]
    fin_cases cell <;> norm_num [eligibleBaseline,ineligibleBaseline]
  refine ⟨hp, ht, hm, ?_, ?_, ?_, hobs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, wald_count_scale, ?_⟩
  · norm_num [countToyTreatment, sum_binary_indicator]
  · simp [countToyTreatment]
  · intro cell
    change (∑ i : Fin 100, binaryIndicator (eligibleBaseline cell) i) = (eligibleBaseline cell:ℝ) ∧
      (∑ i : Fin 100, (binaryIndicator (eligibleBaseline cell+5) i - binaryIndicator (eligibleBaseline cell) i)) = 5
    rw [Finset.sum_sub_distrib]
    simp only [sum_binary_indicator]
    fin_cases cell <;> norm_num [eligibleBaseline]
  all_goals norm_num [waldRatio,binaryPopulationVariance,sampleVariance,sampleMean,Fin.sum_univ_succ]
  intro n hn y scale hscale
  exact sample_sd_scale hn y scale hscale

/-- T6(i) exact population Bernoulli bound; this is a finite algebra lemma,
not the complete corrected power statement. -/
theorem binary_variance_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryPopulationVariance p = 1/4-(p-1/2)^2 ∧
    0 ≤ binaryPopulationVariance p ∧ binaryPopulationVariance p ≤ 1/4 ∧
    Real.sqrt (binaryPopulationVariance p) ≤ 1/2 := by
  have hv0 : 0 ≤ binaryPopulationVariance p := mul_nonneg hp0 (by linarith)
  have hid : binaryPopulationVariance p = 1/4-(p-1/2)^2 := by unfold binaryPopulationVariance; ring
  refine ⟨hid,hv0,by rw [hid]; nlinarith [sq_nonneg (p-1/2)], ?_⟩
  have hs := Real.sq_sqrt hv0
  have hs0 := Real.sqrt_nonneg (binaryPopulationVariance p)
  nlinarith [sq_nonneg (p-1/2)]

/-- Stored robust SE for Coppock-Green, a deposited-results premise in T6(iii),
not a number inferred by Lean from the paper or dataset. -/
def binaryStudySE : ℝ := 154987506828555/10^16

/-- T6(iv), one-row exact weighted-share correction, conditional on the stored
weight and indicator change; it does not determine the 60%/80% classifications. -/
theorem binary_table_arithmetic :
    (((15/4 : ℝ)/36 = 5/48) ∧ ((11/4 : ℝ)/10 = 11/40)) ∧
    (((15/4 : ℝ)-1)/36 = 11/144) ∧ (((11/4 : ℝ)-1)/10 = 7/40) := by norm_num


/-! ## Caliper null and correction (T7-T8) -/

/-- Printed caliper cutoff 1.96, main p. 5, Table 1; the replication uses the
unrounded normal quantile, whose distinction is retained in other targets. -/
def caliperCutoff : ℝ := 49/25

/-- A_h=∫c^(c+h) f, target notation for the finite calipers on main p. 5. -/
def caliperAbove (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  ∫ x in caliperCutoff..caliperCutoff+h, f x

/-- B_h=∫(c-h)^c f, target notation for main p. 5. -/
def caliperBelow (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  ∫ x in caliperCutoff-h..caliperCutoff, f x

/-- Conditional chance of being above the threshold in the caliper,
p_h=A_h/(A_h+B_h), a mathematical interpretation of main p. 5. -/
def caliperProbability (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  caliperAbove f h/(caliperAbove f h+caliperBelow f h)

/-- "A binomial distribution with equal success probability", "one-tailed"
(main p. 5): G_n,k(p) is its upper tail, notation used here. -/
def binomialTail (n k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc k n, (n.choose j:ℝ)*p^j*(1-p)^(n-j)

/-- Actual probability measure for independent absolute t-statistics having a
density f and all being published; T7/T8. Positivity/normalization of f are
explicit hypotheses, rather than assumed equal side masses. -/
def caliperDataLaw (M : ℕ) (f : ℝ → ℝ) : Measure (Fin M → ℝ) :=
  Measure.pi (fun _ => volume.withDensity (fun x => ENNReal.ofReal (f x)))

/-- Number N of studies in the caliper window, main p. 5 test. -/
def caliperCount {M : ℕ} (h : ℝ) (X : Fin M → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => X i ∈ Icc (caliperCutoff-h) (caliperCutoff+h))).card

/-- Number K of studies at or above c inside the caliper; boundaries are
null events under a density, T8(i). -/
def caliperSuccesses {M : ℕ} (h : ℝ) (X : Fin M → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => X i ∈ Icc caliperCutoff (caliperCutoff+h))).card

/-- T7(i)'s selection-free density x/8 on [0,4], zero elsewhere.
This is not an estimate of the distribution of the 45 surveyed studies. -/
def linearCaliperDensity (x : ℝ) : ℝ := if x ∈ Icc 0 4 then x/8 else 0

/-- Smooth-on-the-window density f_m=(m+1)x^m/4^(m+1) on [0,4], T7(iv).
The truncation endpoints are outside all the calipers. -/
def powerCaliperDensity (m : ℕ) (x : ℝ) : ℝ :=
  if x ∈ Icc 0 4 then ((m:ℝ)+1)*x^m/4^(m+1) else 0

/-- CDF of |N(θ,1)| for x≥0, T7(v). This is defined with the actual Gaussian
CDF and not an abstract distribution supplied with its desired properties. -/
def foldedNormalCDF (θ x : ℝ) : ℝ := normalCDF (x-θ)-normalCDF (-x-θ)

/-- Folded-normal caliper probability calculated from the CDF, T7(v). -/
def foldedCaliperProbability (θ h : ℝ) : ℝ :=
  (foldedNormalCDF θ (caliperCutoff+h)-foldedNormalCDF θ caliperCutoff) /
  (foldedNormalCDF θ (caliperCutoff+h)-foldedNormalCDF θ (caliperCutoff-h))

/-- T7(ii)-(iii)/T8(vi), exact binomial arithmetic of Table 1 and the linear-density
witness. This does not assert that the equal-mass benchmark follows from
publication independence or that the corrected tails fit the historical data. -/
theorem caliper_exact_tails :
    binomialTail 12 9 (1/2) = 299/4096 ∧
    binomialTail 12 9 (21/40) = 336637329302285487/3355443200000000000 ∧
    binomialTail 15 11 (1/2) = 1941/32768 ∧
    binomialTail 15 11 (43/80) = 3589476431322242287677900507/35184372088832000000000000000 ∧
    binomialTail 19 14 (1/2) = 2083/65536 ∧
    binomialTail 19 14 (11/20) = 50930691593528557166389/655360000000000000000000 ∧
    binomialTail 19 13 (1/2) = 10949/131072 ∧
    (1/20:ℝ) < binomialTail 19 13 (1/2) ∧
    binomialTail 19 14 (1/2) < (1/20:ℝ) ∧
    (1/20:ℝ) < binomialTail 19 14 (11/20) := by
  have h9 : Finset.Icc 9 12 = {9,10,11,12} := by decide
  have h11 : Finset.Icc 11 15 = {11,12,13,14,15} := by decide
  have h14 : Finset.Icc 14 19 = {14,15,16,17,18,19} := by decide
  have h13 : Finset.Icc 13 19 = {13,14,15,16,17,18,19} := by decide
  norm_num [binomialTail,h9,h11,h14,h13,Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

/-- T8(ii), exact equal-mass criterion, with positive window probability.
Absence of publication selection is not used as a substitute for this condition. -/
theorem equal_caliper_mass_iff (A B : ℝ) (hAB : 0 < A+B) :
    A/(A+B) = 1/2 ↔ A = B := by
  rw [div_eq_iff (ne_of_gt hAB)]
  constructor <;> intro h <;> linarith


/-! ## Saved normal powers (T9) -/

/-- ρ=G/(G_L+G_R), with finite sets of distinct cluster labels on both sides.
Target T9(iii), interpreting saved powers; no formula is printed on p. 9. -/
def clusterCountRatio {α : Type*} [DecidableEq α] (L R : Finset α) : ℝ :=
  ((L ∪ R).card:ℝ)/((L.card:ℝ)+(R.card:ℝ))

/-- T9(iii), exact union/overlap identity and the ratio bounds. Labels that
appear on both sides are counted once in the union; the nonempty hypotheses
are those of the target. -/
theorem cluster_count_ratio {α : Type*} [DecidableEq α] (L R : Finset α)
    (hL : L.Nonempty) (hR : R.Nonempty) :
    L.card+R.card = (L ∪ R).card+(L ∩ R).card ∧
    1/2 ≤ clusterCountRatio L R ∧ clusterCountRatio L R ≤ 1 ∧
    (clusterCountRatio L R < 1 ↔ L ∩ R ≠ ∅) := by
  have he := Finset.card_union_add_card_inter L R
  have heR : ((L ∪ R).card:ℝ)+((L ∩ R).card:ℝ) = (L.card:ℝ)+(R.card:ℝ) := by
    exact_mod_cast he
  have hI : ((L ∩ R).card:ℝ) ≤ ((L ∪ R).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card (show L ∩ R ⊆ L ∪ R from
      fun x hx => Finset.mem_union_left _ (Finset.mem_inter.mp hx).1))
  have hLn : 0 < (L.card:ℝ) := by exact_mod_cast hL.card_pos
  have hRn : 0 < (R.card:ℝ) := by exact_mod_cast hR.card_pos
  have hd : 0 < (L.card:ℝ)+(R.card:ℝ) := by linarith
  have hI0 : 0 ≤ ((L ∩ R).card:ℝ) := by positivity
  unfold clusterCountRatio
  refine ⟨he.symm, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd]; linarith
  · rw [div_lt_iff₀ hd]
    constructor
    · intro h hzero
      simp [hzero] at heR
      linarith
    · intro h
      have hic : 0 < (L ∩ R).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)
      have hicR : 0 < ((L ∩ R).card:ℝ) := by exact_mod_cast hic
      linarith

/-- T9(iv)-(v) exact four-study ratios, overlaps and six one-row changes.
These deposited-data counts and stored-share premises do not identify the
unknown package source or certify the native fitted variances. -/
theorem native_power_arithmetic :
    ((23+46 : ℕ) = 57+12 ∧ (98+101 : ℕ) = 185+14 ∧
      (202+226 : ℕ) = 278+150 ∧ (133+130 : ℕ) = 204+59) ∧
    ((57/(23+46):ℝ) = 19/23 ∧ (185/(98+101):ℝ) = 185/199 ∧
      (278/(202+226):ℝ) = 139/214 ∧ (204/(133+130):ℝ) = 204/263) ∧
    ((19/23:ℝ) < 1 ∧ (185/199:ℝ) < 1 ∧ (139/214:ℝ) < 1 ∧ (204/263:ℝ) < 1) ∧
    ((31/48:ℝ)-1/36 = 89/144 ∧ (113/144:ℝ)-1/36 = 109/144 ∧
      (61/104:ℝ)-1/26 = 57/104 ∧ (81/104:ℝ)-1/26 = 77/104) := by norm_num


/-! ## Interval-based pseudo p-values (T12-T13) -/

/-- "Pseudo t-statistics based on the width of the confidence intervals"
(main p. 8, supplement S9 p. 16). The normal-tail transform
p_star is specified by the replication code (Figure S9; T12/T13). -/
def pseudoP (estimate halfLength : ℝ) : ℝ :=
  2*normalCDF (-normalCritical*|estimate|/halfLength)

/-- Fixed-variance, fixed-bias-bound model T=θ+b+Z, Z~N(0,1).
This is not a claim about the paper's data-estimated smoothness bound. -/
def biasModelLaw (θ b : ℝ) : Measure ℝ := gaussianReal (θ+b) 1

/-- Coverage C_b(H) of a centered interval in the unit-variance Gaussian bias
model, T12/T13. -/
def biasCoverage (b H : ℝ) : ℝ := normalCDF (H-b)-normalCDF (-H-b)

/-- Worst-case 95% half-length H for known bound B≥0 in T12/T13: infimum of
nonnegative half-lengths with C_B(H)≥19/20. Existence, positivity, the equality
and uniqueness are part of the stated targets, not assumed axioms. -/
def honestHalfLength (B : ℝ) : ℝ := sInf {H : ℝ | 0 ≤ H ∧ 19/20 ≤ biasCoverage B H}

/-- "A valid p-value" in target notation: superuniformity for every null law
N(b,1), |b|≤B, and every α∈(0,1). This definition does not equate a decision at
one α with validity at all levels. -/
def ValidBiasP (B : ℝ) (P : ℝ → ℝ) : Prop :=
  ∀ b : ℝ, |b| ≤ B → ∀ α : ℝ, 0 < α → α < 1 →
    (biasModelLaw 0 b).real {t | P t ≤ α} ≤ α

/-- Valid worst-case null-tail p_B(t)=Φ(B-|t|)+Φ(-B-|t|), T13(v).
Known variance is one and B is fixed, not estimated. -/
def biasAwareP (B t : ℝ) : ℝ := normalCDF (B-|t|)+normalCDF (-B-|t|)

/-- T13(i), supporting interval geometry: the symmetric closed interval
includes zero exactly when |estimate|≤halfLength. -/
theorem zero_in_interval (t h : ℝ) :
    (0 ∈ Icc (t-h) (t+h) ↔ |t| ≤ h) := by
  simp only [mem_Icc, abs_le]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith


/-! ## Additional finite probability proofs for T1–T6 -/

/-- T2(b): M1 and M2 have exactly the same regular conditional outcome law at
the eight stipulated scores. This is an equality of actual product Gaussian
measures, rather than an assumed premise or an equality of full population laws. -/
theorem m2_conditional_law_eq :
    rdConditionalLaw m2Treated m1Control = rdConditionalLaw m1Treated m1Control := by
  unfold rdConditionalLaw
  congr 1
  funext si
  rcases si with ⟨side,i⟩
  dsimp only
  split_ifs
  · rfl
  · have hm : m2Treated (m1Distance i) = m1Treated (m1Distance i) := by
      fin_cases i <;> norm_num [m2Treated,m1Treated,m1Distance,m2Perturbation]
    rw [hm]

/-- T2(e): for every N and S the same product conditional law results, so every
measurable statistic of all studies has the same distribution. This does not
yet establish the coverage classification or impossibility-of-counting clause. -/
theorem study_laws_identical (N : ℕ) (S : Finset (Fin N)) :
    studyDataLaw N S = studyDataLaw N ∅ ∧
    (∀ (E : Type*) [MeasurableSpace E] (F : (Fin N → (Fin 2 × Fin 4) → ℝ) → E),
      Measurable F → (studyDataLaw N S).map F = (studyDataLaw N ∅).map F) := by
  have h : studyDataLaw N S = studyDataLaw N ∅ := by
    simp [studyDataLaw,m2_conditional_law_eq]
  exact ⟨h,by intro E mE F hF; rw [h]⟩

/-- Uniform finite expectation commutes with a finite sum, as used in T3's
design-based independent-sign model. No measure approximation is involved. -/
theorem finite_mean_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι] (Y : ι → Ω → ℝ) :
    finiteMean (fun ω => ∑ i, Y i ω) = ∑ i, finiteMean (Y i) := by
  unfold finiteMean
  rw [Finset.sum_comm,Finset.sum_div]

/-- Uniform finite expectation is linear in a constant multiplier, T3. -/
theorem finite_mean_mul {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ) (a : ℝ) :
    finiteMean (fun ω => a*Y ω) = a*finiteMean Y := by
  unfold finiteMean
  rw [← Finset.mul_sum]
  ring

/-- One-coordinate sign flip on the independent Boolean cube, a bijection
used to prove T3's moments without enumerating 1024 or 2^60 assignments. -/
def flipSign {ι : Type*} [DecidableEq ι] (i : ι) (ω : ι → Bool) : ι → Bool :=
  Function.update ω i (!(ω i))

/-- Applying the one-coordinate flip twice gives the original assignment. -/
theorem flip_sign_involution {ι : Type*} [DecidableEq ι] (i : ι) :
    Function.Involutive (flipSign i) := by
  intro ω
  funext j
  by_cases h : j=i
  · subst j; simp [flipSign]
  · simp [flipSign,Function.update_of_ne h]

/-- Negating a Boolean sign negates its ±1 real value. -/
theorem sign_shock_not (u : Bool) : signShock (!u) = -signShock u := by
  cases u <;> norm_num [signShock]

/-- The uniform sum of a coordinate sign is zero by a sign-flip bijection,
T3's independent-cluster mean calculation. -/
theorem sum_sign_shock_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    (∑ ω : ι → Bool, signShock (ω i)) = 0 := by
  let e : (ι → Bool) ≃ (ι → Bool) := (flip_sign_involution i).toPerm (flipSign i)
  have h : (∑ ω : ι → Bool, signShock (ω i)) =
      ∑ ω : ι → Bool, -signShock (ω i) := by
    apply Fintype.sum_equiv e
    intro ω
    change signShock (ω i) = -signShock ((flipSign i ω) i)
    simp [flipSign,sign_shock_not]
  rw [Finset.sum_neg_distrib] at h
  linarith

/-- Uniform sign-product moments are one on the diagonal and zero off it.
This is the independence/variance-one calculation needed for T3. -/
theorem finite_sign_product {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    finiteMean (fun ω : ι → Bool => signShock (ω i)*signShock (ω j)) =
      if i=j then 1 else 0 := by
  classical
  have hcard : (Fintype.card (ι → Bool):ℝ) ≠ 0 := by positivity
  by_cases hij : i=j
  · subst j
    have hs : ∀ ω : ι → Bool, signShock (ω i)*signShock (ω i) = 1 := by
      intro ω; cases ω i <;> norm_num [signShock]
    simp [finiteMean,hs,hcard]
  · simp only [hij,ite_false]
    let e : (ι → Bool) ≃ (ι → Bool) := (flip_sign_involution i).toPerm (flipSign i)
    have h : (∑ ω : ι → Bool, signShock (ω i)*signShock (ω j)) =
        ∑ ω : ι → Bool, -(signShock (ω i)*signShock (ω j)) := by
      apply Fintype.sum_equiv e
      intro ω
      change signShock (ω i)*signShock (ω j) =
        -(signShock ((flipSign i ω) i)*signShock ((flipSign i ω) j))
      simp [flipSign,Function.update_of_ne (Ne.symm hij),sign_shock_not]
    rw [Finset.sum_neg_distrib] at h
    have hz : (∑ ω : ι → Bool, signShock (ω i)*signShock (ω j)) = 0 := by linarith
    simp [finiteMean,hz]

/-- General exact variance of a linear combination of independent uniform
signs. This proves the sampling variance under the actual finite probability
law, rather than defining variance to be a sum of squares (support for T3). -/
theorem weighted_sign_moments {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    finiteMean (fun ω : ι → Bool => ∑ i, a i*signShock (ω i)) = 0 ∧
    finiteVariance (fun ω : ι → Bool => ∑ i, a i*signShock (ω i)) = ∑ i, a i^2 := by
  classical
  have hm : finiteMean (fun ω : ι → Bool => ∑ i, a i*signShock (ω i)) = 0 := by
    rw [finite_mean_sum]
    simp_rw [finite_mean_mul]
    simp [finiteMean,sum_sign_shock_zero]
  refine ⟨hm, ?_⟩
  unfold finiteVariance
  rw [hm]
  simp only [sub_zero]
  have hexp : ∀ ω : ι → Bool, (∑ i, a i*signShock (ω i))^2 =
      ∑ i, ∑ j, (a i*a j)*(signShock (ω i)*signShock (ω j)) := by
    intro ω
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hexp]
  rw [finite_mean_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finite_mean_sum]
  simp_rw [finite_mean_mul,finite_sign_product]
  simp [pow_two]

/-- T3(i)-(iii), the exact core counterexample: under independent uniform
cluster signs, both actual variances are positive, but both reported clustered
NN variances are identically zero. -/
theorem clustered_zero_vs_positive :
    finiteMean (clusterEstimator clusterLinear) = 0 ∧
    finiteMean (clusterEstimator clusterCorrected) = 0 ∧
    finiteVariance (clusterEstimator clusterLinear) = 62/25 ∧
    finiteVariance (clusterEstimator clusterCorrected) = 10 ∧
    (∀ f : ℝ, ∀ y : Fin 10 → Fin 5 → ℝ,
      clusterScoreVariance f (fun g => (clusterLinear g/5)*∑ i, nnResidual (y g) i) = 0 ∧
      clusterScoreVariance f (fun g => (clusterCorrected g/5)*∑ i, nnResidual (y g) i) = 0) := by
  have hA := weighted_sign_moments clusterLinear
  have hB := weighted_sign_moments clusterCorrected
  refine ⟨hA.1,hB.1,?_,?_,?_⟩
  · exact hA.2.trans (by norm_num [clusterLinear,Fin.sum_univ_succ])
  · exact hB.2.trans (by norm_num [clusterCorrected,Fin.sum_univ_succ])
  · intro f y
    simp [clusterScoreVariance,nn_residual_sum (by norm_num : 2 ≤ 5)]

/-- T4(i), normalization identity for each cell residual, with m≥2.
Together with nn_residual_sum this proves the complete cancellation identity. -/
theorem nn_residual_centered {m : ℕ} (hm : 2 ≤ m) (y : Fin m → ℝ) (i : Fin m) :
    nnResidual y i = Real.sqrt ((m:ℝ)/((m:ℝ)-1)) *
      (y i-(∑ j, y j)/(m:ℝ)) := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m:ℝ) ≠ 0 := by linarith
  have hm1 : (m:ℝ)-1 ≠ 0 := by linarith
  have hmp : 0 < (m:ℝ) := by linarith
  have hm1p : 0 < (m:ℝ)-1 := by linarith
  have hp : 0 ≤ ((m:ℝ)-1)/(m:ℝ) := div_nonneg (le_of_lt hm1p) (le_of_lt hmp)
  have hq : 0 ≤ (m:ℝ)/((m:ℝ)-1) := div_nonneg (le_of_lt hmp) (le_of_lt hm1p)
  have hs : (Real.sqrt (((m:ℝ)-1)/(m:ℝ))*(m:ℝ)/((m:ℝ)-1))^2 =
      (Real.sqrt ((m:ℝ)/((m:ℝ)-1)))^2 := by
    calc
      _ = (Real.sqrt (((m:ℝ)-1)/(m:ℝ)))^2*(m:ℝ)^2/((m:ℝ)-1)^2 := by rw [div_pow,mul_pow]
      _ = (m:ℝ)/((m:ℝ)-1) := by
        rw [Real.sq_sqrt hp]
        field_simp
        <;> ring
      _ = _ := (Real.sq_sqrt hq).symm
  have hc : Real.sqrt (((m:ℝ)-1)/(m:ℝ))*(m:ℝ)/((m:ℝ)-1) =
      Real.sqrt ((m:ℝ)/((m:ℝ)-1)) :=
    (sq_eq_sq₀ (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hmp)) (le_of_lt hm1p)) (Real.sqrt_nonneg _)).mp hs
  unfold nnResidual
  rw [← hc]
  field_simp
  <;> ring

/-- T4(iii) finite power-sum certificate for the shrinking-bandwidth derivation.
These all-n identities are proved inductively, not checked on a finite range. -/
theorem finite_power_sums (n : ℕ) :
    (∑ j ∈ Finset.range n, (j:ℝ)) = (n:ℝ)*((n:ℝ)-1)/2 ∧
    (∑ j ∈ Finset.range n, (j:ℝ)^2) = (n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)/6 ∧
    (∑ j ∈ Finset.range n, (j:ℝ)^3) = (n:ℝ)^2*((n:ℝ)-1)^2/4 ∧
    (∑ j ∈ Finset.range n, (j:ℝ)^4) =
      (n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)*(3*(n:ℝ)^2-3*(n:ℝ)-1)/30 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rcases ih with ⟨h1,h2,h3,h4⟩
    rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]
    rw [h1,h2,h3,h4]
    simp only [Nat.cast_add,Nat.cast_one]
    repeat' constructor <;> ring <;> trivial

/-- T1(iii)-(iv), a general finite product-Gaussian moment lemma. Independence
is represented by the product measure; every coordinate has known variance one.
This supplies actual probability moments rather than only sums of coefficients. -/
theorem gaussian_product_moments {ι : Type*} [Fintype ι] (mean w : ι → ℝ) :
    (∫ Y, (∑ i, w i * Y i) ∂Measure.pi (fun i => gaussianReal (mean i) 1)) =
      ∑ i, w i * mean i ∧
    variance (fun Y => ∑ i, w i * Y i)
      (Measure.pi (fun i => gaussianReal (mean i) 1)) = ∑ i, w i^2 := by
  classical
  have hlp : ∀ i, MemLp (fun y : ℝ => w i*y) 2 (gaussianReal (mean i) 1) := by
    intro i
    exact (memLp_id_gaussianReal (μ := mean i) (v := 1) 2).const_mul (w i)
  constructor
  · rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_comp_eval (hlp i).aestronglyMeasurable, integral_const_mul]
      simp only [integral_id_gaussianReal]
    · intro i hi
      exact integrable_comp_eval (MemLp.integrable (by norm_num : (1:ENNReal) ≤ 2) (hlp i))
  · have hv := variance_sum_pi (μ := fun i : ι => gaussianReal (mean i) 1)
      (X := fun i (y : ℝ) => w i*y) hlp
    have hv' : variance (fun Y : ι → ℝ => ∑ i, w i*Y i)
        (Measure.pi (fun i => gaussianReal (mean i) 1)) =
        ∑ i, variance (fun y : ℝ => w i*y) (gaussianReal (mean i) 1) := by
      simpa only [Finset.sum_fn] using hv
    rw [hv']
    apply Finset.sum_congr rfl
    intro i hi
    rw [variance_const_mul]
    simp

/-- T1(iii)-(iv), exact unbiasedness and actual variances of both M1 estimators
under the stipulated conditional outcome law. This does not prove Gaussian
pivots or confidence-interval coverage. -/
theorem m1_probability_moments :
    (∫ Y, rdEstimator m1Linear Y ∂rdConditionalLaw m1Treated m1Control) = 4 ∧
    (∫ Y, rdEstimator m1Corrected Y ∂rdConditionalLaw m1Treated m1Control) = 4 ∧
    variance (rdEstimator m1Linear) (rdConditionalLaw m1Treated m1Control) = 83/25 ∧
    variance (rdEstimator m1Corrected) (rdConditionalLaw m1Treated m1Control) = 82/5 := by
  let mean : (Fin 2 × Fin 4) → ℝ := fun si =>
    if si.1 = 0 then m1Control (-m1Distance si.2) else m1Treated (m1Distance si.2)
  let weight : (Fin 4 → ℝ) → (Fin 2 × Fin 4) → ℝ := fun a si =>
    if si.1 = 0 then -a si.2 else a si.2
  have heq (a : Fin 4 → ℝ) : rdEstimator a = fun Y => ∑ si, weight a si * Y si := by
    funext Y
    norm_num [rdEstimator, Fintype.sum_prod_type, Fin.sum_univ_succ, weight]
    ring
  have hA := gaussian_product_moments mean (weight m1Linear)
  have hB := gaussian_product_moments mean (weight m1Corrected)
  change (∫ Y, rdEstimator m1Linear Y ∂Measure.pi (fun i => gaussianReal (mean i) 1)) = 4 ∧
    (∫ Y, rdEstimator m1Corrected Y ∂Measure.pi (fun i => gaussianReal (mean i) 1)) = 4 ∧
    variance _ (Measure.pi (fun i => gaussianReal (mean i) 1)) = _ ∧
    variance _ (Measure.pi (fun i => gaussianReal (mean i) 1)) = _
  rw [heq m1Linear, heq m1Corrected]
  rw [hA.1,hB.1,hA.2,hB.2]
  norm_num [mean,weight,m1Linear,m1Corrected,m1Bias,m1BiasMoment,m1Curvature,
    m1Distance,m1Control,m1Treated,Fintype.sum_prod_type,Fin.sum_univ_succ]

/-- T3(v), covariance of two weighted sums of the same independent signs.
This finite identity supplies all noisy-record covariances without enumerating
the 2^60-point randomization space. -/
theorem weighted_sign_covariance {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) :
    finiteCovariance (fun ω : ι → Bool => ∑ i, a i*signShock (ω i))
      (fun ω : ι → Bool => ∑ i, b i*signShock (ω i)) = ∑ i, a i*b i := by
  classical
  unfold finiteCovariance
  rw [(weighted_sign_moments a).1,(weighted_sign_moments b).1]
  simp only [sub_zero]
  have he : ∀ ω : ι → Bool,
      (∑ i, a i*signShock (ω i))*(∑ i, b i*signShock (ω i)) =
      ∑ i, ∑ j, (a i*b j)*(signShock (ω i)*signShock (ω j)) := by
    intro ω
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [finite_mean_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finite_mean_sum]
  simp_rw [finite_mean_mul,finite_sign_product]
  simp

/-- T3(v), the noisy estimator expressed on independent signs: cluster weights
on U_g and one fifth of each weight on the five independent record shocks. -/
def noisySignWeights (a : Fin 10 → ℝ) : Fin 10 ⊕ (Fin 10 × Fin 5) → ℝ :=
  Sum.elim a (fun gi => a gi.1/5)

/-- T3(v), actual variances of every weighted noisy cluster-mean estimator,
and the numerical conventional and bias-corrected values. -/
theorem noisy_cluster_moments :
    (∀ a : Fin 10 → ℝ,
      finiteMean (noisyClusterEstimator a) = 0 ∧
      finiteVariance (noisyClusterEstimator a) = (6/5:ℝ)*∑ g, a g^2) ∧
    finiteVariance (noisyClusterEstimator clusterLinear) = 372/125 ∧
    finiteVariance (noisyClusterEstimator clusterCorrected) = 12 := by
  have heq (a : Fin 10 → ℝ) : noisyClusterEstimator a =
      fun ω => ∑ i, noisySignWeights a i*signShock (ω i) := by
    funext ω
    simp only [noisyClusterEstimator,noisyClusterMean,noisyClusterOutcome,noisySignWeights,
      Fintype.sum_sum_type,Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul]
    simp only [mul_add,mul_div_assoc,← Finset.mul_sum,Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g hg
    ring
  have h (a : Fin 10 → ℝ) :
      finiteMean (noisyClusterEstimator a) = 0 ∧
      finiteVariance (noisyClusterEstimator a) = (6/5:ℝ)*∑ g, a g^2 := by
    rw [heq]
    refine ⟨(weighted_sign_moments (noisySignWeights a)).1,?_⟩
    rw [(weighted_sign_moments (noisySignWeights a)).2]
    simp only [noisySignWeights,Fintype.sum_sum_type,Fintype.sum_prod_type,
      Sum.elim_inl,Sum.elim_inr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul]
    have he : ∀ g : Fin 10, (5:ℝ)*(a g/5)^2 = a g^2/5 := by intro g; ring
    norm_num only [Nat.cast_ofNat]
    simp_rw [he]
    rw [← Finset.sum_div]
    ring
  refine ⟨h,?_,?_⟩
  · rw [(h clusterLinear).2]
    norm_num [clusterLinear,Fin.sum_univ_succ]
  · rw [(h clusterCorrected).2]
    norm_num [clusterCorrected,Fin.sum_univ_succ]

/-- T3(v), the quadratic form of I_5+11ᵀ is strictly positive for every
nonzero real vector; record noise therefore removes covariance degeneracy. -/
theorem noisy_covariance_positive (v : Fin 5 → ℝ) (hv : v ≠ 0) :
    0 < (∑ i, v i^2)+(∑ i, v i)^2 := by
  have hnonneg : 0 ≤ ∑ i, v i^2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hne : (∑ i, v i^2) ≠ 0 := by
    intro hz
    apply hv
    funext i
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sq_nonneg (v j))).mp hz
    have := hzero i (Finset.mem_univ i)
    simpa using this
  have hpos : 0 < ∑ i, v i^2 := lt_of_le_of_ne hnonneg (Ne.symm hne)
  exact add_pos_of_pos_of_nonneg hpos (sq_nonneg _)

/-- T4(iii), exact all-n WLS moment and variance certificate for the
shrinking-bandwidth example. The proof uses polynomial sum identities, not
finite-range checks or an assumed variance formula. -/
theorem shrinking_wls_certificate (n : ℕ) (hn : 3 ≤ n) :
    shrinkingMoment n 0 = (n:ℝ)/2 ∧
    shrinkingMoment n 1 = (n:ℝ)*((n:ℝ)+2)/(6*((n:ℝ)+1)) ∧
    shrinkingMoment n 2 = (n:ℝ)*((n:ℝ)+2)/(12*((n:ℝ)+1)) ∧
    shrinkingMoment n 0*shrinkingMoment n 2-shrinkingMoment n 1^2 =
      (n:ℝ)^2*((n:ℝ)+2)*((n:ℝ)-1)/(72*((n:ℝ)+1)^2) ∧
    0 < shrinkingMoment n 0*shrinkingMoment n 2-shrinkingMoment n 1^2 ∧
    (∀ j, shrinkingIntercept n j = 6*((n:ℝ)-(j:ℝ))*((n:ℝ)-1-2*(j:ℝ))/
      ((n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1))) ∧
    (∑ j : Fin n, ((n:ℝ)-(j:ℝ))^2*((n:ℝ)-1-2*(j:ℝ))^2) =
      (n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1)*(4*(n:ℝ)^2+5*(n:ℝ)-1)/30 ∧
    shrinkingVariance n = 12*(4*(n:ℝ)^2+5*(n:ℝ)-1)/
      (5*(n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1)) ∧
    0 < shrinkingVariance n := by
  have hnR : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have hn1 : (n:ℝ)-1 ≠ 0 := by linarith
  have hnp : (n:ℝ)+1 ≠ 0 := by linarith
  have hnp2 : (n:ℝ)+2 ≠ 0 := by linarith
  have hnp0 : 0 < (n:ℝ) := by linarith
  have hnp1 : 0 < (n:ℝ)-1 := by linarith
  have h1 : (∑ j : Fin n, (j:ℝ)) = (n:ℝ)*((n:ℝ)-1)/2 := by
    simpa only [Fin.sum_univ_eq_sum_range] using (finite_power_sums n).1
  have h2 : (∑ j : Fin n, (j:ℝ)^2) = (n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)/6 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (j:ℝ)^2)]
    exact (finite_power_sums n).2.1
  have h3 : (∑ j : Fin n, (j:ℝ)^3) = (n:ℝ)^2*((n:ℝ)-1)^2/4 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (j:ℝ)^3)]
    exact (finite_power_sums n).2.2.1
  have h4 : (∑ j : Fin n, (j:ℝ)^4) =
      (n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)*(3*(n:ℝ)^2-3*(n:ℝ)-1)/30 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (j:ℝ)^4)]
    exact (finite_power_sums n).2.2.2
  have hm0 : shrinkingMoment n 0 = (n:ℝ)/2 := by
    simp only [shrinkingMoment,shrinkingKernel,shrinkingDistance,pow_zero,mul_one,
      Finset.sum_sub_distrib,← Finset.sum_div,Finset.sum_add_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [h1]
    field_simp
    <;> ring
  have hm1 : shrinkingMoment n 1 = (n:ℝ)*((n:ℝ)+2)/(6*((n:ℝ)+1)) := by
    have he : ∀ j : Fin n, shrinkingKernel n j*shrinkingDistance n j =
        ((n:ℝ)+((n:ℝ)-1)*(j:ℝ)-(j:ℝ)^2)/((n:ℝ)+1)^2 := by
      intro j
      unfold shrinkingKernel shrinkingDistance
      field_simp
      <;> ring
    simp only [shrinkingMoment,pow_one,he,← Finset.sum_div,Finset.sum_sub_distrib,
      Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    rw [h1,h2]
    field_simp
    <;> ring
  have hm2 : shrinkingMoment n 2 = (n:ℝ)*((n:ℝ)+2)/(12*((n:ℝ)+1)) := by
    have he : ∀ j : Fin n, shrinkingKernel n j*shrinkingDistance n j^2 =
        ((n:ℝ)+(2*(n:ℝ)-1)*(j:ℝ)+((n:ℝ)-2)*(j:ℝ)^2-(j:ℝ)^3)/((n:ℝ)+1)^3 := by
      intro j
      unfold shrinkingKernel shrinkingDistance
      field_simp
      <;> ring
    simp only [shrinkingMoment,he,← Finset.sum_div,Finset.sum_sub_distrib,
      Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    rw [h1,h2,h3]
    field_simp
    <;> ring
  have hd : shrinkingMoment n 0*shrinkingMoment n 2-shrinkingMoment n 1^2 =
      (n:ℝ)^2*((n:ℝ)+2)*((n:ℝ)-1)/(72*((n:ℝ)+1)^2) := by
    rw [hm0,hm1,hm2]
    field_simp
    <;> ring
  have hdp : 0 < shrinkingMoment n 0*shrinkingMoment n 2-shrinkingMoment n 1^2 := by
    rw [hd]
    apply div_pos
    · positivity
    · positivity
  have ha : ∀ j, shrinkingIntercept n j =
      6*((n:ℝ)-(j:ℝ))*((n:ℝ)-1-2*(j:ℝ))/((n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1)) := by
    intro j
    unfold shrinkingIntercept
    rw [hd,hm1,hm2]
    unfold shrinkingKernel shrinkingDistance
    field_simp
    <;> ring
  have hp : (∑ j : Fin n, ((n:ℝ)-(j:ℝ))^2*((n:ℝ)-1-2*(j:ℝ))^2) =
      (n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1)*(4*(n:ℝ)^2+5*(n:ℝ)-1)/30 := by
    have he : ∀ j : Fin n, ((n:ℝ)-(j:ℝ))^2*((n:ℝ)-1-2*(j:ℝ))^2 =
        (n:ℝ)^4-2*(n:ℝ)^3+(n:ℝ)^2+
        (-6*(n:ℝ)^3+8*(n:ℝ)^2-2*(n:ℝ))*(j:ℝ)+
        (13*(n:ℝ)^2-10*(n:ℝ)+1)*(j:ℝ)^2+
        (-12*(n:ℝ)+4)*(j:ℝ)^3+4*(j:ℝ)^4 := by
      intro j
      ring
    simp only [he,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [h1,h2,h3,h4]
    ring
  have hv : shrinkingVariance n = 12*(4*(n:ℝ)^2+5*(n:ℝ)-1)/
      (5*(n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1)) := by
    unfold shrinkingVariance
    simp_rw [ha]
    have he : ∀ j : Fin n,
        (6*((n:ℝ)-(j:ℝ))*((n:ℝ)-1-2*(j:ℝ))/((n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1)))^2 =
        36/((n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1))^2 *
          (((n:ℝ)-(j:ℝ))^2*((n:ℝ)-1-2*(j:ℝ))^2) := by
      intro j
      rw [div_pow,mul_pow,mul_pow]
      ring
    simp_rw [he]
    rw [← Finset.mul_sum,hp]
    field_simp
    <;> ring
  refine ⟨hm0,hm1,hm2,hd,hdp,ha,hp,hv,?_⟩
  rw [hv]
  apply div_pos
  · nlinarith [sq_nonneg (n:ℝ)]
  · positivity

/-- T4(iii), the actual all-n conventional variance obeys n V_n → 48/5.
The eventual WLS formula is used only after it has been proved for every n≥3. -/
theorem shrinking_variance_limit :
    Tendsto (fun n : ℕ => (n:ℝ)*shrinkingVariance n) atTop (𝓝 (48/5)) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc (c : ℝ) : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hl : Tendsto (fun n : ℕ =>
      12*(4+5*(n:ℝ)⁻¹-((n:ℝ)⁻¹)^2)/(5*(1-((n:ℝ)⁻¹)^2))) atTop (𝓝 (48/5)) := by
    convert ((hc 12).mul (((hc 4).add ((hc 5).mul hi)).sub (hi.pow 2))).div
      ((hc 5).mul ((hc 1).sub (hi.pow 2))) (by norm_num) using 1 <;> norm_num
  apply hl.congr'
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  have hv := (shrinking_wls_certificate n hn).2.2.2.2.2.2.2.1
  have hnR : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have hn1 : (n:ℝ)-1 ≠ 0 := by linarith
  have hnp : (n:ℝ)+1 ≠ 0 := by linarith
  rw [hv]
  have hnsq : (n:ℝ)^2-1 ≠ 0 := by nlinarith
  field_simp [hnsq]
  <;> ring

/-- Integer-valued independent signs, used only as a compact computable
certificate for T3(iv)'s exact finite coverage counts. -/
def integerSign (u : Bool) : ℤ := if u then 1 else -1

/-- Five times the conventional cluster weights, T3(i),(iv). -/
def clusterLinearInteger : Fin 10 → ℤ := ![1,1,0,-2,-5,5,2,0,-1,-1]

/-- Five times the bias-corrected cluster weights, T3(ii),(iv). -/
def clusterCorrectedInteger : Fin 10 → ℤ := ![-2,1,4,2,-10,10,-2,-4,-1,2]

/-- T3(iv), zero real estimators correspond exactly to zero integer signed
sums. This bridge prevents the count certificate from changing the event. -/
theorem integer_cluster_zero (a : Fin 10 → ℝ) (z : Fin 10 → ℤ)
    (ha : ∀ g, a g = (z g:ℝ)/5) (ω : Fin 10 → Bool) :
    clusterEstimator a ω = 0 ↔ (∑ g, z g*integerSign (ω g)) = 0 := by
  have hc (u : Bool) : signShock u = (integerSign u:ℝ) := by
    cases u <;> norm_num [signShock,integerSign]
  have he : clusterEstimator a ω = ((∑ g, z g*integerSign (ω g):ℤ):ℝ)/5 := by
    unfold clusterEstimator
    simp_rw [ha,hc]
    calc
      _ = (∑ g, (z g:ℝ)*(integerSign (ω g):ℝ))/5 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro g hg
        ring
      _ = _ := by push_cast; rfl
  rw [he]
  rw [div_eq_zero_iff]
  norm_num only [OfNat.ofNat_ne_zero,or_false]
  exact_mod_cast (Iff.rfl : (∑ g, z g*integerSign (ω g)) = 0 ↔ (∑ g, z g*integerSign (ω g)) = 0)

set_option maxRecDepth 4096 in
/-- T3(iv), exact zero and nonzero counts under the 1024-point sign design.
Integer arithmetic is used only after an exact bridge to the real estimators. -/
theorem cluster_coverage_counts :
    Fintype.card (Fin 10 → Bool) = 1024 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterLinear ω ≠ 0)).card = 912 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterCorrected ω ≠ 0)).card = 968 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterLinear ω = 0)).card = 112 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterCorrected ω = 0)).card = 56 := by
  have ha : ∀ g, clusterLinear g = (clusterLinearInteger g:ℝ)/5 := by
    intro g
    fin_cases g <;> norm_num [clusterLinear,clusterLinearInteger]
  have hb : ∀ g, clusterCorrected g = (clusterCorrectedInteger g:ℝ)/5 := by
    intro g
    fin_cases g <;> norm_num [clusterCorrected,clusterCorrectedInteger]
  have hca : (Finset.univ.filter (fun ω : Fin 10 → Bool =>
      (∑ g, clusterLinearInteger g*integerSign (ω g)) = 0)).card = 112 := by decide +kernel
  have hcb : (Finset.univ.filter (fun ω : Fin 10 → Bool =>
      (∑ g, clusterCorrectedInteger g*integerSign (ω g)) = 0)).card = 56 := by decide +kernel
  have heqa : (Finset.univ.filter (fun ω => clusterEstimator clusterLinear ω = 0)) =
      (Finset.univ.filter (fun ω : Fin 10 → Bool =>
        (∑ g, clusterLinearInteger g*integerSign (ω g)) = 0)) := by
    apply Finset.filter_congr
    intro ω hω
    exact integer_cluster_zero _ _ ha ω
  have heqb : (Finset.univ.filter (fun ω => clusterEstimator clusterCorrected ω = 0)) =
      (Finset.univ.filter (fun ω : Fin 10 → Bool =>
        (∑ g, clusterCorrectedInteger g*integerSign (ω g)) = 0)) := by
    apply Finset.filter_congr
    intro ω hω
    exact integer_cluster_zero _ _ hb ω
  have hzeroa : (Finset.univ.filter (fun ω => clusterEstimator clusterLinear ω = 0)).card = 112 := by rw [heqa,hca]
  have hzerob : (Finset.univ.filter (fun ω => clusterEstimator clusterCorrected ω = 0)).card = 56 := by rw [heqb,hcb]
  have htotal : Fintype.card (Fin 10 → Bool) = 1024 := by norm_num
  refine ⟨htotal,?_,?_,hzeroa,hzerob⟩
  · have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 10 → Bool))) (p := fun ω => clusterEstimator clusterLinear ω = 0)
    simp only [hzeroa,Finset.card_univ,htotal] at hc
    change 112 + (Finset.univ.filter (fun ω => clusterEstimator clusterLinear ω ≠ 0)).card = 1024 at hc
    omega
  · have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 10 → Bool))) (p := fun ω => clusterEstimator clusterCorrected ω = 0)
    simp only [hzerob,Finset.card_univ,htotal] at hc
    change 56 + (Finset.univ.filter (fun ω => clusterEstimator clusterCorrected ω ≠ 0)).card = 1024 at hc
    omega

/-- Coefficients of one noisy record on the independent-sign cube, T3(v).
The only nonzero entries are its cluster shock and its own record shock. -/
def noisyRecordWeights (g : Fin 10) (i : Fin 5) : Fin 10 ⊕ (Fin 10 × Fin 5) → ℝ :=
  Sum.elim (fun h => if h=g then 1 else 0)
    (fun hi => if hi=(g,i) then 1 else 0)

/-- T3(v), the actual within-cluster covariance is I_5+11ᵀ and every
cluster mean has actual variance 6/5 under independent record and cluster signs. -/
theorem noisy_record_covariance :
    (∀ g i j, finiteCovariance (fun ω => noisyClusterOutcome ω g i)
      (fun ω => noisyClusterOutcome ω g j) = (if i=j then 1 else 0)+1) ∧
    (∀ g, finiteVariance (fun ω => noisyClusterMean ω g) = 6/5) := by
  have he (g : Fin 10) (i : Fin 5) : (fun ω => noisyClusterOutcome ω g i) =
      fun ω => ∑ j, noisyRecordWeights g i j*signShock (ω j) := by
    funext ω
    simp [noisyRecordWeights,noisyClusterOutcome,Fintype.sum_sum_type,Fintype.sum_prod_type,
      ite_mul]
  constructor
  · intro g i j
    rw [he g i,he g j,weighted_sign_covariance]
    by_cases hij : i=j
    · subst j
      simp [noisyRecordWeights,Fintype.sum_sum_type,Fintype.sum_prod_type,
        ite_mul,mul_ite]
    · simp [noisyRecordWeights,Fintype.sum_sum_type,Fintype.sum_prod_type,
        ite_mul,mul_ite,hij,Ne.symm hij]
  · intro g
    have hm : (fun ω => noisyClusterMean ω g) = noisyClusterEstimator (Pi.single g 1) := by
      funext ω
      simp [noisyClusterEstimator,Pi.single_apply,ite_mul]
    rw [hm,(noisy_cluster_moments.1 (Pi.single g 1)).2]
    simp [Pi.single_apply]

/-- T1(v), a finite weighted sum of independent unit-variance Gaussian
coordinates has the Gaussian law with the already proved mean and variance.
This supporting law does not assume a central limit approximation. -/
theorem gaussian_product_law {ι : Type*} [Fintype ι] (mean w : ι → ℝ) :
    HasLaw (fun Y => ∑ i, w i*Y i)
      (gaussianReal (∑ i, w i*mean i) ((∑ i, w i^2).toNNReal))
      (Measure.pi (fun i => gaussianReal (mean i) 1)) := by
  have hc (i : ι) : HasLaw (fun Y : ι → ℝ => Y i) (gaussianReal (mean i) 1)
      (Measure.pi (fun i => gaussianReal (mean i) 1)) := by
    exact ⟨(measurable_pi_apply i).aemeasurable,
      (measurePreserving_eval (fun i => gaussianReal (mean i) 1) i).map_eq⟩
  have hgi (i : ι) : HasGaussianLaw (fun Y : ι → ℝ => w i*Y i)
      (Measure.pi (fun i => gaussianReal (mean i) 1)) :=
    (gaussianReal_const_mul (hc i) (w i)).hasGaussianLaw
  have hind : iIndepFun (fun i (Y : ι → ℝ) => w i*Y i)
      (Measure.pi (fun i => gaussianReal (mean i) 1)) := by
    exact iIndepFun_pi (μ := fun i => gaussianReal (mean i) 1)
      (X := fun i (x : ℝ) => w i*x) (fun i => by fun_prop)
  have hg := hind.hasGaussianLaw_fun_sum hgi
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,(gaussian_product_moments mean w).1,
    (gaussian_product_moments mean w).2]

/-- T2(e), no measurable statistic can equal the number of M2 studies almost
surely for every subset S, because every S has the same actual conditional data
law and N≥1. This is not a historical count of invalid original intervals. -/
theorem no_uniform_subset_count (N : ℕ) (hN : 1 ≤ N) :
    ¬ ∃ F : (Fin N → (Fin 2 × Fin 4) → ℝ) → ℕ, Measurable F ∧
      ∀ S : Finset (Fin N), ∀ᵐ Y ∂studyDataLaw N S, F Y = S.card := by
  letI : IsProbabilityMeasure (studyDataLaw N ∅) := by
    simp only [studyDataLaw,Finset.notMem_empty,if_false]
    unfold rdConditionalLaw
    infer_instance
  rintro ⟨F,hF,hall⟩
  have h0 : ∀ᵐ Y ∂studyDataLaw N ∅, F Y = 0 := by
    simpa using hall ∅
  have hfull : ∀ᵐ Y ∂studyDataLaw N ∅, F Y = N := by
    have h := hall Finset.univ
    rw [(study_laws_identical.{0} N Finset.univ).1] at h
    simpa using h
  have hfalse : ∀ᵐ Y ∂studyDataLaw N ∅, False := by
    filter_upwards [h0,hfull] with Y hY0 hYN
    omega
  obtain ⟨Y,hY⟩ := hfalse.exists
  exact hY
/-- T3 complete counterexample to the default clustered variance construction
presupposed by main pp. 7 and 9. It includes exact coverage counts and the
positive-definite noisy extension; it does not claim the package selects h=6. -/
theorem clustered_variance_counterexample :
    Continuous (fun _ : ℝ => (0:ℝ)) ∧
    (∀ g i, finiteMean (fun ω => clusterOutcome ω g i) = 0) ∧
    rdEffect (fun _ => 0) (fun _ => 0) 0 = 0 ∧
    (∀ data g i, clusterOutcome data g i ∈ Icc (-1) 1) ∧
    finiteMean (clusterEstimator clusterLinear) = 0 ∧
    finiteMean (clusterEstimator clusterCorrected) = 0 ∧
    finiteVariance (clusterEstimator clusterLinear) = 62/25 ∧
    finiteVariance (clusterEstimator clusterCorrected) = 10 ∧
    (∀ f : ℝ, ∀ ω : Fin 10 → Bool,
      clusterScoreVariance f (fun g => (clusterLinear g/5)*∑ i, nnResidual (clusterOutcome ω g) i) = 0 ∧
      clusterScoreVariance f (fun g => (clusterCorrected g/5)*∑ i, nnResidual (clusterOutcome ω g) i) = 0) ∧
    Fintype.card (Fin 10 → Bool) = 1024 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterLinear ω ≠ 0)).card = 912 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterCorrected ω ≠ 0)).card = 968 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterLinear ω = 0)).card = 112 ∧
    (Finset.univ.filter (fun ω => clusterEstimator clusterCorrected ω = 0)).card = 56 ∧
    (∀ g i j, finiteCovariance (fun ω => noisyClusterOutcome ω g i)
      (fun ω => noisyClusterOutcome ω g j) = (if i=j then 1 else 0)+1) ∧
    (∀ v : Fin 5 → ℝ, v ≠ 0 → 0 < (∑ i, v i^2)+(∑ i, v i)^2) ∧
    (∀ g, finiteVariance (fun ω => noisyClusterMean ω g) = 6/5) ∧
    finiteVariance (noisyClusterEstimator clusterLinear) = 372/125 ∧
    finiteVariance (noisyClusterEstimator clusterCorrected) = 12 ∧
    (∀ f : ℝ, ∀ ω : (Fin 10 ⊕ (Fin 10 × Fin 5)) → Bool,
      clusterScoreVariance f (fun g => (clusterLinear g/5)*∑ i, nnResidual (noisyClusterOutcome ω g) i) = 0 ∧
      clusterScoreVariance f (fun g => (clusterCorrected g/5)*∑ i, nnResidual (noisyClusterOutcome ω g) i) = 0) := by
  rcases clustered_zero_vs_positive with ⟨hma,hmb,hva,hvb,hzero⟩
  rcases cluster_coverage_counts with ⟨hcard,hna,hnb,hza,hzb⟩
  rcases noisy_record_covariance with ⟨hcov,hmean⟩
  refine ⟨continuous_const,?_,?_,?_,hma,hmb,hva,hvb,?_,hcard,hna,hnb,hza,hzb,
    hcov,noisy_covariance_positive,hmean,noisy_cluster_moments.2.1,
    noisy_cluster_moments.2.2,?_⟩
  · intro g i
    simp [clusterOutcome,finiteMean,sum_sign_shock_zero]
  · norm_num [rdEffect]
  · intro data g i
    cases h : data g <;> simp [clusterOutcome,signShock,h]
  · intro f ω
    exact hzero f (clusterOutcome ω)
  · intro f ω
    exact hzero f (noisyClusterOutcome ω)


/-- T4(iv), exact mean and variance of a weighted sum of independent
square-integrable cluster outcomes with a common mean and variance. -/
theorem independent_weighted_moments {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, MemLp (Z i) 2 μ) (hI : iIndepFun Z μ)
    (mean varZ : ℝ) (hmean : ∀ i, (∫ ω, Z i ω ∂μ) = mean)
    (hvar : ∀ i, variance (Z i) μ = varZ) (a : ι → ℝ) :
    (∫ ω, (∑ i, a i*Z i ω) ∂μ) = mean*∑ i, a i ∧
    variance (fun ω => ∑ i, a i*Z i ω) μ = varZ*∑ i, a i^2 := by
  classical
  have hLp : ∀ i, MemLp (fun ω => a i*Z i ω) 2 μ := fun i => (hZ i).const_mul (a i)
  constructor
  · rw [integral_finsetSum]
    · simp_rw [integral_const_mul,hmean]
      rw [← Finset.sum_mul]
      ring
    · intro i hi
      exact (hLp i).integrable (by norm_num)
  · have hp : Set.Pairwise (↑(Finset.univ : Finset ι))
        (fun i j => IndepFun (fun ω => a i*Z i ω) (fun ω => a j*Z j ω) μ) := by
      intro i hi j hj hij
      exact (hI.indepFun hij).comp (by fun_prop) (by fun_prop)
    have hv := IndepFun.variance_sum (fun i hi => hLp i) hp
    have hv' : variance (fun ω => ∑ i, a i*Z i ω) μ =
        ∑ i, variance (fun ω => a i*Z i ω) μ := by
      simpa only [Finset.sum_fn] using hv
    rw [hv']
    simp_rw [variance_const_mul,hvar]
    rw [← Finset.sum_mul]
    ring

/-- Coefficients for Z_g-barZ in T4(iv), with every cluster counted once. -/
def centeredClusterWeights {G : ℕ} (g i : Fin G) : ℝ :=
  (if i=g then 1 else 0)-1/(G:ℝ)

/-- T4(iv), the centered-cluster coefficient sums; the common mean cancels
and the common-variance multiplier is 1-1/G. -/
theorem centered_cluster_weights {G : ℕ} (hG : 2 ≤ G) (g : Fin G) :
    (∑ i, centeredClusterWeights g i) = 0 ∧
    (∑ i, centeredClusterWeights g i^2) = 1-1/(G:ℝ) := by
  have hGR : (2:ℝ) ≤ G := by exact_mod_cast hG
  have hG0 : (G:ℝ) ≠ 0 := by linarith
  constructor
  · simp [centeredClusterWeights,Finset.sum_sub_distrib,Finset.sum_const]
    field_simp
    <;> ring
  · have he (i : Fin G) : centeredClusterWeights g i^2 =
        (if i=g then 1-2/(G:ℝ) else 0)+1/(G:ℝ)^2 := by
      unfold centeredClusterWeights
      split_ifs <;> field_simp <;> ring
    simp_rw [he]
    simp [Finset.sum_add_distrib,Finset.sum_const]
    field_simp
    <;> ring

/-- T4(iv), the centered cluster outcome is exactly the linear combination
with centeredClusterWeights, for every outcome vector, without assumptions. -/
theorem centered_cluster_sum {G : ℕ} (g : Fin G) (Z : Fin G → ℝ) :
    (∑ i, centeredClusterWeights g i*Z i) = Z g-sampleMean Z := by
  unfold centeredClusterWeights sampleMean
  simp only [sub_mul,ite_mul,one_mul,zero_mul,Finset.sum_sub_distrib]
  simp [← Finset.mul_sum]
  ring

/-- T4(iv), exact expected centered squares and an unbiased cluster-component
plug-in variance under the stated independence and common moments. -/
theorem centered_cluster_moments {G : ℕ} (hG : 2 ≤ G)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin G → Ω → ℝ) (hZ : ∀ i, MemLp (Z i) 2 μ) (hI : iIndepFun Z μ)
    (mean varZ : ℝ) (hmean : ∀ i, (∫ ω, Z i ω ∂μ) = mean)
    (hvar : ∀ i, variance (Z i) μ = varZ) :
    (∀ g, (∫ ω, (Z g ω-sampleMean (fun j => Z j ω))^2 ∂μ) = (1-1/(G:ℝ))*varZ) ∧
    (∀ a : Fin G → ℝ,
      (∫ ω, clusterPlugin a (fun j => Z j ω) ∂μ) = varZ*∑ g, a g^2 ∧
      variance (fun ω => ∑ g, a g*Z g ω) μ = varZ*∑ g, a g^2) := by
  have hGR : (2:ℝ) ≤ G := by exact_mod_cast hG
  have hG0 : (G:ℝ) ≠ 0 := by linarith
  have hG1 : (G:ℝ)-1 ≠ 0 := by linarith
  have he (g : Fin G) : (fun ω => ∑ i, centeredClusterWeights g i*Z i ω) =
      (fun ω => Z g ω-sampleMean (fun j => Z j ω)) := by
    funext ω
    exact centered_cluster_sum g _
  have hLp (g : Fin G) : MemLp (fun ω => Z g ω-sampleMean (fun j => Z j ω)) 2 μ := by
    rw [← he g]
    exact memLp_finsetSum Finset.univ (fun i hi => (hZ i).const_mul (centeredClusterWeights g i))
  have hs (g : Fin G) : (∫ ω, (Z g ω-sampleMean (fun j => Z j ω))^2 ∂μ) =
      (1-1/(G:ℝ))*varZ := by
    have hm := independent_weighted_moments μ Z hZ hI mean varZ hmean hvar (centeredClusterWeights g)
    rw [he g,(centered_cluster_weights hG g).1,mul_zero,(centered_cluster_weights hG g).2] at hm
    have hv := hm.2
    rw [variance_eq_integral (hLp g).aemeasurable,hm.1] at hv
    simp only [sub_zero] at hv
    simpa only [mul_comm] using hv
  refine ⟨hs,?_⟩
  intro a
  refine ⟨?_,(independent_weighted_moments μ Z hZ hI mean varZ hmean hvar a).2⟩
  simp only [clusterPlugin]
  rw [integral_const_mul,integral_finsetSum]
  · simp_rw [integral_const_mul,hs]
    rw [← Finset.sum_mul]
    field_simp
    <;> ring
  · intro g hg
    exact ((hLp g).integrable_sq).const_mul (a g^2)

/-- T4(iv), a finite expectation version of the same plug-in calculation.
The expected centered square r is a hypothesis of this linearity lemma; actual
toy-model centered moments are proved below before applying it. -/
theorem finite_plugin_moment {G : ℕ} {Ω : Type*} [Fintype Ω]
    (a : Fin G → ℝ) (Z : Ω → Fin G → ℝ) (r : ℝ)
    (hZ : ∀ g, finiteMean (fun ω => (Z ω g-sampleMean (Z ω))^2) = r) :
    finiteMean (fun ω => clusterPlugin a (Z ω)) =
      (G:ℝ)/((G:ℝ)-1)*r*∑ g, a g^2 := by
  simp only [clusterPlugin]
  rw [finite_mean_mul,finite_mean_sum]
  simp_rw [finite_mean_mul,hZ]
  rw [← Finset.sum_mul]
  ring

/-- T4(iv), finite plug-in arithmetic for a ten-cluster law with expected
centered square 9/10. The concrete sign-law premise is proved separately. -/
theorem finite_toy_plugin_moment {Ω : Type*} [Fintype Ω] (Z : Fin 10 → Ω → ℝ)
    (hZ : ∀ g, finiteMean (fun ω => (Z g ω-sampleMean (fun j => Z j ω))^2) = (9/10:ℝ)) :
    finiteMean (fun ω => clusterPlugin clusterLinear (fun j => Z j ω)) = 62/25 ∧
    finiteMean (fun ω => clusterPlugin clusterCorrected (fun j => Z j ω)) = 10 := by
  rw [finite_plugin_moment clusterLinear (fun ω j => Z j ω) (9/10) hZ,
    finite_plugin_moment clusterCorrected (fun ω j => Z j ω) (9/10) hZ]
  norm_num [clusterLinear,clusterCorrected,Fin.sum_univ_succ]

/-- T4(iv), exact finite centered moments and unbiased plug-in variances in
both versions of the T3 toy. The record-noise model retains its 60 independent
coordinates and no enumeration of that cube is used. -/
theorem toy_plugin_moments :
    finiteMean (fun ω => clusterPlugin clusterLinear (fun g => clusterOutcome ω g 0)) = 62/25 ∧
    finiteMean (fun ω => clusterPlugin clusterCorrected (fun g => clusterOutcome ω g 0)) = 10 ∧
    finiteMean (fun ω => clusterPlugin clusterLinear (noisyClusterMean ω)) = 372/125 ∧
    finiteMean (fun ω => clusterPlugin clusterCorrected (noisyClusterMean ω)) = 12 := by
  have hc (g : Fin 10) : clusterEstimator (centeredClusterWeights g) =
      (fun ω => clusterOutcome ω g 0-sampleMean (fun j => clusterOutcome ω j 0)) := by
    funext ω
    exact centered_cluster_sum g _
  have hn (g : Fin 10) : noisyClusterEstimator (centeredClusterWeights g) =
      (fun ω => noisyClusterMean ω g-sampleMean (noisyClusterMean ω)) := by
    funext ω
    exact centered_cluster_sum g _
  have hs (g : Fin 10) : finiteMean
      (fun ω => (clusterOutcome ω g 0-sampleMean (fun j => clusterOutcome ω j 0))^2) = 9/10 := by
    have hm := weighted_sign_moments (centeredClusterWeights g)
    change finiteMean (clusterEstimator (centeredClusterWeights g)) = 0 ∧
      finiteVariance (clusterEstimator (centeredClusterWeights g)) = _ at hm
    rw [hc g] at hm
    have hv := hm.2
    unfold finiteVariance at hv
    rw [hm.1] at hv
    norm_num [centered_cluster_weights (by norm_num : 2 ≤ 10) g] at hv ⊢
    exact hv
  have hns (g : Fin 10) : finiteMean
      (fun ω => (noisyClusterMean ω g-sampleMean (noisyClusterMean ω))^2) = (6/5)*(9/10) := by
    have hm := noisy_cluster_moments.1 (centeredClusterWeights g)
    rw [hn g] at hm
    have hv := hm.2
    unfold finiteVariance at hv
    rw [hm.1] at hv
    norm_num [centered_cluster_weights (by norm_num : 2 ≤ 10) g] at hv ⊢
    exact hv
  have hi := finite_toy_plugin_moment (fun j ω => clusterOutcome ω j 0) hs
  refine ⟨hi.1,hi.2,?_,?_⟩
  · rw [finite_plugin_moment clusterLinear noisyClusterMean ((6/5)*(9/10)) hns]
    norm_num [clusterLinear,Fin.sum_univ_succ]
  · rw [finite_plugin_moment clusterCorrected noisyClusterMean ((6/5)*(9/10)) hns]
    norm_num [clusterCorrected,Fin.sum_univ_succ]

/-- T4(iii), the actual mean and design variance of the conventional
shrinking-bandwidth estimator on independent uniform signs. -/
theorem shrinking_sampling_moments (n : ℕ) :
    finiteMean (shrinkingEstimator n) = 0 ∧
    finiteVariance (shrinkingEstimator n) = shrinkingVariance n := by
  let a : Fin 2 × Fin n → ℝ := fun si =>
    if si.1=0 then -shrinkingIntercept n si.2 else shrinkingIntercept n si.2
  have he : shrinkingEstimator n = fun ω => ∑ i, a i*signShock (ω i) := by
    funext ω
    unfold shrinkingEstimator
    simp only [Fintype.sum_prod_type,Fin.sum_univ_succ,a]
    norm_num
    simp only [mul_sub,Finset.sum_sub_distrib,neg_mul,Finset.sum_neg_distrib]
    ring
  rw [he]
  refine ⟨(weighted_sign_moments a).1,?_⟩
  rw [(weighted_sign_moments a).2]
  simp [a,Fintype.sum_prod_type,Fin.sum_univ_succ,shrinkingVariance]

/-- The shrinking noisy estimator’s independent-sign coefficients in T4(iii):
a signed intercept weight on each U and one fifth on each record error. -/
def shrinkingNoisyWeights (n : ℕ) :
    (Fin 2 × Fin n) ⊕ ((Fin 2 × Fin n) × Fin 5) → ℝ :=
  Sum.elim
    (fun si => if si.1=0 then -shrinkingIntercept n si.2 else shrinkingIntercept n si.2)
    (fun sii => (if sii.1.1=0 then -shrinkingIntercept n sii.1.2 else shrinkingIntercept n sii.1.2)/5)

/-- T4(iii), independent record noise multiplies the actual variance by 6/5
at every n, while within-cell residual cancellation continues to apply. -/
theorem shrinking_noisy_sampling_moments (n : ℕ) :
    finiteMean (shrinkingNoisyEstimator n) = 0 ∧
    finiteVariance (shrinkingNoisyEstimator n) = (6/5)*shrinkingVariance n := by
  have he : shrinkingNoisyEstimator n =
      fun ω => ∑ i, shrinkingNoisyWeights n i*signShock (ω i) := by
    funext ω
    simp only [shrinkingNoisyEstimator,shrinkingNoisyWeights,Fintype.sum_sum_type,
      Fintype.sum_prod_type,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_two]
    norm_num
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,neg_mul,Finset.sum_neg_distrib]
    simp only [← Finset.sum_add_distrib,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
    ring
  rw [he]
  refine ⟨(weighted_sign_moments (shrinkingNoisyWeights n)).1,?_⟩
  rw [(weighted_sign_moments (shrinkingNoisyWeights n)).2]
  simp only [shrinkingNoisyWeights,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_two]
  norm_num
  try simp only [neg_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hd : ∀ j : Fin n, (5:ℝ)*(shrinkingIntercept n j/5)^2 = shrinkingIntercept n j^2/5 := by
    intro j
    ring
  simp_rw [hd]
  rw [← Finset.sum_div]
  unfold shrinkingVariance
  simp only [div_eq_mul_inv,← Finset.sum_mul]
  ring_nf
  rw [← Finset.sum_mul]
  ring

/-- T7(i), exact window masses for the actual selection-free density x/8
on [0,4]. This supporting proof integrates the density itself, rather than
defining window mass by the desired polynomial formula. -/
theorem linear_caliper_masses (h : ℝ) (hh : 0 < h) (hc : h < caliperCutoff) :
    caliperAbove linearCaliperDensity h = (2*caliperCutoff*h+h^2)/16 ∧
    caliperBelow linearCaliperDensity h = (2*caliperCutoff*h-h^2)/16 ∧
    caliperProbability linearCaliperDensity h = 1/2+h/(4*caliperCutoff) ∧
    (∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h), 0 < linearCaliperDensity x) := by
  have hc0 : 0 < caliperCutoff := by norm_num [caliperCutoff]
  have hc2 : caliperCutoff < 2 := by norm_num [caliperCutoff]
  have hf : ∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h), linearCaliperDensity x = x/8 := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hx4 : x ≤ 4 := by linarith [hx.2]
    simp [linearCaliperDensity,show x ∈ Icc (0:ℝ) 4 from ⟨hx0,hx4⟩]
  have hA : caliperAbove linearCaliperDensity h = (2*caliperCutoff*h+h^2)/16 := by
    unfold caliperAbove
    calc
      _ = ∫ x in caliperCutoff..(caliperCutoff+h), x/8 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : caliperCutoff ≤ caliperCutoff+h)] at hx
        exact hf x ⟨by linarith [hx.1],hx.2⟩
      _ = _ := by rw [intervalIntegral.integral_div,integral_id]; ring
  have hB : caliperBelow linearCaliperDensity h = (2*caliperCutoff*h-h^2)/16 := by
    unfold caliperBelow
    calc
      _ = ∫ x in (caliperCutoff-h)..caliperCutoff, x/8 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : caliperCutoff-h ≤ caliperCutoff)] at hx
        exact hf x ⟨hx.1,by linarith [hx.2]⟩
      _ = _ := by rw [intervalIntegral.integral_div,integral_id]; ring
  refine ⟨hA,hB,?_,?_⟩
  · unfold caliperProbability
    rw [hA,hB]
    have hd : 0 < (2*caliperCutoff*h+h^2)/16+(2*caliperCutoff*h-h^2)/16 := by nlinarith
    rw [div_eq_iff (ne_of_gt hd)]
    field_simp
    <;> ring
  · intro x hx
    rw [hf x hx]
    have hx0 : 0 < x := by linarith [hx.1]
    positivity

/-- T7(i)-(iii), actual density normalization and the three window-probability
values, including a binomial rejection tail strictly above the nominal 5%. -/
theorem linear_caliper_witness :
    (∫ x in (0:ℝ)..4, x/8) = 1 ∧
    caliperProbability linearCaliperDensity (caliperCutoff/10) = 21/40 ∧
    caliperProbability linearCaliperDensity (caliperCutoff*3/20) = 43/80 ∧
    caliperProbability linearCaliperDensity (caliperCutoff/5) = 11/20 ∧
    caliperAbove linearCaliperDensity (caliperCutoff/5) = 26411/250000 ∧
    caliperBelow linearCaliperDensity (caliperCutoff/5) = 21609/250000 ∧
    (1/20:ℝ) < binomialTail 19 14 (caliperProbability linearCaliperDensity (caliperCutoff/5)) := by
  have h1 := linear_caliper_masses (caliperCutoff/10) (by norm_num [caliperCutoff]) (by norm_num [caliperCutoff])
  have h2 := linear_caliper_masses (caliperCutoff*3/20) (by norm_num [caliperCutoff]) (by norm_num [caliperCutoff])
  have h3 := linear_caliper_masses (caliperCutoff/5) (by norm_num [caliperCutoff]) (by norm_num [caliperCutoff])
  have hp1 : caliperProbability linearCaliperDensity (caliperCutoff/10) = 21/40 :=
    h1.2.2.1.trans (by norm_num [caliperCutoff])
  have hp2 : caliperProbability linearCaliperDensity (caliperCutoff*3/20) = 43/80 :=
    h2.2.2.1.trans (by norm_num [caliperCutoff])
  have hp3 : caliperProbability linearCaliperDensity (caliperCutoff/5) = 11/20 :=
    h3.2.2.1.trans (by norm_num [caliperCutoff])
  have ha3 : caliperAbove linearCaliperDensity (caliperCutoff/5) = 26411/250000 :=
    h3.1.trans (by norm_num [caliperCutoff])
  have hb3 : caliperBelow linearCaliperDensity (caliperCutoff/5) = 21609/250000 :=
    h3.2.1.trans (by norm_num [caliperCutoff])
  refine ⟨?_,hp1,hp2,hp3,ha3,hb3,?_⟩
  · rw [intervalIntegral.integral_div,integral_id]
    norm_num
  · rw [hp3]
    exact caliper_exact_tails.2.2.2.2.2.2.2.2.2


/-- T4(i)-(v), complete corrected clustered-variance statement, including the
shrinking-bandwidth asymptotic statement without replacing it by finite checks.
Default residual applicability is restricted to tied cells m≥4 nested in clusters. -/
theorem clustered_variance_correction :
    (∀ m : ℕ, 2 ≤ m → ∀ y : Fin m → ℝ,
      (∀ i, nnResidual y i = Real.sqrt ((m:ℝ)/((m:ℝ)-1)) *
        (y i-(∑ j, y j)/(m:ℝ))) ∧ (∑ i, nnResidual y i) = 0) ∧
    (∀ C G : ℕ, ∀ m : Fin C → ℕ, (∀ c, 4 ≤ m c) →
      ∀ owner : Fin C → Fin G, ∀ ell : Fin C → ℝ,
      ∀ y : (c : Fin C) → Fin (m c) → ℝ, ∀ f : ℝ,
      (∀ g, nestedClusterScore m owner ell y g = 0) ∧
      clusterScoreVariance f (nestedClusterScore m owner ell y) = 0) ∧
    (∀ n : ℕ, 3 ≤ n →
      shrinkingMoment n 0 = (n:ℝ)/2 ∧
      shrinkingMoment n 1 = (n:ℝ)*((n:ℝ)+2)/(6*((n:ℝ)+1)) ∧
      shrinkingMoment n 2 = (n:ℝ)*((n:ℝ)+2)/(12*((n:ℝ)+1)) ∧
      shrinkingMoment n 0*shrinkingMoment n 2-shrinkingMoment n 1^2 =
        (n:ℝ)^2*((n:ℝ)+2)*((n:ℝ)-1)/(72*((n:ℝ)+1)^2) ∧
      0 < shrinkingMoment n 0*shrinkingMoment n 2-shrinkingMoment n 1^2 ∧
      (∀ j, shrinkingIntercept n j = 6*((n:ℝ)-(j:ℝ))*((n:ℝ)-1-2*(j:ℝ))/
        ((n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1))) ∧
      (∑ j : Fin n, ((n:ℝ)-(j:ℝ))^2*((n:ℝ)-1-2*(j:ℝ))^2) =
        (n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1)*(4*(n:ℝ)^2+5*(n:ℝ)-1)/30 ∧
      shrinkingVariance n = 12*(4*(n:ℝ)^2+5*(n:ℝ)-1)/
        (5*(n:ℝ)*((n:ℝ)-1)*((n:ℝ)+1)) ∧
      0 < shrinkingVariance n ∧
      finiteMean (shrinkingEstimator n) = 0 ∧
      finiteVariance (shrinkingEstimator n) = shrinkingVariance n ∧
      finiteMean (shrinkingNoisyEstimator n) = 0 ∧
      finiteVariance (shrinkingNoisyEstimator n) = (6/5)*shrinkingVariance n ∧
      (∀ f : ℝ, ∀ y : (Fin 2 × Fin n) → Fin 5 → ℝ,
        f*(∑ g, ((shrinkingIntercept n g.2/5)*∑ i, nnResidual (y g) i)^2) = 0)) ∧
    Tendsto (fun n : ℕ => (n:ℝ)*shrinkingVariance n) atTop (𝓝 (48/5)) ∧
    (∀ G : ℕ, 2 ≤ G → ∀ (Ω : Type*) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Fin G → Ω → ℝ) (a : Fin G → ℝ)
      (mean varZ : ℝ), (∀ g, MemLp (Z g) 2 μ) → iIndepFun Z μ →
      (∀ g, (∫ ω, Z g ω ∂μ) = mean) → (∀ g, variance (Z g) μ = varZ) →
      (∀ g, (∫ ω, (Z g ω-sampleMean (fun j => Z j ω))^2 ∂μ) = (1-1/(G:ℝ))*varZ) ∧
      (∫ ω, clusterPlugin a (fun j => Z j ω) ∂μ) = varZ*∑ g, a g^2 ∧
      variance (fun ω => ∑ g, a g*Z g ω) μ = varZ*∑ g, a g^2) ∧
    (∀ (Ω : Type*) [Fintype Ω] (Z : Fin 10 → Ω → ℝ),
      (∀ g, finiteMean (fun ω => (Z g ω-sampleMean (fun j => Z j ω))^2) = (9/10:ℝ)) →
      finiteMean (fun ω => clusterPlugin clusterLinear (fun j => Z j ω)) = 62/25 ∧
      finiteMean (fun ω => clusterPlugin clusterCorrected (fun j => Z j ω)) = 10) ∧
    finiteMean (fun ω => clusterPlugin clusterLinear (fun g => clusterOutcome ω g 0)) = 62/25 ∧
    finiteMean (fun ω => clusterPlugin clusterCorrected (fun g => clusterOutcome ω g 0)) = 10 ∧
    finiteMean (fun ω => clusterPlugin clusterLinear (noisyClusterMean ω)) = 372/125 ∧
    finiteMean (fun ω => clusterPlugin clusterCorrected (noisyClusterMean ω)) = 12 ∧
    ((1/6 : ℝ)-1/36 = 5/36) ∧ ((11/72 : ℝ)-1/36 = 1/8) ∧
    ((5/48 : ℝ)-1/36 = 11/144) ∧ ((1/13 : ℝ)-1/26 = 1/26) ∧
    ((1/26 : ℝ)-1/26 = 0) := by
  rcases toy_plugin_moments with ⟨hta,htb,htna,htnb⟩
  refine ⟨?_,?_,?_,shrinking_variance_limit,?_,?_,hta,htb,htna,htnb,
    clustered_table_arithmetic⟩
  · intro m hm y
    exact ⟨nn_residual_centered hm y,nn_residual_sum hm y⟩
  · intro C G m hm owner ell y f
    exact nested_cells_zero_variance m hm owner ell y f
  · intro n hn
    rcases shrinking_wls_certificate n hn with ⟨h0,h1,h2,hd,hdp,ha,hp,hv,hvp⟩
    refine ⟨h0,h1,h2,hd,hdp,ha,hp,hv,hvp,(shrinking_sampling_moments n).1,
      (shrinking_sampling_moments n).2,(shrinking_noisy_sampling_moments n).1,
      (shrinking_noisy_sampling_moments n).2,?_⟩
    intro f y
    simp [nn_residual_sum (by norm_num : 2 ≤ 5)]
  · intro G hG Ω inst μ instP Z a mean varZ hZ hI hm hv
    have h := centered_cluster_moments hG μ Z hZ hI mean varZ hm hv
    exact ⟨h.1,(h.2 a).1,(h.2 a).2⟩
  · intro Ω inst Z hZ
    exact finite_toy_plugin_moment Z hZ


/-- T6(i), actual variance of any measurable binary random variable, with
P(Y=1)=p. The model is not a variance formula supplied as a definition. -/
theorem binary_probability_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (p : ℝ)
    (hY : Measurable Y) (hy : ∀ᵐ ω ∂μ, Y ω = 0 ∨ Y ω = 1)
    (hp : μ.real {ω | Y ω = 1} = p) :
    variance Y μ = p*(1-p) ∧ variance Y μ = 1/4-(p-1/2)^2 ∧
    variance Y μ ≤ 1/4 ∧ Real.sqrt (variance Y μ) ≤ 1/2 := by
  have hb : ∀ᵐ ω ∂μ, Y ω ∈ Icc (0:ℝ) 1 := by
    filter_upwards [hy] with ω h
    rcases h with h | h <;> norm_num [h]
  have hLp : MemLp Y 2 μ := memLp_of_bounded hb hY.aestronglyMeasurable 2
  let E : Set Ω := {ω | Y ω = 1}
  have hE : MeasurableSet E := hY (measurableSet_singleton (1:ℝ))
  have he : Y =ᵐ[μ] E.indicator (fun _ => (1:ℝ)) := by
    filter_upwards [hy] with ω h
    rcases h with h | h <;> simp [E,h]
  have hm : (∫ ω, Y ω ∂μ) = p := by
    rw [integral_congr_ae he,integral_indicator hE]
    simpa [E] using hp
  have hsq : Y^2 =ᵐ[μ] Y := by
    filter_upwards [hy] with ω h
    rcases h with h | h <;> norm_num [Pi.pow_apply,h]
  have hv : variance Y μ = p*(1-p) := by
    rw [variance_eq_sub hLp,integral_congr_ae hsq,hm]
    ring
  have hi : variance Y μ = 1/4-(p-1/2)^2 := by rw [hv]; ring
  have hv0 := variance_nonneg Y μ
  have hbound : variance Y μ ≤ 1/4 := by rw [hi]; nlinarith [sq_nonneg (p-1/2)]
  refine ⟨hv,hi,hbound,?_⟩
  nlinarith [Real.sq_sqrt hv0,Real.sqrt_nonneg (variance Y μ)]

/-- T6(i), actual binary sample variance and the N−1 correction to the
Cohen-d effect bound, for every sample size N≥2 and every binary vector. -/
theorem binary_sample_bound {n : ℕ} (hn : 2 ≤ n) (Y : Fin n → ℝ)
    (hy : ∀ i, Y i = 0 ∨ Y i = 1) :
    sampleVariance Y = (n:ℝ)/((n:ℝ)-1)*sampleMean Y*(1-sampleMean Y) ∧
    sampleVariance Y ≤ (n:ℝ)/(4*((n:ℝ)-1)) ∧
    (1/10:ℝ)*sampleSD Y ≤ (1/20:ℝ)*Real.sqrt ((n:ℝ)/((n:ℝ)-1)) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have hn1 : (n:ℝ)-1 ≠ 0 := by linarith
  have hnpos : 0 < (n:ℝ) := by linarith
  have hn1pos : 0 < (n:ℝ)-1 := by linarith
  have hy2 : (∑ i, Y i^2) = ∑ i, Y i := by
    apply Finset.sum_congr rfl
    intro i hi
    rcases hy i with h | h <;> norm_num [h]
  have he : (∑ i, (Y i-sampleMean Y)^2) =
      (∑ i, Y i^2)-2*sampleMean Y*(∑ i, Y i)+(n:ℝ)*sampleMean Y^2 := by
    calc
      _ = ∑ i, (Y i^2-2*sampleMean Y*Y i+sampleMean Y^2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
          Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hm : (∑ i, Y i) = (n:ℝ)*sampleMean Y := by
    unfold sampleMean
    field_simp
  have hv : sampleVariance Y = (n:ℝ)/((n:ℝ)-1)*sampleMean Y*(1-sampleMean Y) := by
    unfold sampleVariance
    rw [he,hy2,hm]
    field_simp
    <;> ring
  have hc : 0 < (n:ℝ)/((n:ℝ)-1) := div_pos hnpos hn1pos
  have hid : sampleVariance Y = (n:ℝ)/((n:ℝ)-1)*(1/4-(sampleMean Y-1/2)^2) := by
    rw [hv]
    ring
  have hq : (n:ℝ)/(4*((n:ℝ)-1)) = ((n:ℝ)/((n:ℝ)-1))/4 := by
    field_simp
    <;> ring
  have hbound : sampleVariance Y ≤ (n:ℝ)/(4*((n:ℝ)-1)) := by
    rw [hq,hid]
    nlinarith [sq_nonneg (sampleMean Y-1/2)]
  have hv0 : 0 ≤ sampleVariance Y := by
    unfold sampleVariance
    exact div_nonneg (Finset.sum_nonneg (fun i hi => sq_nonneg _)) (le_of_lt hn1pos)
  refine ⟨hv,hbound,?_⟩
  unfold sampleSD
  rw [hq] at hbound
  nlinarith [Real.sq_sqrt hv0,Real.sqrt_nonneg (sampleVariance Y),
    Real.sq_sqrt (le_of_lt hc),Real.sqrt_nonneg ((n:ℝ)/((n:ℝ)-1))]

end
end AronowAudit.P033

