import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Real.Sqrt

noncomputable section
namespace AronowAudit.P041

open Matrix
open scoped BigOperators

/-- "Ordinary least squares estimates on survival" (S11, opening paragraph).
For a full-rank finite real design X, the coefficient vector is
(XᵀX)⁻¹Xᵀy. The formula is supplied by targets P041-T7 and P041-T9;
the paper does not display it. -/
def olsCoefficients {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ y)

/-- The regression residual "eᵢ = yᵢ - xᵢᵀβ̂", P041-T7, P041-T9,
from the deposited OLS specification behind S11 Tables A and B. -/
def olsResidual {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (X : Matrix n k ℝ) (y : n → ℝ) : n → ℝ := y - X *ᵥ olsCoefficients X y

/-- "∑ᵢ eᵢ² xᵢxᵢᵀ", target P041-T9(i), the heteroskedasticity-robust
meat matrix in the S11 regression reproduction. -/
def robustMeat {n k : Type*} [Fintype n] (X : Matrix n k ℝ)
    (u : n → ℝ) : Matrix k k ℝ := fun j l => ∑ i, (u i)^2 * X i j * X i l

/-- "n/(n-k) (XᵀX)⁻¹ (∑ᵢeᵢ²xᵢxᵢᵀ) (XᵀX)⁻¹", target
P041-T7 and P041-T9, the HC1 covariance used by the deposited robust OLS. -/
def hc1Covariance {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  ((Fintype.card n : ℝ) / (Fintype.card n - Fintype.card k)) •
    ((X.transpose * X)⁻¹ * robustMeat X (olsResidual X y) * (X.transpose * X)⁻¹)

/-- P041-T9(i), correcting the S11 phrase "was removed": complementing
the outcome in a full-rank design with an intercept changes β to e₁-β.
Invertibility of XᵀX expresses full column rank over ℝ; Xe₁=1 expresses
that the intercept column is ones. -/
theorem ols_complement_coefficients {n k : Type*} [Fintype n] [Fintype k]
    [DecidableEq k] (X : Matrix n k ℝ) (e₁ : k → ℝ) (S : n → ℝ)
    (hX : IsUnit (X.transpose * X).det) (h₁ : X *ᵥ e₁ = 1) :
    olsCoefficients X (1-S) = e₁ - olsCoefficients X S := by
  unfold olsCoefficients
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
  congr 1
  rw [← h₁, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hX, Matrix.one_mulVec]

/-- P041-T9(i): with an intercept, removal residuals are the negatives of
survival residuals. Consequently the robust meat and HC1 covariances agree. -/
theorem ols_complement_residuals_and_covariance {n k : Type*} [Fintype n]
    [Fintype k] [DecidableEq k] (X : Matrix n k ℝ) (e₁ : k → ℝ) (S : n → ℝ)
    (hX : IsUnit (X.transpose * X).det) (h₁ : X *ᵥ e₁ = 1) :
    olsResidual X (1-S) = -olsResidual X S ∧
    robustMeat X (olsResidual X (1-S)) = robustMeat X (olsResidual X S) ∧
    hc1Covariance X (1-S) = hc1Covariance X S := by
  have hr : olsResidual X (1-S) = -olsResidual X S := by
    unfold olsResidual
    rw [ols_complement_coefficients X e₁ S hX h₁, Matrix.mulVec_sub, h₁]
    ext i
    simp only [Pi.sub_apply, Pi.one_apply, Pi.neg_apply]
    ring
  have hm : robustMeat X (olsResidual X (1-S)) = robustMeat X (olsResidual X S) := by
    rw [hr]
    unfold robustMeat
    simp only [Pi.neg_apply, neg_sq]
    rfl
  refine ⟨hr, hm, ?_⟩
  unfold hc1Covariance
  rw [hm]

/-- P041-T9(ii) bridge: full-rank finite OLS satisfies the normal equations. -/
theorem ols_normal_equations {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (X : Matrix n k ℝ) (y : n → ℝ) (hX : IsUnit (X.transpose * X).det) :
    (X.transpose * X) *ᵥ olsCoefficients X y = X.transpose *ᵥ y := by
  unfold olsCoefficients
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]

/-- XᵀX for S11's positive-fact regression on intercept, positive,
Study 2 and Study 4: 50 treated and 50 controls within each study,
P041-T9(ii), P041-E010. -/
def positiveStudyGram : Matrix (Fin 4) (Fin 4) ℝ :=
  !![300,150,100,100;150,150,50,50;100,50,100,0;100,50,0,100]

/-- P041-T9(ii): balanced treatment within each study makes the
study-adjusted positive-fact OLS slope the pooled difference. The study
survival totals w₂,w₄ may be arbitrary; only the two arm totals matter. -/
theorem positive_balanced_slope (β : Fin 4 → ℝ) (sT sB w₂ w₄ : ℝ)
    (hβ : positiveStudyGram *ᵥ β = ![sT+sB,sT,w₂,w₄]) :
    β 1 = sT/150 - sB/150 := by
  have h0 := congrFun hβ 0
  have h1 := congrFun hβ 1
  norm_num [positiveStudyGram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
  linarith

/-- Four (study,cited) design rows "xᵢ=(1,cᵢ,wᵢ)ᵀ", P041-T7,
P041-E011: (1,U),(1,C),(4,U),(4,C). -/
def citationCellDesign : Matrix (Fin 4) (Fin 3) ℝ :=
  !![1,0,0; 1,1,0; 1,0,1; 1,1,1]

/-- "12,25,23,42" survivors in four cells of 50 (P041-E011;
P041-T7). These are recounted deposited counts, not printed observations. -/
def citationCellSurvivors : Fin 4 → ℝ := ![12,25,23,42]

/-- XᵀX from the four balanced cells, P041-T7(ii), S11 Table A column 2. -/
def citationGram : Matrix (Fin 3) (Fin 3) ℝ :=
  !![200,100,100; 100,100,50; 100,50,100]

/-- (XᵀX)⁻¹ from P041-T7(ii), certified by multiplication below. -/
def citationGramInverse : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3/200,-1/100,-1/100; -1/100,1/50,0; -1/100,0,1/50]

/-- β̂=(21/100,8/25,7/25), P041-T7(ii), from the six-hour S11 fit. -/
def citationBeta : Fin 3 → ℝ := ![21/100,8/25,7/25]

/-- P041-T9(ii): the citation design is balanced within each study;
its normal-equation slope is the pooled cited-minus-uncited survival
difference, independently of the Study 4 survival total. -/
theorem cited_balanced_slope (β : Fin 3 → ℝ) (sT sB w₄ : ℝ)
    (hβ : citationGram *ᵥ β = ![sT+sB,sT,w₄]) :
    β 1 = sT/100 - sB/100 := by
  have h0 := congrFun hβ 0
  have h1 := congrFun hβ 1
  norm_num [citationGram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
  linarith

/-- P041-T9(ii): the two-group former-senator regression with 75
positive and 76 negative facts has slope sT/75-sB/76. -/
theorem former_two_group_slope (β : Fin 2 → ℝ) (sT sB : ℝ)
    (hβ : (!![151,75;75,75] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ β = ![sT+sB,sT]) :
    β 1 = sT/75 - sB/76 := by
  have h0 := congrFun hβ 0
  have h1 := congrFun hβ 1
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
  linarith

/-- Sum of squared residuals of n binary observations, a of them one,
with common fitted value f: "a(1-f)²+(n-a)f²", P041-E011. -/
def binaryCellSSR (n a f : ℝ) : ℝ := a*(1-f)^2 + (n-a)*f^2

/-- P041-T7(ii): the sufficient-statistic matrices really come from the
four cells; the given inverse is two-sided; multiplying gives the printed
0.320 citation slope, also the mean of the within-study differences. -/
theorem citation_ols_exact_fit :
    (fun j l => ∑ i : Fin 4, (50:ℝ) * citationCellDesign i j *
      citationCellDesign i l) = citationGram ∧
    (fun j => ∑ i : Fin 4, citationCellSurvivors i * citationCellDesign i j) =
      ![102,67,65] ∧
    citationGram * citationGramInverse = 1 ∧
    citationGramInverse * citationGram = 1 ∧
    citationGramInverse *ᵥ ![102,67,65] = citationBeta ∧
    citationBeta 1 = 0.320 ∧
    citationBeta 1 = (1/2)*((25-12)/50 + (42-23)/50) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext j l; fin_cases j <;> fin_cases l <;>
      norm_num [citationCellDesign, citationGram, Fin.sum_univ_succ]
  · ext j; fin_cases j <;>
      norm_num [citationCellSurvivors, citationCellDesign, Fin.sum_univ_succ]
  · ext j l; fin_cases j <;> fin_cases l <;>
      norm_num [citationGram, citationGramInverse, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext j l; fin_cases j <;> fin_cases l <;>
      norm_num [citationGram, citationGramInverse, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext j; fin_cases j <;>
      norm_num [citationGramInverse, citationBeta, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num [citationBeta]
  · norm_num [citationBeta]

/-- P041-T7(ii): the displayed inverse is the actual matrix inverse,
not merely a matrix given that name; multiplication certifies it. -/
theorem citation_gram_inverse_is_inverse : citationGram⁻¹ = citationGramInverse := by
  exact Matrix.inv_eq_right_inv citation_ols_exact_fit.2.2.1

/-- P041-T7(iii): the four fitted probabilities and four residual square
sums, their total, and the citation influence row squared, 1/10000 in
every cell. This yields the exact HC1 citation variance 2047/492500. -/
theorem citation_hc1_exact_variance :
    (fun i => citationCellDesign i ⬝ᵥ citationBeta) = ![21/100,53/100,49/100,81/100] ∧
    binaryCellSSR 50 12 (21/100) = 1833/200 ∧
    binaryCellSSR 50 25 (53/100) = 2509/200 ∧
    binaryCellSSR 50 23 (49/100) = 2493/200 ∧
    binaryCellSSR 50 42 (81/100) = 1353/200 ∧
    ((1833/200 + 2509/200 + 2493/200 + 1353/200 : ℝ)) = 2047/50 ∧
    (∀ i : Fin 4, (citationGramInverse 1 ⬝ᵥ citationCellDesign i)^2 = 1/10000) ∧
    (200/197 : ℝ) * (∑ i : Fin 4,
      binaryCellSSR 50 (citationCellSurvivors i) (citationCellDesign i ⬝ᵥ citationBeta) *
      (citationGramInverse 1 ⬝ᵥ citationCellDesign i)^2) = 2047/492500 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i; fin_cases i <;>
      norm_num [citationCellDesign, citationBeta, dotProduct, Fin.sum_univ_succ]
  · norm_num [binaryCellSSR]
  · norm_num [binaryCellSSR]
  · norm_num [binaryCellSSR]
  · norm_num [binaryCellSSR]
  · norm_num
  · intro i; fin_cases i <;>
      norm_num [citationGramInverse, citationCellDesign, dotProduct, Fin.sum_univ_succ]
  · norm_num [binaryCellSSR, citationCellSurvivors, citationCellDesign, citationBeta,
      citationGramInverse, dotProduct, Fin.sum_univ_succ]

/-- P041-T7(i),(iv),(v), correcting (0.645) to (0.064) in S11 Table A:
the printed t is below 1; the actual HC1 square root rounds to 0.064;
its square differs from the typo; the corrected |t| exceeds 4.89 and 2.61.
No Student-t or normal tail evaluation is asserted here. -/
theorem corrected_citation_standard_error :
    (0.320/0.645 : ℝ) = 64/129 ∧ (64/129 : ℝ) < 1 ∧
    (0.0635 : ℝ)^2 ≤ 2047/492500 ∧ (2047/492500 : ℝ) < 0.0645^2 ∧
    0.0635 ≤ Real.sqrt (2047/492500) ∧ Real.sqrt (2047/492500) < 0.0645 ∧
    (0.645 : ℝ)^2 = 16641/40000 ∧ (16641/40000 : ℝ) ≠ 2047/492500 ∧
    ((8/25 : ℝ)^2 / (2047/492500)) = 50432/2047 ∧
    (24 : ℝ) < 50432/2047 ∧ (2.61 : ℝ)^2 < 24 ∧
    4.89 < (8/25 : ℝ) / Real.sqrt (2047/492500) ∧
    2.61 < (8/25 : ℝ) / Real.sqrt (2047/492500) := by
  have hs : 0 < Real.sqrt (2047/492500) := Real.sqrt_pos.2 (by norm_num)
  have he := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2047/492500)
  have hl : (0.0635:ℝ) ≤ Real.sqrt (2047/492500) := by nlinarith
  have hu : Real.sqrt (2047/492500) < (0.0645:ℝ) := by nlinarith
  have ht : (4.89:ℝ) < (8/25:ℝ) / Real.sqrt (2047/492500) := by
    apply (lt_div_iff₀ hs).2
    nlinarith
  have ht2 : (2.61:ℝ) < (8/25:ℝ) / Real.sqrt (2047/492500) :=
    lt_trans (by norm_num : (2.61:ℝ) < 4.89) ht
  simp only [hl, hu, ht, ht2, and_true]
  norm_num


/-- Treatment-minus-comparison proportion surviving, P041-T9(ii), S11.
In the balanced study-adjusted P/C designs this equals the treatment slope;
in the unadjusted F design it is the ordinary two-group treatment slope. -/
def armSurvivalDifference (nT nB sT sB : ℝ) : ℝ := sT/nT - sB/nB

/-- Three-decimal enclosure "v ± 0.0005", targets standing assumption S7. -/
def withinPrintedPrecision (x v : ℝ) : Prop := |x-v| ≤ 0.0005

/-- P041-T9(ii)-(iii): all twelve exact survival contrasts reproduce the
printed coefficients within 0.0005; their negatives fail that enclosure.
The three repeated former-senator rows have the same counts. -/
theorem s11_survival_slopes_and_not_removal :
    armSurvivalDifference 150 150 105 88 = 17/150 ∧
    armSurvivalDifference 150 150 98 75 = 23/150 ∧
    armSurvivalDifference 150 150 90 68 = 11/75 ∧
    armSurvivalDifference 150 150 68 49 = 19/150 ∧
    armSurvivalDifference 100 100 67 35 = 8/25 ∧
    armSurvivalDifference 100 100 63 26 = 37/100 ∧
    armSurvivalDifference 100 100 58 19 = 39/100 ∧
    armSurvivalDifference 100 100 34 11 = 23/100 ∧
    armSurvivalDifference 75 76 72 75 = -51/1900 ∧
    armSurvivalDifference 75 76 68 73 = -307/5700 ∧
    (∀ p ∈ ({(17/150,0.113),(23/150,0.153),(11/75,0.147),(19/150,0.127),
      (8/25,0.320),(37/100,0.370),(39/100,0.390),(23/100,0.230),
      (-51/1900,-0.027),(-307/5700,-0.054)} : Finset (ℝ × ℝ)),
      p.1 ≠ 0 ∧ withinPrintedPrecision p.1 p.2 ∧
        ¬ withinPrintedPrecision (-p.1) p.2) := by
  norm_num [armSurvivalDifference, withinPrintedPrecision]

end AronowAudit.P041

