import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
P023: A Note on Close Elections and Regression Analysis of the Party Incumbency
Advantage. Printed pages and PDF pages coincide. Definitions of OLS below use
the normal equations, the exact characterization of unconstrained least squares
over a finite real design. Empty nuisance bins cause no division by zero.
-/

namespace AronowAudit.P023

noncomputable section
open scoped BigOperators
open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Equation (1), p. 5: "includes all N elections". The index type represents
the observed election pairs (i,t); `dot` is the unnormalized finite sum. -/
def dot (a b : ι → ℝ) : ℝ := ∑ i, a i * b i

/-- Equation (1), p. 5: α + β DemWin + ∑ γ_j X_j. Columns include the
intercept and DemWin, and all coefficients are unconstrained real numbers. -/
def predict (X : ι → κ → ℝ) (c : κ → ℝ) (i : ι) : ℝ := ∑ j, X i j * c j

/-- "the OLS estimator of β in (2)", pp. 6–7: a solution of all normal
equations for the finite least-squares regression. This permits nonunique
nuisance coefficients when a bin is empty. -/
def IsOLS (X : ι → κ → ℝ) (y : ι → ℝ) (c : κ → ℝ) : Prop :=
  ∀ j, dot (fun i => X i j) (fun i => y i - predict X c i) = 0

/-- Full column rank means that the only coefficient vector giving zero fitted
values at every observed election is zero. P023-T1(i), T2(i), and T3(b). -/
def FullRank (X : ι → κ → ℝ) : Prop :=
  ∀ c, (∀ i, predict X c i = 0) → c = 0

/-- OLS as an estimator: choose a normal-equation solution. Existence for
full-rank designs is proved below. -/
def olsCoefficients (X : ι → κ → ℝ) (y : ι → ℝ) : κ → ℝ :=
  Classical.epsilon (fun c => IsOLS X y c)

/-- Equation (2), p. 6: columns (1,DemWin,DemVot,...,DemVot^J). Column 1
is the party-win coefficient; column 0 is the intercept. -/
def polynomialDesign (J : ℕ) (x d : ι → ℝ) : ι → Fin (J + 2) → ℝ :=
  fun i j => if j.val = 0 then 1 else if j.val = 1 then d i else x i ^ (j.val - 1)

/-- Proposition 2, p. 7: "the OLS estimator of β in (2)". -/
def polynomialOLS (J : ℕ) (x d y : ι → ℝ) : ℝ :=
  olsCoefficients (polynomialDesign J x d) y ⟨1, by omega⟩

/-- p. 6: "U_b ≡ {it: −k < DemVot_it ≤ k}". The lower endpoint is open
and the upper endpoint is closed, exactly as printed. -/
def close (k : ℝ) (x : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => -k < x i ∧ x i ≤ k)

/-- Remark to Condition 3, pp. 5–6: the displayed difference of Democratic
winner and loser outcome means in U_b. It is used when both counts are positive;
Lean's total division extends it to empty sides for sample sequences only. -/
def rd (k : ℝ) (x d y : ι → ℝ) : ℝ :=
  (∑ i ∈ close k x, d i * y i) / (∑ i ∈ close k x, d i) -
  (∑ i ∈ close k x, (1 - d i) * y i) / (∑ i ∈ close k x, (1 - d i))

/-- Condition 1, p. 5: there is an election strictly on each side of zero
inside the bandwidth. This is sufficient and no necessity is asserted. -/
def Condition1 (k : ℝ) (x : ι → ℝ) : Prop :=
  (∃ i, 0 < x i ∧ x i < k) ∧ (∃ i, -k < x i ∧ x i < 0)

/-- Standing two-party assumption, p. 5: DemWin is binary and agrees with
the sign of DemVot away from ties. A tie at zero may have either indicator. -/
def TwoParty (x d : ι → ℝ) : Prop :=
  (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧ (∀ i, d i = 0 ∨ d i = 1) ∧
  (∀ i, 0 < x i → d i = 1) ∧ (∀ i, x i < 0 → d i = 0)

/-- Condition 2, p. 5: "J = 2⌈(1-k)/(2k)⌉". The ceiling is nonnegative
for the prescribed bandwidth 0 < k < 1. -/
def binCount (k : ℝ) : ℕ := 2 * Nat.ceil ((1 - k) / (2 * k))

/-- Condition 2, p. 5, and Appendix A's reference bin, p. 9:
X_j = I[2j-J-1 < DemVot/k ≤ 2j-J+1] for j≥1;
X_0 = I[−J−1 ≤ DemVot/k ≤ −J+1]. -/
def inBin (k : ℝ) (j : ℕ) (x : ℝ) : Prop :=
  if j = 0 then -(binCount k : ℝ) - 1 ≤ x / k ∧ x / k ≤ -(binCount k : ℝ) + 1
  else 2 * (j : ℝ) - binCount k - 1 < x / k ∧ x / k ≤ 2 * (j : ℝ) - binCount k + 1

/-- The Condition 2 indicator X_ijt (pp. 5,9), with empty-bin indicators zero. -/
def binIndicator (k : ℝ) (j : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if inBin k j x then 1 else 0

/-- The coarsened regression of Condition 2, p. 5: (1,DemWin,X_1,...,X_J). -/
def coarsenedDesign (k : ℝ) (x d : ι → ℝ) : ι → Fin (binCount k + 2) → ℝ :=
  fun i j => if j.val = 0 then 1 else if j.val = 1 then d i
    else binIndicator k (j.val - 1) (x i)

/-- Sole reliance on close-election outcomes (pp. 3 and 7): holding margins
fixed, agreeing on U_b implies equal estimates. -/
def Localized (k : ℝ) (x : ι → ℝ) (est : (ι → ℝ) → ℝ) : Prop :=
  ∀ y y', (∀ i ∈ close k x, y i = y' i) → est y = est y'

/-- Finite-sum linearity used in the FWL identity (Appendix A, p. 9). -/
theorem dot_sub_right (a b c : ι → ℝ) :
    dot a (fun i => b i - c i) = dot a b - dot a c := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

/-- A linear combination of regressor columns pairs with an outcome by the
same linear combination of the column-outcome sums. Appendix A's FWL step. -/
theorem dot_predict_left (X : ι → κ → ℝ) (c : κ → ℝ) (z : ι → ℝ) :
    dot (predict X c) z = ∑ j, c j * dot (fun i => X i j) z := by
  unfold dot predict
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The right-hand counterpart of the finite FWL column-sum identity. -/
theorem dot_predict_right (X : ι → κ → ℝ) (c : κ → ℝ) (z : ι → ℝ) :
    dot z (predict X c) = ∑ j, c j * dot z (fun i => X i j) := by
  unfold dot predict
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A finite dual certificate proves the actual OLS coefficient on a selected
column for every outcome and every normal-equation solution (T1(iii), T2(iii)). -/
theorem ols_weight_certificate [DecidableEq κ] (X : ι → κ → ℝ)
    (w : ι → ℝ) (a : κ → ℝ) (q : κ)
    (hspan : w = predict X a)
    (hmom : ∀ j, dot w (fun i => X i j) = if j = q then 1 else 0)
    (y : ι → ℝ) (c : κ → ℝ) (hc : IsOLS X y c) : c q = dot w y := by
  have hz : dot w (fun i => y i - predict X c i) = 0 := by
    rw [hspan, dot_predict_left]
    apply Finset.sum_eq_zero
    intro j _
    rw [hc j, mul_zero]
  have hp : dot w (predict X c) = c q := by
    rw [dot_predict_right]
    simp_rw [hmom]
    simp
  rw [dot_sub_right, hp] at hz
  linarith


/-- Under full column rank the finite OLS normal equations have a solution for
every real outcome vector, as used in Proposition 2's finite examples. -/
theorem ols_exists_of_fullRank (X : ι → κ → ℝ) (hX : FullRank X) (y : ι → ℝ) :
    ∃ c, IsOLS X y c := by
  classical
  let A : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) :=
    { toFun := fun c j => dot (fun i => X i j) (predict X c)
      map_add' := by
        intro a b
        funext j
        simp [dot, predict, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        funext j
        simp [dot, predict, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm] }
  have hker : ∀ c, A c = 0 → c = 0 := by
    intro c hc
    have hn : dot (predict X c) (predict X c) = 0 := by
      rw [dot_predict_left]
      apply Finset.sum_eq_zero
      intro j _
      have hj : dot (fun i => X i j) (predict X c) = 0 := congrFun hc j
      rw [hj, mul_zero]
    apply hX c
    intro i
    have hs : ∑ i, predict X c i * predict X c i = 0 := hn
    exact (Finset.sum_mul_self_eq_zero_iff Finset.univ (predict X c)).mp hs i (Finset.mem_univ i)
  have hinj : Function.Injective A := by
    intro a b hab
    have he : a - b = 0 := hker _ (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp he
  obtain ⟨c, hc⟩ := LinearMap.surjective_of_injective hinj (fun j => dot (fun i => X i j) y)
  refine ⟨c, ?_⟩
  intro j
  rw [dot_sub_right]
  have he : dot (fun i => X i j) (predict X c) = dot (fun i => X i j) y := congrFun hc j
  rw [he, sub_self]

/-- The chosen finite coefficient vector really satisfies the normal equations
under full column rank; T1 and T2 consequently quantify over every outcome. -/
theorem chosen_ols_spec (X : ι → κ → ℝ) (hX : FullRank X) (y : ι → ℝ) :
    IsOLS X y (olsCoefficients X y) := by
  exact Classical.epsilon_spec (ols_exists_of_fullRank X hX y)

/-- Finite witness for P023-T1: explicit DemVot, DemWin, baseline DV,
perturbed DV, and OLS weights. -/
def linearX : Fin 6 → ℝ := ![(-3 / 4 : ℝ), (-1 / 4 : ℝ), (-1 / 400 : ℝ), (1 / 400 : ℝ), (1 / 4 : ℝ), (3 / 4 : ℝ)]
/-- P023-E001: explicit linearD for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def linearD : Fin 6 → ℝ := ![0, 0, 0, 1, 1, 1]
/-- P023-E001: explicit linearY for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def linearY : Fin 6 → ℝ := ![(37 / 80 : ℝ), (39 / 80 : ℝ), (3999 / 8000 : ℝ), (4801 / 8000 : ℝ), (49 / 80 : ℝ), (51 / 80 : ℝ)]
/-- P023-E001: explicit linearYprime for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def linearYprime : Fin 6 → ℝ := ![(37 / 80 : ℝ), (39 / 80 : ℝ), (3999 / 8000 : ℝ), (4801 / 8000 : ℝ), (49 / 80 : ℝ), (259 / 400 : ℝ)]
/-- P023-E001: explicit linearW for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def linearW : Fin 6 → ℝ := ![(20299 / 139202 : ℝ), (-59901 / 139202 : ℝ), (-49800 / 69601 : ℝ), (49800 / 69601 : ℝ), (59901 / 139202 : ℝ), (-20299 / 139202 : ℝ)]
/-- P023-E001: explicit linearDual for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def linearDual : Fin 3 → ℝ := ![(-100001 / 139202 : ℝ), (100001 / 69601 : ℝ), (-80200 / 69601 : ℝ)]
/-- P023-E001: explicit linearExact for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def linearExact : Fin 3 → ℝ := ![(1 / 2 : ℝ), (1 / 10 : ℝ), (1 / 20 : ℝ)]

/-- P023-T1(i): the design has rank 3. -/
theorem linear_fullRank : FullRank (polynomialDesign 1 linearX linearD) := by
  intro c h
  have h0 := h 0
  norm_num [predict, polynomialDesign, linearX, linearD, Fin.sum_univ_succ] at h0
  have h1 := h 1
  norm_num [predict, polynomialDesign, linearX, linearD, Fin.sum_univ_succ] at h1
  have h2 := h 5
  norm_num [predict, polynomialDesign, linearX, linearD, Fin.sum_univ_succ] at h2
  funext j
  fin_cases j
  · dsimp
    linear_combination (-1 / 2 : ℝ) * h0 + (3 / 2 : ℝ) * h1
  · dsimp
    linear_combination 2 * h0 + -3 * h1 + 1 * h2
  · dsimp
    linear_combination -2 * h0 + 2 * h1

/-- The exact weight vector belongs to the polynomial-regressor column span, as required by the FWL certificate. -/
theorem linear_dual_span : linearW = predict (polynomialDesign 1 linearX linearD) linearDual := by
  funext i
  fin_cases i <;> norm_num [predict, polynomialDesign, linearX, linearD, linearW, linearDual, Fin.sum_univ_succ]

/-- The weight vector pairs to one with DemWin and to zero with every polynomial column, including the intercept. -/
theorem linear_dual_moments (j : Fin 3) : dot linearW (fun i => polynomialDesign 1 linearX linearD i j) = if j = 1 then 1 else 0 := by
  fin_cases j <;> norm_num [dot, polynomialDesign, linearX, linearD, linearW, Fin.sum_univ_succ]

/-- P023-T1(iii): for every real outcome vector, the actual polynomial OLS coefficient equals the displayed weighted sum. -/
theorem linear_weights (z : Fin 6 → ℝ) : polynomialOLS 1 linearX linearD z = dot linearW z := by
  exact ols_weight_certificate (polynomialDesign 1 linearX linearD) linearW linearDual 1
    linear_dual_span linear_dual_moments z _ (chosen_ols_spec _ linear_fullRank z)

/-- P023-T1(ii): the baseline is exactly equation (2) with the printed witness coefficients and u=0. -/
theorem linear_exact_model : linearY = predict (polynomialDesign 1 linearX linearD) linearExact := by
  funext i
  fin_cases i <;> norm_num [predict, polynomialDesign, linearX, linearD, linearY, linearExact, Fin.sum_univ_succ]

/-- P023-T1: precisely the two central elections belong to U_b. -/
theorem linear_window : close (1 / 200 : ℝ) linearX = ({2, 3} : Finset (Fin 6)) := by
  ext i
  fin_cases i <;> norm_num [close, linearX]

/-- P023-T1: all margins and win indicators satisfy the standing two-party assumptions and Condition 1. -/
theorem linear_hypotheses : TwoParty linearX linearD ∧ Condition1 (1 / 200 : ℝ) linearX := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals intro i; fin_cases i <;> norm_num [TwoParty, linearX, linearD]
  · exact ⟨⟨3, by norm_num [linearX]⟩, ⟨2, by norm_num [linearX]⟩⟩

/-- Every outcome in both finite witness vectors lies strictly between zero and one. -/
theorem linear_outcomes_bounded (i : Fin 6) : 0 < linearY i ∧ linearY i < 1 ∧ 0 < linearYprime i ∧ linearYprime i < 1 := by
  fin_cases i <;> norm_num [linearY, linearYprime]

/-- The baseline and changed outcome agree at every close election. -/
theorem linear_agrees_on_close : ∀ i ∈ close (1 / 200 : ℝ) linearX, linearY i = linearYprime i := by
  rw [linear_window]
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> norm_num [linearY, linearYprime]

/-- P023-T1(ii),(iv): the distant perturbation changes the polynomial coefficient by a nonzero exact rational number. -/
theorem linear_coefficient_values : polynomialOLS 1 linearX linearD linearY = 1 / 10 ∧
    polynomialOLS 1 linearX linearD linearYprime = (1371721 / 13920200 : ℝ) ∧
    polynomialOLS 1 linearX linearD linearYprime - polynomialOLS 1 linearX linearD linearY = (-20299 / 13920200 : ℝ) ∧ (-20299 / 13920200 : ℝ) ≠ 0 := by
  rw [linear_weights, linear_weights]
  norm_num [dot, linearW, linearY, linearYprime, Fin.sum_univ_succ]

/-- P023-T1(v): both degree-0 rectangular RD estimates have the same exact value. -/
theorem linear_rd_values : rd (1 / 200 : ℝ) linearX linearD linearY = (401 / 4000 : ℝ) ∧
    rd (1 / 200 : ℝ) linearX linearD linearYprime = (401 / 4000 : ℝ) := by
  norm_num [rd, linear_window, linearD, linearY, linearYprime]

/-- P023-T1(vii): a correctly specified polynomial regression is not solely a function of close-election outcomes. The same margins meet Condition 1 and the baseline is exactly specified. -/
theorem linear_nonlocal : ¬ Localized (1 / 200 : ℝ) linearX (polynomialOLS 1 linearX linearD) := by
  intro h
  have he := h linearY linearYprime linear_agrees_on_close
  rw [linear_coefficient_values.1, linear_coefficient_values.2.1] at he
  norm_num at he

/-- Finite witness for P023-T2: explicit DemVot, DemWin, baseline DV,
perturbed DV, and OLS weights. -/
def degree7X : Fin 16 → ℝ := ![-1, (-7 / 8 : ℝ), (-3 / 4 : ℝ), (-5 / 8 : ℝ), (-1 / 2 : ℝ), (-3 / 8 : ℝ), (-1 / 4 : ℝ), (-1 / 8 : ℝ), (1 / 8 : ℝ), (1 / 4 : ℝ), (3 / 8 : ℝ), (1 / 2 : ℝ), (5 / 8 : ℝ), (3 / 4 : ℝ), (7 / 8 : ℝ), 1]
/-- P023-E001: explicit degree7D for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def degree7D : Fin 16 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1]
/-- P023-E001: explicit degree7Y for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def degree7Y : Fin 16 → ℝ := ![(11 / 25 : ℝ), (94859017 / 209715200 : ℝ), (755573 / 1638400 : ℝ), (3929035 / 8388608 : ℝ), (6079 / 12800 : ℝ), (100923253 / 209715200 : ℝ), (798719 / 1638400 : ℝ), (103546879 / 209715200 : ℝ), (127139841 / 209715200 : ℝ), (1003521 / 1638400 : ℝ), (129763467 / 209715200 : ℝ), (8001 / 12800 : ℝ), (26492169 / 41943040 : ℝ), (1046667 / 1638400 : ℝ), (135827703 / 209715200 : ℝ), (33 / 50 : ℝ)]
/-- P023-E001: explicit degree7Yprime for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def degree7Yprime : Fin 16 → ℝ := ![(11 / 25 : ℝ), (94859017 / 209715200 : ℝ), (755573 / 1638400 : ℝ), (3929035 / 8388608 : ℝ), (6079 / 12800 : ℝ), (100923253 / 209715200 : ℝ), (798719 / 1638400 : ℝ), (103546879 / 209715200 : ℝ), (127139841 / 209715200 : ℝ), (1003521 / 1638400 : ℝ), (129763467 / 209715200 : ℝ), (8001 / 12800 : ℝ), (26492169 / 41943040 : ℝ), (1046667 / 1638400 : ℝ), (135827703 / 209715200 : ℝ), (67 / 100 : ℝ)]
/-- P023-E001: explicit degree7W for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def degree7W : Fin 16 → ℝ := ![(-175 / 1607 : ℝ), (725 / 1607 : ℝ), (-685 / 1607 : ℝ), (-643 / 1607 : ℝ), (554 / 1607 : ℝ), (1289 / 1607 : ℝ), (239 / 1607 : ℝ), (-2911 / 1607 : ℝ), (2911 / 1607 : ℝ), (-239 / 1607 : ℝ), (-1289 / 1607 : ℝ), (-554 / 1607 : ℝ), (643 / 1607 : ℝ), (685 / 1607 : ℝ), (-725 / 1607 : ℝ), (175 / 1607 : ℝ)]
/-- P023-E001: explicit degree7Dual for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def degree7Dual : Fin 9 → ℝ := ![(-7429 / 1607 : ℝ), (14858 / 1607 : ℝ), (-1335266 / 56245 : ℝ), 0, (131424 / 1607 : ℝ), 0, (-970752 / 8035 : ℝ), 0, (655360 / 11249 : ℝ)]
/-- P023-E001: explicit degree7Exact for the fixed finite witness; polynomial regression (2), p. 6, and U_b, p. 6. -/
def degree7Exact : Fin 9 → ℝ := ![(1 / 2 : ℝ), (1 / 10 : ℝ), (1 / 20 : ℝ), 0, 0, 0, 0, 0, (1 / 100 : ℝ)]

/-- P023-T2(i): the design has rank 9. -/
theorem degree7_fullRank : FullRank (polynomialDesign 7 degree7X degree7D) := by
  intro c h
  have h0 := h 0
  norm_num [predict, polynomialDesign, degree7X, degree7D, Fin.sum_univ_succ] at h0
  have h1 := h 1
  norm_num [predict, polynomialDesign, degree7X, degree7D, Fin.sum_univ_succ] at h1
  have h2 := h 2
  norm_num [predict, polynomialDesign, degree7X, degree7D, Fin.sum_univ_succ] at h2
  have h3 := h 3
  norm_num [predict, polynomialDesign, degree7X, degree7D, Fin.sum_univ_succ] at h3
  have h4 := h 4
  norm_num [predict, polynomialDesign, degree7X, degree7D, Fin.sum_univ_succ] at h4
  have h5 := h 5
  norm_num [predict, polynomialDesign, degree7X, degree7D, Fin.sum_univ_succ] at h5
  have h6 := h 6
  norm_num [predict, polynomialDesign, degree7X, degree7D, Fin.sum_univ_succ] at h6
  have h7 := h 7
  norm_num [predict, polynomialDesign, degree7X, degree7D, Fin.sum_univ_succ] at h7
  have h8 := h 15
  norm_num [predict, polynomialDesign, degree7X, degree7D, Fin.sum_univ_succ] at h8
  funext j
  fin_cases j
  · dsimp
    linear_combination -1 * h0 + 8 * h1 + -28 * h2 + 56 * h3 + -70 * h4 + 56 * h5 + -28 * h6 + 8 * h7
  · dsimp
    linear_combination 6435 * h0 + -48048 * h1 + 154440 * h2 + -277200 * h3 + 300300 * h4 + -196560 * h5 + 72072 * h6 + -11440 * h7 + 1 * h8
  · dsimp
    linear_combination (-726 / 35 : ℝ) * h0 + (824 / 5 : ℝ) * h1 + (-8572 / 15 : ℝ) * h2 + 1128 * h3 + -1382 * h4 + (16024 / 15 : ℝ) * h5 + (-2484 / 5 : ℝ) * h6 + (3848 / 35 : ℝ) * h7
  · dsimp
    linear_combination (-7504 / 45 : ℝ) * h0 + (59024 / 45 : ℝ) * h1 + -4488 * h2 + (78256 / 9 : ℝ) * h3 + (-93248 / 9 : ℝ) * h4 + (38256 / 5 : ℝ) * h5 + (-146824 / 45 : ℝ) * h6 + (5584 / 9 : ℝ) * h7
  · dsimp
    linear_combination (-30944 / 45 : ℝ) * h0 + (240128 / 45 : ℝ) * h1 + (-89696 / 5 : ℝ) * h2 + (305408 / 9 : ℝ) * h3 + (-351776 / 9 : ℝ) * h4 + (137216 / 5 : ℝ) * h5 + (-489248 / 45 : ℝ) * h6 + (84224 / 45 : ℝ) * h7
  · dsimp
    linear_combination (-14336 / 9 : ℝ) * h0 + (109312 / 9 : ℝ) * h1 + -39936 * h2 + (660736 / 9 : ℝ) * h3 + (-733184 / 9 : ℝ) * h4 + 54528 * h5 + (-183296 / 9 : ℝ) * h6 + (29440 / 9 : ℝ) * h7
  · dsimp
    linear_combination (-94208 / 45 : ℝ) * h0 + (702464 / 45 : ℝ) * h1 + (-249856 / 5 : ℝ) * h2 + (800768 / 9 : ℝ) * h3 + (-856064 / 9 : ℝ) * h4 + (305152 / 5 : ℝ) * h5 + (-978944 / 45 : ℝ) * h6 + (149504 / 45 : ℝ) * h7
  · dsimp
    linear_combination (-65536 / 45 : ℝ) * h0 + (475136 / 45 : ℝ) * h1 + -32768 * h2 + (507904 / 9 : ℝ) * h3 + (-524288 / 9 : ℝ) * h4 + (180224 / 5 : ℝ) * h5 + (-557056 / 45 : ℝ) * h6 + (16384 / 9 : ℝ) * h7
  · dsimp
    linear_combination (-131072 / 315 : ℝ) * h0 + (131072 / 45 : ℝ) * h1 + (-131072 / 15 : ℝ) * h2 + (131072 / 9 : ℝ) * h3 + (-131072 / 9 : ℝ) * h4 + (131072 / 15 : ℝ) * h5 + (-131072 / 45 : ℝ) * h6 + (131072 / 315 : ℝ) * h7

/-- The exact weight vector belongs to the polynomial-regressor column span, as required by the FWL certificate. -/
theorem degree7_dual_span : degree7W = predict (polynomialDesign 7 degree7X degree7D) degree7Dual := by
  funext i
  fin_cases i <;> norm_num [predict, polynomialDesign, degree7X, degree7D, degree7W, degree7Dual, Fin.sum_univ_succ]

/-- The weight vector pairs to one with DemWin and to zero with every polynomial column, including the intercept. -/
theorem degree7_dual_moments (j : Fin 9) : dot degree7W (fun i => polynomialDesign 7 degree7X degree7D i j) = if j = 1 then 1 else 0 := by
  fin_cases j <;> norm_num [dot, polynomialDesign, degree7X, degree7D, degree7W, Fin.sum_univ_succ]

/-- P023-T2(iii): for every real outcome vector, the actual polynomial OLS coefficient equals the displayed weighted sum. -/
theorem degree7_weights (z : Fin 16 → ℝ) : polynomialOLS 7 degree7X degree7D z = dot degree7W z := by
  exact ols_weight_certificate (polynomialDesign 7 degree7X degree7D) degree7W degree7Dual 1
    degree7_dual_span degree7_dual_moments z _ (chosen_ols_spec _ degree7_fullRank z)

/-- P023-T2(ii): the baseline is exactly equation (2) with the printed witness coefficients and u=0. -/
theorem degree7_exact_model : degree7Y = predict (polynomialDesign 7 degree7X degree7D) degree7Exact := by
  funext i
  fin_cases i <;> norm_num [predict, polynomialDesign, degree7X, degree7D, degree7Y, degree7Exact, Fin.sum_univ_succ]

/-- P023-T2: precisely the two central elections belong to U_b. -/
theorem degree7_window : close (1 / 5 : ℝ) degree7X = ({7, 8} : Finset (Fin 16)) := by
  ext i
  fin_cases i <;> norm_num [close, degree7X]

/-- P023-T2: all margins and win indicators satisfy the standing two-party assumptions and Condition 1. -/
theorem degree7_hypotheses : TwoParty degree7X degree7D ∧ Condition1 (1 / 5 : ℝ) degree7X := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals intro i; fin_cases i <;> norm_num [TwoParty, degree7X, degree7D]
  · exact ⟨⟨8, by norm_num [degree7X]⟩, ⟨7, by norm_num [degree7X]⟩⟩

/-- Every outcome in both finite witness vectors lies strictly between zero and one. -/
theorem degree7_outcomes_bounded (i : Fin 16) : 0 < degree7Y i ∧ degree7Y i < 1 ∧ 0 < degree7Yprime i ∧ degree7Yprime i < 1 := by
  fin_cases i <;> norm_num [degree7Y, degree7Yprime]

/-- The baseline and changed outcome agree at every close election. -/
theorem degree7_agrees_on_close : ∀ i ∈ close (1 / 5 : ℝ) degree7X, degree7Y i = degree7Yprime i := by
  rw [degree7_window]
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> norm_num [degree7Y, degree7Yprime]

/-- P023-T2(ii),(iv): the distant perturbation changes the polynomial coefficient by a nonzero exact rational number. -/
theorem degree7_coefficient_values : polynomialOLS 7 degree7X degree7D degree7Y = 1 / 10 ∧
    polynomialOLS 7 degree7X degree7D degree7Yprime = (3249 / 32140 : ℝ) ∧
    polynomialOLS 7 degree7X degree7D degree7Yprime - polynomialOLS 7 degree7X degree7D degree7Y = (7 / 6428 : ℝ) ∧ (7 / 6428 : ℝ) ≠ 0 := by
  rw [degree7_weights, degree7_weights]
  norm_num [dot, degree7W, degree7Y, degree7Yprime, Fin.sum_univ_succ]

/-- P023-T2(v): both degree-0 rectangular RD estimates have the same exact value. -/
theorem degree7_rd_values : rd (1 / 5 : ℝ) degree7X degree7D degree7Y = (11796481 / 104857600 : ℝ) ∧
    rd (1 / 5 : ℝ) degree7X degree7D degree7Yprime = (11796481 / 104857600 : ℝ) := by
  norm_num [rd, degree7_window, degree7D, degree7Y, degree7Yprime]

/-- P023-T2(vii): a correctly specified polynomial regression is not solely a function of close-election outcomes. The same margins meet Condition 1 and the baseline is exactly specified. -/
theorem degree7_nonlocal : ¬ Localized (1 / 5 : ℝ) degree7X (polynomialOLS 7 degree7X degree7D) := by
  intro h
  have he := h degree7Y degree7Yprime degree7_agrees_on_close
  rw [degree7_coefficient_values.1, degree7_coefficient_values.2.1] at he
  norm_num at he

/-- P023-T2(iii): every one of the sixteen polynomial OLS outcome weights is nonzero. -/
theorem degree7_all_weights_nonzero (i : Fin 16) : degree7W i ≠ 0 := by
  fin_cases i <;> norm_num [degree7W]

/-- Appendix A, p. 9: the bins Ũ_j partition observed election pairs. A per-bin
intercept is the redundant parametrization of the intercept plus X_1,...,X_J;
its fitted-value space is exactly that of Condition 2. -/
def binLabel (k x : ℝ) : Fin (binCount k + 1) :=
  ⟨min (binCount k) (Nat.ceil ((x / k + (binCount k : ℝ) - 1) / 2)),
    Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩

/-- Appendix A, p. 9: "U_b = Ũ_{J/2}". -/
def centralLabel (k : ℝ) : Fin (binCount k + 1) :=
  ⟨Nat.ceil ((1 - k) / (2 * k)), by unfold binCount; omega⟩

/-- OLS with one intercept per bin and a common party-win coefficient. This
is the same nuisance span as equation (1) under Condition 2 (pp. 5,9).
All bin normal equations are retained; empty-bin equations are just 0=0. -/
def IsBinOLS {η : Type*} [Fintype η] [DecidableEq η]
    (B : ι → η) (d y : ι → ℝ) (a : η → ℝ) (β : ℝ) : Prop :=
  (∀ j, (∑ i, if B i = j then y i - a (B i) - β * d i else 0) = 0) ∧
  (∑ i, d i * (y i - a (B i) - β * d i)) = 0

/-- The Democratic party coefficient of Condition 2, p. 5, as a relation
rather than a choice of nuisance coefficients. This remains meaningful with
empty bins; every fit is included. -/
def CoarsenedOLS (k : ℝ) (x d y : ι → ℝ) (β : ℝ) : Prop :=
  ∃ a, IsBinOLS (fun i => binLabel k (x i)) d y a β

/-- Finite exact bin-regression identity underlying Proposition 1. For every
partition with binary treatment constant in the noncentral bins, all OLS
solutions give the difference in winner and loser means in the central bin. -/
theorem binned_ols_identity {η : Type*} [Fintype η] [DecidableEq η]
    (B : ι → η) (b : η) (d y : ι → ℝ) (a : η → ℝ) (β : ℝ)
    (hd01 : ∀ i, d i = 0 ∨ d i = 1)
    (e : η → ℝ) (hconst : ∀ i, B i ≠ b → d i = e (B i))
    (hn1 : 0 < ∑ i ∈ (univ.filter (fun i => B i = b)), d i)
    (hn0 : 0 < ∑ i ∈ (univ.filter (fun i => B i = b)), (1 - d i))
    (hfit : IsBinOLS B d y a β) :
    β = (∑ i ∈ (univ.filter (fun i => B i = b)), d i * y i) /
        (∑ i ∈ (univ.filter (fun i => B i = b)), d i) -
      (∑ i ∈ (univ.filter (fun i => B i = b)), (1 - d i) * y i) /
        (∑ i ∈ (univ.filter (fun i => B i = b)), (1 - d i)) := by
  classical
  let C := univ.filter (fun i => B i = b)
  let R := fun i => y i - a (B i) - β * d i
  have hf (f : η → ℝ) : (∑ i, f (B i) * R i) = 0 := by
    calc
      _ = ∑ j, f j * (∑ i, if B i = j then R i else 0) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        simp [eq_comm]
      _ = 0 := by
        simp only [R, hfit.1, mul_zero, Finset.sum_const_zero]
  have hdcentral : (∑ i ∈ C, d i * R i) = 0 := by
    have heq : (∑ i, d i * R i) = (∑ i ∈ C, d i * R i) +
        ∑ i, (if B i = b then 0 else e (B i)) * R i := by
      simp only [C, Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : B i = b
      · simp [hi]
      · simp [hi, hconst i hi]
    have hout := hf (fun j => if j = b then 0 else e j)
    have htot : (∑ i, d i * R i) = 0 := hfit.2
    rw [heq, hout, add_zero] at htot
    exact htot
  have htotal : (∑ i ∈ C, R i) = 0 := by
    simpa only [C, Finset.sum_filter] using hfit.1 b
  have hloser : (∑ i ∈ C, (1 - d i) * R i) = 0 := by
    simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
    rw [htotal, hdcentral, sub_self]
  have hwin : (∑ i ∈ C, d i * y i) =
      (a b + β) * (∑ i ∈ C, d i) := by
    have heq : (∑ i ∈ C, d i * R i) = (∑ i ∈ C, d i * y i) -
        (a b + β) * (∑ i ∈ C, d i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hib : B i = b := (Finset.mem_filter.mp hi).2
      rcases hd01 i with hdi | hdi <;> simp [R, hib, hdi] <;> ring
    rw [heq] at hdcentral
    linarith
  have hlose : (∑ i ∈ C, (1 - d i) * y i) =
      a b * (∑ i ∈ C, (1 - d i)) := by
    have heq : (∑ i ∈ C, (1 - d i) * R i) = (∑ i ∈ C, (1 - d i) * y i) -
        a b * (∑ i ∈ C, (1 - d i)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hib : B i = b := (Finset.mem_filter.mp hi).2
      rcases hd01 i with hdi | hdi <;> simp [R, hib, hdi] <;> ring
    rw [heq] at hloser
    linarith
  have q1 : (∑ i ∈ C, d i * y i) / (∑ i ∈ C, d i) = a b + β :=
    (div_eq_iff (ne_of_gt hn1)).mpr (by rw [hwin])
  have q0 : (∑ i ∈ C, (1 - d i) * y i) / (∑ i ∈ C, (1 - d i)) = a b :=
    (div_eq_iff (ne_of_gt hn0)).mpr (by rw [hlose])
  change β = (∑ i ∈ C, d i * y i) / (∑ i ∈ C, d i) -
    (∑ i ∈ C, (1 - d i) * y i) / (∑ i ∈ C, (1 - d i))
  rw [q1, q0]
  ring

/-- Scalar ceiling/endpoint calculation for the exact bins on pp. 5 and 9.
The natural-number ceiling is only used under 0<k<1. -/
theorem bin_scalar_geometry (k z : ℝ) (hk : 0 < k ∧ k < 1)
    (hz : -1 ≤ z ∧ z ≤ 1) :
    (∀ j : Fin (binCount k + 1), inBin k j.val z ↔ binLabel k z = j) ∧
    (binLabel k z = centralLabel k ↔ -k < z ∧ z ≤ k) ∧
    (centralLabel k < binLabel k z → 0 < z) ∧
    (binLabel k z < centralLabel k → z < 0) := by
  let M : ℕ := Nat.ceil ((1 - k) / (2 * k))
  have hMpos : 0 < M := Nat.ceil_pos.mpr (div_pos (by linarith) (by linarith))
  have hJ : (binCount k : ℝ) = 2 * (M : ℝ) := by simp [binCount, M]
  have hcover : 1 ≤ ((binCount k : ℝ) + 1) * k := by
    have hc : (1 - k) / (2 * k) ≤ (M : ℝ) := Nat.le_ceil _
    have ht := (div_le_iff₀ (show 0 < 2 * k by linarith)).mp hc
    nlinarith
  have htlo : -(binCount k : ℝ) - 1 ≤ z / k := by
    apply (le_div_iff₀ hk.1).mpr
    nlinarith [hz.1]
  have hthi : z / k ≤ (binCount k : ℝ) + 1 := by
    apply (div_le_iff₀ hk.1).mpr
    nlinarith [hz.2]
  let u : ℝ := (z / k + (binCount k : ℝ) - 1) / 2
  have hcBound : Nat.ceil u ≤ binCount k := Nat.ceil_le.mpr (by dsimp [u]; linarith)
  have hlabel : (binLabel k z).val = Nat.ceil u := by
    change min (binCount k) (Nat.ceil u) = Nat.ceil u
    exact Nat.min_eq_right hcBound
  have hpart : ∀ j : Fin (binCount k + 1), inBin k j.val z ↔ binLabel k z = j := by
    intro j
    rw [Fin.ext_iff, hlabel]
    by_cases hj : j.val = 0
    · simp only [inBin, hj, if_pos rfl, Nat.ceil_eq_zero]
      constructor
      · intro h; dsimp [u]; linarith [h.2]
      · intro h; dsimp [u] at h; exact ⟨htlo, by linarith⟩
    · simp only [inBin, if_neg hj, Nat.ceil_eq_iff hj]
      have hj1 : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr hj
      rw [Nat.cast_sub hj1, Nat.cast_one]
      dsimp [u]
      constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hlo : 2 * (M : ℝ) - (binCount k : ℝ) - 1 = -1 := by rw [hJ]; ring
  have hhi : 2 * (M : ℝ) - (binCount k : ℝ) + 1 = 1 := by rw [hJ]; ring
  have hcenter : binLabel k z = centralLabel k ↔ -k < z ∧ z ≤ k := by
    rw [← hpart]
    change inBin k M z ↔ _
    simp only [inBin, if_neg (Nat.ne_of_gt hMpos), hlo, hhi]
    rw [lt_div_iff₀ hk.1, div_le_iff₀ hk.1]
    simp
  have hcurrent : inBin k (binLabel k z).val z := (hpart _).mpr rfl
  refine ⟨hpart, hcenter, ?_, ?_⟩
  · intro hj
    have hn : M < (binLabel k z).val := hj
    have hj0 : (binLabel k z).val ≠ 0 := by omega
    have hjr : (M : ℝ) + 1 ≤ ((binLabel k z).val : ℝ) := by exact_mod_cast hn
    simp only [inBin, if_neg hj0] at hcurrent
    have ht : 0 < z / k := by nlinarith [hcurrent.1]
    have ht' := (lt_div_iff₀ hk.1).mp ht
    simpa using ht'
  · intro hj
    have hn : (binLabel k z).val < M := hj
    have hjr : ((binLabel k z).val : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hn
    have hmreal : 1 ≤ (M : ℝ) := by exact_mod_cast hMpos
    by_cases hj0 : (binLabel k z).val = 0
    · simp only [inBin, if_pos hj0] at hcurrent
      have ht : z / k < 0 := by nlinarith [hcurrent.2]
      have ht' := (div_lt_iff₀ hk.1).mp ht
      simpa using ht'
    · simp only [inBin, if_neg hj0] at hcurrent
      have ht : z / k < 0 := by nlinarith [hcurrent.2]
      have ht' := (div_lt_iff₀ hk.1).mp ht
      simpa using ht'

/-- The exact interval geometry of Condition 2 and Appendix A (pp. 5,9):
all observations in [-1,1] belong to exactly their assigned bin; the central
bin is (-k,k], and every other bin has constant party-win indicator. -/
theorem paper_bin_geometry (k : ℝ) (hk : 0 < k ∧ k < 1) (x d : ι → ℝ)
    (hdata : TwoParty x d) :
    (∀ (i : ι) (j : Fin (binCount k + 1)), inBin k j.val (x i) ↔ binLabel k (x i) = j) ∧
    (∀ i, binLabel k (x i) = centralLabel k ↔ -k < x i ∧ x i ≤ k) ∧
    (∀ i, binLabel k (x i) ≠ centralLabel k →
      d i = if centralLabel k < binLabel k (x i) then 1 else 0) := by
  have hg (i : ι) := bin_scalar_geometry k (x i) hk (hdata.1 i)
  refine ⟨fun i => (hg i).1, fun i => (hg i).2.1, ?_⟩
  intro i hi
  by_cases hlt : centralLabel k < binLabel k (x i)
  · rw [if_pos hlt]
    exact hdata.2.2.1 i ((hg i).2.2.1 hlt)
  · rw [if_neg hlt]
    have hgt : binLabel k (x i) < centralLabel k := lt_of_le_of_ne (le_of_not_gt hlt) hi
    exact hdata.2.2.2 i ((hg i).2.2.2 hgt)

/-- Positive winner and loser counts in U_b follow from Condition 1 and
binary two-party indicators. This is the finite regularity fact of p. 5. -/
theorem close_counts_positive (k : ℝ) (x d : ι → ℝ)
    (hdata : TwoParty x d) (hc : Condition1 k x) :
    (0 < ∑ i ∈ close k x, d i) ∧ (0 < ∑ i ∈ close k x, (1 - d i)) := by
  classical
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hc
  have hdi : d i = 1 := hdata.2.2.1 i hi.1
  have hdj : d j = 0 := hdata.2.2.2 j hj.2
  have hk : 0 < k := lt_trans hi.1 hi.2
  have hiC : i ∈ close k x := by simp [close]; constructor <;> linarith [hi.1, hi.2]
  have hjC : j ∈ close k x := by simp [close]; constructor <;> linarith [hj.1, hj.2]
  constructor
  · have hle := Finset.single_le_sum (f := d)
      (fun l _ => by rcases hdata.2.1 l with h | h <;> simp [h]) hiC
    rw [hdi] at hle
    linarith
  · have hle := Finset.single_le_sum (f := fun l => 1 - d l)
      (fun l _ => by rcases hdata.2.1 l with h | h <;> simp [h]) hjC
    rw [hdj] at hle
    norm_num at hle ⊢
    linarith

/-- Proposition 1, p. 6 (P023-T11): under Conditions 1–3, every OLS solution
for the actual bins of Condition 2 has party-win coefficient τ̂_RD. Outcomes
are arbitrary and no stochastic or causal model is assumed. -/
theorem proposition1 (k : ℝ) (hk : 0 < k ∧ k < 1) (x d y : ι → ℝ)
    (hdata : TwoParty x d) (hc : Condition1 k x) (β : ℝ)
    (hβ : CoarsenedOLS k x d y β) : β = rd k x d y := by
  classical
  obtain ⟨a, hfit⟩ := hβ
  obtain ⟨hpart, hcentral, hconst⟩ := paper_bin_geometry k hk x d hdata
  have hC : univ.filter (fun i => binLabel k (x i) = centralLabel k) = close k x := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, close]
    simp [hcentral]
  have hn := close_counts_positive k x d hdata hc
  simpa only [hC, rd] using binned_ols_identity (fun i => binLabel k (x i))
    (centralLabel k) d y a β hdata.2.1
    (fun j => if centralLabel k < j then 1 else 0) hconst
    (by simpa only [hC] using hn.1) (by simpa only [hC] using hn.2) hfit

/-- Proposition 1's exact localization consequence, P023-T3(a) and the true
coarsened part of P023-T10: positive close winner and loser counts and agreement
on U_b force equal coefficients in all least-squares solutions, including data
with empty nuisance bins. Strictly interior observations are not required. -/
theorem coarsened_localization (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y y' : ι → ℝ) (hdata : TwoParty x d)
    (hn1 : 0 < ∑ i ∈ close k x, d i) (hn0 : 0 < ∑ i ∈ close k x, (1-d i))
    (hag : ∀ i ∈ close k x, y i = y' i) (β β' : ℝ)
    (hβ : CoarsenedOLS k x d y β) (hβ' : CoarsenedOLS k x d y' β') : β = β' := by
  classical
  obtain ⟨hpart, hcentral, hconst⟩ := paper_bin_geometry k hk x d hdata
  have hC : univ.filter (fun i => binLabel k (x i) = centralLabel k) = close k x := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, close]
    simp [hcentral]
  have hrd (z : ι → ℝ) (b : ℝ) (hb : CoarsenedOLS k x d z b) : b = rd k x d z := by
    obtain ⟨a, hfit⟩ := hb
    simpa only [hC, rd] using binned_ols_identity (fun i => binLabel k (x i))
      (centralLabel k) d z a b hdata.2.1
      (fun j => if centralLabel k < j then 1 else 0) hconst
      (by simpa only [hC] using hn1) (by simpa only [hC] using hn0) hfit
  rw [hrd y β hβ, hrd y' β' hβ']
  unfold rd
  congr 2 <;> apply Finset.sum_congr rfl <;> intro i hi <;> rw [hag i hi]

/-- P023-T10's printed data-dependence claim for correctly specified polynomial
controls (pp. 3,7) is false; the six-election witness refutes its formal reading.
The Section 5 "may" claim is separately true via coarsening. -/
theorem printed_polynomial_localization_refuted :
    ¬ (∀ (n J : ℕ) (x d : Fin n → ℝ) (k : ℝ),
      0 < k → k < 1 → TwoParty x d → Condition1 k x →
      FullRank (polynomialDesign J x d) →
      (∃ c : Fin (J + 2) → ℝ, ∀ i, 0 < predict (polynomialDesign J x d) c i ∧
        predict (polynomialDesign J x d) c i < 1) →
      Localized k x (polynomialOLS J x d)) := by
  intro h
  apply linear_nonlocal
  apply h 6 1 linearX linearD (1 / 200) (by norm_num) (by norm_num)
    linear_hypotheses.1 linear_hypotheses.2 linear_fullRank
  refine ⟨linearExact, ?_⟩
  intro i
  rw [← linear_exact_model]
  exact ⟨(linear_outcomes_bounded i).1, (linear_outcomes_bounded i).2.1⟩

/-- The exact bandwidth in this witness gives the printed Condition 2 control count. -/
theorem linear_binCount : binCount (1 / 200 : ℝ) = 200 := by
  unfold binCount
  have hc : Nat.ceil ((1 - (1 / 200 : ℝ)) / (2 * (1 / 200 : ℝ))) = 100 := by
    apply (Nat.ceil_eq_iff (by decide)).mpr
    norm_num
  rw [hc]

/-- Every observation has precisely the specified bin label; endpoint inequalities are those of the paper. -/
theorem linear_bin_labels (i : Fin 6) : (binLabel (1 / 200 : ℝ) (linearX i)).val = ![25, 75, 100, 100, 125, 175] i := by
  fin_cases i
  · change (binLabel (1 / 200 : ℝ) (linearX 0)).val = 25
    have hg := (bin_scalar_geometry (1 / 200 : ℝ) (linearX 0) (by norm_num) (by norm_num [linearX])).1
    have hb : inBin (1 / 200 : ℝ) 25 (linearX 0) := by norm_num [inBin, linear_binCount, linearX]
    exact congrArg Fin.val ((hg ⟨25, by rw [linear_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 200 : ℝ) (linearX 1)).val = 75
    have hg := (bin_scalar_geometry (1 / 200 : ℝ) (linearX 1) (by norm_num) (by norm_num [linearX])).1
    have hb : inBin (1 / 200 : ℝ) 75 (linearX 1) := by norm_num [inBin, linear_binCount, linearX]
    exact congrArg Fin.val ((hg ⟨75, by rw [linear_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 200 : ℝ) (linearX 2)).val = 100
    have hg := (bin_scalar_geometry (1 / 200 : ℝ) (linearX 2) (by norm_num) (by norm_num [linearX])).1
    have hb : inBin (1 / 200 : ℝ) 100 (linearX 2) := by norm_num [inBin, linear_binCount, linearX]
    exact congrArg Fin.val ((hg ⟨100, by rw [linear_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 200 : ℝ) (linearX 3)).val = 100
    have hg := (bin_scalar_geometry (1 / 200 : ℝ) (linearX 3) (by norm_num) (by norm_num [linearX])).1
    have hb : inBin (1 / 200 : ℝ) 100 (linearX 3) := by norm_num [inBin, linear_binCount, linearX]
    exact congrArg Fin.val ((hg ⟨100, by rw [linear_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 200 : ℝ) (linearX 4)).val = 125
    have hg := (bin_scalar_geometry (1 / 200 : ℝ) (linearX 4) (by norm_num) (by norm_num [linearX])).1
    have hb : inBin (1 / 200 : ℝ) 125 (linearX 4) := by norm_num [inBin, linear_binCount, linearX]
    exact congrArg Fin.val ((hg ⟨125, by rw [linear_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 200 : ℝ) (linearX 5)).val = 175
    have hg := (bin_scalar_geometry (1 / 200 : ℝ) (linearX 5) (by norm_num) (by norm_num [linearX])).1
    have hb : inBin (1 / 200 : ℝ) 175 (linearX 5) := by norm_num [inBin, linear_binCount, linearX]
    exact congrArg Fin.val ((hg ⟨175, by rw [linear_binCount]; decide⟩).mp hb)

/-- Explicit per-occupied-bin mean of Y−βD for the linear witness.
Empty bins have intercept zero; they do not constrain the party coefficient. -/
def linearBinIntercept (j : Fin (binCount (1 / 200 : ℝ) + 1)) : ℝ := if j.val = 25 then (37 / 80 : ℝ) else if j.val = 75 then (39 / 80 : ℝ) else if j.val = 100 then (3999 / 8000 : ℝ) else if j.val = 125 then (2049 / 4000 : ℝ) else if j.val = 175 then (2149 / 4000 : ℝ) else 0

/-- An explicit least-squares solution exists for the actual coarsened bins, with the unchanged RD coefficient. -/
theorem linear_bin_fit : IsBinOLS (fun i => binLabel (1 / 200 : ℝ) (linearX i)) linearD linearY linearBinIntercept (401 / 4000 : ℝ) := by
  constructor
  · intro j
    by_cases h25 : j.val = 25
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinIntercept, linearY, linearD, h25]
    by_cases h75 : j.val = 75
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinIntercept, linearY, linearD, h25, h75]
    by_cases h100 : j.val = 100
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinIntercept, linearY, linearD, h25, h75, h100]
    by_cases h125 : j.val = 125
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinIntercept, linearY, linearD, h25, h75, h100, h125]
    by_cases h175 : j.val = 175
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinIntercept, linearY, linearD, h25, h75, h100, h125, h175]
    norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinIntercept, linearY, linearD, h25, h75, h100, h125, h175]
  · norm_num [Fin.sum_univ_succ, linear_bin_labels, linearBinIntercept, linearY, linearD]

/-- Explicit per-occupied-bin mean of Y−βD for the linear witness.
Empty bins have intercept zero; they do not constrain the party coefficient. -/
def linearBinInterceptprime (j : Fin (binCount (1 / 200 : ℝ) + 1)) : ℝ := if j.val = 25 then (37 / 80 : ℝ) else if j.val = 75 then (39 / 80 : ℝ) else if j.val = 100 then (3999 / 8000 : ℝ) else if j.val = 125 then (2049 / 4000 : ℝ) else if j.val = 175 then (2189 / 4000 : ℝ) else 0

/-- An explicit least-squares solution exists for the actual coarsened bins, with the unchanged RD coefficient. -/
theorem linear_bin_fitprime : IsBinOLS (fun i => binLabel (1 / 200 : ℝ) (linearX i)) linearD linearYprime linearBinInterceptprime (401 / 4000 : ℝ) := by
  constructor
  · intro j
    by_cases h25 : j.val = 25
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinInterceptprime, linearYprime, linearD, h25]
    by_cases h75 : j.val = 75
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinInterceptprime, linearYprime, linearD, h25, h75]
    by_cases h100 : j.val = 100
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinInterceptprime, linearYprime, linearD, h25, h75, h100]
    by_cases h125 : j.val = 125
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinInterceptprime, linearYprime, linearD, h25, h75, h100, h125]
    by_cases h175 : j.val = 175
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinInterceptprime, linearYprime, linearD, h25, h75, h100, h125, h175]
    norm_num [Fin.sum_univ_succ, Fin.ext_iff, linear_bin_labels, linearBinInterceptprime, linearYprime, linearD, h25, h75, h100, h125, h175]
  · norm_num [Fin.sum_univ_succ, linear_bin_labels, linearBinInterceptprime, linearYprime, linearD]

/-- P023-T1(vi): both coarsened regressions have an OLS solution, and every solution has the same party-win coefficient. -/
theorem linear_coarsened_values : CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearY (401 / 4000 : ℝ) ∧
    CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearYprime (401 / 4000 : ℝ) ∧
    (∀ β, CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearY β → β = (401 / 4000 : ℝ)) ∧
    (∀ β, CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearYprime β → β = (401 / 4000 : ℝ)) := by
  refine ⟨⟨linearBinIntercept, linear_bin_fit⟩, ⟨linearBinInterceptprime, linear_bin_fitprime⟩, ?_, ?_⟩
  · intro β hβ
    rw [proposition1 (1 / 200 : ℝ) (by norm_num) linearX linearD linearY linear_hypotheses.1 linear_hypotheses.2 β hβ, linear_rd_values.1]
  · intro β hβ
    rw [proposition1 (1 / 200 : ℝ) (by norm_num) linearX linearD linearYprime linear_hypotheses.1 linear_hypotheses.2 β hβ, linear_rd_values.2]

/-- Only the farthest positive-margin outcome is increased, by exactly 1/100. -/
theorem linear_perturbation (i : Fin 6) : linearYprime i = linearY i + if i = 5 then 1/100 else 0 := by
  fin_cases i <;> norm_num [linearY, linearYprime]

/-- Full P023-T1 witness, including all OLS, RD and coarsened-regression claims. Finite sums are exact; no causal assumptions are added. -/
theorem linear_counterexample : TwoParty linearX linearD ∧ Condition1 (1 / 200 : ℝ) linearX ∧
    FullRank (polynomialDesign 1 linearX linearD) ∧
    linearY = predict (polynomialDesign 1 linearX linearD) linearExact ∧
    (∀ z, polynomialOLS 1 linearX linearD z = dot linearW z) ∧
    polynomialOLS 1 linearX linearD linearY = 1/10 ∧
    polynomialOLS 1 linearX linearD linearYprime = (1371721 / 13920200 : ℝ) ∧
    polynomialOLS 1 linearX linearD linearYprime - polynomialOLS 1 linearX linearD linearY = (-20299 / 13920200 : ℝ) ∧
    (-20299 / 13920200 : ℝ) ≠ 0 ∧
    (∀ i ∈ close (1 / 200 : ℝ) linearX, linearY i = linearYprime i) ∧
    (∀ i, linearYprime i = linearY i + if i = 5 then 1/100 else 0) ∧
    rd (1 / 200 : ℝ) linearX linearD linearY = (401 / 4000 : ℝ) ∧
    rd (1 / 200 : ℝ) linearX linearD linearYprime = (401 / 4000 : ℝ) ∧
    binCount (1 / 200 : ℝ) = 200 ∧
    (∀ i, (binLabel (1 / 200 : ℝ) (linearX i)).val = ![25, 75, 100, 100, 125, 175] i) ∧
    CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearY (401 / 4000 : ℝ) ∧
    CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearYprime (401 / 4000 : ℝ) ∧
    (∀ β, CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearY β → β = (401 / 4000 : ℝ)) ∧
    (∀ β, CoarsenedOLS (1 / 200 : ℝ) linearX linearD linearYprime β → β = (401 / 4000 : ℝ)) ∧
    (∀ i, 0 < linearY i ∧ linearY i < 1 ∧ 0 < linearYprime i ∧ linearYprime i < 1) ∧
    ¬ Localized (1 / 200 : ℝ) linearX (polynomialOLS 1 linearX linearD) := by
  exact ⟨linear_hypotheses.1, linear_hypotheses.2, linear_fullRank, linear_exact_model,
    linear_weights, linear_coefficient_values.1, linear_coefficient_values.2.1,
    linear_coefficient_values.2.2.1, linear_coefficient_values.2.2.2,
    linear_agrees_on_close, linear_perturbation, linear_rd_values.1, linear_rd_values.2,
    linear_binCount, linear_bin_labels, linear_coarsened_values.1, linear_coarsened_values.2.1,
    linear_coarsened_values.2.2.1, linear_coarsened_values.2.2.2,
    linear_outcomes_bounded, linear_nonlocal⟩

/-- The exact bandwidth in this witness gives the printed Condition 2 control count. -/
theorem degree7_binCount : binCount (1 / 5 : ℝ) = 4 := by
  unfold binCount
  have hc : Nat.ceil ((1 - (1 / 5 : ℝ)) / (2 * (1 / 5 : ℝ))) = 2 := by
    apply (Nat.ceil_eq_iff (by decide)).mpr
    norm_num
  rw [hc]

/-- Every observation has precisely the specified bin label; endpoint inequalities are those of the paper. -/
theorem degree7_bin_labels (i : Fin 16) : (binLabel (1 / 5 : ℝ) (degree7X i)).val = ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 4] i := by
  fin_cases i
  · change (binLabel (1 / 5 : ℝ) (degree7X 0)).val = 0
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 0) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 0 (degree7X 0) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨0, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 1)).val = 0
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 1) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 0 (degree7X 1) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨0, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 2)).val = 0
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 2) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 0 (degree7X 2) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨0, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 3)).val = 0
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 3) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 0 (degree7X 3) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨0, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 4)).val = 1
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 4) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 1 (degree7X 4) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨1, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 5)).val = 1
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 5) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 1 (degree7X 5) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨1, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 6)).val = 1
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 6) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 1 (degree7X 6) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨1, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 7)).val = 2
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 7) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 2 (degree7X 7) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨2, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 8)).val = 2
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 8) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 2 (degree7X 8) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨2, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 9)).val = 3
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 9) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 3 (degree7X 9) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨3, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 10)).val = 3
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 10) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 3 (degree7X 10) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨3, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 11)).val = 3
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 11) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 3 (degree7X 11) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨3, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 12)).val = 4
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 12) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 4 (degree7X 12) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨4, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 13)).val = 4
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 13) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 4 (degree7X 13) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨4, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 14)).val = 4
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 14) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 4 (degree7X 14) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨4, by rw [degree7_binCount]; decide⟩).mp hb)
  · change (binLabel (1 / 5 : ℝ) (degree7X 15)).val = 4
    have hg := (bin_scalar_geometry (1 / 5 : ℝ) (degree7X 15) (by norm_num) (by norm_num [degree7X])).1
    have hb : inBin (1 / 5 : ℝ) 4 (degree7X 15) := by norm_num [inBin, degree7_binCount, degree7X]
    exact congrArg Fin.val ((hg ⟨4, by rw [degree7_binCount]; decide⟩).mp hb)

/-- Explicit per-occupied-bin mean of Y−βD for the degree7 witness.
Empty bins have intercept zero; they do not constrain the party coefficient. -/
def degree7BinIntercept (j : Fin (binCount (1 / 5 : ℝ) + 1)) : ℝ := if j.val = 0 then (95518231 / 209715200 : ℝ) else if j.val = 1 then (100919207 / 209715200 : ℝ) else if j.val = 2 then (103546879 / 209715200 : ℝ) else if j.val = 3 then (106174551 / 209715200 : ℝ) else if j.val = 4 then (111575527 / 209715200 : ℝ) else 0

/-- An explicit least-squares solution exists for the actual coarsened bins, with the unchanged RD coefficient. -/
theorem degree7_bin_fit : IsBinOLS (fun i => binLabel (1 / 5 : ℝ) (degree7X i)) degree7D degree7Y degree7BinIntercept (11796481 / 104857600 : ℝ) := by
  constructor
  · intro j
    by_cases h0 : j.val = 0
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinIntercept, degree7Y, degree7D, h0]
    by_cases h1 : j.val = 1
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinIntercept, degree7Y, degree7D, h0, h1]
    by_cases h2 : j.val = 2
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinIntercept, degree7Y, degree7D, h0, h1, h2]
    by_cases h3 : j.val = 3
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinIntercept, degree7Y, degree7D, h0, h1, h2, h3]
    by_cases h4 : j.val = 4
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinIntercept, degree7Y, degree7D, h0, h1, h2, h3, h4, eq_comm]
    norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinIntercept, degree7Y, degree7D, h0, h1, h2, h3, h4, eq_comm]
  · norm_num [Fin.sum_univ_succ, degree7_bin_labels, degree7BinIntercept, degree7Y, degree7D]

/-- Explicit per-occupied-bin mean of Y−βD for the degree7 witness.
Empty bins have intercept zero; they do not constrain the party coefficient. -/
def degree7BinInterceptprime (j : Fin (binCount (1 / 5 : ℝ) + 1)) : ℝ := if j.val = 0 then (95518231 / 209715200 : ℝ) else if j.val = 1 then (100919207 / 209715200 : ℝ) else if j.val = 2 then (103546879 / 209715200 : ℝ) else if j.val = 3 then (106174551 / 209715200 : ℝ) else if j.val = 4 then (22419963 / 41943040 : ℝ) else 0

/-- An explicit least-squares solution exists for the actual coarsened bins, with the unchanged RD coefficient. -/
theorem degree7_bin_fitprime : IsBinOLS (fun i => binLabel (1 / 5 : ℝ) (degree7X i)) degree7D degree7Yprime degree7BinInterceptprime (11796481 / 104857600 : ℝ) := by
  constructor
  · intro j
    by_cases h0 : j.val = 0
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinInterceptprime, degree7Yprime, degree7D, h0]
    by_cases h1 : j.val = 1
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinInterceptprime, degree7Yprime, degree7D, h0, h1]
    by_cases h2 : j.val = 2
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinInterceptprime, degree7Yprime, degree7D, h0, h1, h2]
    by_cases h3 : j.val = 3
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinInterceptprime, degree7Yprime, degree7D, h0, h1, h2, h3]
    by_cases h4 : j.val = 4
    · norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinInterceptprime, degree7Yprime, degree7D, h0, h1, h2, h3, h4, eq_comm]
    norm_num [Fin.sum_univ_succ, Fin.ext_iff, degree7_bin_labels, degree7BinInterceptprime, degree7Yprime, degree7D, h0, h1, h2, h3, h4, eq_comm]
  · norm_num [Fin.sum_univ_succ, degree7_bin_labels, degree7BinInterceptprime, degree7Yprime, degree7D]

/-- P023-T2(vi): both coarsened regressions have an OLS solution, and every solution has the same party-win coefficient. -/
theorem degree7_coarsened_values : CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Y (11796481 / 104857600 : ℝ) ∧
    CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Yprime (11796481 / 104857600 : ℝ) ∧
    (∀ β, CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Y β → β = (11796481 / 104857600 : ℝ)) ∧
    (∀ β, CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Yprime β → β = (11796481 / 104857600 : ℝ)) := by
  refine ⟨⟨degree7BinIntercept, degree7_bin_fit⟩, ⟨degree7BinInterceptprime, degree7_bin_fitprime⟩, ?_, ?_⟩
  · intro β hβ
    rw [proposition1 (1 / 5 : ℝ) (by norm_num) degree7X degree7D degree7Y degree7_hypotheses.1 degree7_hypotheses.2 β hβ, degree7_rd_values.1]
  · intro β hβ
    rw [proposition1 (1 / 5 : ℝ) (by norm_num) degree7X degree7D degree7Yprime degree7_hypotheses.1 degree7_hypotheses.2 β hβ, degree7_rd_values.2]

/-- Only the farthest positive-margin outcome is increased, by exactly 1/100. -/
theorem degree7_perturbation (i : Fin 16) : degree7Yprime i = degree7Y i + if i = 15 then 1/100 else 0 := by
  fin_cases i <;> norm_num [degree7Y, degree7Yprime]

/-- Full P023-T2 witness, including all OLS, RD and coarsened-regression claims. Finite sums are exact; no causal assumptions are added. -/
theorem degree7_counterexample : TwoParty degree7X degree7D ∧ Condition1 (1 / 5 : ℝ) degree7X ∧
    FullRank (polynomialDesign 7 degree7X degree7D) ∧
    degree7Y = predict (polynomialDesign 7 degree7X degree7D) degree7Exact ∧
    (∀ z, polynomialOLS 7 degree7X degree7D z = dot degree7W z) ∧
    polynomialOLS 7 degree7X degree7D degree7Y = 1/10 ∧
    polynomialOLS 7 degree7X degree7D degree7Yprime = (3249 / 32140 : ℝ) ∧
    polynomialOLS 7 degree7X degree7D degree7Yprime - polynomialOLS 7 degree7X degree7D degree7Y = (7 / 6428 : ℝ) ∧
    (7 / 6428 : ℝ) ≠ 0 ∧
    (∀ i ∈ close (1 / 5 : ℝ) degree7X, degree7Y i = degree7Yprime i) ∧
    (∀ i, degree7Yprime i = degree7Y i + if i = 15 then 1/100 else 0) ∧
    rd (1 / 5 : ℝ) degree7X degree7D degree7Y = (11796481 / 104857600 : ℝ) ∧
    rd (1 / 5 : ℝ) degree7X degree7D degree7Yprime = (11796481 / 104857600 : ℝ) ∧
    binCount (1 / 5 : ℝ) = 4 ∧
    (∀ i, (binLabel (1 / 5 : ℝ) (degree7X i)).val = ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 4] i) ∧
    CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Y (11796481 / 104857600 : ℝ) ∧
    CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Yprime (11796481 / 104857600 : ℝ) ∧
    (∀ β, CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Y β → β = (11796481 / 104857600 : ℝ)) ∧
    (∀ β, CoarsenedOLS (1 / 5 : ℝ) degree7X degree7D degree7Yprime β → β = (11796481 / 104857600 : ℝ)) ∧
    (∀ i, 0 < degree7Y i ∧ degree7Y i < 1 ∧ 0 < degree7Yprime i ∧ degree7Yprime i < 1) ∧
    ¬ Localized (1 / 5 : ℝ) degree7X (polynomialOLS 7 degree7X degree7D) ∧ (∀ i, degree7W i ≠ 0) := by
  exact ⟨degree7_hypotheses.1, degree7_hypotheses.2, degree7_fullRank, degree7_exact_model,
    degree7_weights, degree7_coefficient_values.1, degree7_coefficient_values.2.1,
    degree7_coefficient_values.2.2.1, degree7_coefficient_values.2.2.2,
    degree7_agrees_on_close, degree7_perturbation, degree7_rd_values.1, degree7_rd_values.2,
    degree7_binCount, degree7_bin_labels, degree7_coarsened_values.1, degree7_coarsened_values.2.1,
    degree7_coarsened_values.2.2.1, degree7_coarsened_values.2.2.2,
    degree7_outcomes_bounded, degree7_nonlocal, degree7_all_weights_nonzero⟩

/-! Population and asymptotic objects. Unlike a finite randomization design,
the paper's Appendix B uses an i.i.d. population law. The definitions use Borel
probability measures and Bochner integrals. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Appendix B, p. 10: E[DV | DemVot] uses a population probability law. -/
def ProbabilityLaw {E : Type*} [MeasurableSpace E] (μ : Measure E) : Prop := μ univ = 1

/-- Appendix B, p. 10: DemVot is on [-1,1]. This is an almost-sure support
restriction, not a restriction on the law's density away from the cutoff. -/
def MarginSupport (μ : Measure ℝ) : Prop := μ (Set.Icc (-1) 1)ᶜ = 0

/-- Appendix B, p. 10: I[DemVot≥0]. The convention at ties is explicit here;
all population witnesses and corrected asymptotics have no atom at zero. -/
def party (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

/-- Population expectations of functions of DemVot in Appendix B, p. 10. -/
def expectation (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ := ∫ x, f x ∂μ

/-- The polynomial projection of DemWin on span(1,X,...,X^J), P023-E002.
Orthogonality is imposed against every power 0,...,J. -/
def IsProjection (μ : Measure ℝ) (J : ℕ) (q : Polynomial ℝ) : Prop :=
  q.natDegree ≤ J ∧ ∀ j ≤ J, expectation μ (fun x => (party x - q.eval x) * x^j) = 0

/-- q_J, the unique L² polynomial projection of DemWin under the full-rank
hypotheses. Choice is made from genuine projection equations. Existence and
uniqueness are obligations of the population theorems, not extra assumptions. -/
def projection (μ : Measure ℝ) (J : ℕ) : Polynomial ℝ :=
  Classical.epsilon (IsProjection μ J)

/-- r_J=D-q_J, residualized party-win indicator; P023-E002. -/
def popResidual (μ : Measure ℝ) (J : ℕ) (x : ℝ) : ℝ := party x - (projection μ J).eval x

/-- v_J=E[r_J²], residual treatment information; P023-E002. -/
def residualVariance (μ : Measure ℝ) (J : ℕ) : ℝ := expectation μ (fun x => popResidual μ J x ^ 2)

/-- κ_J=E|r_J|/v_J, the amplification multiplier; P023-E002. -/
def amplification (μ : Measure ℝ) (J : ℕ) : ℝ :=
  expectation μ (fun x => |popResidual μ J x|) / residualVariance μ J

/-- T_J h=E[r_J h]/v_J; P023-E002. This is a functional, not the
population OLS coefficient until the FWL identity has been established. -/
def biasFunctional (μ : Measure ℝ) (J : ℕ) (h : ℝ → ℝ) : ℝ :=
  expectation μ (fun x => popResidual μ J x * h x) / residualVariance μ J

/-- The second-moment matrix of (1,D,X,...,X^J) is positive definite exactly
when every nonzero coefficient vector has positive mean squared fitted value. -/
def MomentPositiveDefinite (μ : Measure ℝ) (J : ℕ) : Prop :=
  ∀ c : Fin (J + 2) → ℝ, c ≠ 0 →
    0 < expectation μ (fun x => predict (polynomialDesign J (fun x : ℝ => x) party) c x ^ 2)

/-- Population normal equations for regression (2), pp. 6–7. Noise of zero
conditional mean does not change these equations for the conditional mean m. -/
def PopNormal (μ : Measure ℝ) (J : ℕ) (m : ℝ → ℝ) (c : Fin (J + 2) → ℝ) : Prop :=
  ∀ j, expectation μ (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
    (m x - predict (polynomialDesign J (fun x : ℝ => x) party) c x)) = 0

/-- b_J, the population least-squares coefficient on D in (2), as the chosen
normal-equation coefficient. Positive definiteness ensures uniqueness.
It is not defined to equal a target jump or a precomputed witness number. -/
def populationCoefficient (μ : Measure ℝ) (J : ℕ) (m : ℝ → ℝ) : ℝ :=
  (Classical.epsilon (PopNormal μ J m)) ⟨1, by omega⟩

/-- Uniform X on [-1,1], the law in P023-T3(e), T4 and T6:
Lebesgue measure restricted to [-1,1], scaled by its reciprocal length. -/
def uniformMargins : Measure ℝ := (1 / 2 : ℝ≥0∞) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)

/-- Population counterpart of the rectangular degree-0 RD estimator, p. 6.
All uses assume no atom at 0; intervals agree with the displayed finite U_b. -/
def populationRD (μ : Measure ℝ) (m : ℝ → ℝ) (k : ℝ) : ℝ :=
  (∫ x in Set.Ioc 0 k, m x ∂μ) / (μ (Set.Ioc 0 k)).toReal -
  (∫ x in Set.Ioo (-k) 0, m x ∂μ) / (μ (Set.Ioo (-k) 0)).toReal

/-- Supremum norm over the paper's margin domain [-1,1]. -/
def supError (h : ℝ → ℝ) (p : Polynomial ℝ) : ℝ :=
  sSup ((fun x => |h x - p.eval x|) '' Set.Icc (-1) 1)

/-- RMS error in L²(P_X), used in the correction of Appendix B (P023-E002). -/
def rmsError (μ : Measure ℝ) (h : ℝ → ℝ) (p : Polynomial ℝ) : ℝ :=
  Real.sqrt (expectation μ (fun x => (h x - p.eval x)^2))

/-- Conditional mean as equality against every bounded measurable test
function of X. This is the defining integral characterization of E[Y|X]=m(X)
for the joint law ν; it does not presume a causal interpretation (p. 10). -/
def ConditionalMean (ν : Measure (ℝ × ℝ)) (m : ℝ → ℝ) : Prop :=
  Integrable (fun z => z.2) ν ∧ Integrable (fun z => m z.1) ν ∧
  ∀ t : ℝ → ℝ, Measurable t → (∃ B, ∀ x, |t x| ≤ B) →
    (∫ z, t z.1 * z.2 ∂ν) = ∫ z, t z.1 * m z.1 ∂ν

/-- Marginal law of DemVot from the joint law of (DemVot,DV), p. 10. -/
def marginLaw (ν : Measure (ℝ × ℝ)) : Measure ℝ := Measure.map Prod.fst ν

/-- The two symmetric independent errors ±1/10 in witnesses T4,T5. -/
def noiseLaw : Measure ℝ := (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 / 10) +
  (1 / 2 : ℝ≥0∞) • Measure.dirac (1 / 10)

/-- Witness joint law: independently draw X∼μ and U∈{−1/10,1/10}, then
Y=1/2+h(X)+U. Product measure explicitly implements independence. -/
def witnessLaw (μ : Measure ℝ) (h : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (fun z : ℝ × ℝ => (z.1, 1 / 2 + h z.1 + z.2)) (μ.prod noiseLaw)

/-- P023-T4, P023-E002: h_η=a clip(x/η,−1,1). -/
def sigmoid (a η x : ℝ) : ℝ := a * max (-1) (min 1 (x / η))

/-- P023-T5, P023-E002: normalized triangular density t_{c,w}. -/
def triangular (c w x : ℝ) : ℝ := max (w - |x - c|) 0 / w^2

/-- P023-T5: full-support density q/2 + (1−q)(t_{a,w}+t_{−a,w})/2 on
[-1,1], where a=1/2, w=d/2 and q=d⁴. -/
def clusterDensity (d x : ℝ) : ℝ := d^4 / 2 +
  (1 - d^4) / 2 * (triangular (1 / 2) (d / 2) x + triangular (-1 / 2) (d / 2) x)

/-- P023-T5's actual probability law, defined by the density just quoted. -/
def clusteredMargins (d : ℝ) : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Set.Icc (-1) 1)).withDensity (fun x => ENNReal.ofReal (clusterDensity d x))

/-- P023-T5's odd, continuous piecewise-linear h. On the positive half its
three slopes are −1,+1,−1 on [a−2w,a−w],[a−w,a+w],[a+w,a+2w], and it is
zero elsewhere; P023-E002. -/
def clusterPositive (d x : ℝ) : ℝ :=
  if x < 1 / 2 - d then 0 else if x ≤ 1 / 2 - d / 2 then 1 / 2 - d - x
  else if x ≤ 1 / 2 + d / 2 then x - 1 / 2
  else if x ≤ 1 / 2 + d then 1 / 2 + d - x else 0

/-- P023-E002: odd extension of the three-piece smooth part, h(x)=−h(−x)
for x<0; Appendix B's h, p. 10. -/
def clusterSmooth (d x : ℝ) : ℝ := if x < 0 then -clusterPositive d (-x) else clusterPositive d x

/-- Projections for uniform margins (P023-E001, P023-E002). -/
def projection1 (x : ℝ) : ℝ := 1 / 2 + 3 / 4 * x
/-- P023-E001: the degree-7 L² projection of D under uniform margins,
with explicit polynomial coefficients. -/
def projection7 (x : ℝ) : ℝ := 1 / 2 +
  (11025*x - 40425*x^3 + 63063*x^5 - 32175*x^7) / 4096

/-- The exact uniform residual variance formula, P023-E002: with
n=⌊(J+1)/2⌋ and c_n=choose(2n,n)/4^n, v_J=c_n²/4. -/
def centralBinomial (n : ℕ) : ℝ := (Nat.choose (2*n) n : ℝ) / 4^n

/-- Appendix B's definition of h, p. 10; the finite left limit α is explicitly
presupposed, as required by the printed "Let α=lim_{x↑0} g(x)". -/
def appendixSmooth (g f : ℝ → ℝ) (α β x : ℝ) : ℝ :=
  if x < 0 then g x - α else f x - (α + β)

/-- The conditional mean as originally printed in Appendix B, p. 10. -/
def appendixMean (g f : ℝ → ℝ) (x : ℝ) : ℝ := if x < 0 then g x else f x

/-- P023-T12 finite lemma (i): the printed rewriting of the conditional mean
is an exact identity on both sides, including zero. -/
theorem appendix_rewriting (g f : ℝ → ℝ) (α : ℝ) (x : ℝ) :
    appendixMean g f x = α + (f 0 - α) * party x + appendixSmooth g f α (f 0 - α) x := by
  by_cases hx : x < 0
  · simp [appendixMean, appendixSmooth, party, hx, not_le.mpr hx]
  · simp [appendixMean, appendixSmooth, party, hx, le_of_not_gt hx]

/-- P023-T12 finite lemma (ii): h(0)=0, exactly as Appendix B, p. 10. -/
theorem appendix_smooth_zero (g f : ℝ → ℝ) (α : ℝ) :
    appendixSmooth g f α (f 0 - α) 0 = 0 := by
  simp [appendixSmooth]


/-- Convergence in probability is explicitly a limit of probabilities of
absolute-error events. The notation →_p denotes this convergence; the paper's
undefined ≈ is not interpreted as an exact finite equality. -/
def ConvergesInProbability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℕ → Ω → ℝ) (z : ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun N => P {ω | ε < |Z N ω - z|}) atTop (nhds 0)

/-- Appendix B, p. 10: "the sample is drawn i.i.d.". Each sample coordinate
is measurable, has the fixed joint law ν, and the coordinates are independent. -/
def IIDSample {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ) : Prop :=
  ProbabilityLaw P ∧ (∀ i, Measurable (sample i)) ∧
  (∀ i, Measure.map (sample i) P = ν) ∧ ProbabilityTheory.iIndepFun sample P

/-- OLS estimator (2) on the first N i.i.d. elections, pp. 6–7. Singular
samples use the chosen normal-equation coefficient; no rank is silently
assumed for every sample. Corrected convergence is an in-probability claim. -/
def samplePolynomial {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ) (N J : ℕ) (ω : Ω) : ℝ :=
  polynomialOLS J (fun i : Fin N => (sample i ω).1)
    (fun i : Fin N => party (sample i ω).1) (fun i : Fin N => (sample i ω).2)

/-- The displayed rectangular RD difference (p. 6) on the first N elections.
Total real division extends the estimator to empty-side samples, which have
vanishing probability in the repaired theorem. -/
def sampleRD {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ) (k : ℕ → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  rd (k N) (fun i : Fin N => (sample i ω).1)
    (fun i : Fin N => party (sample i ω).1) (fun i : Fin N => (sample i ω).2)

/-- The primitive correction of Proposition 2 (P023-E002):
a fixed probability law supported in margin on [-1,1], square-integrable
outcomes, a lower Lebesgue-density bound only near zero, no atom at zero,
h Lipschitz on [-1,1] with h(0)=0, and bounded local conditional variance.
The variance inequality against all local Borel sets is the almost-sure
integral formulation of Var(Y|X)≤σ̄². -/
def RepairedRegularity (ν : Measure (ℝ × ℝ)) (α β : ℝ) (h : ℝ → ℝ)
    (c δ L σ2 : ℝ) : Prop :=
  ProbabilityLaw ν ∧ MarginSupport (marginLaw ν) ∧ marginLaw ν {0} = 0 ∧
  Integrable (fun z => z.2^2) ν ∧ 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ σ2 ∧
  (∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc (-δ) δ →
    ENNReal.ofReal c * volume A ≤ marginLaw ν A) ∧
  h 0 = 0 ∧ (∀ x ∈ Set.Icc (-1) 1, ∀ x' ∈ Set.Icc (-1) 1, |h x - h x'| ≤ L * |x-x'|) ∧
  ConditionalMean ν (fun x => α + β*party x + h x) ∧
  (∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc (-δ) δ →
    (∫ z in {z : ℝ × ℝ | z.1 ∈ A}, (z.2 - (α + β*party z.1 + h z.1))^2 ∂ν) ≤
      σ2 * (marginLaw ν A).toReal)

/-- P023-E002: Jackson-kernel constant, deliberately nonoptimal. -/
def jacksonK : ℝ := 3 * (1 + Real.pi^4) / (4 * Real.pi)

/-- Smallest eigenvalue λ_J of the real symmetric second-moment matrix:
the minimum Rayleigh quotient on unit Euclidean coefficient vectors. This
representation avoids choosing a coordinate ordering beyond equation (2). -/
def smallestMomentEigenvalue (μ : Measure ℝ) (J : ℕ) : ℝ :=
  sInf {r | ∃ a : Fin (J+2) → ℝ, (∑ j, a j^2) = 1 ∧
    r = expectation μ (fun x => predict (polynomialDesign J (fun x : ℝ => x) party) a x ^ 2)}


/-- The "usual conditions for RD" invoked on p. 10, made explicit for the
printed Proposition 2: no atom at zero, increasing expected counts on both
shrinking-window sides, and an almost-sure bound on local conditional variance.
No quantitative smoothness or coefficient-bias bound is smuggled in. -/
def UsualRDRegularity (ν : Measure (ℝ × ℝ)) (m : ℝ → ℝ) (k : ℕ → ℝ) : Prop :=
  marginLaw ν {0} = 0 ∧
  Tendsto (fun N : ℕ => (N:ℝ)*(marginLaw ν (Set.Ioc 0 (k N))).toReal) atTop atTop ∧
  Tendsto (fun N : ℕ => (N:ℝ)*(marginLaw ν (Set.Ioo (-k N) 0)).toReal) atTop atTop ∧
  ∃ δ σ2 : ℝ, 0 < δ ∧ 0 ≤ σ2 ∧
    ∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc (-δ) δ →
      (∫ z in {z : ℝ × ℝ | z.1 ∈ A}, (z.2-m z.1)^2 ∂ν) ≤ σ2*(marginLaw ν A).toReal


/-- Condition 2 and Appendix A, pp. 5,9: convert the printed intercept and
J bin coefficients to one intercept for each of the J+1 bins. -/
def coarsenedIntercepts (k : ℝ) (c : Fin (binCount k+2) → ℝ)
    (j : Fin (binCount k+1)) : ℝ :=
  c ⟨0, by omega⟩ + if j.val=0 then 0 else c ⟨j.val+1, by have := j.isLt; omega⟩

/-- Exact equality of printed Condition 2 fitted values and the per-bin
intercept parametrization, including the reference bin and empty bins. -/
theorem printed_coarsened_prediction (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d : ι → ℝ) (hdata : TwoParty x d) (c : Fin (binCount k+2) → ℝ) (i : ι) :
    predict (coarsenedDesign k x d) c i =
      coarsenedIntercepts k c (binLabel k (x i)) + c ⟨1, by omega⟩*d i := by
  classical
  let b := binLabel k (x i)
  have hg := (bin_scalar_geometry k (x i) hk (hdata.1 i)).1
  have hb : b.val ≤ binCount k := Nat.le_of_lt_succ b.isLt
  have hs : (∑ j : Fin (binCount k), binIndicator k (j.val+1) (x i)*c j.succ.succ) =
      if b.val=0 then 0 else c ⟨b.val+1, by omega⟩ := by
    by_cases h0 : b.val=0
    · rw [if_pos h0]
      apply Finset.sum_eq_zero
      intro j _
      have hn : binLabel k (x i) ≠ (⟨j.val+1, by have := j.isLt; omega⟩ : Fin (binCount k+1)) := by
        intro he
        have hv := congrArg Fin.val he
        change b.val=j.val+1 at hv
        omega
      simp [binIndicator, (hg ⟨j.val+1, by have := j.isLt; omega⟩).not.mpr hn]
    · rw [if_neg h0]
      let t : Fin (binCount k) := ⟨b.val-1, by omega⟩
      have hbt : binLabel k (x i) = (⟨t.val+1, by have := t.isLt; omega⟩ : Fin (binCount k+1)) := by
        apply Fin.ext
        dsimp [t,b]
        omega
      have hct : t.succ.succ = (⟨b.val+1, by omega⟩ : Fin (binCount k+2)) := by
        apply Fin.ext
        dsimp [t]
        omega
      rw [Finset.sum_eq_single t]
      · simp [binIndicator, (hg _).mpr hbt, hct]
      · intro j _ hj
        have hn : binLabel k (x i) ≠ (⟨j.val+1, by have := j.isLt; omega⟩ : Fin (binCount k+1)) := by
          intro he
          have hv := congrArg Fin.val he
          have ht := congrArg Fin.val hbt
          apply hj
          apply Fin.ext
          dsimp only at hv ht
          omega
        simp [binIndicator, (hg _).not.mpr hn]
      · simp
  change _ = c ⟨0, by omega⟩ + (if b.val=0 then 0 else c ⟨b.val+1, by omega⟩) + c ⟨1, by omega⟩*d i
  simp only [predict, coarsenedDesign, Fin.sum_univ_succ, Fin.val_zero,
    Fin.val_succ, zero_add, if_pos, one_mul]
  simp only [Nat.add_eq_zero_iff, Nat.succ_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  have haux : ∀ j : Fin (binCount k), j.val+1+1 ≠ 1 := by intro j; omega
  simp only [haux, ite_false]
  rw [hs]
  have hf1 : (Fin.succ 0 : Fin (binCount k+2)) = ⟨1, by omega⟩ := by
    apply Fin.ext
    rfl
  rw [hf1]
  have hf0 : (0 : Fin (binCount k+2)) = ⟨0, by omega⟩ := rfl
  rw [hf0]
  ring

/-- Every least-squares solution in the paper's original Condition 2 design
satisfies the per-bin normal equations used in Proposition 1. -/
theorem printed_coarsened_to_bins (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y : ι → ℝ) (hdata : TwoParty x d) (c : Fin (binCount k+2) → ℝ)
    (hc : IsOLS (coarsenedDesign k x d) y c) :
    IsBinOLS (fun i => binLabel k (x i)) d y (coarsenedIntercepts k c) (c ⟨1, by omega⟩) := by
  classical
  let R := fun i => y i-predict (coarsenedDesign k x d) c i
  have hrow : ∀ i, y i-coarsenedIntercepts k c (binLabel k (x i))-c ⟨1, by omega⟩*d i=R i := by
    intro i
    dsimp [R]
    rw [printed_coarsened_prediction k hk x d hdata c i]
    have hf1 : (1 : Fin (binCount k+2)) = ⟨1, by omega⟩ := by
      apply Fin.ext
      simp
    simp only [hf1]
    ring
  have hbin (j : Fin (binCount k+1)) (hj : j.val ≠ 0) :
      (∑ i, if binLabel k (x i)=j then R i else 0)=0 := by
    have hh := hc ⟨j.val+1, by have := j.isLt; omega⟩
    have hj1 : j.val+1 ≠ 1 := by omega
    have hjfin : j ≠ 0 := by intro he; exact hj (congrArg Fin.val he)
    have hg : ∀ i, inBin k j.val (x i) ↔ binLabel k (x i)=j :=
      fun i => (bin_scalar_geometry k (x i) hk (hdata.1 i)).1 j
    simpa [dot, coarsenedDesign, binIndicator, hj, hjfin, hj1, hg, ite_mul, R] using hh
  have htot : (∑ i, R i)=0 := by
    simpa [dot,coarsenedDesign,R] using hc ⟨0, by omega⟩
  have hbin0 : (∑ i, if binLabel k (x i)=(0:Fin (binCount k+1)) then R i else 0)=0 := by
    have hpart : (∑ j : Fin (binCount k+1), ∑ i, if binLabel k (x i)=j then R i else 0)=∑ i, R i := by
      rw [Finset.sum_comm]
      simp
    have hrest : (∑ j : Fin (binCount k), ∑ i, if binLabel k (x i)=j.succ then R i else 0)=0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact hbin j.succ (by simp)
    rw [Fin.sum_univ_succ,hrest,add_zero,htot] at hpart
    exact hpart
  unfold IsBinOLS
  constructor
  · intro j
    simp_rw [hrow]
    by_cases hj : j.val=0
    · have he : j=0 := Fin.ext hj
      simpa [he] using hbin0
    · exact hbin j hj
  · simp_rw [hrow]
    simpa [dot,coarsenedDesign,R] using hc ⟨1, by omega⟩

/-- Proposition 1, p. 6, with its OLS hypothesis stated directly in the
printed intercept, DemWin, X_1,...,X_J parametrization. Every solution has
DemWin coefficient equal to RD; empty nuisance bins need not have full rank. -/
theorem printed_coarsened_proposition1 (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y : ι → ℝ) (hdata : TwoParty x d) (h1 : Condition1 k x)
    (c : Fin (binCount k+2) → ℝ) (hc : IsOLS (coarsenedDesign k x d) y c) :
    c ⟨1, by omega⟩=rd k x d y := by
  apply proposition1 k hk x d y hdata h1
  exact ⟨coarsenedIntercepts k c, printed_coarsened_to_bins k hk x d y hdata c hc⟩

/-- Condition 2, p. 5: recover its printed coefficient vector from bin
intercepts by taking the reference-bin intercept and differences from it. -/
def coarsenedFromBins (k : ℝ) (a : Fin (binCount k+1) → ℝ) (β : ℝ)
    (j : Fin (binCount k+2)) : ℝ :=
  if j.val=0 then a ⟨0, by omega⟩ else if j.val=1 then β
  else a ⟨j.val-1, by have := j.isLt; omega⟩-a ⟨0, by omega⟩

/-- Reference-intercept and bin-indicator differences reproduce every bin
intercept exactly, as the fixed-effects interpretation on p. 5 requires. -/
theorem coarsened_intercepts_from_bins (k : ℝ) (a : Fin (binCount k+1) → ℝ)
    (β : ℝ) (j : Fin (binCount k+1)) :
    coarsenedIntercepts k (coarsenedFromBins k a β) j=a j := by
  by_cases hj : j.val=0
  · have hje : j=(⟨0, by omega⟩ : Fin (binCount k+1)) := Fin.ext hj
    simp [coarsenedIntercepts,coarsenedFromBins,hj,hje]
  · have hj1 : j.val+1 ≠ 1 := by omega
    have hjp : j.val+1 ≠ 0 := by omega
    simp [coarsenedIntercepts,coarsenedFromBins,hj,hj1,hjp]

/-- A per-bin least-squares solution yields a solution of the paper's printed
intercept, DemWin and X_1,...,X_J normal equations, without requiring nonempty
bins or unique nuisance coefficients. -/
theorem bins_to_printed_coarsened (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y : ι → ℝ) (hdata : TwoParty x d) (a : Fin (binCount k+1) → ℝ)
    (β : ℝ) (hfit : IsBinOLS (fun i => binLabel k (x i)) d y a β) :
    IsOLS (coarsenedDesign k x d) y (coarsenedFromBins k a β) := by
  classical
  have hpredict (i : ι) : predict (coarsenedDesign k x d) (coarsenedFromBins k a β) i=
      a (binLabel k (x i))+β*d i := by
    rw [printed_coarsened_prediction k hk x d hdata,coarsened_intercepts_from_bins]
    simp [coarsenedFromBins]
  let R := fun i => y i-a (binLabel k (x i))-β*d i
  have htot : (∑ i, R i)=0 := by
    calc
      _ = ∑ j : Fin (binCount k+1), ∑ i, if binLabel k (x i)=j then R i else 0 := by
        rw [Finset.sum_comm]
        simp
      _ = 0 := Finset.sum_eq_zero (fun j _ => hfit.1 j)
  intro j
  by_cases hj0 : j.val=0
  · simpa [dot,coarsenedDesign,hj0,hpredict,sub_add_eq_sub_sub,R] using htot
  · by_cases hj1 : j.val=1
    · simpa [dot,coarsenedDesign,hj0,hj1,hpredict,sub_add_eq_sub_sub] using hfit.2
    · let t : Fin (binCount k+1) := ⟨j.val-1, by have := j.isLt; omega⟩
      have hg : ∀ i, inBin k (j.val-1) (x i) ↔ binLabel k (x i)=t :=
        fun i => (bin_scalar_geometry k (x i) hk (hdata.1 i)).1 t
      simpa [dot,coarsenedDesign,hj0,hj1,binIndicator,hg,hpredict,ite_mul,
        sub_add_eq_sub_sub] using hfit.1 t

/-- The paper's exact Condition 2 OLS relation is equivalent to the per-bin
relation used throughout this file. This is a proved parametrization bridge;
it preserves the DemWin coefficient and includes every empty-bin fit. -/
theorem coarsened_ols_printed_equivalence (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y : ι → ℝ) (hdata : TwoParty x d) (β : ℝ) :
    CoarsenedOLS k x d y β ↔ ∃ c : Fin (binCount k+2) → ℝ,
      IsOLS (coarsenedDesign k x d) y c ∧ c ⟨1, by omega⟩=β := by
  constructor
  · rintro ⟨a,hfit⟩
    refine ⟨coarsenedFromBins k a β,bins_to_printed_coarsened k hk x d y hdata a β hfit,?_⟩
    simp [coarsenedFromBins]
  · rintro ⟨c,hc,hβ⟩
    refine ⟨coarsenedIntercepts k c,?_⟩
    have hh := printed_coarsened_to_bins k hk x d y hdata c hc
    simpa only [hβ] using hh


/-- P023-T3(a), weight form: close-window treated and untreated means have
weights 1/n₁ and −1/n₀, and every other election has weight zero. -/
def coarsenedWeight (k : ℝ) (x d : ι → ℝ) (i : ι) : ℝ := by
  classical
  exact if i ∈ close k x then d i / (∑ l ∈ close k x, d l) -
    (1-d i) / (∑ l ∈ close k x, (1-d l)) else 0

/-- The exact difference in means is the stated finite weighted sum, pp. 5–6. -/
theorem rd_weights (k : ℝ) (x d y : ι → ℝ) :
    rd k x d y = dot (coarsenedWeight k x d) y := by
  classical
  unfold dot coarsenedWeight rd
  simp_rw [ite_mul, zero_mul, ← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter]
  rw [Finset.univ_inter]
  simp_rw [sub_mul, Finset.sum_sub_distrib, div_mul_eq_mul_div, ← Finset.sum_div]
  simp only [sub_mul, one_mul, Finset.sum_sub_distrib]

/-- P023-T3(a): all coarsened least-squares solutions have the localized
weight formula under exactly the positive winner and loser counts in the
correction, allowing ties and either endpoint of the printed bandwidth. -/
theorem corrected_coarsened_weights (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y : ι → ℝ) (hdata : TwoParty x d)
    (hn1 : 0 < ∑ i ∈ close k x, d i) (hn0 : 0 < ∑ i ∈ close k x, (1-d i))
    (β : ℝ) (hβ : CoarsenedOLS k x d y β) :
    β = dot (coarsenedWeight k x d) y ∧ β = rd k x d y ∧
    (∀ i, i ∉ close k x → coarsenedWeight k x d i = 0) ∧
    (∀ i ∈ close k x, d i = 1 → coarsenedWeight k x d i = 1 / (∑ l ∈ close k x, d l)) ∧
    (∀ i ∈ close k x, d i = 0 → coarsenedWeight k x d i = -1 / (∑ l ∈ close k x, (1-d l))) := by
  classical
  obtain ⟨a, hfit⟩ := hβ
  obtain ⟨hpart, hcentral, hconst⟩ := paper_bin_geometry k hk x d hdata
  have hC : Finset.univ.filter (fun i => binLabel k (x i) = centralLabel k) = close k x := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, close]
    simp [hcentral]
  have he : β = rd k x d y := by
    simpa only [hC, rd] using binned_ols_identity (fun i => binLabel k (x i)) (centralLabel k)
      d y a β hdata.2.1 (fun j => if centralLabel k < j then 1 else 0) hconst
      (by simpa only [hC] using hn1) (by simpa only [hC] using hn0) hfit
  refine ⟨he.trans (rd_weights k x d y), he, ?_, ?_, ?_⟩
  · intro i hi; simp [coarsenedWeight, hi]
  · intro i hi hd; simp [coarsenedWeight, hi, hd]
  · intro i hi hd; simp [coarsenedWeight, hi, hd, neg_div]

/-- P023-T3(b), T7(g): the nuisance design (1,x,...,x^J), excluding DemWin. -/
def smoothDesign (J : ℕ) (x : ι → ℝ) : ι → Fin (J+1) → ℝ := fun i j => x i ^ j.val

/-- Finite-sample residual r=d−Z(ZᵀZ)⁻¹Zᵀd, represented by the equivalent
unique least-squares projection on the powers. P023-T3(b) and T7(g). -/
def finiteResidual (J : ℕ) (x d : ι → ℝ) (i : ι) : ℝ :=
  d i - predict (smoothDesign J x) (olsCoefficients (smoothDesign J x) d) i

/-- Finite polynomial OLS observation weights r_i/(rᵀr); P023-E001. -/
def finiteWeight (J : ℕ) (x d : ι → ℝ) (i : ι) : ℝ :=
  finiteResidual J x d i / dot (finiteResidual J x d) (finiteResidual J x d)

/-- Embed polynomial-only nuisance coefficients in equation (2) by inserting
zero at the DemWin column. This preserves every fitted value. -/
def liftSmooth (J : ℕ) (c : Fin (J+1) → ℝ) (j : Fin (J+2)) : ℝ :=
  if h0 : j.val = 0 then c ⟨0, by omega⟩
  else if h1 : j.val = 1 then 0
  else c ⟨j.val-1, by have := j.isLt; omega⟩

/-- The embedding of nuisance coefficients gives the same polynomial fit. -/
theorem liftSmooth_predict (J : ℕ) (x d : ι → ℝ) (c : Fin (J+1) → ℝ) (i : ι) :
    predict (polynomialDesign J x d) (liftSmooth J c) i = predict (smoothDesign J x) c i := by
  simp [predict, polynomialDesign, smoothDesign, liftSmooth, Fin.sum_univ_succ]

/-- Full rank of (1,D,x,...,x^J) implies full rank of (1,x,...,x^J). -/
theorem smooth_fullRank (J : ℕ) (x d : ι → ℝ)
    (hfull : FullRank (polynomialDesign J x d)) : FullRank (smoothDesign J x) := by
  intro c hc
  have he := hfull (liftSmooth J c) (fun i => by rw [liftSmooth_predict]; exact hc i)
  funext j
  by_cases hj : j.val = 0
  · have hz := congrFun he ⟨0, by omega⟩
    have hje : j = (⟨0, by omega⟩ : Fin (J+1)) := Fin.ext hj
    simpa [liftSmooth, hje] using hz
  · have hz := congrFun he ⟨j.val+1, by have := j.isLt; omega⟩
    have hj1 : j.val+1 ≠ 1 := by omega
    have hje : j ≠ 0 := by intro h; exact hj (congrArg Fin.val h)
    simpa [liftSmooth, hj1, hje] using hz

/-- Symmetry of finite real column products. -/
theorem dot_comm (a b : ι → ℝ) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- An unnormalized finite FWL certificate extracts the selected coefficient
without assuming its weights or its value by definition. -/
theorem ols_residual_certificate [DecidableEq κ] (X : ι → κ → ℝ)
    (r : ι → ℝ) (a : κ → ℝ) (q : κ) (v : ℝ) (hv : v ≠ 0)
    (hspan : r = predict X a)
    (hmom : ∀ j, dot r (fun i => X i j) = if j = q then v else 0)
    (y : ι → ℝ) (c : κ → ℝ) (hc : IsOLS X y c) : c q = dot r y / v := by
  have hz : dot r (fun i => y i - predict X c i) = 0 := by
    rw [hspan, dot_predict_left]
    apply Finset.sum_eq_zero
    intro j _
    rw [hc j, mul_zero]
  have hp : dot r (predict X c) = c q * v := by
    rw [dot_predict_right]
    simp_rw [hmom]
    simp
  rw [dot_sub_right, hp] at hz
  apply (eq_div_iff hv).mpr
  linarith

/-- The finite residual is orthogonal to every nuisance power. This is
Zᵀr=0 in P023-T3(b) and T7(g), derived from actual least squares. -/
theorem finite_residual_orthogonal (J : ℕ) (x d : ι → ℝ)
    (hfull : FullRank (polynomialDesign J x d)) (j : Fin (J+1)) :
    dot (finiteResidual J x d) (fun i => x i^j.val) = 0 := by
  rw [dot_comm]
  exact chosen_ols_spec (smoothDesign J x) (smooth_fullRank J x d hfull) d j

/-- Orthogonality proves rᵀd=rᵀr in the finite FWL denominator. -/
theorem finite_residual_denominator (J : ℕ) (x d : ι → ℝ)
    (hfull : FullRank (polynomialDesign J x d)) :
    dot (finiteResidual J x d) d = dot (finiteResidual J x d) (finiteResidual J x d) := by
  let a := olsCoefficients (smoothDesign J x) d
  have hz : dot (finiteResidual J x d) (predict (smoothDesign J x) a) = 0 := by
    rw [dot_predict_right]
    apply Finset.sum_eq_zero
    intro j _
    change a j * dot (finiteResidual J x d) (fun i => x i^j.val) = 0
    rw [finite_residual_orthogonal J x d hfull j, mul_zero]
  have he := dot_sub_right (finiteResidual J x d) d (predict (smoothDesign J x) a)
  change dot (finiteResidual J x d) (finiteResidual J x d) = _ at he
  rw [hz, sub_zero] at he
  exact he.symm

/-- The residual vector lies in the column space of the full design: D minus
its fitted polynomial. Its DemWin coordinate in this representation is one. -/
theorem finite_residual_span (J : ℕ) (x d : ι → ℝ) :
    finiteResidual J x d = predict (polynomialDesign J x d)
      (fun j => (if j = 1 then 1 else 0) - liftSmooth J (olsCoefficients (smoothDesign J x) d) j) := by
  classical
  funext i
  have ht : predict (polynomialDesign J x d) (fun j => if j = 1 then 1 else 0) i = d i := by
    simp [predict, mul_ite, polynomialDesign]
  simp only [predict, mul_sub, Finset.sum_sub_distrib]
  change _ = predict (polynomialDesign J x d) (fun j => if j = 1 then 1 else 0) i -
    predict (polynomialDesign J x d) (liftSmooth J (olsCoefficients (smoothDesign J x) d)) i
  rw [ht, liftSmooth_predict]
  rfl

/-- Full rank ensures positive finite residual treatment information. It is
proved by a zero sum-of-squares argument, not assumed to get the FWL formula. -/
theorem finite_residual_positive (J : ℕ) (x d : ι → ℝ)
    (hfull : FullRank (polynomialDesign J x d)) :
    0 < dot (finiteResidual J x d) (finiteResidual J x d) := by
  classical
  have hnonneg : 0 ≤ dot (finiteResidual J x d) (finiteResidual J x d) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hne : dot (finiteResidual J x d) (finiteResidual J x d) ≠ 0 := by
    intro hz
    have hr : ∀ i, finiteResidual J x d i = 0 :=
      fun i => (Finset.sum_mul_self_eq_zero_iff Finset.univ (finiteResidual J x d)).mp hz i (Finset.mem_univ i)
    have hc := hfull (fun j => (if j = 1 then 1 else 0) -
      liftSmooth J (olsCoefficients (smoothDesign J x) d) j)
      (fun i => by rw [← finite_residual_span]; exact hr i)
    have h1 := congrFun hc ⟨1, by omega⟩
    norm_num [liftSmooth] at h1
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Finite FWL coefficient formula for every real outcome vector, derived from
normal equations and full rank. P023-T3(b) and T7(g). -/
theorem finite_ols_fwl (J : ℕ) (x d : ι → ℝ)
    (hfull : FullRank (polynomialDesign J x d)) (y : ι → ℝ) :
    polynomialOLS J x d y = dot (finiteResidual J x d) y /
      dot (finiteResidual J x d) (finiteResidual J x d) := by
  classical
  let r := finiteResidual J x d
  have hmom : ∀ j : Fin (J+2), dot r (fun i => polynomialDesign J x d i j) =
      if j = 1 then dot r r else 0 := by
    intro j
    by_cases hj0 : j.val = 0
    · have hjne : j ≠ 1 := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp only [polynomialDesign, hj0, if_pos rfl, if_neg hjne]
      simpa using finite_residual_orthogonal J x d hfull ⟨0, by omega⟩
    · by_cases hj1 : j.val = 1
      · have hje : j = 1 := Fin.ext hj1
        simp only [polynomialDesign, if_neg hj0, hj1, if_pos rfl, hje]
        exact finite_residual_denominator J x d hfull
      · have hjne : j ≠ 1 := by intro h; exact hj1 (congrArg Fin.val h)
        simp only [polynomialDesign, if_neg hj0, if_neg hj1, if_neg hjne]
        exact finite_residual_orthogonal J x d hfull ⟨j.val-1, by have := j.isLt; omega⟩
  exact ols_residual_certificate _ r _ 1 _ (ne_of_gt (finite_residual_positive J x d hfull))
    (finite_residual_span J x d) hmom y _ (chosen_ols_spec _ hfull y)

/-- Normalization of a finite residual yields the observation-weight sum. -/
theorem finite_fwl_weights (J : ℕ) (x d y : ι → ℝ) :
    dot (finiteResidual J x d) y / dot (finiteResidual J x d) (finiteResidual J x d) =
      dot (finiteWeight J x d) y := by
  unfold finiteWeight dot
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- P023-T3(b): all finite FWL identities for every degree and full-rank
design, including exactly how changing one outcome changes the coefficient. -/
theorem corrected_finite_polynomial_weights [DecidableEq ι] (J : ℕ) (hJ : 1 ≤ J) (x d : ι → ℝ)
    (hdata : TwoParty x d) (hfull : FullRank (polynomialDesign J x d)) :
    let r := finiteResidual J x d
    let w := finiteWeight J x d
    dot r d = dot r r ∧ 0 < dot r r ∧
    (∀ j ≤ J, dot r (fun i => x i^j) = 0) ∧
    (∀ y, polynomialOLS J x d y = dot r y / dot r r ∧ polynomialOLS J x d y = dot w y) ∧
    (∑ i, w i) = 0 ∧ (∀ j, 1 ≤ j → j ≤ J → (∑ i, w i*x i^j) = 0) ∧
    (∑ i, w i*d i) = 1 ∧
    (∀ (y : ι → ℝ) (i : ι) (δ : ℝ),
      polynomialOLS J x d (fun l => y l + if l = i then δ else 0) - polynomialOLS J x d y = w i*δ) := by
  classical
  let r := finiteResidual J x d
  let w := finiteWeight J x d
  let v := dot r r
  have hv : 0 < v := finite_residual_positive J x d hfull
  have hden : dot r d = v := finite_residual_denominator J x d hfull
  have ho (j : ℕ) (hj : j ≤ J) : dot r (fun i => x i^j) = 0 :=
    finite_residual_orthogonal J x d hfull ⟨j, by omega⟩
  have hw (z : ι → ℝ) : dot w z = dot r z/v := (finite_fwl_weights J x d z).symm
  have he (z : ι → ℝ) : polynomialOLS J x d z = dot w z :=
    (finite_ols_fwl J x d hfull z).trans (finite_fwl_weights J x d z)
  refine ⟨hden, hv, ho, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    exact ⟨finite_ols_fwl J x d hfull y, he y⟩
  · have hz := hw (fun _ => 1)
    have hzero : dot r (fun _ => 1) = 0 := by simpa using ho 0 (by omega)
    rw [hzero] at hz
    simpa [dot] using hz
  · intro j hj0 hj
    have hz := hw (fun i => x i^j)
    rw [ho j hj] at hz
    exact hz.trans (zero_div _)
  · have hz := hw d
    rw [hden, div_self (ne_of_gt hv)] at hz
    exact hz
  · intro y i δ
    rw [he, he]
    have hdelta : dot w (fun l => y l + if l=i then δ else 0) = dot w y + w i*δ := by
      unfold dot
      simp [mul_add, Finset.sum_add_distrib, mul_ite]
    rw [hdelta]
    ring

/-- P023-T3(c), P023-E001: write the actual finite nuisance fit as a
polynomial of degree at most J, using its least-squares coefficients. -/
def finiteFitPolynomial (J : ℕ) (x d : ι → ℝ) : Polynomial ℝ :=
  ∑ j : Fin (J+1), Polynomial.C (olsCoefficients (smoothDesign J x) d j)*Polynomial.X^j.val

/-- The polynomial representing the nuisance fit has exactly the fitted
values used in the finite residualized DemWin vector. -/
theorem finite_fit_polynomial_eval (J : ℕ) (x d : ι → ℝ) (i : ι) :
    (finiteFitPolynomial J x d).eval (x i)=
      predict (smoothDesign J x) (olsCoefficients (smoothDesign J x) d) i := by
  unfold finiteFitPolynomial
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_X,predict,smoothDesign]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The nuisance fit retains the prescribed degree J; arbitrary real margins
and coefficients do not require a numeric interpolation certificate. -/
theorem finite_fit_polynomial_degree (J : ℕ) (x d : ι → ℝ) :
    (finiteFitPolynomial J x d).natDegree ≤ J := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := j.isLt; omega)

/-- With at least one winner and loser, the nuisance projection is neither
the zero nor the one polynomial: its intercept residual equation rules both
out. This makes the root-counting argument nonvacuous. -/
theorem finite_fit_polynomial_nontrivial (J : ℕ) (x d : ι → ℝ)
    (hdata : TwoParty x d) (hfull : FullRank (polynomialDesign J x d))
    (hboth : (∃ i, d i=1) ∧ (∃ i, d i=0)) :
    finiteFitPolynomial J x d ≠ 0 ∧ finiteFitPolynomial J x d ≠ Polynomial.C 1 := by
  classical
  have h01 := hdata.2.1
  have hnonneg : ∀ i, 0 ≤ d i := by intro i; rcases h01 i with he|he <;> simp [he]
  have hnonneg0 : ∀ i, 0 ≤ 1-d i := by intro i; rcases h01 i with he|he <;> simp [he]
  have hp1 : 0 < ∑ i, d i := by
    rcases hboth.1 with ⟨i,hi⟩
    exact Finset.sum_pos' (fun j _ => hnonneg j) ⟨i,Finset.mem_univ i,by simp [hi]⟩
  have hp0 : 0 < ∑ i, (1-d i) := by
    rcases hboth.2 with ⟨i,hi⟩
    exact Finset.sum_pos' (fun j _ => hnonneg0 j) ⟨i,Finset.mem_univ i,by simp [hi]⟩
  have ho : (∑ i, finiteResidual J x d i)=0 := by
    simpa [dot] using finite_residual_orthogonal J x d hfull ⟨0,by omega⟩
  have he (i : ι) : finiteResidual J x d i=d i-(finiteFitPolynomial J x d).eval (x i) := by
    rw [finite_fit_polynomial_eval]
    rfl
  constructor
  · intro hz
    simp_rw [he,hz,Polynomial.eval_zero,sub_zero] at ho
    linarith
  · intro hz
    simp_rw [he,hz,Polynomial.eval_C] at ho
    have hs : (∑ i : ι, (d i - 1)) = -(∑ i : ι, (1 - d i)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs] at ho
    linarith

/-- P023-T3(c)'s exact root-count bound: among distinct negative margins
at most J have zero outcome weight, and among positive margins at most J do.
The two counted root polynomials are the nuisance fit and that fit minus one. -/
theorem finite_polynomial_zero_weight_counts [DecidableEq ι] (J : ℕ) (x d : ι → ℝ)
    (hdata : TwoParty x d) (hfull : FullRank (polynomialDesign J x d))
    (hboth : (∃ i, d i=1) ∧ (∃ i, d i=0)) :
    ((Finset.univ.filter (fun i => x i<0 ∧ finiteWeight J x d i=0)).image x).card ≤ J ∧
    ((Finset.univ.filter (fun i => 0<x i ∧ finiteWeight J x d i=0)).image x).card ≤ J := by
  classical
  let q := finiteFitPolynomial J x d
  have hq := finite_fit_polynomial_nontrivial J x d hdata hfull hboth
  have hdq := finite_fit_polynomial_degree J x d
  have hv := finite_residual_positive J x d hfull
  have hrzero (i : ι) (hi : finiteWeight J x d i=0) : finiteResidual J x d i=0 :=
    (div_eq_zero_iff.mp hi).resolve_right (ne_of_gt hv)
  have he (i : ι) : finiteResidual J x d i=d i-q.eval (x i) := by
    dsimp [q]
    rw [finite_fit_polynomial_eval]
    rfl
  constructor
  · apply le_trans (Polynomial.card_le_degree_of_subset_roots (p:=q) ?_) hdq
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i,hi,rfl⟩
    rcases (Finset.mem_filter.mp hi).2 with ⟨hneg,hw⟩
    have hres := hrzero i hw
    rw [he,hdata.2.2.2 i hneg] at hres
    apply (Polynomial.mem_roots hq.1).mpr
    change q.eval (x i)=0
    linarith
  · have hneq : q-Polynomial.C 1 ≠ 0 := sub_ne_zero.mpr hq.2
    have hdeg : (q-Polynomial.C 1).natDegree ≤ J :=
      (Polynomial.natDegree_sub_le _ _).trans (max_le hdq (by simp))
    apply le_trans (Polynomial.card_le_degree_of_subset_roots (p:=q-Polynomial.C 1) ?_) hdeg
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i,hi,rfl⟩
    rcases (Finset.mem_filter.mp hi).2 with ⟨hpos,hw⟩
    have hres := hrzero i hw
    rw [he,hdata.2.2.1 i hpos] at hres
    apply (Polynomial.mem_roots hneq).mpr
    change (q-Polynomial.C 1).eval (x i)=0
    rw [Polynomial.eval_sub,Polynomial.eval_C]
    linarith

/-- P023-T3(c): a full-rank finite polynomial regression cannot put zero
outcome weights on more than J distinct nonzero margins on either side. More
than 2J distinct distant margins therefore give a one-election perturbation
that changes polynomial OLS and leaves RD and coarsened OLS unchanged. -/
theorem corrected_finite_nonlocality [DecidableEq ι]
    (J : ℕ) (hJ : 1 ≤ J) (k : ℝ) (hk : 0 < k ∧ k < 1) (x d : ι → ℝ)
    (hdata : TwoParty x d) (hfull : FullRank (polynomialDesign J x d))
    (hboth : (∃ i, d i = 1) ∧ (∃ i, d i = 0)) :
    ((Finset.univ.filter (fun i => x i < 0 ∧ finiteWeight J x d i = 0)).image x).card ≤ J ∧
    ((Finset.univ.filter (fun i => 0 < x i ∧ finiteWeight J x d i = 0)).image x).card ≤ J ∧
    (((Finset.univ.filter (fun i => i ∉ close k x ∧ x i ≠ 0)).image x).card > 2*J →
      ∃ (i : ι) (y y' : ι → ℝ), i ∉ close k x ∧
      (∀ l, l ≠ i → y l = y' l) ∧ (∀ l ∈ close k x, y l = y' l) ∧
      polynomialOLS J x d y ≠ polynomialOLS J x d y' ∧ rd k x d y = rd k x d y' ∧
      (∀ β β', CoarsenedOLS k x d y β → CoarsenedOLS k x d y' β' →
        (0 < ∑ l ∈ close k x, d l) → (0 < ∑ l ∈ close k x, (1-d l)) → β = β')) := by
  classical
  have hc := finite_polynomial_zero_weight_counts J x d hdata hfull hboth
  refine ⟨hc.1,hc.2,?_⟩
  intro hmany
  have hex : ∃ i, i ∉ close k x ∧ finiteWeight J x d i ≠ 0 := by
    by_contra he
    have hw (i : ι) (hi : i ∉ close k x) : finiteWeight J x d i=0 := by
      by_contra hn
      exact he ⟨i,hi,hn⟩
    let Z := (Finset.univ.filter (fun i => i ∉ close k x ∧ x i ≠ 0)).image x
    let Zneg := (Finset.univ.filter (fun i => x i<0 ∧ finiteWeight J x d i=0)).image x
    let Zpos := (Finset.univ.filter (fun i => 0<x i ∧ finiteWeight J x d i=0)).image x
    have hsub : Z ⊆ Zneg ∪ Zpos := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨i,hi,rfl⟩
      rcases (Finset.mem_filter.mp hi).2 with ⟨hout,hne⟩
      by_cases hneg : x i<0
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hneg,hw i hout⟩,rfl⟩
      · apply Finset.mem_union_right
        have hpos : 0<x i := by
          rcases lt_trichotomy (x i) 0 with hh|hh|hh
          · exact False.elim (hneg hh)
          · exact False.elim (hne hh)
          · exact hh
        exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hpos,hw i hout⟩,rfl⟩
    have hcn : Zneg.card ≤ J := hc.1
    have hcp : Zpos.card ≤ J := hc.2
    have hcard : Z.card ≤ 2*J := by
      calc
        _ ≤ (Zneg ∪ Zpos).card := Finset.card_le_card hsub
        _ ≤ Zneg.card+Zpos.card := Finset.card_union_le _ _
        _ ≤ 2*J := by omega
    change 2*J<Z.card at hmany
    omega
  obtain ⟨i,hout,hwi⟩ := hex
  let y : ι → ℝ := fun _ => 0
  let y' : ι → ℝ := fun l => if l=i then 1 else 0
  have hagree : ∀ l ∈ close k x, y l=y' l := by
    intro l hl
    have hli : l ≠ i := by intro he; subst l; exact hout hl
    simp [y,y',hli]
  have hp0 : polynomialOLS J x d y=0 := by
    rw [finite_ols_fwl J x d hfull y]
    simp [dot,y]
  have hp1 : polynomialOLS J x d y'=finiteWeight J x d i := by
    rw [finite_ols_fwl J x d hfull y',finite_fwl_weights]
    simp [dot,y',mul_ite]
  have hrd0 : rd k x d y=0 := by simp [rd,y]
  have hrd1 : rd k x d y'=0 := by
    rw [rd_weights]
    simp [dot,y',mul_ite,coarsenedWeight,hout]
  have hrd : rd k x d y=rd k x d y' := hrd0.trans hrd1.symm
  refine ⟨i,y,y',hout,?_,hagree,?_,hrd,?_⟩
  · intro l hl; simp [y,y',hl]
  · rw [hp0,hp1]
    exact Ne.symm hwi
  · intro β β' hβ hβ' hn1 hn0
    exact (corrected_coarsened_weights k hk x d y hdata hn1 hn0 β hβ).2.1.trans
      (hrd.trans (corrected_coarsened_weights k hk x d y' hdata hn1 hn0 β' hβ').2.1.symm)

/-- Appendix A, p. 9: Ũ_j is the set of observed election pairs in bin j. -/
def binSet {η : Type*} [DecidableEq η] (B : ι → η) (j : η) : Finset ι :=
  Finset.univ.filter (fun i => B i = j)

/-- Appendix A's |Ũ_j|⁻¹∑_{i't'∈Ũ_j} z_{i't'}, p. 9. Only the bin
containing an actual observed pair is queried, so its denominator is positive;
empty bins are omitted rather than used to alter the regression. -/
def binMean {η : Type*} [DecidableEq η] (B : ι → η) (j : η) (z : ι → ℝ) : ℝ :=
  (∑ i ∈ binSet B j, z i) / (binSet B j).card

/-- The double-dotted DemWin and DV of Appendix A, p. 9: subtract the mean
of the bin containing the observed election pair. -/
def demeaned {η : Type*} [DecidableEq η] (B : ι → η) (z : ι → ℝ) (i : ι) : ℝ :=
  z i - binMean B (B i) z

/-- Exact finite sums behind Appendix A, p. 9: in a central bin with n₁
winners and n₀ losers, ∑(D−p)²=n₁n₀/(n₁+n₀)>0 and the centered FWL
ratio is the difference in the two outcome means. -/
theorem central_bin_fwl (C : Finset ι) (d y : ι → ℝ)
    (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hn1 : 0 < ∑ i ∈ C, d i) (hn0 : 0 < ∑ i ∈ C, (1-d i)) :
    let p := (∑ i ∈ C, d i) / (C.card : ℝ)
    let ybar := (∑ i ∈ C, y i) / (C.card : ℝ)
    let V := ∑ i ∈ C, (d i-p)^2
    V = (∑ i ∈ C, d i)*(∑ i ∈ C, (1-d i))/(C.card : ℝ) ∧ 0 < V ∧
    V⁻¹ * (∑ i ∈ C, (d i-p)*(y i-ybar)) =
      (∑ i ∈ C, d i*y i)/(∑ i ∈ C, d i) -
      (∑ i ∈ C, (1-d i)*y i)/(∑ i ∈ C, (1-d i)) := by
  let n : ℝ := C.card
  let n1 := ∑ i ∈ C, d i
  let n0 := ∑ i ∈ C, (1-d i)
  let S := ∑ i ∈ C, y i
  let A := ∑ i ∈ C, d i*y i
  let B := ∑ i ∈ C, (1-d i)*y i
  let p := n1/n
  let ybar := S/n
  have hcount : n = n1+n0 := by
    simp [n, n1, n0, Finset.sum_sub_distrib]
  have hn : 0 < n := by linarith
  have hsum : S = A+B := by
    dsimp [S,A,B]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hd2 (i : ι) : d i^2=d i := by rcases hd i with h | h <;> simp [h]
  have hrzero : (∑ i ∈ C, (d i-p)) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    change n1-n*p=0
    dsimp [p]
    field_simp [ne_of_gt hn]
    ring
  have hV : (∑ i ∈ C, (d i-p)^2) = n1-2*p*n1+p^2*n := by
    simp_rw [show ∀ i, (d i-p)^2=d i^2-2*p*d i+p^2 by intro i; ring]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hd2,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    change n1-2*p*n1+n*p^2 = _
    ring
  have hVformula : (∑ i ∈ C, (d i-p)^2) = n1*n0/n := by
    rw [hV]
    dsimp [p]
    rw [hcount]
    have hne : n1+n0 ≠ 0 := by linarith
    field_simp [hne]
    ring
  have hVpos : 0 < ∑ i ∈ C, (d i-p)^2 := by
    rw [hVformula]
    exact div_pos (mul_pos hn1 hn0) hn
  have hcov : (∑ i ∈ C, (d i-p)*(y i-ybar)) = A-p*S := by
    simp_rw [show ∀ i, (d i-p)*(y i-ybar) = d i*y i-p*y i-ybar*(d i-p) by intro i; ring]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hrzero, mul_zero, sub_zero]
    rfl
  refine ⟨hVformula, hVpos, ?_⟩
  change (∑ i ∈ C, (d i-p)^2)⁻¹ * (∑ i ∈ C, (d i-p)*(y i-ybar)) = A/n1-B/n0
  rw [hVformula, hcov]
  dsimp [p]
  rw [hsum, hcount]
  have hn1ne : n1 ≠ 0 := ne_of_gt hn1
  have hn0ne : n0 ≠ 0 := ne_of_gt hn0
  have hnne : n1+n0 ≠ 0 := by linarith
  field_simp
  ring

/-- P023-T9, the corrected Appendix A statement in full, explicitly indexed
by observed pairs (region,election). The partition and central-bin identification
use the exact printed bin inequalities; both FWL sums run over those pairs. -/
theorem corrected_appendix_pairs (S : Finset (ℕ × ℕ))
    (k : ℝ) (hk : 0 < k ∧ k < 1)
    (x d y : {p : ℕ × ℕ // p ∈ S} → ℝ) (hdata : TwoParty x d)
    (hc : Condition1 k x) (β : ℝ) (hβ : CoarsenedOLS k x d y β) :
    let B := fun p => binLabel k (x p)
    let r := demeaned B d
    let z := demeaned B y
    (∀ p j, inBin k j.val (x p) ↔ B p = j) ∧
    (binSet B (centralLabel k) = close k x) ∧
    (∀ p, p ∉ close k x → r p = 0) ∧
    0 < (∑ p ∈ close k x, r p^2) ∧
    β = (∑ p ∈ close k x, r p^2)⁻¹ * (∑ p ∈ close k x, r p*z p) := by
  classical
  let B := fun p => binLabel k (x p)
  let r := demeaned B d
  let z := demeaned B y
  obtain ⟨hpart,hcentral,hconst⟩ := paper_bin_geometry k hk x d hdata
  have hC : binSet B (centralLabel k) = close k x := by
    ext p
    simp only [binSet, Finset.mem_filter, Finset.mem_univ, true_and, B, close]
    simp [hcentral]
  have houtside : ∀ p, p ∉ close k x → r p = 0 := by
    intro p hp
    have hpB : B p ≠ centralLabel k := by
      intro he
      have he' : -k < x p ∧ x p ≤ k := (hcentral p).mp he
      exact hp (by simp [close, he'])
    have hpMem : p ∈ binSet B (B p) := by simp [binSet]
    have hn : 0 < ((binSet B (B p)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨p,hpMem⟩
    have hsum : (∑ l ∈ binSet B (B p), d l) = (binSet B (B p)).card * d p := by
      calc
        _ = ∑ l ∈ binSet B (B p), d p := by
          apply Finset.sum_congr rfl
          intro l hl
          have hleq : B l=B p := (Finset.mem_filter.mp hl).2
          have hlB : B l ≠ centralLabel k := by rw [hleq]; exact hpB
          have hdl := hconst l hlB
          have hdp := hconst p hpB
          change d l = if centralLabel k < B l then 1 else 0 at hdl
          change d p = if centralLabel k < B p then 1 else 0 at hdp
          rw [hdl,hleq,← hdp]
        _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
    change d p - binMean B (B p) d = 0
    unfold binMean
    rw [hsum]
    field_simp
    ring
  have hrC (p) (hp : p ∈ close k x) :
      r p = d p - (∑ l ∈ close k x, d l)/(close k x).card := by
    have he : B p=centralLabel k := (hcentral p).mpr (by simpa [close] using hp)
    dsimp [r,demeaned]
    rw [he]
    unfold binMean
    rw [hC]
  have hzC (p) (hp : p ∈ close k x) :
      z p = y p - (∑ l ∈ close k x, y l)/(close k x).card := by
    have he : B p=centralLabel k := (hcentral p).mpr (by simpa [close] using hp)
    dsimp [z,demeaned]
    rw [he]
    unfold binMean
    rw [hC]
  have hvEq : (∑ p ∈ close k x, r p^2) =
      ∑ p ∈ close k x, (d p-(∑ l ∈ close k x, d l)/(close k x).card)^2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hrC p hp]
  have hcEq : (∑ p ∈ close k x, r p*z p) =
      ∑ p ∈ close k x, (d p-(∑ l ∈ close k x, d l)/(close k x).card)*
        (y p-(∑ l ∈ close k x, y l)/(close k x).card) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hrC p hp,hzC p hp]
  have hn := close_counts_positive k x d hdata hc
  have hfwl := central_bin_fwl (close k x) d y hdata.2.1 hn.1 hn.2
  refine ⟨hpart,hC,houtside,?_,?_⟩
  · rw [hvEq]
    exact hfwl.2.1
  · rw [hvEq,hcEq]
    exact (proposition1 k hk x d y hdata hc β hβ).trans hfwl.2.2.symm

/-- P023-T7(b)'s exact integral algebra. Once residual orthogonality and the
FWL coefficient have been obtained from least squares, subtracting any
orthogonal polynomial changes neither the numerator nor the coefficient bias.
Integrability is explicit, so no total-integral convention supplies the result. -/
theorem residual_bias_integral_identity (μ : Measure ℝ) (r h p : ℝ → ℝ)
    (α β v : ℝ) (hv : v ≠ 0)
    (hr : Integrable r μ) (hrD : Integrable (fun x => r x * party x) μ)
    (hrh : Integrable (fun x => r x * h x) μ) (hrp : Integrable (fun x => r x * p x) μ)
    (hzero : expectation μ r = 0) (hD : expectation μ (fun x => r x * party x) = v)
    (hp : expectation μ (fun x => r x * p x) = 0) :
    expectation μ (fun x => r x * (α + β*party x + h x)) / v - β =
      expectation μ (fun x => r x * (h x-p x)) / v := by
  have hleft : expectation μ (fun x => r x * (α + β*party x + h x)) =
      α*expectation μ r + β*expectation μ (fun x => r x*party x) +
      expectation μ (fun x => r x*h x) := by
    unfold expectation
    simp_rw [show ∀ x, r x*(α+β*party x+h x) = α*r x+β*(r x*party x)+r x*h x by intro x; ring]
    have hsum : Integrable (fun x => α*r x+β*(r x*party x)) μ := (hr.const_mul α).add (hrD.const_mul β)
    rw [integral_add hsum hrh,
      integral_add (hr.const_mul α) (hrD.const_mul β), integral_const_mul, integral_const_mul]
  have hright : expectation μ (fun x => r x*(h x-p x)) = expectation μ (fun x => r x*h x) := by
    unfold expectation at hp ⊢
    simp_rw [mul_sub]
    rw [integral_sub hrh hrp, hp, sub_zero]
  rw [hleft, hright, hzero, hD]
  field_simp
  ring

/-- P023-T7(c), uniform-error bound for a genuine population integral:
|E[ra]/v| ≤ (E|r|/v) ε whenever |a|≤ε almost surely and v>0. -/
theorem residual_uniform_error_bound (μ : Measure ℝ) (r a : ℝ → ℝ) (ε v : ℝ)
    (hv : 0 < v) (hrabs : Integrable (fun x => |r x|) μ)
    (hprod : Integrable (fun x => r x*a x) μ)
    (hbound : ∀ᵐ x ∂μ, |a x| ≤ ε) :
    |expectation μ (fun x => r x*a x) / v| ≤ expectation μ (fun x => |r x|) / v * ε := by
  have hi : |expectation μ (fun x => r x*a x)| ≤
      ε*expectation μ (fun x => |r x|) := by
    calc
      _ ≤ ∫ x, |r x*a x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, ε*|r x| ∂μ := by
        apply integral_mono_ae hprod.abs (hrabs.const_mul ε)
        filter_upwards [hbound] with x hx
        rw [abs_mul]
        nlinarith [abs_nonneg (r x)]
      _ = _ := integral_const_mul _ _
  rw [abs_div, abs_of_pos hv]
  calc
    _ ≤ (ε*expectation μ (fun x => |r x|)) / v := div_le_div_of_nonneg_right hi hv.le
    _ = _ := by ring

/-- The integral Cauchy–Schwarz inequality used in P023-T7(c), derived
from the nonnegative square ∫(t r−a)² with t=E[ra]/E[r²]. -/
theorem residual_rms_error_bound (μ : Measure ℝ) (r a : ℝ → ℝ)
    (hrr : Integrable (fun x => r x^2) μ) (haa : Integrable (fun x => a x^2) μ)
    (hra : Integrable (fun x => r x*a x) μ)
    (hv : 0 < expectation μ (fun x => r x^2)) :
    |expectation μ (fun x => r x*a x) / expectation μ (fun x => r x^2)| ≤
      Real.sqrt (expectation μ (fun x => a x^2)) /
        Real.sqrt (expectation μ (fun x => r x^2)) := by
  let v := expectation μ (fun x => r x^2)
  let B := expectation μ (fun x => a x^2)
  let C := expectation μ (fun x => r x*a x)
  let t := C/v
  have hB : 0 ≤ B := integral_nonneg (fun x => sq_nonneg _)
  have hsq : 0 ≤ t^2*v-2*t*C+B := by
    have hn : 0 ≤ ∫ x, (t*r x-a x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    have he : (∫ x, (t*r x-a x)^2 ∂μ) = t^2*v-2*t*C+B := by
      simp_rw [show ∀ x, (t*r x-a x)^2 = t^2*r x^2-(2*t)*(r x*a x)+a x^2 by intro x; ring]
      have hf1 : Integrable (fun x => t^2*r x^2) μ := hrr.const_mul _
      have hf2 : Integrable (fun x => (2*t)*(r x*a x)) μ := hra.const_mul _
      have hmid : Integrable (fun x => t^2*r x^2-(2*t)*(r x*a x)) μ := hf1.sub hf2
      rw [integral_add hmid haa,
        integral_sub hf1 hf2, integral_const_mul, integral_const_mul]
      rfl
    rw [he] at hn
    exact hn
  have htv : t*v=C := by dsimp [t]; exact div_mul_cancel₀ _ (ne_of_gt hv)
  have ht2 : t^2*v^2=C^2 := by calc
    _ = (t*v)^2 := by ring
    _ = _ := by rw [htv]
  have htC : t*C*v=C^2 := by calc
    _ = (t*v)*C := by ring
    _ = _ := by rw [htv]; ring
  have hC2 : C^2 ≤ v*B := by
    have hn := mul_nonneg hsq hv.le
    nlinarith [ht2, htC]
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hsB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hroot : (Real.sqrt v * Real.sqrt B)^2 = v*B := by
    rw [mul_pow, Real.sq_sqrt hv.le, Real.sq_sqrt hB]
  have habs : |C| ≤ Real.sqrt v * Real.sqrt B := by
    nlinarith [sq_abs C, abs_nonneg C, mul_nonneg hsv.le hsB]
  change |C/v| ≤ Real.sqrt B / Real.sqrt v
  rw [abs_div, abs_of_pos hv]
  calc
    _ ≤ (Real.sqrt v*Real.sqrt B)/v := div_le_div_of_nonneg_right habs hv.le
    _ = _ := by
      apply (div_eq_div_iff (ne_of_gt hv) (ne_of_gt hsv)).mpr
      have hs := Real.sq_sqrt hv.le
      nlinarith

/-- P023-T7(d), P023-E002: every centered treatment residual
with E[rD]=v>0 has amplification E|r|/v at least two. -/
theorem residual_amplification_lower_bound (μ : Measure ℝ) (r : ℝ → ℝ) (v : ℝ)
    (hv : 0 < v) (hr : Integrable r μ)
    (hrD : Integrable (fun x => r x*party x) μ)
    (hzero : expectation μ r=0)
    (hD : expectation μ (fun x => r x*party x)=v) :
    2 ≤ expectation μ (fun x => |r x|)/v := by
  have hsign : Integrable (fun x => r x*(2*party x-1)) μ := by
    have he : (fun x => r x*(2*party x-1)) = (fun x => 2*(r x*party x)-r x) := by
      funext x; ring
    rw [he]
    exact (hrD.const_mul 2).sub hr
  have hpair : expectation μ (fun x => r x*(2*party x-1)) = 2*v := by
    unfold expectation at hzero hD ⊢
    simp_rw [show ∀ x, r x*(2*party x-1)=2*(r x*party x)-r x by intro x; ring]
    rw [integral_sub (hrD.const_mul 2) hr,integral_const_mul,hzero,hD]
    ring
  have hle : expectation μ (fun x => r x*(2*party x-1)) ≤
      expectation μ (fun x => |r x|) := by
    apply integral_mono hsign hr.abs
    intro x
    by_cases hx : 0 ≤ x
    · simpa [party,hx,show (2:ℝ)-1=1 by norm_num] using le_abs_self (r x)
    · simpa [party,hx] using neg_le_abs (r x)
  rw [hpair] at hle
  exact (le_div_iff₀ hv).mpr hle

/-- P023-T8's rate follows from the two finite inequalities v≥cδ/(4n) and
ε≤4KL/n together with the RMS bound; no asymptotic conclusion is assumed. -/
theorem repaired_rate_from_finite_bounds (b β ε v c δ K L n : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (hn : 0 < n) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hv : c*δ/(4*n) ≤ v) (he : ε ≤ 4*K*L/n)
    (hb : |b-β| ≤ ε / Real.sqrt v) :
    |b-β| ≤ 8*K*L / Real.sqrt (c*δ*n) := by
  have hcd : 0 < c*δ := mul_pos hc hδ
  have hv0 : 0 < c*δ/(4*n) := div_pos hcd (by positivity)
  have hvpos : 0 < v := lt_of_lt_of_le hv0 hv
  have hlow : 0 < Real.sqrt (c*δ/(4*n)) := Real.sqrt_pos.mpr hv0
  have hmono := Real.sqrt_le_sqrt hv
  have hnum : 0 ≤ 4*K*L/n := by positivity
  calc
    _ ≤ ε/Real.sqrt v := hb
    _ ≤ (4*K*L/n)/Real.sqrt v := div_le_div_of_nonneg_right he (Real.sqrt_nonneg _)
    _ ≤ (4*K*L/n)/Real.sqrt (c*δ/(4*n)) := div_le_div_of_nonneg_left hnum hlow hmono
    _ = _ := by
      rw [Real.sqrt_div hcd.le, Real.sqrt_mul hcd.le]
      have h4 : Real.sqrt (4*n) = 2*Real.sqrt n := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
          show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
      rw [h4]
      have hs1 : Real.sqrt (c*δ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hcd)
      have hs2 : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
      field_simp [hs1, hs2, ne_of_gt hn]
      rw [Real.sq_sqrt hn.le]
      ring

/-- Exact numerical algebra of the clustered-law coefficient certificate,
P023-T5(iv); the integration and population-OLS connection remain separate. -/
theorem clustered_bias_rational_certificate :
    -((1-(1/1000:ℝ)^4)*(1/2000)^2/6+2*(1/1000)^4*(1/2000)^3) /
      ((1-(1/1000:ℝ)^4)*(1/2000)^2/6+(1/1000)^4/12) =
      -499999999999503/500000999999500 := by
  norm_num

/-- Exact degree-1 and degree-7 sigmoid bias numbers and tiny fit-improvement
bound in P023-T4(iv),(v). These algebraic certificates do not assert
probability-law properties. -/
theorem sigmoid_rational_certificates :
    2*(1/20:ℝ)*(1-1/10000)^2 = 99980001/1000000000 ∧
    (1/10:ℝ)-(4096/6125)*(1/10000)+(6/5)*(1/10000)^2-(33/25)*(1/10000)^4+
      (858/875)*(1/10000)^6-(143/490)*(1/10000)^8 =
      4896723787999993532000048047999857/49000000000000000000000000000000000 ∧
    (1/20:ℝ)^2*(1/10000)/3 = 1/12000000 := by
  norm_num

/-- The uniform law has probability mass one and is
supported on [-1,1]. This rules out a degenerate formal measure in T3(e),
T4, T6 and the uniform finite lemmas of T7/T8. -/
theorem uniform_law_normalized : ProbabilityLaw uniformMargins ∧ MarginSupport uniformMargins := by
  constructor
  · norm_num [ProbabilityLaw, uniformMargins, Measure.smul_apply, Real.volume_Icc]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  · simp [MarginSupport, uniformMargins, Measure.smul_apply, Measure.restrict_apply,
      measurableSet_Icc, measurableSet_Icc.compl]

/-- T6's gliding-hump lower-bound arithmetic (P023-E002): a main
contribution κ/(2·4^m) and tail cost κ/(3·4^m) leave at least m
if κ≥6m4^m. Analytic existence of the polynomials is not assumed here. -/
theorem gliding_hump_finite_inequality (m : ℕ) (κ : ℝ)
    (hκ : 6*(m:ℝ)*4^m ≤ κ) :
    (4:ℝ)^(- (m:ℤ))*κ/2 - (4:ℝ)^(- (m:ℤ))*κ/3 ≥ (m:ℝ) := by
  have hp : 0 < (4:ℝ)^m := by positivity
  have he : (4:ℝ)^(- (m:ℤ)) = 1/(4:ℝ)^m := by simp [zpow_neg, zpow_natCast, one_div]
  rw [he]
  have h := (div_le_div_of_nonneg_right hκ hp.le)
  have hne : (4:ℝ)^m ≠ 0 := ne_of_gt hp
  field_simp
  nlinarith


/-- Fixed-margin conditional expectation commutes with the finite polynomial
OLS estimator. Outcomes are integrable under their conditional law; no
unconditional integrability of an inverse random design is assumed. -/
theorem finite_ols_mean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (J : ℕ) (x d : ι → ℝ) (hfull : FullRank (polynomialDesign J x d))
    (Y : ι → Ω → ℝ) (hint : ∀ i, Integrable (Y i) P) :
    (∫ ω, polynomialOLS J x d (fun i => Y i ω) ∂P) =
      polynomialOLS J x d (fun i => ∫ ω, Y i ω ∂P) := by
  have he (y : ι → ℝ) : polynomialOLS J x d y = dot (finiteWeight J x d) y :=
    (finite_ols_fwl J x d hfull y).trans (finite_fwl_weights J x d y)
  simp_rw [he]
  unfold dot
  rw [integral_finset_sum Finset.univ (fun i _ => (hint i).const_mul _)]
  simp_rw [integral_const_mul]

/-- Auxiliary integral linearity for the finite FWL formula: raw outcome
integrals over an arbitrary measure produce the residual pairing. This is an
algebraic lemma, not a conditional-expectation statement from the paper. -/
theorem finite_ols_bias_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (J : ℕ) (hJ : 1 ≤ J) (x d : ι → ℝ) (hdata : TwoParty x d)
    (hfull : FullRank (polynomialDesign J x d)) (α β : ℝ) (h : ℝ → ℝ)
    (Y : ι → Ω → ℝ) (hint : ∀ i, Integrable (Y i) P)
    (hmean : ∀ i, (∫ ω, Y i ω ∂P) = α+β*d i+h (x i)) :
    0 < dot (finiteResidual J x d) (finiteResidual J x d) ∧
    (∫ ω, polynomialOLS J x d (fun i => Y i ω) ∂P) - β =
      dot (finiteResidual J x d) (fun i => h (x i)) /
        dot (finiteResidual J x d) (finiteResidual J x d) := by
  classical
  have hw := corrected_finite_polynomial_weights J hJ x d hdata hfull
  have he (y : ι → ℝ) : polynomialOLS J x d y = dot (finiteWeight J x d) y := (hw.2.2.2.1 y).2
  refine ⟨finite_residual_positive J x d hfull, ?_⟩
  rw [finite_ols_mean P J x d hfull Y hint, he]
  simp_rw [hmean]
  have halg : dot (finiteWeight J x d) (fun i => α+β*d i+h (x i)) =
      α*(∑ i, finiteWeight J x d i)+β*(∑ i, finiteWeight J x d i*d i)+
      dot (finiteWeight J x d) (fun i => h (x i)) := by
    unfold dot
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [halg, hw.2.2.2.2.1, hw.2.2.2.2.2.2.1]
  simp only [mul_zero,mul_one,zero_add,add_sub_cancel_left]
  exact (finite_fwl_weights J x d (fun i => h (x i))).symm

/-- P023-T7(g): given fixed margins and their conditional probability law,
with d_i=I[x_i≥0] including ties, the exact conditional coefficient error is
Σ r_i h(x_i)/Σ r_i² and the denominator is positive. No unconditional
inverse-matrix expectation or asymptotic approximation is asserted. -/
theorem finite_conditional_bias {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hprob : ProbabilityLaw P)
    (J : ℕ) (hJ : 1 ≤ J) (x d : ι → ℝ) (hdata : TwoParty x d)
    (hd : ∀ i, d i = party (x i))
    (hfull : FullRank (polynomialDesign J x d)) (α β : ℝ) (h : ℝ → ℝ)
    (Y : ι → Ω → ℝ) (hint : ∀ i, Integrable (Y i) P)
    (hmean : ∀ i, (∫ ω, Y i ω ∂P) = α+β*d i+h (x i)) :
    0 < dot (finiteResidual J x d) (finiteResidual J x d) ∧
    (∫ ω, polynomialOLS J x d (fun i => Y i ω) ∂P) - β =
      dot (finiteResidual J x d) (fun i => h (x i)) /
        dot (finiteResidual J x d) (finiteResidual J x d) := by
  exact finite_ols_bias_integral P J hJ x d hdata hfull α β h Y hint hmean


/-- Every polynomial of degree at most J is annihilated by the finite
residual, not just the individual powers. P023-T3(b), T7(g). -/
theorem finite_residual_polynomial (J : ℕ) (x d : ι → ℝ)
    (hfull : FullRank (polynomialDesign J x d)) (p : Polynomial ℝ) (hp : p.natDegree ≤ J) :
    dot (finiteResidual J x d) (fun i => p.eval (x i)) = 0 := by
  have hpeval (i : ι) := Polynomial.eval_eq_sum_range' (show p.natDegree < J+1 by omega) (x i)
  unfold dot
  simp_rw [hpeval, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have hjle : j ≤ J := by have := Finset.mem_range.mp hj; omega
  have he : (∑ i, finiteResidual J x d i * (p.coeff j*x i^j)) =
      p.coeff j * dot (finiteResidual J x d) (fun i => x i^j) := by
    unfold dot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, finite_residual_orthogonal J x d hfull ⟨j, by omega⟩, mul_zero]

/-- Exact finite second-moment algebra: integrable variables with integrable
squares and zero cross moments satisfy ∫(Σ w_i u_i)² = Σ w_i² ∫u_i².
The product integrability is proved by domination by the two squares. -/
theorem weighted_uncorrelated_squares [DecidableEq ι]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (w : ι → ℝ)
    (u : ι → Ω → ℝ) (hu : ∀ i, Integrable (u i) P)
    (hsq : ∀ i, Integrable (fun ω => u i ω^2) P)
    (hcorr : ∀ i j, i ≠ j → (∫ ω, u i ω*u j ω ∂P) = 0) :
    (∫ ω, (∑ i, w i*u i ω)^2 ∂P) = ∑ i, w i^2*(∫ ω, u i ω^2 ∂P) := by
  have hprod (i j : ι) : Integrable (fun ω => u i ω*u j ω) P := by
    apply ((hsq i).add (hsq j)).mono' ((hu i).aestronglyMeasurable.mul (hu j).aestronglyMeasurable)
    apply ae_of_all
    intro ω
    change |u i ω*u j ω| ≤ u i ω^2+u j ω^2
    rw [abs_mul]
    nlinarith [sq_abs (u i ω),sq_abs (u j ω),
      sq_nonneg (|u i ω|-|u j ω|),mul_nonneg (abs_nonneg (u i ω)) (abs_nonneg (u j ω))]
  have hexp (ω : Ω) : (∑ i, w i*u i ω)^2 =
      ∑ i, ∑ j, (w i*w j)*(u i ω*u j ω) := by
    rw [pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexp]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => (hprod i j).const_mul _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => (hprod i j).const_mul _)]
  simp_rw [integral_const_mul]
  have hmom (j : ι) : (∫ ω, u i ω*u j ω ∂P) =
      if j=i then (∫ ω, u i ω^2 ∂P) else 0 := by
    by_cases hj : j=i
    · subst j; simp [pow_two]
    · simp only [if_neg hj]
      exact hcorr i j (Ne.symm hj)
  simp_rw [hmom,mul_ite,mul_zero]
  simp [pow_two]

/-- P023-T3(d) and T7(g): fixed margins are conditioned on by treating their
conditional outcome law P as a genuine probability measure. The mean identity
needs only integrable outcomes; the variance identity assumes square-integrable,
pairwise uncorrelated errors. These are not unconditional inverse-matrix moments. -/
theorem corrected_finite_conditional_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (hprob : P Set.univ = 1)
    (J : ℕ) (hJ : 1 ≤ J) (x d : ι → ℝ) (hdata : TwoParty x d)
    (hfull : FullRank (polynomialDesign J x d)) (α β : ℝ) (h : ℝ → ℝ)
    (Y : ι → Ω → ℝ) (hint : ∀ i, MeasureTheory.Integrable (Y i) P)
    (hmean : ∀ i, (∫ ω, Y i ω ∂P) = α + β*d i+h (x i)) :
    (∫ ω, polynomialOLS J x d (fun i => Y i ω) ∂P) - β =
      dot (finiteResidual J x d) (fun i => h (x i)) /
        dot (finiteResidual J x d) (finiteResidual J x d) ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ J → (∀ i, h (x i) = p.eval (x i)) →
      (∫ ω, polynomialOLS J x d (fun i => Y i ω) ∂P) = β) ∧
    (let u := fun i ω => Y i ω - (α+β*d i+h (x i))
     (∀ i, MeasureTheory.Integrable (fun ω => u i ω^2) P) →
     (∀ i l, i ≠ l → (∫ ω, u i ω * u l ω ∂P) = 0) →
     (∫ ω, (polynomialOLS J x d (fun i => Y i ω) -
       (∫ ω', polynomialOLS J x d (fun i => Y i ω') ∂P))^2 ∂P) =
       ∑ i, (finiteWeight J x d i)^2 * (∫ ω, u i ω^2 ∂P)) ∧
    (∀ i (σ2 : ℝ), finiteWeight J x d i ≠ 0 → 0 < σ2 → 0 < (finiteWeight J x d i)^2*σ2) := by
  classical
  letI : IsProbabilityMeasure P := ⟨hprob⟩
  have hbias := finite_ols_bias_integral P J hJ x d hdata hfull α β h Y hint hmean
  have he (y : ι → ℝ) : polynomialOLS J x d y = dot (finiteWeight J x d) y :=
    (finite_ols_fwl J x d hfull y).trans (finite_fwl_weights J x d y)
  refine ⟨hbias.2, ?_, ?_, ?_⟩
  · intro p hp hhp
    have hpoly : (fun i => h (x i)) = (fun i => p.eval (x i)) := funext hhp
    have hz := hbias.2
    rw [hpoly, finite_residual_polynomial J x d hfull p hp, zero_div] at hz
    linarith
  · dsimp only
    intro hsq hcorr
    let u := fun i ω => Y i ω - (α+β*d i+h (x i))
    have hu : ∀ i, Integrable (u i) P := fun i => (hint i).sub (integrable_const _)
    have hE : (∫ ω, polynomialOLS J x d (fun i => Y i ω) ∂P) =
        dot (finiteWeight J x d) (fun i => α+β*d i+h (x i)) := by
      rw [finite_ols_mean P J x d hfull Y hint, he]
      simp_rw [hmean]
    have hcenter (ω : Ω) : polynomialOLS J x d (fun i => Y i ω) -
        (∫ ω', polynomialOLS J x d (fun i => Y i ω') ∂P) =
        ∑ i, finiteWeight J x d i*u i ω := by
      rw [he,hE]
      unfold dot
      simp only [u,mul_sub,Finset.sum_sub_distrib]
    calc
      _ = ∫ ω, (∑ i, finiteWeight J x d i*u i ω)^2 ∂P := by
        apply integral_congr_ae
        apply ae_of_all
        intro ω
        exact congrArg (fun t : ℝ => t^2) (hcenter ω)
      _ = _ := weighted_uncorrelated_squares P (finiteWeight J x d) u hu hsq hcorr
  · intro i σ2 hi hσ
    exact mul_pos (sq_pos_of_ne_zero hi) hσ


/-- Mean squared prediction risk under the joint election law, giving a
precise reading of the Remark's further-fit criterion, p. 7. The predictor
is a measurable function of DemVot. -/
def predictionRisk (ν : Measure (ℝ × ℝ)) (f : ℝ → ℝ) : ℝ :=
  ∫ z, (z.2-f z.1)^2 ∂ν

/-- Minimum population prediction risk within equation (2)'s full regressor
span, including the intercept and party indicator. P023-E002. -/
def fittedRisk (ν : Measure (ℝ × ℝ)) (J : ℕ) : ℝ :=
  sInf {e | ∃ c : Fin (J+2) → ℝ,
    e = predictionRisk ν (predict (polynomialDesign J (fun x : ℝ => x) party) c)}


/-- Appendix B's continuity assertion, P023-T12 finite lemma (ii), explicitly
including the finite left limit the printed definition of α presupposes. -/
theorem appendix_smooth_continuous (g f : ℝ → ℝ) (α : ℝ)
    (hg : ContinuousOn g (Set.Ico (-1) 0)) (hf : ContinuousOn f (Set.Icc 0 1))
    (hleft : Tendsto g (nhdsWithin 0 (Set.Iio 0)) (nhds α)) :
    ContinuousOn (appendixSmooth g f α (f 0-α)) (Set.Icc (-1) 1) := by
  have hsum : α+(f 0-α)=f 0 := by ring
  change ContinuousOn (fun x => if x<0 then g x-α else f x-(α+(f 0-α))) (Set.Icc (-1) 1)
  simp only [hsum]
  apply ContinuousOn.if'
  · intro a ha
    have ha0 : a=0 := by
      have hh : a ∈ frontier (Set.Iio (0:ℝ)) := ha.2
      simpa only [frontier_Iio,Set.mem_singleton_iff] using hh
    subst a
    have ht : Tendsto (fun x => g x-α) (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
      simpa using hleft.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => α) (nhdsWithin 0 (Set.Iio 0)) (nhds α))
    have hsub : Set.Icc (-1:ℝ) 1 ∩ {x : ℝ | x<0} ⊆ Set.Iio (0:ℝ) := by
      intro x hx
      exact hx.2
    simpa only [lt_self_iff_false,ite_false,sub_self] using
      ht.mono_left (nhdsWithin_mono 0 hsub)
  · intro a ha
    have ha0 : a=0 := by
      have hh : a ∈ frontier (Set.Iio (0:ℝ)) := ha.2
      simpa only [frontier_Iio,Set.mem_singleton_iff] using hh
    subst a
    have hsub : Set.Icc (-1:ℝ) 1 ∩ {x | ¬ x<0} ⊆ Set.Icc 0 1 := by
      intro x hx
      exact ⟨le_of_not_gt hx.2,hx.1.2⟩
    have ht := ((hf 0 (by norm_num)).sub (continuousWithinAt_const :
      ContinuousWithinAt (fun _ : ℝ => f 0) (Set.Icc 0 1) 0)).mono hsub
    change Tendsto (fun x : ℝ => f x-f 0)
      (nhdsWithin 0 (Set.Icc (-1:ℝ) 1 ∩ {x : ℝ | ¬ x<0})) (nhds (f 0-f 0)) at ht
    simpa only [lt_self_iff_false,ite_false] using ht
  · apply (hg.sub continuousOn_const).mono
    intro x hx
    exact ⟨hx.1.1,hx.2⟩
  · apply (hf.sub continuousOn_const).mono
    intro x hx
    exact ⟨le_of_not_gt hx.2,hx.1.2⟩

/-- The exact Weierstrass step printed on p. 10, P023-T12 finite lemma (iii),
 also used in T6's gliding-hump construction: continuous h with h(0)=0 can
be uniformly approximated by a polynomial with zero constant coefficient. -/
theorem weierstrass_without_constant (h : ℝ → ℝ)
    (hc : ContinuousOn h (Set.Icc (-1) 1)) (hzero : h 0 = 0) :
    ∀ ε > 0, ∃ p : Polynomial ℝ, p.eval 0=0 ∧
      ∀ x ∈ Set.Icc (-1) 1, |h x-p.eval x| < ε := by
  intro ε hε
  obtain ⟨q,hq⟩ := exists_polynomial_near_of_continuousOn (-1) 1 h hc (ε/2) (by positivity)
  refine ⟨q-Polynomial.C (q.eval 0), by simp, ?_⟩
  intro x hx
  have h0 := hq 0 (by norm_num)
  rw [hzero,sub_zero] at h0
  calc
    |h x-(q-Polynomial.C (q.eval 0)).eval x| = |(h x-q.eval x)+q.eval 0| := by
      congr 1
      simp only [Polynomial.eval_sub,Polynomial.eval_C]
      ring
    _ ≤ |h x-q.eval x|+|q.eval 0| := abs_add_le _ _
    _ < ε/2+ε/2 := add_lt_add (by simpa only [abs_sub_comm] using hq x hx) h0
    _ = ε := by ring

/-- Exact central-binomial recurrence used in the uniform-law variance
calculation: c_{n+1}(2n+2)=c_n(2n+1). -/
theorem central_binomial_recurrence (n : ℕ) :
    centralBinomial (n+1) * (2*(n:ℝ)+2) = centralBinomial n * (2*(n:ℝ)+1) := by
  have h1 := Nat.choose_mul_succ_eq (2*n) n
  have h2 := Nat.choose_mul_succ_eq (2*n+1) (n+1)
  rw [Nat.choose_symm_half] at h2
  have e1 : 2*n+1-n=n+1 := by omega
  have e3 : 2*n+1+1=2*(n+1) := by omega
  have e4 : 2*(n+1)-(n+1)=n+1 := by omega
  simp only [e1] at h1
  simp only [e3,e4] at h2
  have r1 : (Nat.choose (2*n) n : ℝ)*(2*(n:ℝ)+1) =
      (Nat.choose (2*n+1) n : ℝ)*((n:ℝ)+1) := by exact_mod_cast h1
  have r2' : (Nat.choose (2*n+1) n : ℝ)*(2*((n:ℝ)+1)) =
      (Nat.choose (2*(n+1)) (n+1) : ℝ)*((n:ℝ)+1) := by exact_mod_cast h2
  have r2 : (Nat.choose (2*n+1) n : ℝ)*(2*(n:ℝ)+2) =
      (Nat.choose (2*(n+1)) (n+1) : ℝ)*((n:ℝ)+1) := by nlinarith [r2']
  have hn1 : 0 < (n:ℝ)+1 := by positivity
  have hfact : ((Nat.choose (2*(n+1)) (n+1) : ℝ)-2*(Nat.choose (2*n+1) n : ℝ))*((n:ℝ)+1)=0 := by nlinarith [r2]
  have hnext : (Nat.choose (2*(n+1)) (n+1) : ℝ)=2*(Nat.choose (2*n+1) n : ℝ) := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfact).resolve_right (ne_of_gt hn1))
  unfold centralBinomial
  rw [pow_succ]
  field_simp
  rw [hnext]
  nlinarith [r1]

/-- The stronger multiplicative form of c_n²≥1/(4n), proved by induction
from the exact recurrence and (2n+1)²≥4n(n+1). P023-T8 finite lemma (2). -/
theorem central_binomial_lower_bound_mul (n : ℕ) (hn : 1 ≤ n) :
    (1:ℝ) ≤ 4*(n:ℝ)*centralBinomial n^2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n; norm_num [centralBinomial,Nat.choose]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hnreal : 0 < (n:ℝ) := by exact_mod_cast hnpos
      have hprev := ih (by omega)
      have hrec := central_binomial_recurrence n
      have hsquare := congrArg (fun t : ℝ => t^2) hrec
      have hmul := mul_le_mul_of_nonneg_right hprev (show 0 ≤ (n:ℝ)+1 by positivity)
      have hcore : 0 ≤ (4*((n:ℝ)+1)*centralBinomial (n+1)^2-1)*((n:ℝ)+1) := by
        nlinarith [hsquare,hmul,sq_nonneg (centralBinomial n)]
      have hpos : 0 < (n:ℝ)+1 := by positivity
      have hfinal : 0 ≤ 4*((n:ℝ)+1)*centralBinomial (n+1)^2-1 :=
        (mul_nonneg_iff_of_pos_right hpos).mp hcore
      simpa only [Nat.cast_add,Nat.cast_one] using (sub_nonneg.mp hfinal)

/-- The exact uniform-margin lower bound used by corrected Proposition 2,
P023-E002, P023-T8 finite lemma (2). -/
theorem central_binomial_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    1/(4*(n:ℝ)) ≤ centralBinomial n^2 := by
  have hnreal : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  apply (div_le_iff₀ (show 0 < 4*(n:ℝ) by positivity)).mpr
  nlinarith [central_binomial_lower_bound_mul n hn]

/-- P023-E002: the normalized central-binomial square is the
reciprocal of (2n+1) times the Wallis product. This connects the literal choose
values to Mathlib's analytic bounds without postulating the variance formula. -/
theorem central_binomial_wallis (n : ℕ) :
    Real.Wallis.W n * ((2*(n:ℝ)+1)*centralBinomial n^2)=1 := by
  induction n with
  | zero => norm_num [Real.Wallis.W,centralBinomial,Nat.choose]
  | succ n ih =>
    have h2 : 2*(n:ℝ)+2 ≠ 0 := by positivity
    have h1 : 2*(n:ℝ)+1 ≠ 0 := by positivity
    have h3 : 2*(n:ℝ)+3 ≠ 0 := by positivity
    have hc : centralBinomial (n+1)=centralBinomial n*(2*(n:ℝ)+1)/(2*(n:ℝ)+2) :=
      (eq_div_iff h2).mpr (central_binomial_recurrence n)
    simp only [Nat.cast_add,Nat.cast_one]
    rw [Real.Wallis.W_succ,hc]
    calc
      _ = Real.Wallis.W n * ((2*(n:ℝ)+1)*centralBinomial n^2) := by
        field_simp [h1,h2,h3]
        ring
      _ = 1 := ih

/-- P023-T6 finite lemma (3), P023-E002: the exact two Wallis
bounds 1/(pi(n+1/2))≤c_n²≤1/(pi n), for every n≥1. -/
theorem central_binomial_wallis_bounds (n : ℕ) (hn : 1 ≤ n) :
    1/(Real.pi*((n:ℝ)+1/2)) ≤ centralBinomial n^2 ∧
    centralBinomial n^2 ≤ 1/(Real.pi*(n:ℝ)) := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hproduct := central_binomial_wallis n
  have hpos : 0 ≤ (2*(n:ℝ)+1)*centralBinomial n^2 := by positivity
  constructor
  · apply (div_le_iff₀ (show 0 < Real.pi*((n:ℝ)+1/2) by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right (Real.Wallis.W_le n) hpos
    rw [hproduct] at hm
    nlinarith [hm]
  · have hm0 := mul_le_mul_of_nonneg_right (Real.Wallis.le_W n) hpos
    rw [hproduct] at hm0
    have hm : Real.pi*(2*(n:ℝ)+1)^2*centralBinomial n^2/(4*(n:ℝ)+4) ≤ 1 := by
      calc
        _ = ((2*(n:ℝ)+1)/(2*(n:ℝ)+2)*(Real.pi/2))*((2*(n:ℝ)+1)*centralBinomial n^2) := by
          field_simp
          ring
        _ ≤ 1 := hm0
    have hcore : Real.pi*(n:ℝ)*centralBinomial n^2 ≤ 1 := by
      calc
        _ ≤ Real.pi*(2*(n:ℝ)+1)^2*centralBinomial n^2/(4*(n:ℝ)+4) := by
          apply (le_div_iff₀ (show 0 < 4*(n:ℝ)+4 by positivity)).mpr
          have hx := mul_le_mul_of_nonneg_left
            (show (n:ℝ)*(4*(n:ℝ)+4) ≤ (2*(n:ℝ)+1)^2 by nlinarith)
            (show 0 ≤ Real.pi*centralBinomial n^2 by positivity)
          nlinarith [hx]
        _ ≤ 1 := hm
    apply (le_div_iff₀ (show 0 < Real.pi*(n:ℝ) by positivity)).mpr
    nlinarith [hcore]


/-- P023-E002: the unnormalized Jackson kernel is
(sin(s t/2)/sin(t/2))⁴, with the removable singularities filled by s⁴. -/
def jacksonRaw (s : ℕ) (t : ℝ) : ℝ :=
  (if Real.sin (t/2)=0 then (s:ℝ) else Real.sin ((s:ℝ)*t/2)/Real.sin (t/2))^4

/-- P023-E002: for `s ≥ 1`, normalize K_s so its integral on [-pi,pi]
is 2pi; integration is ordinary Lebesgue integration. At `s = 0`,
total division gives the zero kernel. -/
def jacksonKernel (s : ℕ) (t : ℝ) : ℝ :=
  jacksonRaw s t / ((∫ u in Set.Icc (-Real.pi) Real.pi, jacksonRaw s u)/(2*Real.pi))

/-- P023-E002: convolution H*K_s with H(theta)=h(cos theta),
using the normalized 1/(2pi) circular-convolution convention. -/
def jacksonConvolution (s : ℕ) (h : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (∫ t in Set.Icc (-Real.pi) Real.pi, h (Real.cos (θ-t))*jacksonKernel s t)/(2*Real.pi)


/-- P023-T8 finite lemma (5), P023-E002: each RD window side
has probability at least ck, and the population RD difference is beta plus the
two smooth-part conditional means, with error bounded by 2Lk. -/
theorem repaired_rd_finite_bounds (ν : Measure (ℝ × ℝ)) (α β : ℝ)
    (h : ℝ → ℝ) (c δ L σ2 : ℝ) (hr : RepairedRegularity ν α β h c δ L σ2)
    (k : ℝ) (hk : 0 < k ∧ k ≤ δ) :
    let μ := marginLaw ν
    ENNReal.ofReal (c*k) ≤ μ (Set.Ioc 0 k) ∧ ENNReal.ofReal (c*k) ≤ μ (Set.Ioo (-k) 0) ∧
    populationRD μ (fun x => α+β*party x+h x) k = β+populationRD μ h k ∧
    |populationRD μ (fun x => α+β*party x+h x) k-β| ≤ 2*L*k := by
  rcases hr with ⟨hprob, hsupport, hnoatom, hsq, hc, hδ, hδ1, hL, hσ,
    hdom, h0, hlip, hmean, hvar⟩
  let μ := marginLaw ν
  letI : IsProbabilityMeasure ν := ⟨hprob⟩
  letI : IsProbabilityMeasure μ := by dsimp [μ,marginLaw]; infer_instance
  have hsubP : Set.Ioc 0 k ⊆ Set.Icc (-δ) δ := by
    intro x hx; constructor <;> linarith [hx.1,hx.2,hk.2]
  have hsubN : Set.Ioo (-k) 0 ⊆ Set.Icc (-δ) δ := by
    intro x hx; constructor <;> linarith [hx.1,hx.2,hk.2]
  have hmassP : ENNReal.ofReal (c*k) ≤ μ (Set.Ioc 0 k) := by
    have hd := hdom (Set.Ioc 0 k) measurableSet_Ioc hsubP
    simpa only [Real.volume_Ioc,sub_zero,← ENNReal.ofReal_mul hc.le] using hd
  have hmassN : ENNReal.ofReal (c*k) ≤ μ (Set.Ioo (-k) 0) := by
    have hd := hdom (Set.Ioo (-k) 0) measurableSet_Ioo hsubN
    simpa only [Real.volume_Ioo,zero_sub,neg_neg,← ENNReal.ofReal_mul hc.le] using hd
  have hPpos : 0 < (μ (Set.Ioc 0 k)).toReal := by
    have hb := ENNReal.toReal_mono (measure_ne_top μ _) hmassP
    rw [ENNReal.toReal_ofReal (mul_pos hc hk.1).le] at hb
    exact lt_of_lt_of_le (mul_pos hc hk.1) hb
  have hNpos : 0 < (μ (Set.Ioo (-k) 0)).toReal := by
    have hb := ENNReal.toReal_mono (measure_ne_top μ _) hmassN
    rw [ENNReal.toReal_ofReal (mul_pos hc hk.1).le] at hb
    exact lt_of_lt_of_le (mul_pos hc hk.1) hb
  have hsubP1 : Set.Ioc 0 k ⊆ Set.Icc (-1) 1 := by
    intro x hx; have ht:=hsubP hx; constructor <;> linarith [ht.1,ht.2]
  have hsubN1 : Set.Ioo (-k) 0 ⊆ Set.Icc (-1) 1 := by
    intro x hx; have ht:=hsubN hx; constructor <;> linarith [ht.1,ht.2]
  have hcont : ContinuousOn h (Set.Icc (-1) 1) := by
    apply LipschitzOnWith.continuousOn (K:=⟨L,hL⟩)
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |h x-h y| ≤ L*|x-y|
    exact hlip x hx y hy
  have hb (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) (habs : |x| ≤ k) : |h x| ≤ L*k := by
    have hh := hlip x hx 0 (by norm_num)
    simp only [h0,sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left habs hL)
  have hbP (x : ℝ) (hx : x ∈ Set.Ioc 0 k) : |h x| ≤ L*k :=
    hb x (hsubP1 hx) ((abs_le).mpr ⟨by linarith [hx.1],hx.2⟩)
  have hbN (x : ℝ) (hx : x ∈ Set.Ioo (-k) 0) : |h x| ≤ L*k :=
    hb x (hsubN1 hx) ((abs_le).mpr ⟨le_of_lt hx.1,by linarith [hx.2]⟩)
  have haeP : ∀ᵐ x ∂μ.restrict (Set.Ioc 0 k), ‖h x‖ ≤ L*k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simpa only [Real.norm_eq_abs] using hbP x hx
  have haeN : ∀ᵐ x ∂μ.restrict (Set.Ioo (-k) 0), ‖h x‖ ≤ L*k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using hbN x hx
  have hiP : Integrable h (μ.restrict (Set.Ioc 0 k)) :=
    Integrable.of_bound ((hcont.mono hsubP1).aestronglyMeasurable measurableSet_Ioc) (L*k) haeP
  have hiN : Integrable h (μ.restrict (Set.Ioo (-k) 0)) :=
    Integrable.of_bound ((hcont.mono hsubN1).aestronglyMeasurable measurableSet_Ioo) (L*k) haeN
  have heP : (∫ x in Set.Ioc 0 k, α+β*party x+h x ∂μ) =
      (μ (Set.Ioc 0 k)).toReal*(α+β)+(∫ x in Set.Ioc 0 k, h x ∂μ) := by
    calc
      _ = ∫ x in Set.Ioc 0 k, (α+β)+h x ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx; simp only [party,if_pos (le_of_lt hx.1),mul_one]
      _ = _ := by
        rw [integral_add (integrable_const _) hiP,setIntegral_const,smul_eq_mul]
        rfl
  have heN : (∫ x in Set.Ioo (-k) 0, α+β*party x+h x ∂μ) =
      (μ (Set.Ioo (-k) 0)).toReal*α+(∫ x in Set.Ioo (-k) 0, h x ∂μ) := by
    calc
      _ = ∫ x in Set.Ioo (-k) 0, α+h x ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro x hx; simp only [party,if_neg (not_le.mpr hx.2),mul_zero,add_zero]
      _ = _ := by
        rw [integral_add (integrable_const _) hiN,setIntegral_const,smul_eq_mul]
        rfl
  have he : populationRD μ (fun x => α+β*party x+h x) k=β+populationRD μ h k := by
    unfold populationRD
    rw [heP,heN]
    field_simp [ne_of_gt hPpos,ne_of_gt hNpos]
    ring
  have hmP : |(∫ x in Set.Ioc 0 k, h x ∂μ)/(μ (Set.Ioc 0 k)).toReal| ≤ L*k := by
    rw [abs_div,abs_of_pos hPpos]
    apply (div_le_iff₀ hPpos).mpr
    simpa only [Real.norm_eq_abs,Measure.real,Measure.restrict_apply_univ] using
      norm_integral_le_of_norm_le_const haeP
  have hmN : |(∫ x in Set.Ioo (-k) 0, h x ∂μ)/(μ (Set.Ioo (-k) 0)).toReal| ≤ L*k := by
    rw [abs_div,abs_of_pos hNpos]
    apply (div_le_iff₀ hNpos).mpr
    simpa only [Real.norm_eq_abs,Measure.real,Measure.restrict_apply_univ] using
      norm_integral_le_of_norm_le_const haeN
  refine ⟨hmassP,hmassN,he,?_⟩
  rw [he,add_sub_cancel_left]
  calc
    |populationRD μ h k| ≤
        |(∫ x in Set.Ioc 0 k, h x ∂μ)/(μ (Set.Ioc 0 k)).toReal|+
        |(∫ x in Set.Ioo (-k) 0, h x ∂μ)/(μ (Set.Ioo (-k) 0)).toReal| := by
          change |_ - _| ≤ _
          simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le
            ((∫ x in Set.Ioc 0 k, h x ∂μ)/(μ (Set.Ioc 0 k)).toReal) (0:ℝ)
            ((∫ x in Set.Ioo (-k) 0, h x ∂μ)/(μ (Set.Ioo (-k) 0)).toReal)
    _ ≤ L*k+L*k := add_le_add hmP hmN
    _ = 2*L*k := by ring


/-- P023-T8(e), population limit: under the primitive correction, the
rectangular population RD difference tends to the cutoff jump as its positive
bandwidth tends to zero. This does not assert sample consistency. -/
theorem repaired_population_rd_limit (ν : Measure (ℝ × ℝ)) (α β : ℝ)
    (h : ℝ → ℝ) (c δ L σ2 : ℝ) (hr : RepairedRegularity ν α β h c δ L σ2)
    (k : ℕ → ℝ) (hkpos : ∀ N, 0 < k N) (hk0 : Tendsto k atTop (nhds 0)) :
    Tendsto (fun N => populationRD (marginLaw ν) (fun x => α+β*party x+h x) (k N))
      atTop (nhds β) := by
  have hreg := hr
  obtain ⟨hprob, hsupport, hnoatom, hsq, hc, hδ, hδ1, hL, hσ,
    hdom, h0, hlip, hmean, hvar⟩ := hr
  rw [Metric.tendsto_nhds] at hk0 ⊢
  intro ε hε
  have hden : 0 < 2*(L+1) := by linarith
  have ht := hk0 (min δ (ε/(2*(L+1)))) (lt_min hδ (div_pos hε hden))
  filter_upwards [ht] with N hsmall
  rw [Real.dist_eq,sub_zero,abs_of_pos (hkpos N)] at hsmall
  have hkδ : k N ≤ δ := (lt_of_lt_of_le hsmall (min_le_left _ _)).le
  have hke : k N < ε/(2*(L+1)) := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hrate : 2*L*k N < ε := by
    have hmul := (lt_div_iff₀ hden).mp hke
    nlinarith [hkpos N]
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (repaired_rd_finite_bounds ν α β h c δ L σ2 hreg (k N) ⟨hkpos N,hkδ⟩).2.2.2 hrate


/-- P023-E002: the number of sampled margin values in a
Borel window A, as a finite sum of membership indicators. -/
def sampleWindowCount {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ) (A : Set ℝ)
    (N : ℕ) (ω : Ω) : ℝ := by
  classical
  exact ∑ i : Fin N, if (sample i ω).1 ∈ A then (1:ℝ) else 0

/-- P023-T8 finite lemma (5), P023-E002: an IID window count
with mean Np has probability at most 4/(Np) of falling below Np/2. The count
is a literal sum of sample membership indicators. -/
theorem iid_window_count_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure (ℝ × ℝ)) (sample : ℕ → Ω → ℝ × ℝ)
    (hiid : IIDSample P ν sample) (A : Set ℝ) (hA : MeasurableSet A)
    (hp : 0 < (marginLaw ν A).toReal) (N : ℕ) (hN : 1 ≤ N) :
    P {ω | sampleWindowCount sample A N ω <
      (N:ℝ)*(marginLaw ν A).toReal/2} ≤ ENNReal.ofReal (4/((N:ℝ)*(marginLaw ν A).toReal)) := by
  classical
  letI : IsProbabilityMeasure P := ⟨hiid.1⟩
  let p := (marginLaw ν A).toReal
  let B : ℕ → Ω → ℝ := fun i => {ω | (sample i ω).1 ∈ A}.indicator (fun _ => 1)
  have hset (i : ℕ) : MeasurableSet {ω | (sample i ω).1 ∈ A} :=
    hA.preimage ((hiid.2.1 i).fst)
  have hmeas (i : ℕ) : Measurable (B i) := measurable_const.indicator (hset i)
  have hmem (i : ℕ) : MemLp (B i) 2 P := by
    apply MemLp.of_bound (hmeas i).aestronglyMeasurable 1
    apply ae_of_all
    intro ω
    by_cases hw : (sample i ω).1 ∈ A <;> simp [B,hw]
  have hmean (i : ℕ) : (∫ ω, B i ω ∂P)=p := by
    have hmass : P {ω | (sample i ω).1 ∈ A}=marginLaw ν A := by
      unfold marginLaw
      rw [Measure.map_apply measurable_fst hA,← hiid.2.2.1 i,
        Measure.map_apply (hiid.2.1 i) (hA.preimage measurable_fst)]
      rfl
    change (∫ ω, {ω | (sample i ω).1 ∈ A}.indicator (fun _ => (1:ℝ)) ω ∂P)=p
    rw [integral_indicator_const 1 (hset i),smul_eq_mul,mul_one]
    exact congrArg ENNReal.toReal hmass
  have hvar (i : ℕ) : ProbabilityTheory.variance (B i) P ≤ p := by
    have hs : (B i)^2=B i := by
      funext ω
      by_cases hw : (sample i ω).1 ∈ A <;> simp [B,hw]
    calc
      _ ≤ ∫ ω, ((B i)^2) ω ∂P := ProbabilityTheory.variance_le_expectation_sq (hmeas i).aestronglyMeasurable
      _ = p := by rw [hs,hmean]
  have hind (i j : Fin N) (hij : i≠j) : ProbabilityTheory.IndepFun (B i.val) (B j.val) P := by
    let g : ℝ × ℝ → ℝ := (Prod.fst ⁻¹' A).indicator (fun _ => 1)
    have hg : Measurable g := measurable_const.indicator (hA.preimage measurable_fst)
    have hi : i.val≠j.val := by intro he; apply hij; exact Fin.ext he
    have h := (hiid.2.2.2.indepFun hi).comp hg hg
    change ProbabilityTheory.IndepFun (g ∘ sample i.val) (g ∘ sample j.val) P at h
    exact h
  let S : Ω → ℝ := fun ω => ∑ i : Fin N, B i.val ω
  have hSmem : MemLp S 2 P :=
    memLp_finsetSum (Finset.univ : Finset (Fin N)) (fun i _ => hmem i.val)
  have hSmean : (∫ ω, S ω ∂P)=(N:ℝ)*p := by
    change (∫ ω, ∑ i : Fin N, B i.val ω ∂P)=_
    rw [integral_finset_sum Finset.univ (fun i _ => (hmem i.val).integrable (by norm_num))]
    simp only [hmean,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hSvar : ProbabilityTheory.variance S P ≤ (N:ℝ)*p := by
    have hv : ProbabilityTheory.variance S P=∑ i : Fin N, ProbabilityTheory.variance (B i.val) P := by
      have ht := ProbabilityTheory.IndepFun.variance_sum (s:=(Finset.univ : Finset (Fin N)))
        (X:=fun i : Fin N => B i.val) (fun i _ => hmem i.val)
        (by intro i _ j _ hij; exact hind i j hij)
      have hsum : (∑ i : Fin N, B i.val)=S := by
        funext ω; simp only [S,Finset.sum_apply]
      rw [hsum] at ht
      exact ht
    rw [hv]
    calc
      _ ≤ ∑ _i : Fin N, p := Finset.sum_le_sum (fun i _ => hvar i.val)
      _ = _ := by simp
  have hcount (ω : Ω) : sampleWindowCount sample A N ω=S ω := by
    simp only [sampleWindowCount,S,Finset.sum_apply,B,Set.indicator_apply,Set.mem_setOf_eq]
  have hNp : 0 < (N:ℝ)*p := mul_pos (by exact_mod_cast (show 0<N by omega)) hp
  calc
    _ ≤ P {ω | (N:ℝ)*p/2 ≤ |S ω-(∫ ω, S ω ∂P)|} := by
      apply measure_mono
      intro ω hw
      simp only [Set.mem_setOf_eq,hcount] at hw ⊢
      rw [hSmean]
      have ht : (N:ℝ)*p/2 ≤ (N:ℝ)*p-S ω := by linarith
      have ha := neg_le_abs (S ω-(N:ℝ)*p)
      linarith
    _ ≤ ENNReal.ofReal (ProbabilityTheory.variance S P / ((N:ℝ)*p/2)^2) :=
      ProbabilityTheory.meas_ge_le_variance_div_sq hSmem (by linarith)
    _ ≤ ENNReal.ofReal (4/((N:ℝ)*p)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((N:ℝ)*p)/((N:ℝ)*p/2)^2 :=
          div_le_div_of_nonneg_right hSvar (sq_nonneg _)
        _ = _ := by field_simp [ne_of_gt hNp]; ring


/-- P023-E002: G_J=E[z_J z_Jᵀ], z_J=(1,D,X,...,X^J). -/
def populationGram (μ : Measure ℝ) (J : ℕ) (j l : Fin (J+2)) : ℝ :=
  expectation μ (fun x => polynomialDesign J (fun x : ℝ => x) party x j *
    polynomialDesign J (fun x : ℝ => x) party x l)

/-- P023-E002: the sample Gram matrix Ghat=N⁻¹ sum z_i z_iᵀ. -/
def sampleGram {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ) (N J : ℕ)
    (ω : Ω) (j l : Fin (J+2)) : ℝ :=
  (∑ i : Fin N, polynomialDesign J (fun i => (sample i ω).1)
    (fun i => party (sample i ω).1) i j *
    polynomialDesign J (fun i => (sample i ω).1) (fun i => party (sample i ω).1) i l)/(N:ℝ)

/-- P023-E002: t_J=E[z_J Y], the population cross moment. -/
def populationCross (ν : Measure (ℝ × ℝ)) (J : ℕ) (j : Fin (J+2)) : ℝ :=
  ∫ z, polynomialDesign J (fun x : ℝ => x) party z.1 j*z.2 ∂ν

/-- P023-E002: that=N⁻¹ sum z_i Y_i. -/
def sampleCross {Ω : Type*} (sample : ℕ → Ω → ℝ × ℝ) (N J : ℕ)
    (ω : Ω) (j : Fin (J+2)) : ℝ :=
  (∑ i : Fin N, polynomialDesign J (fun i => (sample i ω).1)
    (fun i => party (sample i ω).1) i j * (sample i ω).2)/(N:ℝ)

/-- P023-E002: the square of the Euclidean coefficient norm. -/
def vectorSquared (J : ℕ) (v : Fin (J+2) → ℝ) : ℝ := ∑ j, v j^2

/-- P023-E002: squared Frobenius matrix norm, sum of squares
of every entry, not a bound assumed for the matrix error. -/
def frobeniusSquared (J : ℕ) (A : Fin (J+2) → Fin (J+2) → ℝ) : ℝ := ∑ j, ∑ l, A j l^2

/-- P023-E002: the induced Euclidean operator norm of a finite
matrix, defined as the supremum of ||Av|| over unit Euclidean vectors. -/
def matrixOperatorNorm (J : ℕ) (A : Fin (J+2) → Fin (J+2) → ℝ) : ℝ :=
  sSup {r | ∃ v : Fin (J+2) → ℝ, vectorSquared J v=1 ∧
    r=Real.sqrt (∑ j, (∑ l, A j l*v l)^2)}


end
end AronowAudit.P023

