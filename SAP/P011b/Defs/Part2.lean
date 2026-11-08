import SAP.P011b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-! Limits, residuals, and full-rank ordinary least squares.
The normal quantile is used only for 0 < alpha < 1. -/

def Phi (t : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t

def normalQuantile (α : ℝ) : ℝ := sInf {t : ℝ | 1 - α / 2 ≤ Phi t}

def coverage {n : ℕ} (m : Model n) (V : (Fin n → ℝ) → ℝ) (α : ℝ) : ℝ :=
  probability m {y | |betaHat m y - beta m| ≤ normalQuantile α * Real.sqrt (max (V y) 0)}

def l2 {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

def Tight (F : Family) (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧ ∃ k0 : ℕ, ∀ k ≥ k0,
    probability (F.model k) {y | |T k y| > B} ≤ ε

def MeanModel {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ) (γ : Fin p → ℝ) : Prop :=
  (∀ i, Integrable (fun y => y i) m.law) ∧
  ∀ i, expectation m (fun y => y i) = (D *ᵥ γ) i

def trueResidual {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ)
    (γ : Fin p → ℝ) (y : Fin n → ℝ) : Fin n → ℝ := fun i => m.theta i*(y i-(D *ᵥ γ) i)

def fittedResidual {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ)
    (γhat : (Fin n → ℝ) → (Fin p → ℝ)) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => m.theta i*(y i-(D *ᵥ (γhat y)) i)

def VResidual {n : ℕ} (A : Graph n) (r : Fin n → ℝ) : ℝ := quadratic (oracleMatrix A) r/(n : ℝ)^2

def scaledTrue (F : Family) (k : ℕ) : ℝ := (F.size k : ℝ) * var (F.model k) (betaHat (F.model k))

def scaledOracle (F : Family) (k : ℕ) (y : Fin (F.size k) → ℝ) : ℝ :=
  (F.size k : ℝ) * V1 (F.model k).G (weighted (F.model k) y)

def meanVariance {n : ℕ} (m : Model n) : ℝ := (∑ i, covariance m i i) / n

def varianceRemainder {n : ℕ} (m : Model n) (y : Fin n → ℝ) : ℝ :=
  sampleVariance (weighted m y)-meanVariance m-meanSpread m

def ols {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) : Fin p → ℝ :=
  (Dᵀ*D)⁻¹ *ᵥ (Dᵀ *ᵥ y)

def olsTheta {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin p) (Fin n) ℝ :=
  (n : ℝ) • ((Dᵀ*D)⁻¹*Dᵀ)

abbrev Edge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

def fromUpper {n : ℕ} (a : Edge n → Bool) : Graph n :=
  ⟨fun (i j : Fin n) => if h : i < j then a ⟨(i,j),h⟩ else if h' : j < i then a ⟨(j,i),h'⟩ else false, by
    constructor
    · intro i j
      by_cases h : i < j
      · have h' : ¬ (j < i) := by omega
        simp [h,h']
      · by_cases h' : j < i
        · simp [h,h']
        · simp [h,h']
    · intro i; simp⟩

def toUpper {n : ℕ} (A : Graph n) : Edge n → Bool := fun e => A.val e.val.1 e.val.2

def upperObjective {n : ℕ} (a : Edge n → Bool) (w : Edge n → ℝ) : ℝ :=
  ∑ e, if a e then w e else 0

def upperDegree {n : ℕ} (a : Edge n → Bool) (i : Fin n) : ℕ :=
  ∑ e, if a e && decide (e.val.1=i ∨ e.val.2=i) then 1 else 0

def RelaxedFeasible {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (a : Edge n → ℝ) : Prop :=
  (∀ e, 0 ≤ a e ∧ a e ≤ 1) ∧ (∀ e, toUpper R e = true → a e = 1) ∧
  ∀ i, (∑ e, if e.val.1=i ∨ e.val.2=i then a e else 0) ≤ d i

def upperSum {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ := ∑ i, ∑ j with i < j, f i j

def ProgramFeasible {n : ℕ} (R : Graph n) (d : Fin n → ℕ) (A : Graph n) : Prop :=
  (∀ i, (∑ j, adjacency A i j) ≤ d i) ∧ (∀ i j, adjacency R i j ≤ adjacency A i j)

def V1R {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, centered x i^2)/((n : ℝ)*((n : ℝ)-1)) + quadratic (adjacency A) (centered x)/(n : ℝ)^2

def V2R {n : ℕ} (A : Graph n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, centered x i^2)/((n : ℝ)*((n : ℝ)-1))*(1+(∑ i, ∑ j, adjacency A i j)/n)

def V2primeR {n : ℕ} (d : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, centered x i^2)/((n : ℝ)*((n : ℝ)-1))*(1+(∑ i, (truncatedDegree d i : ℝ))/n)

end
end SAP.P011b
