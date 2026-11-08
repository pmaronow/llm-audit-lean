import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P034

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- The fitted function `m(w,v,z)=a+bw+cv+dwv+γ'z` (validator P034-A001,
derivation.md §3). The paper calls the factors “Information” and “Deepfake”
(Appendix Tables OA5-OA6, pp. 13-14). `w=0` means no information and `v=0`
means real video. The covariate term uses an arbitrary finite real vector. -/
def fittedOutcome {k : ℕ} (a b c d : ℝ) (γ z : Fin k → ℝ) (w v : ℝ) : ℝ :=
  a + b * w + c * v + d * w * v + ∑ j, γ j * z j

/-- The four cell outcomes `(0,0,0,2)` of the constructed factorial witness
(validator P034-A001 §3); this is not a transcription of actual outcomes. -/
def factorialCell (w v : Bool) : ℝ := if w && v then 2 else 0

/-- P034-T3: unique factorial interpolation and both unequal averaged contrasts. -/
def T3Statement : Prop :=
    (∀ a b c d : ℝ,
      (∀ w v : Bool, fittedOutcome a b c d (0 : Fin 0 → ℝ) 0
        (if w then 1 else 0) (if v then 1 else 0) = factorialCell w v) ↔
          a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 2) ∧
    factorialCell true false - factorialCell false false = 0 ∧
    (1/2 : ℝ) * (factorialCell true false - factorialCell false false) +
      (1/2 : ℝ) * (factorialCell true true - factorialCell false true) = 1 ∧
    factorialCell false true - factorialCell false false = 0 ∧
    (1/2 : ℝ) * (factorialCell false true - factorialCell false false) +
      (1/2 : ℝ) * (factorialCell true true - factorialCell true false) = 1 ∧
    (0 : ℝ) ≠ 1

/-- P034-T4(i)-(v): reference contrasts, weighted contrasts, and exact equality conditions. -/
def T4Statement : Prop :=
  ∀ {k : ℕ} (a b c d : ℝ) (γ z : Fin k → ℝ),
    (∀ v : ℝ, fittedOutcome a b c d γ z 1 v - fittedOutcome a b c d γ z 0 v = b+d*v) ∧
    fittedOutcome a b c d γ z 1 0 - fittedOutcome a b c d γ z 0 0 = b ∧
    fittedOutcome a b c d γ z 1 1 - fittedOutcome a b c d γ z 0 1 = b+d ∧
    (∀ w : ℝ, fittedOutcome a b c d γ z w 1 - fittedOutcome a b c d γ z w 0 = c+d*w) ∧
    fittedOutcome a b c d γ z 0 1 - fittedOutcome a b c d γ z 0 0 = c ∧
    fittedOutcome a b c d γ z 1 1 - fittedOutcome a b c d γ z 1 0 = c+d ∧
    (∀ q : ℝ, (1-q) * (fittedOutcome a b c d γ z 1 0 - fittedOutcome a b c d γ z 0 0) +
      q * (fittedOutcome a b c d γ z 1 1 - fittedOutcome a b c d γ z 0 1) = b+q*d) ∧
    (∀ p : ℝ, (1-p) * (fittedOutcome a b c d γ z 0 1 - fittedOutcome a b c d γ z 0 0) +
      p * (fittedOutcome a b c d γ z 1 1 - fittedOutcome a b c d γ z 1 0) = c+p*d) ∧
    (∀ q : ℝ, b+q*d = b ↔ q*d = 0) ∧
    (∀ p : ℝ, c+p*d = c ↔ p*d = 0) ∧
    (∀ q : ℝ, 0 < q → (b+q*d = b ↔ d = 0)) ∧
    (∀ p : ℝ, 0 < p → (c+p*d = c ↔ d = 0))

end SAP.P034
