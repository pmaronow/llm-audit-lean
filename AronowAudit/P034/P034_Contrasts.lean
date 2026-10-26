import Mathlib

namespace AronowAudit.P034

/-!
P034-T3 and P034-T4. Appendix pp. 13-14, Tables OA5-OA6.
The paper prints no regression formula. The formula below describes the
fitted regression in the released code. It is not an assumption that the
fitted regression is a causal response function.
-/

/-- The fitted function `m(w,v,z)=a+bw+cv+dwv+γ'z`.
The paper calls the factors “Information” and “Deepfake”
(Appendix Tables OA5-OA6, pp. 13-14). `w=0` means no information and `v=0`
means real video. The covariate term uses an arbitrary finite real vector. -/
def fittedOutcome {k : ℕ} (a b c d : ℝ) (γ z : Fin k → ℝ) (w v : ℝ) : ℝ :=
  a + b * w + c * v + d * w * v + ∑ j, γ j * z j

/-- P034-T4(i): the information contrast holding video type and covariates
fixed is `b+d*v`; the formula even holds for arbitrary real `v`. -/
theorem information_contrast {k : ℕ} (a b c d : ℝ) (γ z : Fin k → ℝ) (v : ℝ) :
    fittedOutcome a b c d γ z 1 v - fittedOutcome a b c d γ z 0 v = b + d * v := by
  unfold fittedOutcome
  ring

/-- P034-T4(ii): the deepfake contrast holding information and covariates
fixed is `c+d*w`; the formula even holds for arbitrary real `w`. -/
theorem deepfake_contrast {k : ℕ} (a b c d : ℝ) (γ z : Fin k → ℝ) (w : ℝ) :
    fittedOutcome a b c d γ z w 1 - fittedOutcome a b c d γ z w 0 = c + d * w := by
  unfold fittedOutcome
  ring

/-- P034-T4(iii)-(iv): averaging the two fitted contrasts with any real weights
gives `b+q*d` and `c+p*d`, correcting OA5-OA6 row labels. -/
theorem averaged_contrasts {k : ℕ} (a b c d : ℝ) (γ z : Fin k → ℝ) (q p : ℝ) :
    (1-q) * (fittedOutcome a b c d γ z 1 0 - fittedOutcome a b c d γ z 0 0) +
      q * (fittedOutcome a b c d γ z 1 1 - fittedOutcome a b c d γ z 0 1) = b+q*d ∧
    (1-p) * (fittedOutcome a b c d γ z 0 1 - fittedOutcome a b c d γ z 0 0) +
      p * (fittedOutcome a b c d γ z 1 1 - fittedOutcome a b c d γ z 1 0) = c+p*d := by
  constructor <;> unfold fittedOutcome <;> ring

/-- P034-T4, all parts of the corrected contrast algebra. Both reference
conditions, both weighted averages, and the exact equality conditions are
explicit. For positive weights an average equals its main coefficient iff
the interaction coefficient is zero. Appendix Tables OA5-OA6, pp. 13-14. -/
theorem corrected_factorial_contrasts {k : ℕ} (a b c d : ℝ) (γ z : Fin k → ℝ) :
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
    (∀ p : ℝ, 0 < p → (c+p*d = c ↔ d = 0)) := by
  refine ⟨information_contrast a b c d γ z, ?_, ?_,
    deepfake_contrast a b c d γ z, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using information_contrast a b c d γ z 0
  · simpa using information_contrast a b c d γ z 1
  · simpa using deepfake_contrast a b c d γ z 0
  · simpa using deepfake_contrast a b c d γ z 1
  · intro q; exact (averaged_contrasts a b c d γ z q 0).1
  · intro p; exact (averaged_contrasts a b c d γ z 0 p).2
  · intro q; constructor <;> intro h <;> linarith
  · intro p; constructor <;> intro h <;> linarith
  · intro q hq
    constructor
    · intro h
      have : q*d = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hq)
    · intro h; simp [h]
  · intro p hp
    constructor
    · intro h
      have : p*d = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hp)
    · intro h; simp [h]

/-- The four cell outcomes `(0,0,0,2)` of the constructed factorial witness;
this is not a transcription of actual outcomes. -/
def factorialCell (w v : Bool) : ℝ := if w && v then 2 else 0

/-- P034-T3(i): the unique saturated fit to all four cell values is
`(a,b,c,d)=(0,0,0,2)`. One observation in every cell gives this exact fit. -/
theorem factorial_fit_unique (a b c d : ℝ) :
    (∀ w v : Bool, fittedOutcome a b c d (0 : Fin 0 → ℝ) 0
      (if w then 1 else 0) (if v then 1 else 0) = factorialCell w v) ↔
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 2 := by
  constructor
  · intro h
    have h00 := h false false
    have h10 := h true false
    have h01 := h false true
    have h11 := h true true
    norm_num [fittedOutcome, factorialCell] at h00 h10 h01 h11
    exact ⟨h00, by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩ w v
    cases w <;> cases v <;> norm_num [fittedOutcome, factorialCell]

/-- P034-T3, the explicit counterexample: both main coefficients are zero,
both equally weighted effects are one, and the saturated fit is unique.
It refutes the proposed coefficient/average identity, not any printed numbers. -/
theorem factorial_counterexample :
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
    (0 : ℝ) ≠ 1 := by
  refine ⟨factorial_fit_unique, ?_⟩
  norm_num [factorialCell]

end AronowAudit.P034

