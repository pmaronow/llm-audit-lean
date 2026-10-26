import AronowAudit.P005.P005_Formalization

/-!
# P005-T20: counterexample to the printed interacted expansion

The stochastic expansion in Theorem 4.1 (p. 1510) uses the literal printed
condition `κ log d → 0`. `Target` is the negation of that expansion.

The witness has `d ≡ 1`, `m n = n / 2` and `P = spikePopulation`, with
coordinates `spikeV`, `spikeA`, `spikeZ` and variance `spikeQ`. At `d = 1`,
the printed condition is identically `κ·log 1 = 0`. Along even `n ≥ 6`, every
balanced assignment has remainder `|R_n| ≥ n - 6`, while the rate is at most
`1/√n`.

`Sk` denotes a mathematical proposition; `Nk` is either `Sk` itself or an
implication from other stated propositions to `Sk`.
-/

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.InteractedExpansion

open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology

noncomputable section

/-!
## Target
-/

/-- **Target (P005-T20, asymptotic part).** The negation of the stochastic
expansion in Theorem 4.1 as printed, p. 1510. -/
def Target : Prop :=
  ¬ ∀ (d m : ℕ → ℕ) (P : (n : ℕ) → Population n (d n)), standingAssumptions d m P →
      (∀ᶠ n in atTop, interactedRegular (P n) (m n)) →
      Tendsto (fun n => kappa (P n) * Real.log (d n)) atTop (nhds 0) →
      stochasticO m (fun n S => interactedATE (P n) S - ate (P n) - armLeading (P n) S)
        (fun n => Real.sqrt (kappa (P n) * (d n) / n))

/-! ## Witness abbreviations -/

/-- The remainder `interactedATE - ATE - armLeading` of the witness at size `n`. -/
def R (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  interactedATE (spikePopulation n) S - ate (spikePopulation n) - armLeading (spikePopulation n) S

/-- The arm OLS prediction in raw `a`-coordinates, evaluated at the
population mean `1/n` of `a`:
`v̄_A + (1/n - ā_A)·Cov_A(a,v)/Var_A(a)`, denoted q_A(1/n). -/
def armFit (n : ℕ) (A : Finset (Fin n)) : ℝ :=
  mean A (spikeV n) + (1 / (n : ℝ) - mean A (spikeA n)) *
    (sampleCov A (spikeA n) (spikeV n) / sampleCov A (spikeA n) (spikeA n))

/-! ## Mathematical statements -/

/-- **Statement S1.** Exact grid moments for every `n ≥ 3`:
`∑ i, spikeV n i = 0`, `∑ i, (spikeV n i)^2 = n(n-1)/(3(n-2))`,
`|spikeV n i| ≤ 1`, and `∑ i, spikeA n i = 1`.
The centered second moment `spikeQ n` equals
`(n-1)/n² · [1 + 1/(3(n-2)n²)]`.
Reindexing the ordinary units by `j = i - 1 ∈ range (n-1)` reduces these
identities to finite sums of integers and squares. -/
def S1 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (∑ i, spikeV n i = 0) ∧
    (∑ i, spikeV n i ^ 2 = (n : ℝ) * ((n : ℝ) - 1) / (3 * ((n : ℝ) - 2))) ∧
    (∀ i, |spikeV n i| ≤ 1) ∧
    (∑ i, spikeA n i = 1) ∧
    spikeQ n = ((n : ℝ) - 1) / (n : ℝ) ^ 2 * (1 + 1 / (3 * ((n : ℝ) - 2) * (n : ℝ) ^ 2))

/-- **Statement S2.** The witness is standardized at every `n ≥ 3`:
x̄=0 and overline{x²}=1. The calculation uses S1, positivity of `spikeQ n`,
and `x = z/√q`. -/
def S2 : Prop := ∀ n : ℕ, 3 ≤ n → standardized (spikePopulation n)

/-- **Statement S3.** All four clauses of `standingAssumptions` hold with
`K = 1`, `lo = 1/4`, `hi = 3/4`, using S1 (|v|≤1) and S2. -/
def S3 : Prop := standingAssumptions (fun _ => 1) (fun n => n / 2) spikePopulation

/-- **Statement S4.** An intercept-and-x fit is the same line as an
intercept-and-a fit; evaluating at x=0 means evaluating at a=c. For a
one-covariate population with covariate `(a - c)/s`, `s ≠ 0`, and an arm with
`Var_A(a) ≠ 0`, the arm matrix is invertible and
x̄_A·βhat_A = (ā_A - c)·Cov_A(a,y)/Var_A(a). This is scalar matrix algebra
with the covariance scaling and mean identities. -/
def S4 : Prop :=
  ∀ (n : ℕ) (P : Population n 1) (a : Fin n → ℝ) (c s : ℝ), s ≠ 0 →
    (∀ i k, P.x i k = (a i - c) / s) → ∀ (A : Finset (Fin n)) (y : Fin n → ℝ),
      sampleCov A a a ≠ 0 →
      (armL P A).det ≠ 0 ∧
      dot (xMean P A) (armBetaHat P A y) = (mean A a - c) * (sampleCov A a y / sampleCov A a a)

/-- **Statement S5.** For every `n ≥ 6`, every arm with at least two units
has strictly positive sample variance of `spikeA n`. -/
def S5 : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∀ A : Finset (Fin n), 2 ≤ A.card → 0 < sampleCov A (spikeA n) (spikeA n)

/-- **Statement S6.** `interactedRegular` holds for every assignment at
`n ≥ 6`. This follows from S1 (positivity of `spikeQ n`), S4 with `c = 1/n`
and `s = √(spikeQ n)`, and S5, since both arms have at least three units. -/
def S6 : Prop := ∀ n : ℕ, 6 ≤ n → interactedRegular (spikePopulation n) (n / 2)

/-- **Statement S7.** On an arm without the special unit, v=N²a holds
exactly, so its OLS prediction at ā=1/N is exactly N. -/
def S7 : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∀ A : Finset (Fin n), (∀ i ∈ A, i.val ≠ 0) → 2 ≤ A.card → armFit n A = n

/-- **Statement S8.** An arm containing the special unit predicts a value
of absolute value at most 3. Its slope satisfies
|b_H| ≤ [1+(N-3)/N²]/(1-1/N²)² ≤ 2, and its prediction is
q_H(1/N)=v̄_H+b_H(1/N-ā_H). The pairwise covariance and variance formulas
separate the special/ordinary pairs from the ordinary pairs, with
`|1/n - ā_A| < 1`. The bound holds for every arm size at least two:
the slope bound is [1+ε(2t-3)]/(1-ε)² ≤ 2, where ε=1/n² and t≤n. -/
def S8 : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∀ A : Finset (Fin n), (∃ i ∈ A, i.val = 0) → 2 ≤ A.card →
    |armFit n A| ≤ 3

/-- **Statement S9.** The population ATE is zero, and
b=N²/[3(N-2)N²+1] ≤ 1/(N-1), so
|armLeading| ≤ 2+(1+1/N²)/(N-1) ≤ 3. These bounds use S1. -/
def S9 : Prop :=
  ∀ n : ℕ, 6 ≤ n → ate (spikePopulation n) = 0 ∧
    ∀ S ∈ design n (n / 2), |armLeading (spikePopulation n) S| ≤ 3

/-- **Statement S10.** Every balanced assignment with even `n ≥ 6`
satisfies |interactedATE-ate-armLeading| ≥ N-6. By S4 with `c = 1/n` and
`s = √q`, S1 and S5, the estimator is the difference of the two arm fits.
Exactly one arm contains unit 0 (S7, S8), and S9 bounds the remaining terms. -/
def S10 : Prop :=
  ∀ n : ℕ, 6 ≤ n → Even n → ∀ S ∈ design n (n / 2), (n : ℝ) - 6 ≤ |R n S|

/-- **Statement S11.** With ε=1/2 and any proposed stochastic-order cutoff
and tail, choose a sufficiently large even `N`. Every assignment at that
size satisfies |R_N|>M sqrt(κ_N/N), so the tail probability is exactly 1.
The deterministic even-subsequence bound and `κ ≤ 1` contradict
the `stochasticO` quantifiers. -/
def S11 : Prop :=
  (∀ n : ℕ, 6 ≤ n → Even n → ∀ S ∈ design n (n / 2), (n : ℝ) - 6 ≤ |R n S|) →
    (∀ n : ℕ, 6 ≤ n → kappa (spikePopulation n) ≤ 1) →
    ¬ stochasticO (fun n => n / 2) R
        (fun n => Real.sqrt (kappa (spikePopulation n) * ((1 : ℕ) : ℝ) / n))

/-! ## Implications between statements -/

def N1 : Prop := S1
def N2 : Prop := S1 → S2
def N3 : Prop := S1 → S2 → S3
def N4 : Prop := S4
def N5 : Prop := S5
def N6 : Prop := S1 → S4 → S5 → S6
def N7 : Prop := S5 → S7
def N8 : Prop := S1 → S5 → S8
def N9 : Prop := S1 → S9
def N10 : Prop := S1 → S4 → S5 → S7 → S8 → S9 → S10
def N11 : Prop := S11

/-! ## Assembly -/

/-- **Assembly.** The stated implications suffice for the refutation. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7)
    (h8 : N8) (h9 : N9) (h10 : N10) (h11 : N11) : Target := by
  have s2 : S2 := h2 h1
  have s3 : S3 := h3 h1 s2
  have s6 : S6 := h6 h1 h4 h5
  have s10 : S10 := h10 h1 h4 h5 (h7 h5) (h8 h1 h5) (h9 h1)
  have hκ : ∀ n : ℕ, 6 ≤ n → kappa (spikePopulation n) ≤ 1 := fun n hn =>
    (kappa_bounds (spikePopulation n) (by omega) (s2 n (by omega)).2).2
  intro hall
  have hlog : Tendsto (fun n => kappa (spikePopulation n) *
      Real.log (((fun _ => 1 : ℕ → ℕ) n : ℕ) : ℝ)) atTop (nhds 0) := by
    simp only [Nat.cast_one, Real.log_one, mul_zero]
    exact tendsto_const_nhds
  exact h11 s10 hκ (hall (fun _ => 1) (fun n => n / 2) spikePopulation s3
    (Filter.eventually_atTop.2 ⟨6, s6⟩) hlog)

end

end AronowAudit.P005.Wave1.InteractedExpansion
