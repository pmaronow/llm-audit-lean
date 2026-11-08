import AronowAudit.P005.P005_Formalization

/-!
# Blueprint: P005-T20, refutation of `printed_interacted_expansion`

Wave 1, group P005-P006-P017-P023-P046-P047. Resolution `refute` (mapper, accepted by both
referees with no fixes).

The frozen record `AronowAudit.P005.printed_interacted_expansion` (P005_Formalization.lean,
line 829) asserts the stochastic expansion of Theorem 4.1 (p. 1510) under the literal printed
condition `κ log d → 0`. `Target` is its exact negation (checked by `rfl` below).

Witness (mapper §2, accepted): `d ≡ 1`, `m n = n / 2`, `P = spikePopulation` (existing
definitions `spikeV`, `spikeA`, `spikeZ`, `spikeQ`, `spikePopulation`). At `d = 1` the printed
condition is identically `κ·log 1 = 0`. Along even `n ≥ 6`, every balanced assignment has
remainder `|R_n| ≥ n - 6`, while the rate is at most `1/√n`.

Writers: prove `theorem nk_proof : Nk` in `AronowAudit/P005/Wave1/InteractedExpansion/Nk.lean`.
`Sk` is the statement of node k; `Nk` is `Sk` with, as hypotheses, the statements of the nodes
it may use. Do not use the admitted `univariate_endpoint_counterexample` (its proof is `sorry`).
Proved helpers that may be used: `univariate_printed_condition`, `kappa_bounds`,
`scalar_armL_det`-style algebra (`sampleCov_scale_left`, `sampleCov_scale_both`), `mean_*`
lemmas, `arm_slope_decomposition`, `inclusion_count`.

Paper proof: map-P005-P006-P017-P023-P046-P047 REPORT.md, §2 "Paper proof", steps 1–6.
-/

set_option autoImplicit false

namespace AronowAudit.P005.Wave1.InteractedExpansion

open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology

noncomputable section

/-! ## Frozen target -/

/-- **Target (P005-T20, asymptotic part).** The exact negation of the frozen printed contract
`printed_interacted_expansion` (Theorem 4.1 as printed, p. 1510). -/
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

/-- The arm OLS prediction in raw `a`-coordinates, evaluated at the population mean `1/n` of `a`:
`v̄_A + (1/n - ā_A)·Cov_A(a,v)/Var_A(a)` (paper proof step 4, `q_A(1/n)`). -/
def armFit (n : ℕ) (A : Finset (Fin n)) : ℝ :=
  mean A (spikeV n) + (1 / (n : ℝ) - mean A (spikeA n)) *
    (sampleCov A (spikeA n) (spikeV n) / sampleCov A (spikeA n) (spikeA n))

/-! ## Node statements -/

/-- **Statement S1** (paper proof step 1, "Σv_i=0, |v_i|≤1 and Q=Σv_i²=N(N-1)/(3(N-2)),
Σa_i=1, s²=(N-1)/N²·[1+1/(3(N-2)N²)]>0"): exact grid moments for every `n ≥ 3`. Reindex the
ordinary units by `j = i - 1 ∈ range (n-1)` and use `Finset.sum_range_id_mul_two`,
`Finset.sum_range_id`, `Finset.sum_range_sq`-type identities (or induction). -/
def S1 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (∑ i, spikeV n i = 0) ∧
    (∑ i, spikeV n i ^ 2 = (n : ℝ) * ((n : ℝ) - 1) / (3 * ((n : ℝ) - 2))) ∧
    (∀ i, |spikeV n i| ≤ 1) ∧
    (∑ i, spikeA n i = 1) ∧
    spikeQ n = ((n : ℝ) - 1) / (n : ℝ) ^ 2 * (1 + 1 / (3 * ((n : ℝ) - 2) * (n : ℝ) ^ 2))

/-- **Statement S2** (paper proof step 1, "Consequently x̄=0 and overline{x²}=1 at every N≥3"):
the witness is standardized at every `n ≥ 3`. Use S1 (`spikeQ n > 0`) and the proved
`standardized_scalar`-style computation (here `x = z/√q`, not `s·a`). -/
def S2 : Prop := ∀ n : ℕ, 3 ≤ n → standardized (spikePopulation n)

/-- **Statement S3** (paper proof step 1, "These facts verify all four clauses of
standingAssumptions"): with `K = 1`, `lo = 1/4`, `hi = 3/4`. Use S1 (|v|≤1) and S2. -/
def S3 : Prop := standingAssumptions (fun _ => 1) (fun n => n / 2) spikePopulation

/-- **Statement S4** (paper proof step 4, "An intercept-and-x fit is the same line as an
intercept-and-a fit; evaluating it at x=0 means evaluating at ā=1/N"): for a one-covariate
population whose covariate is the affine image `(a - c)/s`, `s ≠ 0`, of `a`, on an arm with
`Var_A(a) ≠ 0`, the arm matrix is invertible and `x̄_A·βhat_A = (ā_A - c)·Cov_A(a,y)/Var_A(a)`.
Generic; use `Matrix.det_unique`, `Matrix.inv` on `1×1` matrices (`Matrix.inv_def`,
`Matrix.det_fin_one`), `sampleCov_scale_left/both`-style algebra and `mean_sub`, `mean_mul`. -/
def S4 : Prop :=
  ∀ (n : ℕ) (P : Population n 1) (a : Fin n → ℝ) (c s : ℝ), s ≠ 0 →
    (∀ i k, P.x i k = (a i - c) / s) → ∀ (A : Finset (Fin n)) (y : Fin n → ℝ),
      sampleCov A a a ≠ 0 →
      (armL P A).det ≠ 0 ∧
      dot (xMean P A) (armBetaHat P A y) = (mean A a - c) * (sampleCov A a y / sampleCov A a a)

/-- **Statement S5** (paper proof step 2, "Every arm therefore has positive within-arm scalar
variance"): `spikeA n` is injective for `n ≥ 3` (unit 0 has `a = 1`, ordinary units have
distinct values in `[-1/n², 1/n²]`), so every arm with at least two units has positive
sample variance of `a`. -/
def S5 : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∀ A : Finset (Fin n), 2 ≤ A.card → 0 < sampleCov A (spikeA n) (spikeA n)

/-- **Statement S6** (paper proof step 2, "Hence interactedRegular holds for every assignment at
all N≥6"). From S1 (`spikeQ n > 0`), S4 (with `c = 1/n`, `s = √(spikeQ n)`) and S5 (both arms
have `≥ 3` units). -/
def S6 : Prop := ∀ n : ℕ, 6 ≤ n → interactedRegular (spikePopulation n) (n / 2)

/-- **Statement S7** (paper proof step 4, "On J the exact relation v=N²a holds ... Its OLS
prediction at ā is therefore exactly N"): an arm without the special unit predicts `n`. -/
def S7 : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∀ A : Finset (Fin n), (∀ i ∈ A, i.val ≠ 0) → 2 ≤ A.card → armFit n A = n

/-- **Statement S8** (paper proof step 4, "|b_H| ≤ [1+(N-3)/N²]/(1-1/N²)² ≤ 2 ... its prediction
q_H(1/N)=v̄_H+b_H(1/N-ā_H) has absolute value at most 3"): an arm containing the special unit
predicts a value of absolute value at most 3. Use the pairwise forms
`card A ^ 2 * Cov_A(a,v) = Σ_{i<j}(a_i-a_j)(v_i-v_j)` (and the same for `Var_A(a)`), the
`t-1` special/ordinary pairs and the ordinary pairs, and `|1/n - ā_A| < 1`. The bound holds
for every arm size `≥ 2` (the slope bound is `[1+ε(2t-3)]/(1-ε)² ≤ 2`, `ε = 1/n²`, `t ≤ n`). -/
def S8 : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∀ A : Finset (Fin n), (∃ i ∈ A, i.val = 0) → 2 ≤ A.card →
    |armFit n A| ≤ 3

/-- **Statement S9** (paper proof step 5, "The population ATE is zero ... b=N²/[3(N-2)N²+1] ≤
1/(N-1) ... |armLeading| ≤ 2+(1+1/N²)/(N-1) ≤ 3"). Uses S1. -/
def S9 : Prop :=
  ∀ n : ℕ, 6 ≤ n → ate (spikePopulation n) = 0 ∧
    ∀ S ∈ design n (n / 2), |armLeading (spikePopulation n) S| ≤ 3

/-- **Statement S10** (paper proof step 5, "Therefore every balanced assignment satisfies
|interactedATE-ate-armLeading| ≥ N-6"). By S4 (with `c = 1/n`, `s = √q`, S1, S5) both arm
terms of `interactedATE` are `armFit`s, so `interactedATE = armFit S - armFit (control S)`;
exactly one arm contains unit 0 (S7, S8), and S9 bounds the rest. -/
def S10 : Prop :=
  ∀ n : ℕ, 6 ≤ n → Even n → ∀ S ∈ design n (n / 2), (n : ℝ) - 6 ≤ |R n S|

/-- **Statement S11** (paper proof step 6, "Choose its ε=1/2 ... every member of the nonempty
design satisfies |R_N|>M sqrt(κ_N/N). The probability in stochasticO is exactly 1"): the
generic contradiction with the exact `stochasticO` quantifiers, given the deterministic
remainder bound and `κ ≤ 1`. Note `Real.sqrt` is monotone also for negative arguments. -/
def S11 : Prop :=
  (∀ n : ℕ, 6 ≤ n → Even n → ∀ S ∈ design n (n / 2), (n : ℝ) - 6 ≤ |R n S|) →
    (∀ n : ℕ, 6 ≤ n → kappa (spikePopulation n) ≤ 1) →
    ¬ stochasticO (fun n => n / 2) R
        (fun n => Real.sqrt (kappa (spikePopulation n) * ((1 : ℕ) : ℝ) / n))

/-! ## Nodes (`Nk` = statements it may use → `Sk`) -/

/-- Node N1 = S1. -/
def N1 : Prop := S1
/-- Node N2: may use S1. -/
def N2 : Prop := S1 → S2
/-- Node N3: may use S1, S2. -/
def N3 : Prop := S1 → S2 → S3
/-- Node N4 = S4 (generic). -/
def N4 : Prop := S4
/-- Node N5 = S5. -/
def N5 : Prop := S5
/-- Node N6: may use S1, S4, S5. -/
def N6 : Prop := S1 → S4 → S5 → S6
/-- Node N7: may use S5. -/
def N7 : Prop := S5 → S7
/-- Node N8: may use S1, S5. -/
def N8 : Prop := S1 → S5 → S8
/-- Node N9: may use S1. -/
def N9 : Prop := S1 → S9
/-- Node N10: may use S1, S4, S5, S7, S8, S9. -/
def N10 : Prop := S1 → S4 → S5 → S7 → S8 → S9 → S10
/-- Node N11 = S11 (generic). -/
def N11 : Prop := S11

/-! ## Assembly -/

/-- **Assembly.** The nodes suffice for the refutation. -/
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

/-- Fidelity check: `Target` is literally the negation of the frozen statement
`AronowAudit.P005.printed_interacted_expansion` (only its type is read). -/
example : Target = ¬ type_of% @AronowAudit.P005.printed_interacted_expansion := rfl

/-- The witness rate at `d ≡ 1` is the printed rate `sqrt(κ d / n)`. -/
example (n : ℕ) : Real.sqrt (kappa (spikePopulation n) * (((fun _ => 1 : ℕ → ℕ) n : ℕ) : ℝ) / n) =
    Real.sqrt (kappa (spikePopulation n) * ((1 : ℕ) : ℝ) / n) := rfl

end

end AronowAudit.P005.Wave1.InteractedExpansion
