import AronowAudit.P015.Wave1.Gap.FidP015

namespace AronowAudit.P015.Wave1.FidP015Contracts

open scoped BigOperators
open MeasureTheory Matrix




/-- P015-T11, printed p. 257 (PDF p. 8), left column, and Appendix C,
p. 265 (PDF p. 16): the unrestricted arbitrary-precision Taylor promise at
the logit of the outcome mean.

Conventions for the finite-sample statement:
* This is the fitted-mean interpretation of the Taylor substitution used to
  approximate the weights. The paper defines no separate nonlinear weights.
* `G` arbitrary groups encode a finite binary sample without loss: group `i`
  repeats design row `W i` exactly `n i` times, with `k i` successes. Counts are
  natural numbers, group sizes positive, and `k i ≤ n i`; singleton groups
  encode every ungrouped sample. The likelihood is the sum of the individual
  Bernoulli log likelihoods, with constants independent of coefficients omitted.
* Column 0 is the unit intercept, column 1 is the arbitrary real treatment,
  and the other `K` columns are arbitrary real controls. The weighted Gram
  determinant expresses full column rank of the repeated individual design.
* `p` is the empirical outcome mean, in the finite-data reading of p. 257;
  `0 < p < 1` makes its logit finite. A fit is any real global likelihood
  maximizer; no uniqueness or special coefficient values are imposed.
* A Taylor polynomial is `logisticTaylor degree (logit p)`, using the actual
  iterated derivatives through every natural degree, including zero. Arbitrary
  precision means: for each positive absolute-error tolerance, some common
  degree approximates all fitted means within that tolerance. The center stays
  fixed, and there is no restriction to predictors inside a convergence disk.

All sample sizes, control dimensions, designs, integer counts, fitted coefficient
vectors, and positive tolerances are universally quantified. -/
def printedContract_T11 : Prop :=
  ∀ (G K : ℕ) (W : Matrix (Fin G) (Fin (K + 2)) ℝ)
    (n k : Fin G → ℕ),
    (∀ i, W i 0 = 1) →
    (∀ i, 0 < n i ∧ k i ≤ n i) →
    ((W.transpose * Matrix.diagonal (fun i => (n i : ℝ))) * W).det ≠ 0 →
    let p := (∑ i, (k i : ℝ)) / (∑ i, (n i : ℝ));
    0 < p → p < 1 →
    ∀ θhat : Fin (K + 2) → ℝ,
      (∀ θ : Fin (K + 2) → ℝ,
        AronowAudit.P015.groupedLikelihood W (fun i => (n i : ℝ))
            (fun i => (k i : ℝ)) AronowAudit.P015.logistic θ ≤
          AronowAudit.P015.groupedLikelihood W (fun i => (n i : ℝ))
            (fun i => (k i : ℝ)) AronowAudit.P015.logistic θhat) →
      ∀ ε : ℝ, 0 < ε → ∃ degree : ℕ, ∀ i : Fin G,
        |AronowAudit.P015.logisticTaylor degree (AronowAudit.P015.logit p)
            (W.mulVec θhat i) - AronowAudit.P015.logistic (W.mulVec θhat i)| < ε

end AronowAudit.P015.Wave1.FidP015Contracts

namespace AronowAudit.P015.Wave1

open scoped BigOperators
open Matrix

/-- The two-cell counterexample refutes the universally quantified
printed P015-T11 fitted-mean Taylor assertion at tolerance `1/4`. -/
theorem taylor_counterexample_printed_negation :
    ¬ FidP015Contracts.printedContract_T11 := by
  intro h
  have certificate := taylor_counterexample
  change AronowAudit.P015.TaylorCounterexample at certificate
  let W : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;1,1]
  let n : Fin 2 → ℕ := fun _ => 100
  let k : Fin 2 → ℕ := ![1,99]
  let θhat : Fin 2 → ℝ := ![-Real.log 99,2 * Real.log 99]
  have hW : ∀ i, W i 0 = 1 := by
    intro i
    fin_cases i <;> norm_num [W]
  have hcounts : ∀ i, 0 < n i ∧ k i ≤ n i := by
    intro i
    fin_cases i <;> norm_num [n, k]
  have hgram :
      ((W.transpose * Matrix.diagonal (fun i => (n i : ℝ))) * W).det ≠ 0 := by
    norm_num [W, n, Matrix.det_fin_two, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.diagonal, Fin.sum_univ_succ]
  have hmean : (∑ i, (k i : ℝ)) / (∑ i, (n i : ℝ)) = (1 + 99) / 200 := by
    norm_num [n, k, Fin.sum_univ_succ]
  have hmean_pos : 0 < (∑ i, (k i : ℝ)) / (∑ i, (n i : ℝ)) := by
    rw [hmean]
    norm_num
  have hmean_lt : (∑ i, (k i : ℝ)) / (∑ i, (n i : ℝ)) < 1 := by
    rw [hmean]
    norm_num
  have hlikelihood : ∀ θ : Fin 2 → ℝ,
      AronowAudit.P015.groupedLikelihood W (fun i => (n i : ℝ))
        (fun i => (k i : ℝ)) AronowAudit.P015.logistic θ =
        AronowAudit.P015.extremeLikelihood θ := by
    intro θ
    simp [AronowAudit.P015.groupedLikelihood, AronowAudit.P015.extremeLikelihood,
      W, n, k, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hmax : ∀ θ : Fin 2 → ℝ,
      AronowAudit.P015.groupedLikelihood W (fun i => (n i : ℝ))
          (fun i => (k i : ℝ)) AronowAudit.P015.logistic θ ≤
        AronowAudit.P015.groupedLikelihood W (fun i => (n i : ℝ))
          (fun i => (k i : ℝ)) AronowAudit.P015.logistic θhat := by
    intro θ
    rw [hlikelihood, hlikelihood]
    exact certificate.1.1 θ
  obtain ⟨degree, hdegree⟩ :=
    h 2 0 W n k hW hcounts hgram hmean_pos hmean_lt θhat hmax (1 / 4) (by norm_num)
  have hcenter : AronowAudit.P015.logit
      ((∑ i, (k i : ℝ)) / (∑ i, (n i : ℝ))) = 0 := by
    rw [hmean]
    exact certificate.1.2.2.2.2.1
  have hpredictor : W.mulVec θhat 1 = Real.log 99 := by
    simp [W, θhat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  have hsmall : |AronowAudit.P015.logisticTaylor degree 0 (Real.log 99) -
      AronowAudit.P015.logistic (Real.log 99)| < 1 / 4 := by
    simpa only [hcenter, hpredictor] using hdegree 1
  have hlarge : 49 / 100 ≤
      |AronowAudit.P015.logisticTaylor degree 0 (Real.log 99) -
        AronowAudit.P015.logistic (Real.log 99)| :=
    (certificate.1.2.2.2.2.2.2.2 degree).1
  linarith

end AronowAudit.P015.Wave1

namespace AronowAudit.P015.Wave1.FidP015Contracts


end AronowAudit.P015.Wave1.FidP015Contracts
