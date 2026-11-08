import AronowAudit.P015.Wave1.Gap.FidP015

namespace AronowAudit.P015.Wave1.FidP015Contracts

open scoped BigOperators
open MeasureTheory Matrix

/-! Independent statement copies from `map-fid-P015/map.json`, records 0--2.
Neither referee changes a Lean statement. Referee 2's only T8 fix is prose:
"This states the target's existing unit-intercept and admissible-predictor conditions;
do not add hypotheses to the new named-law theorem."
The approved binders and conclusions below are copied from the mapper records,
with theorem parameters universally closed, rather than inferred from the finals.
-/

/-- Approved statement for P015-T8: `map-fid-P015/map.json`, record 0,
`proposed_statement_lean`; accepted by both `ref1-fid-P015` and `ref2-fid-P015`
without Lean statement changes. -/
def approvedContract_T8 : Prop := ∀ (η : ℝ),
    (MeasureTheory.IsProbabilityMeasure
        (AronowAudit.P015.Wave1.bernoulliResponseLaw η) ∧
      MeasureTheory.Integrable (fun y : ℝ => y)
        (AronowAudit.P015.Wave1.bernoulliResponseLaw η) ∧
      (∫ y : ℝ, y ∂(AronowAudit.P015.Wave1.bernoulliResponseLaw η)) =
        AronowAudit.P015.logistic η ∧
      AronowAudit.P015.logistic η =
        deriv (fun a : ℝ => Real.log (1 + Real.exp a)) η) ∧
    (MeasureTheory.IsProbabilityMeasure
        (AronowAudit.P015.Wave1.poissonResponseLaw η) ∧
      MeasureTheory.Integrable (fun n : ℕ => (n : ℝ))
        (AronowAudit.P015.Wave1.poissonResponseLaw η) ∧
      (∫ n : ℕ, (n : ℝ) ∂(AronowAudit.P015.Wave1.poissonResponseLaw η)) =
        Real.exp η ∧
      Real.exp η = deriv Real.exp η)

example : approvedContract_T8 := @AronowAudit.P015.Wave1.canonical_named_model_means

-- Retain the approved, named hypothesis binder `hW` verbatim.
set_option linter.unusedVariables false in
/-- Approved statement for P015-T21: `map-fid-P015/map.json`, record 1,
`proposed_statement_lean`; accepted by both `ref1-fid-P015` and `ref2-fid-P015`
without Lean statement changes. -/
def approvedContract_T21 : Prop := ∀ (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K + 2)) ℝ)
    (hW : ∀ i, W i 0 = 1) (b c : ℝ)
    (θ : Fin (K + 2) → ℝ) (Y : Fin N → ℝ),
    (∀ i, W.mulVec (AronowAudit.P015.affineTheta 0 b c θ) i =
      b + c * W.mulVec θ i) ∧
    W.transpose.mulVec (fun i => Y i - b - c * W.mulVec θ i) =
      W.transpose.mulVec (fun i =>
        Y i - W.mulVec (AronowAudit.P015.affineTheta 0 b c θ) i)

example : approvedContract_T21 := @AronowAudit.P015.Wave1.affine_predictor

/-- Approved statement for P015-T11: `map-fid-P015/map.json`, record 2,
`proposed_statement_lean`; accepted by both `ref1-fid-P015` and `ref2-fid-P015`
without Lean statement changes. -/
def approvedContract_T11 : Prop :=
    AronowAudit.P015.TaylorCounterexample

example : approvedContract_T11 := @AronowAudit.P015.Wave1.taylor_counterexample

/-- P015-T11, printed p. 257 (PDF p. 8), left column, and Appendix C,
p. 265 (PDF p. 16): the unrestricted arbitrary-precision Taylor promise at
the logit of the outcome mean. Sources: `runs/P015/staged/main.txt:479-482`
and `:1010-1059`, `runs/P015/lean/targets.json` P015-T11 (especially
`definitions_needed`), and `map-fid-P015` record 2 with both referee records.

Conventions left open by the paper, fixed as in the recorded target:
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
* `p` is the empirical outcome mean, as in the target's finite-data reading
  of p. 257; `0 < p < 1` makes its logit finite. A fit is any real global
  likelihood maximizer; no uniqueness or special coefficient values are imposed.
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

/-- The approved two-cell certificate refutes the fully universally closed
printed P015-T11 fitted-mean Taylor contract at tolerance `1/4`. -/
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

#print axioms AronowAudit.P015.Wave1.taylor_counterexample_printed_negation
#print axioms AronowAudit.P015.Wave1.canonical_named_model_means
#print axioms AronowAudit.P015.Wave1.affine_predictor
#print axioms AronowAudit.P015.Wave1.taylor_counterexample

end AronowAudit.P015.Wave1

namespace AronowAudit.P015.Wave1.FidP015Contracts

/-- Exact printed-contract negation credited to P015-T11. -/
abbrev Target_T11 : Prop := ¬ printedContract_T11

example : Target_T11 := AronowAudit.P015.Wave1.taylor_counterexample_printed_negation
example : Target_T11 ↔ ¬ printedContract_T11 := Iff.rfl

end AronowAudit.P015.Wave1.FidP015Contracts
