import Mathlib
import SAP.P046.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

/-- The three categories in the continuous T1 design: low treated, low untreated, high. -/
def wholeCat (o : Unit) : Fin 3 :=
  if o.1 ≤ 3 / 5 then (if o.2.1 then 0 else 1) else 2

def wholeK {n : ℕ} (a : Sample n) : ℕ :=
  (univ.filter (fun i => wholeCat (a i) ≠ 2)).card

def wholeS {n : ℕ} (a : Sample n) : ℕ :=
  (univ.filter (fun i => wholeCat (a i) = 0)).card

def wholeCountMass (k s : ℕ) : ℝ :=
  (Nat.choose 100 k : ℝ) * (Nat.choose k s : ℝ) *
    39 ^ s * 21 ^ (k - s) * 40 ^ (100 - k) / 100 ^ 100

def wholeCountThreshold (k s : ℕ) : ℝ :=
  200 * ((s : ℝ) - 39) ^ 2 / (4225 * IntervalExample.xiK k)

def wholeCoverage (M : Study) {n : ℕ} (est radius : Sample n → ℝ) : ℝ :=
  (sampleLaw M n {a | est a - radius a ≤ mu M ∧ mu M ≤ est a + radius a}).toReal

/-- Reductions on the design support; hence also on every generated sample. -/
def WholeT1Reductions : Prop :=
  ∀ a : Sample 100,
    (∀ i, (a i).2.2 = (false, decide ((a i).1 ≤ (3 / 5 : ℝ)))) →
    ht IntervalExample.study a = (wholeS a : ℝ) / 65 ∧
    ht IntervalExample.study a - mu IntervalExample.study = ((wholeS a : ℝ) - 39) / 65 ∧
    xi IntervalExample.study a = IntervalExample.xiK (wholeK a)

def WholeT1CountLaw : Prop :=
  Measurable wholeCat ∧
  (∀ j : Fin 3, IntervalExample.study.law {o | wholeCat o = j} =
    ENNReal.ofReal (![39 / 100, 21 / 100, 40 / 100] j)) ∧
  ∀ k s : ℕ, s ≤ k → k ≤ 100 →
    sampleLaw IntervalExample.study 100 {a | wholeK a = k ∧ wholeS a = s} =
      ENNReal.ofReal (wholeCountMass k s)

def WholeT1Exclusion : Prop :=
  (∀ k s : ℕ, s ≤ k → k ≤ 100 →
    0 < IntervalExample.xiK k ∧
    (Real.sqrt (IntervalExample.xiK k * Real.log 20000000 / 200) <
        |(s : ℝ) / 65 - 3 / 5| ↔
      IntervalExample.xiK k * Real.log 20000000 / 200 < ((s : ℝ) - 39) ^ 2 / 65 ^ 2) ∧
    (IntervalExample.xiK k * Real.log 20000000 / 200 < ((s : ℝ) - 39) ^ 2 / 65 ^ 2 ↔
      Real.log 20000000 < wholeCountThreshold k s)) ∧
  strictNoncoverage IntervalExample.study 100 (1 / 10000000) =
    ∑ k ∈ range 101, ∑ s ∈ range (k + 1),
      if Real.log 20000000 < wholeCountThreshold k s then wholeCountMass k s else 0

/-- P046-T1; Proposition 3, p. 7 (PDF p. 6), Appendix A, p. 15 (PDF p. 14).
The specified continuous counterexample satisfies all standing assumptions. Its three
category probabilities and joint count law, exact sample-statistic reductions, equivalent
strict exclusion tests, 5151 feasible states and 1946 failures give the exact recorded
noncoverage probability, exceeding 119/10^9 and alpha=10^(-7). The closed interval
undercovers and the non-strict population tail also exceeds alpha. The decimal probability
is specified by its exact rational value. Usual measure-theoretic conditions are assumed. -/
def T1WholeStatement : Prop :=
  T1Statement ∧ WholeT1Reductions ∧ WholeT1CountLaw ∧ WholeT1Exclusion ∧
  (∀ {n : ℕ} (a : Sample n), wholeS a ≤ wholeK a ∧ wholeK a ≤ n) ∧
  (∀ᵐ a ∂sampleLaw IntervalExample.study 100,
    ht IntervalExample.study a = (wholeS a : ℝ) / 65 ∧
    ht IntervalExample.study a - mu IntervalExample.study = ((wholeS a : ℝ) - 39) / 65 ∧
    xi IntervalExample.study a = IntervalExample.xiK (wholeK a)) ∧
  (∑ k ∈ range 101, (k + 1)) = 5151 ∧
  wholeCoverage IntervalExample.study (ht IntervalExample.study)
      (printedRadius IntervalExample.study (1 / 10000000) (n := 100)) =
    1 - (IntervalExample.certifiedNumerator : ℝ) / 100 ^ 100 ∧
  wholeCoverage IntervalExample.study (ht IntervalExample.study)
      (printedRadius IntervalExample.study (1 / 10000000) (n := 100)) < 1 - 1 / 10000000 ∧
  (1 / 10000000 : ℝ) < tailProb IntervalExample.study (ht IntervalExample.study)
    (printedRadius IntervalExample.study (1 / 10000000) (n := 100))

/-- Full data with arbitrary covariates and treatments, obeying the T2 design equations. -/
def wholeConditionalSample (w : Fin 100 → ℝ) (x : Fin 100 → Bool) : Sample 100 :=
  fun i => (w i, (x i, (false, decide ((1 / 2 : ℝ) ≤ w i))))

/-- The summands A_i in the corrected proof. -/
def wholeSummand (M : Study) {n : ℕ} (i : Fin n) (a : Sample n) : ℝ :=
  X (a i) * Y (a i) / ((n : ℝ) * M.pi (W (a i)))

def wholeDenom (M : Study) {n : ℕ} (a : Sample n) : ℝ :=
  ∑ i, ((n : ℝ) * M.pi (W (a i)))⁻¹ ^ 2

/-- P046-T2; Appendix A, proof of Proposition 3, p. 16 (PDF p. 15).
The specified valid continuous design has mu=1/2 and a covariate event of probability
2^(-100). For every covariate vector in this event and every treatment vector, the design
outcomes, HT and the conditional centre mu_W vanish, and the absolute population error
is 1/2. Almost everywhere on the event the actual conditional mean is zero, distinct
from mu; the conditional tail is one while the full printed right side is 1/20.
Usual measure-theoretic conditions are assumed; conditional expectations are asserted
only up to almost-everywhere equality. -/
def T2WholeStatement : Prop :=
  T2Statement ∧
  (∀ (w : Fin 100 → ℝ) (x : Fin 100 → Bool), (∀ i, w i < 1 / 2) →
    (∀ i, Y (wholeConditionalSample w x i) = 0) ∧
    ht ConditionalExample.study (wholeConditionalSample w x) = 0 ∧
    muW ConditionalExample.study (wholeConditionalSample w x) = 0 ∧
    |ht ConditionalExample.study (wholeConditionalSample w x) - mu ConditionalExample.study| = 1 / 2) ∧
  (condExp (sampleCovariateSigma 100) (sampleLaw ConditionalExample.study 100)
    (ht ConditionalExample.study) =ᵐ[sampleLaw ConditionalExample.study 100]
      muW ConditionalExample.study) ∧
  (∀ᵐ a ∂(sampleLaw ConditionalExample.study 100).restrict ConditionalExample.E,
    muW ConditionalExample.study a = 0 ∧
    condExp (sampleCovariateSigma 100) (sampleLaw ConditionalExample.study 100)
      (ht ConditionalExample.study) a = 0 ∧ mu ConditionalExample.study ≠ 0) ∧
  ∀ a : Sample 100, wholeDenom ConditionalExample.study a = 1 / 81 ∧
    2 * Real.exp (-(2 * (xi ConditionalExample.study a * Real.log (2 / (1 / 20 : ℝ)) /
      (2 * 100))) / wholeDenom ConditionalExample.study a) = 1 / 20

def wholeC (n : ℕ) (alpha : ℝ) : ℝ := Real.sqrt (Real.log (4 / alpha) / (2 * n))

def wholeConditionalError (M : Study) (n : ℕ) (alpha : ℝ) : Set (Sample n) :=
  {a | Real.sqrt (xi M a) * wholeC n alpha ≤ |ht M a - muW M a|}

def wholeCovariateError (M : Study) (n : ℕ) (alpha : ℝ) : Set (Sample n) :=
  {a | wholeC n alpha ≤ |muW M a - mu M|}

/-- Independence and equality of coordinate laws, stated without choosing a sample index. -/
def WholeIID (M : Study) (n : ℕ) (f : Unit → ℝ) : Prop :=
  iIndepFun (fun (i : Fin n) (a : Sample n) => f (a i)) (sampleLaw M n) ∧
  ∀ i : Fin n, Measure.map (fun a : Sample n => f (a i)) (sampleLaw M n) =
    Measure.map f M.law

def WholeT3Centres : Prop := ∀ (M : Study), ValidStudy M → ∀ n : ℕ, 0 < n →
  (∀ a : Sample n, ht M a = ∑ i, wholeSummand M i a) ∧
  (∀ i : Fin n, ∀ᵐ a ∂sampleLaw M n,
    X (a i) * Y (a i) = X (a i) * Y1 (a i) ∧
    condExp (sampleCovariateSigma n) (sampleLaw M n) (wholeSummand M i) a =
      condExp covariateSigma M.law (fun o => X o * Y1 o) (a i) /
        ((n : ℝ) * M.pi (W (a i))) ∧
    condExp covariateSigma M.law (fun o => X o * Y1 o) (a i) /
        ((n : ℝ) * M.pi (W (a i))) =
      condExp covariateSigma M.law X (a i) * condExp covariateSigma M.law Y1 (a i) /
        ((n : ℝ) * M.pi (W (a i))) ∧
    condExp covariateSigma M.law X (a i) * condExp covariateSigma M.law Y1 (a i) /
        ((n : ℝ) * M.pi (W (a i))) = M.m (W (a i)) / n) ∧
  (condExp (sampleCovariateSigma n) (sampleLaw M n) (ht M) =ᵐ[sampleLaw M n] muW M) ∧
  (∫ a, ht M a ∂sampleLaw M n) = mu M ∧
  (∫ a, muW M a ∂sampleLaw M n) = mu M ∧
  (∀ i : Fin n, (∫ a : Sample n, M.m (W (a i)) ∂sampleLaw M n) = mu M)

def WholeT3Structure : Prop := ∀ (M : Study) (hM : ValidStudy M) (n : ℕ), 0 < n →
  letI := hM.probability
  (∃ hle : sampleCovariateSigma n ≤ (inferInstance : MeasurableSpace (Sample n)),
    iCondIndepFun (sampleCovariateSigma n) hle (fun i => wholeSummand M (n := n) i)
      (sampleLaw M n)) ∧
  (∀ᵐ a ∂sampleLaw M n, (∀ i, 0 ≤ wholeSummand M i a ∧
      wholeSummand M i a ≤ ((n : ℝ) * M.pi (W (a i)))⁻¹) ∧
    0 < xi M a ∧ 0 < wholeDenom M a ∧ wholeDenom M a = xi M a / n ∧
    Real.sqrt (xi M a) < M.delta⁻¹)

def WholeT3FixedTail : Prop := ∀ (M : Study), ValidStudy M →
  ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 ≤ t → ∀ᵐ a ∂sampleLaw M n,
    condExp (sampleCovariateSigma n) (sampleLaw M n)
      (fun b => if t ≤ |ht M b - muW M b| then (1 : ℝ) else 0) a ≤
      2 * Real.exp (-2 * t ^ 2 / wholeDenom M a) ∧
    2 * Real.exp (-2 * t ^ 2 / wholeDenom M a) =
      2 * Real.exp (-2 * n * t ^ 2 / xi M a)

def WholeT3RandomTail : Prop := ∀ (M : Study), ValidStudy M →
  ∀ n : ℕ, 0 < n → ∀ alpha : ℝ, 0 < alpha ∧ alpha < 1 →
    (∀ᵐ a ∂sampleLaw M n,
      condExp (sampleCovariateSigma n) (sampleLaw M n)
        (fun b => if Real.sqrt (xi M b) * wholeC n alpha ≤ |ht M b - muW M b| then (1 : ℝ) else 0) a ≤ alpha / 2 ∧
      2 * Real.exp (-2 * n * (Real.sqrt (xi M a) * wholeC n alpha) ^ 2 / xi M a) =
        2 * Real.exp (-2 * n * (wholeC n alpha) ^ 2)) ∧
    (sampleLaw M n (wholeConditionalError M n alpha)).toReal ≤ alpha / 2

def WholeT3Sampling : Prop := ∀ (M : Study), ValidStudy M →
  (∀ n : ℕ, WholeIID M n (fun o => M.m (W o))) ∧
  (∀ᵐ o ∂M.law, 0 ≤ M.m (W o) ∧ M.m (W o) ≤ 1) ∧
  (∫ o, M.m (W o) ∂M.law) = mu M ∧
  ∀ n : ℕ, 0 < n → ∀ alpha : ℝ, 0 < alpha ∧ alpha < 1 →
    (sampleLaw M n (wholeCovariateError M n alpha)).toReal ≤
      2 * Real.exp (-2 * n * (wholeC n alpha) ^ 2) ∧
    2 * Real.exp (-2 * n * (wholeC n alpha) ^ 2) =
      2 * Real.exp (-Real.log (4 / alpha)) ∧
    2 * Real.exp (-Real.log (4 / alpha)) = alpha / 2

def WholeT3Union : Prop := ∀ (M : Study), ValidStudy M →
  ∀ n : ℕ, 0 < n → ∀ alpha : ℝ, 0 < alpha ∧ alpha < 1 →
    (∀ a : Sample n, |ht M a - mu M| ≤ |ht M a - muW M a| + |muW M a - mu M|) ∧
    ({a : Sample n | correctedRadius M alpha a ≤ |ht M a - mu M|} ⊆
      wholeConditionalError M n alpha ∪ wholeCovariateError M n alpha) ∧
    tailProb M (ht M) (correctedRadius M alpha (n := n)) ≤
      (sampleLaw M n (wholeConditionalError M n alpha)).toReal +
      (sampleLaw M n (wholeCovariateError M n alpha)).toReal ∧
    (sampleLaw M n (wholeConditionalError M n alpha)).toReal +
      (sampleLaw M n (wholeCovariateError M n alpha)).toReal ≤ alpha ∧
    1 - alpha ≤ wholeCoverage M (ht M) (correctedRadius M alpha (n := n))

def WholeT3Known : Prop := ∀ (M : Study), ValidStudy M →
  ∀ b : ℝ, 0 < b → (∀ᵐ o ∂M.law, b ≤ M.pi (W o)) →
    (∀ n : ℕ, WholeIID M n (fun o => htTerm (M.pi (W o)) (X o) (Y o))) ∧
    (∀ᵐ o ∂M.law, 0 ≤ htTerm (M.pi (W o)) (X o) (Y o) ∧
      htTerm (M.pi (W o)) (X o) (Y o) ≤ b⁻¹) ∧
    (∫ o, htTerm (M.pi (W o)) (X o) (Y o) ∂M.law) = mu M ∧
    (∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 ≤ t →
      tailProb M (ht M) (fun _ : Sample n => t) ≤
        2 * Real.exp (-2 * n * t ^ 2 / (b⁻¹) ^ 2)) ∧
    ∀ n : ℕ, 0 < n → ∀ alpha : ℝ, 0 < alpha ∧ alpha < 1 →
      2 * Real.exp (-2 * n * (b⁻¹ * Real.sqrt (Real.log (2 / alpha) / (2 * n))) ^ 2 /
        (b⁻¹) ^ 2) = alpha ∧
      1 - alpha ≤ wholeCoverage M (ht M)
        (fun _ : Sample n => b⁻¹ * Real.sqrt (Real.log (2 / alpha) / (2 * n)))

/-- P046-T3; corrected Proposition 3, p. 7 (PDF p. 6), proof pp. 15–16
(PDF pp. 14–15). The two-error and known-bound intervals have population coverage
at least nominal. All corrected proof steps are included: conditional factorization and
means, conditional independence and ranges, fixed and covariate-measurable random
threshold bounds, i.i.d. regression sampling, triangle inclusion and union bound, strict
positivity radius bound and inverse-square-root width rate, and the alternative's i.i.d.
summands and Hoeffding calculation. Usual measure-theoretic conditions are assumed. -/
def T3WholeStatement : Prop :=
  T3Statement ∧ WholeT3Centres ∧ WholeT3Structure ∧ WholeT3FixedTail ∧
    WholeT3RandomTail ∧ WholeT3Sampling ∧ WholeT3Union ∧ WholeT3Known

def wholeWeight (w : ℝ) : ℝ :=
  (1 - RegressionExample.score w) / RegressionExample.score w ^ 2

def wholeRegressionSample {n : ℕ} (w : Fin n → ℝ) (z x : Fin n → Bool) : Sample n :=
  fun i => let b := decide (w i ≤ (1 / 2 : ℝ)) && z i
    (w i, (x i, (b, b)))

def wholeUpperTreated {n : ℕ} (T : Finset (Fin n)) (w : Fin n → ℝ)
    (x : Fin n → Bool) : ℕ := (T.filter (fun i => 1 / 2 < w i ∧ x i = true)).card

def wholeTrainingConstant {n : ℕ} (T : Finset (Fin n)) (w : Fin n → ℝ)
    (z x : Fin n → Bool) : ℝ :=
  12 * ∑ i ∈ T.filter (fun i => w i ≤ (1 / 2 : ℝ)), bit (x i) * (bit (z i) - 1 / 2) ^ 2

def wholeH (o : Unit) : ℝ := htTerm (RegressionExample.score (W o)) (X o) (Y o)

def wholeA (o : Unit) : ℝ :=
  adjustedTerm (RegressionExample.score (W o)) (X o) (Y o)
    (RegressionExample.prediction 0 (W o))

def WholeT4Training : Prop :=
  (∀ w : ℝ, wholeWeight w = if w ≤ 1 / 2 then 12 else 4 / 9) ∧
  ∀ (n : ℕ) (T : Finset (Fin n)) (w : Fin n → ℝ) (z x : Fin n → Bool),
    (∀ theta : ℝ,
      empiricalRisk RegressionExample.study T (wholeRegressionSample w z x)
          (RegressionExample.prediction theta) =
        wholeTrainingConstant T w z x + (4 / 9 : ℝ) * wholeUpperTreated T w x * theta ^ 2) ∧
    (∀ theta : ℝ, empiricalRisk RegressionExample.study T (wholeRegressionSample w z x)
        (RegressionExample.prediction 0) ≤
      empiricalRisk RegressionExample.study T (wholeRegressionSample w z x)
        (RegressionExample.prediction theta)) ∧
    (∀ theta : ℝ,
      empiricalRisk RegressionExample.study T (wholeRegressionSample w z x)
          (RegressionExample.prediction theta) =
        empiricalRisk RegressionExample.study T (wholeRegressionSample w z x)
          (RegressionExample.prediction 0) ↔ wholeUpperTreated T w x = 0 ∨ theta = 0)

def WholeT4Population : Prop := ∀ theta : ℝ,
  (∫ o, X o * wholeWeight (W o) * (Y o - RegressionExample.prediction theta (W o)) ^ 2
    ∂ RegressionExample.study.law) = risk RegressionExample.study (RegressionExample.prediction theta) ∧
  risk RegressionExample.study (RegressionExample.prediction theta) = 3 / 8 + theta ^ 2 / 6 ∧
  (risk RegressionExample.study (RegressionExample.prediction theta) =
    risk RegressionExample.study (RegressionExample.prediction 0) ↔ theta = 0)

def WholeT4Table : Prop :=
  (∀ (w : ℝ) (z x : Bool),
    let o := wholeRegressionSample (n := 1) (fun _ => w) (fun _ => z) (fun _ => x) 0
    (if w ≤ 1 / 2 then wholeH o = 4 * bit x * bit z ∧
        wholeA o = 4 * bit x * bit z + (1 / 2 : ℝ) * (1 - 4 * bit x)
      else wholeH o = 0 ∧ wholeA o = 0)) ∧
  (∀ᵐ o ∂ RegressionExample.study.law,
    (1 / 2 < W o → wholeH o = 0 ∧ wholeA o = 0) ∧
    (W o ≤ 1 / 2 ∧ X o = 0 → wholeA o = 1 / 2) ∧
    (W o ≤ 1 / 2 ∧ X o = 1 ∧ Y1 o = 0 → wholeA o = -3 / 2) ∧
    (W o ≤ 1 / 2 ∧ X o = 1 ∧ Y1 o = 1 → wholeA o = 5 / 2) ∧
    0 ≤ wholeH o ∧ wholeH o ≤ 4 ∧ -3 / 2 ≤ wholeA o ∧ wholeA o ≤ 5 / 2) ∧
  RegressionExample.study.law {o | 1 / 2 < W o} = ENNReal.ofReal (1 / 2) ∧
  RegressionExample.study.law {o | W o ≤ 1 / 2 ∧ X o = 0} = ENNReal.ofReal (3 / 8) ∧
  RegressionExample.study.law {o | W o ≤ 1 / 2 ∧ X o = 1 ∧ Y1 o = 0} =
    ENNReal.ofReal (9 / 80) ∧
  RegressionExample.study.law {o | W o ≤ 1 / 2 ∧ X o = 1 ∧ Y1 o = 1} =
    ENNReal.ofReal (1 / 80) ∧
  Integrable wholeH RegressionExample.study.law ∧ Integrable wholeA RegressionExample.study.law ∧
  Integrable (fun o => wholeH o ^ 2) RegressionExample.study.law ∧
  Integrable (fun o => wholeA o ^ 2) RegressionExample.study.law ∧
  (∫ o, wholeH o ∂ RegressionExample.study.law) = 1 / 20 ∧
  (∫ o, wholeA o ∂ RegressionExample.study.law) = 1 / 20 ∧
  (∫ o, wholeH o ^ 2 ∂ RegressionExample.study.law) = 1 / 5 ∧
  (∫ o, wholeA o ^ 2 ∂ RegressionExample.study.law) = 17 / 40 ∧
  variance wholeH RegressionExample.study.law = 79 / 400 ∧
  variance wholeA RegressionExample.study.law = 169 / 400 ∧
  variance Y1 RegressionExample.study.law = 19 / 400

/-- P046-T4; Proposition 4(c), p. 8 (PDF p. 7), treated-case weighted-loss reading.
The specified continuous counterexample has exact balanced fits g_0, with all training
loss decompositions and minimizer characterizations, the unique population minimizer,
the scalar summand table, event probabilities and moments, and bounded i.i.d. summands.
Both finite-sample variances and Gaussian limits reverse the printed efficiency ordering.
Zero is outside the family and its weighted L2 closure; the potential-outcome variance
and positive risk gap are explicit. Usual measure-theoretic conditions are assumed;
sample sizes in estimator formulas are positive. -/
def T4WholeStatement : Prop :=
  T4Statement ∧ WholeT4Training ∧ WholeT4Population ∧ WholeT4Table ∧
  (∀ n : ℕ, WholeIID RegressionExample.study n wholeH ∧ WholeIID RegressionExample.study n wholeA) ∧
  (∀ (n : ℕ) (a : Sample n), ht RegressionExample.study a = (∑ i, wholeH (a i)) / n ∧
    adjusted RegressionExample.study (RegressionExample.fits n) a = (∑ i, wholeA (a i)) / n) ∧
  (∀ (n : ℕ) (j : Bool) (a : Sample n),
    (RegressionExample.fits n).g j a = RegressionExample.prediction 0 ∧
      l2Sq RegressionExample.study
        (fun w => (RegressionExample.fits n).g j a w - RegressionExample.prediction 0 w) = 0) ∧
  (∀ theta : ℝ, RegressionExample.prediction theta ≠ (fun _ => 0)) ∧
  (∀ theta : ℝ, (3 / 8 : ℝ) ≤ weightedNormSq RegressionExample.study
    (RegressionExample.prediction theta)) ∧
  ¬ ZeroBenchmark RegressionExample.study (Set.range RegressionExample.prediction) ∧
  risk RegressionExample.study (RegressionExample.prediction 0) -
    risk RegressionExample.study (fun _ => 0) = 9 / 40 ∧ (0 : ℝ) < 9 / 40

/-- Extended squared L2 norm: infinity remains infinity. -/
def wholeL2Sq (M : Study) (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ o, ENNReal.ofReal ((g (W o)) ^ 2) ∂M.law

def wholeWeightedSq (M : Study) (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ o, ENNReal.ofReal (q M (W o) * (g (W o)) ^ 2) ∂M.law

def wholeRisk (M : Study) (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ o, ENNReal.ofReal (q M (W o) * (Y1 o - g (W o)) ^ 2) ∂M.law

/-- Genuine L2 convergence in probability, allowing infinite errors on rare training events. -/
def WholeL2InProbability (M : Study) (F : ∀ n, CrossFit n) (j : Bool) (g : ℝ → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → Tendsto (fun n =>
    (sampleLaw M n {a | ENNReal.ofReal eps <
      wholeL2Sq M (fun w => (F n).g j a w - g w)}).toReal) atTop (nhds 0)

def WholeT5Norms : Prop := ∀ (M : Study), ValidStudy M →
  (∀ᵐ o ∂M.law, M.delta ≤ q M (W o) ∧ q M (W o) ≤ M.delta⁻¹) ∧
  (∀ g : ℝ → ℝ, Measurable g →
    ENNReal.ofReal M.delta * wholeL2Sq M g ≤ wholeWeightedSq M g ∧
    wholeWeightedSq M g ≤ ENNReal.ofReal M.delta⁻¹ * wholeL2Sq M g) ∧
  (∀ u : ℕ → ℝ → ℝ, (∀ k, Measurable (u k)) →
    (Tendsto (fun k => wholeWeightedSq M (u k)) atTop (nhds 0) ↔
      Tendsto (fun k => wholeL2Sq M (u k)) atTop (nhds 0)))

def WholeT5Family : Prop := ∀ (M : Study), ValidStudy M →
  ∀ (d : ℕ) (family : (Fin d → ℝ) → ℝ → ℝ) (F : ∀ n, CrossFit n), Balanced F →
  (∀ theta, MemLp (fun o => family theta (W o)) 2 M.law) →
  ZeroBenchmark M (Set.range family) →
  (∀ n j, ∀ᵐ a ∂sampleLaw M n, ∃ theta,
    (F n).g j a = family theta ∧ ∀ eta,
    empiricalRisk M (univ.filter (fun i => (F n).fold i ≠ j)) a (family theta) ≤
      empiricalRisk M (univ.filter (fun i => (F n).fold i ≠ j)) a (family eta)) →
  ∀ gstar : ℝ → ℝ, gstar ∈ Set.range family →
    (∀ theta, risk M gstar ≤ risk M (family theta)) →
    (∀ j, WholeL2InProbability M F j gstar) → EfficiencyComparison M F gstar

def WholeT5Direct : Prop := ∀ (M : Study), ValidStudy M →
  ∀ (F : ∀ n, CrossFit n), Balanced F → ∀ gstar : ℝ → ℝ, Measurable gstar →
    (∀ j, WholeL2InProbability M F j gstar) →
    wholeRisk M gstar ≤ wholeRisk M (fun _ => 0) →
      MemLp (fun o => gstar (W o)) 2 M.law ∧
      wholeRisk M gstar < ⊤ ∧ risk M gstar ≤ risk M (fun _ => 0) ∧
      EfficiencyComparison M F gstar

/-- P046-T5; corrected Proposition 4(c), p. 8 (PDF p. 7).
The zero-benchmark square-integrable working-family theorem and the family-free direct
risk-comparison theorem give both Gaussian limits and the efficiency ordering.
The genuine extended L2 errors converge in probability; individual fitted functions
may have infinite error on events whose probabilities vanish. Finite limit risk implies
square integrability. The fixed-summand variance identity and equivalence of weighted
and ordinary L2 norms are included. Usual measure-theoretic conditions are assumed;
functions are measurable and Gaussian variance zero denotes a point mass. -/
def T5WholeStatement : Prop :=
  WholeT5Norms ∧
  (∀ (M : Study), ValidStudy M → ∀ g : ℝ → ℝ,
    MemLp (fun o => g (W o)) 2 M.law →
      variance (fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o))) M.law = V M g) ∧
  WholeT5Family ∧ WholeT5Direct

end
end SAP.P046
