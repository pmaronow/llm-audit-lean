import Mathlib
import SAP.P046.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

/-- The evaluated opposite-fold prediction for observation i. -/
def wholePrediction {n : ℕ} (F : CrossFit n) (i : Fin n) (a : Sample n) : ℝ :=
  F.g (F.fold i) a (W (a i))

/-- The second term in the printed three-term expansion. -/
def wholeWeightedPrediction (M : Study) {n : ℕ} (F : CrossFit n) (i : Fin n)
    (a : Sample n) : ℝ := X (a i) * wholePrediction F i a / M.pi (W (a i))

/-- Conditioning on this observation's covariate, rather than all covariates. -/
abbrev wholeOwnSigma (n : ℕ) (i : Fin n) : MeasurableSpace (Sample n) :=
  MeasurableSpace.comap (fun a => W (a i)) inferInstance

/-- The integrable HT summand and the expectation chain in the printed proof.
All conditional expectations here are on the single-unit probability space. -/
def wholeHTChain (M : Study) : Prop :=
  Integrable (fun o => X o * Y1 o / M.pi (W o)) M.law ∧
  (∫ o, X o * Y1 o / M.pi (W o) ∂M.law) =
    (∫ o, condExp covariateSigma M.law (fun u => X u * Y1 u) o /
      M.pi (W o) ∂M.law) ∧
  (∫ o, condExp covariateSigma M.law (fun u => X u * Y1 u) o /
      M.pi (W o) ∂M.law) =
    (∫ o, condExp covariateSigma M.law X o * condExp covariateSigma M.law Y1 o /
      M.pi (W o) ∂M.law) ∧
  (∫ o, condExp covariateSigma M.law X o * condExp covariateSigma M.law Y1 o /
      M.pi (W o) ∂M.law) = mu M

/-- Treatment and the evaluated opposite-fold prediction are independent
conditional on this observation's covariate, without a fitted-value moment guard. -/
def wholeFitIndependent (M : Study) (hprob : IsProbabilityMeasure M.law)
    {n : ℕ} (F : CrossFit n) (i : Fin n) : Prop := letI := hprob;
  CondIndepFun (wholeOwnSigma n i)
    (by exact (measurable_fst.comp (measurable_pi_apply i)).comap_le)
    (fun a => X (a i)) (wholePrediction F i) (sampleLaw M n)

/-- The printed fitted-term chain when the prediction's expectation exists.
This guard is local to component expectations, not the unbiasedness assertion. -/
def wholeFitMoments (M : Study) {n : ℕ} (F : CrossFit n) (i : Fin n) : Prop :=
  Integrable (wholePrediction F i) (sampleLaw M n) →
    Integrable (wholeWeightedPrediction M F i) (sampleLaw M n) ∧
    (condExp (wholeOwnSigma n i) (sampleLaw M n)
      (fun a => X (a i) * wholePrediction F i a) =ᵐ[sampleLaw M n]
      fun a => condExp (wholeOwnSigma n i) (sampleLaw M n) (fun b => X (b i)) a *
        condExp (wholeOwnSigma n i) (sampleLaw M n) (wholePrediction F i) a) ∧
    (∫ a, wholeWeightedPrediction M F i a ∂sampleLaw M n) =
      (∫ a, condExp (wholeOwnSigma n i) (sampleLaw M n) (fun b => X (b i)) a *
        condExp (wholeOwnSigma n i) (sampleLaw M n) (wholePrediction F i) a /
          M.pi (W (a i)) ∂sampleLaw M n) ∧
    (∫ a, condExp (wholeOwnSigma n i) (sampleLaw M n) (fun b => X (b i)) a *
        condExp (wholeOwnSigma n i) (sampleLaw M n) (wholePrediction F i) a /
          M.pi (W (a i)) ∂sampleLaw M n) =
      ∫ a, wholePrediction F i a ∂sampleLaw M n

/-- The independence and guarded moment assertions in the printed proof. -/
def wholeFitChain (M : Study) (hprob : IsProbabilityMeasure M.law)
    {n : ℕ} (F : CrossFit n) (i : Fin n) : Prop :=
  wholeFitIndependent M hprob F i ∧ wholeFitMoments M F i

/-- P046-T8; Proposition 4(a), p. 8 (PDF p. 7), Appendix A, p. 16 (PDF p. 15).
The cross-fitted regression estimator is finite-sample unbiased whenever its
expectation exists, including cancellation between nonintegrable predictions.
The consistency identity, three-term expansion, HT expectation chain,
opposite-fold conditional independence, and fitted-term expectation and
cancellation chains are included. Component expectation chains are asserted
when their individual expectations exist. The usual measure-theoretic
conditions are assumed. Arbitrary deterministic folds include roughly equal folds. -/
def T8WholeStatement : Prop := ∀ (M : Study) (hM : ValidStudy M),
  ∀ (n : ℕ), 0 < n → ∀ F : CrossFit n,
  (Integrable (adjusted M F) (sampleLaw M n) →
    (∫ a, adjusted M F a ∂sampleLaw M n) = mu M) ∧
  (∀ a : Sample n, (∀ i, X (a i) * Y (a i) = X (a i) * Y1 (a i)) ∧
    adjusted M F a =
      (∑ i, X (a i) * Y1 (a i) / M.pi (W (a i))) / n -
      (∑ i, wholeWeightedPrediction M F i a) / n +
      (∑ i, wholePrediction F i a) / n) ∧
  wholeHTChain M ∧
  (∀ i, (∫ a, X (a i) * Y1 (a i) / M.pi (W (a i)) ∂sampleLaw M n) = mu M) ∧
  (∀ i, wholeFitChain M hM.probability F i) ∧
  ((∀ i, Integrable (wholePrediction F i) (sampleLaw M n)) →
    (∫ a, (∑ i, wholeWeightedPrediction M F i a) / n ∂sampleLaw M n) =
      (∫ a, (∑ i, wholePrediction F i a) / n ∂sampleLaw M n) ∧
    (∫ a, adjusted M F a ∂sampleLaw M n) =
      (∑ _i : Fin n, mu M) / n ∧ (∑ _i : Fin n, mu M) / n = mu M)

/-- Nonnegative extended squared L2 prediction error. Infinity is retained. -/
def wholeL2Error (M : Study) {n : ℕ} (F : CrossFit n) (j : Bool)
    (g : ℝ → ℝ) (a : Sample n) : ℝ≥0∞ :=
  ∫⁻ o, ENNReal.ofReal ((F.g j a (W o) - g (W o)) ^ 2) ∂M.law

/-- L2 prediction consistency in probability, allowing infinite errors on
events whose probabilities tend to zero. Only probabilities are made real. -/
def WholeL2InProbability_W2 (M : Study) (F : ∀ n, CrossFit n) (j : Bool)
    (g : ℝ → ℝ) : Prop := ∀ eps : ℝ, 0 < eps →
  Tendsto (fun n => (sampleLaw M n
    {a | ENNReal.ofReal eps < wholeL2Error M (F n) j g a}).toReal) atTop (nhds 0)

/-- Mean-square convergence as convergence of extended nonnegative expectations.
No total real integral can erase an infinite squared error. -/
def WholeL2InMeanSquare (M : Study) (F : ∀ n, CrossFit n) (j : Bool)
    (g : ℝ → ℝ) : Prop :=
  Tendsto (fun n => ∫⁻ a, wholeL2Error M (F n) j g a ∂sampleLaw M n)
    atTop (nhds 0)

/-- Localize a fit on its training-only error event, using a fixed reference
function when the error exceeds one. -/
def wholeLocalPrediction (M : Study) {n : ℕ} (F : CrossFit n)
    (g : Bool → ℝ → ℝ) (j : Bool) (a : Sample n) (w : ℝ) : ℝ :=
  if wholeL2Error M F j (g j) a ≤ 1 then F.g j a w else g j w

/-- The localized CrossFit preserves the original deterministic partition. -/
def WholeLocalization (M : Study) {n : ℕ} (F G : CrossFit n)
    (g : Bool → ℝ → ℝ) : Prop :=
  G.fold = F.fold ∧ ∀ j a w, G.g j a w = wholeLocalPrediction M F g j a w

/-- Equality with probability tending to one. All measures in its applications
are probability measures, so converting these probabilities to reals is safe. -/
def WholeAsymptoticAgreement (M : Study) (A B : ∀ n, Sample n → ℝ) : Prop :=
  Tendsto (fun n => (sampleLaw M n {a | A n a ≠ B n a}).toReal) atTop (nhds 0)

/-- P046-T9; Proposition 4(b) and 4(d), p. 8 (PDF p. 7).
For balanced deterministic opposite-fold fits, mean-square convergence to any
two fixed L2 functions gives root-n consistency. L2 consistency in probability
for the true regression gives the normal limit with variance equal to the
numerical Hahn efficiency bound, including its zero-variance convention.
Extended squared errors allow infinite-error events of vanishing probability;
no finite-sample L2 condition is added on the fitted functions. The usual
measure-theoretic conditions are assumed. -/
def T9WholeStatement : Prop :=
  (∀ (M : Study), ValidStudy M → ∀ (F : ∀ n, CrossFit n), Balanced F →
    ∀ (g : Bool → ℝ → ℝ), (∀ j, Measurable (g j)) →
    (∀ j, MemLp (fun o => g j (W o)) 2 M.law) →
    (∀ j, WholeL2InMeanSquare M F j (g j)) →
    RootN M (fun n => adjusted M (F n))) ∧
  (∀ (M : Study), ValidStudy M → ∀ (F : ∀ n, CrossFit n), Balanced F →
    (∀ j, WholeL2InProbability_W2 M F j M.m) →
    NormalLimit M (fun n => adjusted M (F n)) (hahnBound M))

end
end SAP.P046
