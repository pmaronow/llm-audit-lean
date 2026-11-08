import Mathlib
import SAP.P001a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

namespace SAP.P001a

universe u v

/-- Uniform convergence in probability, expressed by outer probabilities of error
events. This permits an unbounded supremum on exceptional samples and puts no
condition on the artificial sample of size zero. -/
def W2UniformCP {Ω A : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Θ : Set A) (F : ℕ → Ω → A → ℝ) (L : A → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun n => prob μ {ω | ∃ t ∈ Θ, ε ≤ |F n ω t - L t|}) atTop (nhds 0)

/-- The precise tail meaning of a centered root-n bounded-in-probability sequence. -/
def W2RootNTight {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : ℕ → Ω → ℝ) (θ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n ≥ N,
    prob μ {ω | M ≤ Real.sqrt n * |T n ω - θ|} < η

def W2Response (u : ℝ × Bool × Bool) : ℝ := if u.2.1 then 1 else 0
def W2Covariate (u : ℝ × Bool × Bool) : ℝ := u.1 - 1/4
def W2Noise (u : ℝ × Bool × Bool) : ℝ := noise u.2.2
def W2HotOutcome (u : ℝ × Bool × Bool) : ℝ := 50 + W2Noise u
def W2CensoredOutcome (u : ℝ × Bool × Bool) : ℝ :=
  W2Response u * W2HotOutcome u - 99 * (1 - W2Response u)
def W2Potential (d : Bool) (u : ℝ × Bool × Bool) : ℝ :=
  if d then 0 else W2Noise u
def W2Observed (u : ℝ × Bool × Bool) : ℝ :=
  (1 - W2Response u) * W2Noise u

/-- The continuous-score design: the two uniform marginals, a fair independent
sign, the response probability, and bounded outcomes with the stated means. -/
def W2MatchingMarginals : Prop :=
  IsProbabilityMeasure matchingUnitLaw ∧
  matchingUnitLaw.map (fun u => u.1) = uniformLaw (1/4) (3/4) ∧
  matchingUnitLaw.map W2Covariate = uniformLaw 0 (1/2) ∧
  matchingUnitLaw.map W2Noise =
    (1/2 : ℝ≥0∞) • Measure.dirac 1 + (1/2 : ℝ≥0∞) • Measure.dirac (-1) ∧
  IndepFun W2Noise (fun u => (u.1, W2Response u)) matchingUnitLaw ∧
  prob matchingUnitLaw {u | W2Response u = 1} = 1/2 ∧
  (∀ᵐ u ∂matchingUnitLaw, u.1 ∈ Set.Icc (1/4 : ℝ) (3/4)) ∧
  (∀ x : ℝ, matchingUnitLaw {u | u.1 = x} = 0) ∧
  (∀ u, 49 ≤ W2HotOutcome u ∧ W2HotOutcome u ≤ 51) ∧
  mean matchingUnitLaw W2HotOutcome = 50 ∧
  mean matchingUnitLaw (fun u => W2Potential true u - W2Potential false u) = 0

/-- Propensity versions, MCAR, MAR and strong ignorability. Conditional
independence and the CEF are statements about versions; no conditioning on a
singleton of a continuous covariate is used. -/
def W2MatchingConditional : Prop :=
  IsCEF matchingUnitLaw (fun u => u.1) W2Response id ∧
  IsCEF matchingUnitLaw W2Covariate W2Response (fun x => 1/4 + x) ∧
  IndepFun W2HotOutcome W2Response matchingUnitLaw ∧
  CI matchingUnitLaw (fun u => u.1) measurable_fst W2HotOutcome W2Response ∧
  CI matchingUnitLaw W2Covariate (measurable_fst.sub_const (1/4 : ℝ))
    (fun u => (W2Potential false u, W2Potential true u)) W2Response

/-- Numerical constants, including four-decimal rounding and the exact gap. -/
def W2MatchingConstants : Prop :=
  0 < matchS ∧ matchS < 1 ∧ matchA < 3 ∧ matchB < 3/2 ∧
  0 < matchVB ∧ matchVB < matchV ∧
  matchV - matchVB = (3-matchA)/2 + (3/2-matchB)*(2*Real.log 3-3/2) ∧
  |matchV - 3.0458| < 0.00005 ∧ |matchVB - 2.6471| < 0.00005

/-- Existence of an infinite iid realization of the matching unit law. -/
def W2MatchingRealization : Prop :=
  ∃ μ : Measure (ℕ → ℝ × Bool × Bool), IsProbabilityMeasure μ ∧
    IID μ (fun n ω => ω n) ∧ μ.map (fun ω => ω 0) = matchingUnitLaw

/-- The endpoint for the fitted-score statistic itself, with the score refitted
inside each occurrence of bootVar. -/
def W2EstimatedMatchingFailure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : ℕ → Ω → ℝ × Bool × Bool) : Prop :=
  (∀ n, 0 < n → mean μ (fun ω => causalMatchEstimated (firstSample Z n ω))=0) ∧
  Tendsto (fun (n : ℕ) => (n : ℝ)*var μ
    (fun ω => causalMatchEstimated (firstSample Z n ω))) atTop (nhds matchV) ∧
  Tendsto (fun (n : ℕ) => mean μ
    (fun ω => (n : ℝ)*bootVar causalMatchEstimated (firstSample Z n ω)))
      atTop (nhds matchVB) ∧
  0 < matchVB ∧ matchVB < matchV ∧
  ¬ CP μ (fun n ω => (n : ℝ)*bootVar causalMatchEstimated (firstSample Z n ω)) matchV

/-- An auxiliary universal consistency implication used only to describe the
independent hot-deck failure example. It is stronger than the printed qualitative
assurance, and its negation receives no literal printed-claim credit. Even exact
unbiasedness, root-n tightness and a finite scaled sampling-variance limit do not
guarantee bootstrap standard-error consistency in the displayed design. -/
def W2HotDeckBiasOnlyCalibration : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ × Bool × Bool), IID μ Z → μ.map (Z 0)=matchingUnitLaw →
    (∀ n, 0 < n → mean μ (fun ω => hotDeck (firstSample Z n ω))=50) →
    W2RootNTight μ (fun n ω => hotDeck (firstSample Z n ω)) 50 →
    Tendsto (fun (n : ℕ) => (n : ℝ)*var μ (fun ω => hotDeck (firstSample Z n ω)))
      atTop (nhds matchV) →
    CP μ (fun (n : ℕ) ω => Real.sqrt n*Real.sqrt (bootVar hotDeck (firstSample Z n ω)))
      (Real.sqrt matchV)

/-- An auxiliary universal consistency implication for the independent
fitted-score failure example. It is stronger than the printed qualified assurance.
The score error is constant in x, so intercept consistency is uniform score
consistency. Its negation concerns bootstrap calibration, not the printed hedge,
the application numbers, or a root-n guarantee from score consistency alone. -/
def W2EstimatedMatchBiasOnlyCalibration : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ × Bool × Bool), IID μ Z → μ.map (Z 0)=matchingUnitLaw →
    CP μ (fun n ω => estimatedMatchIntercept (firstSample Z n ω)) (1/4) →
    (∀ n, 0 < n → mean μ (fun ω => causalMatchEstimated (firstSample Z n ω))=0) →
    W2RootNTight μ (fun n ω => causalMatchEstimated (firstSample Z n ω)) 0 →
    Tendsto (fun (n : ℕ) => (n : ℝ)*var μ
      (fun ω => causalMatchEstimated (firstSample Z n ω))) atTop (nhds matchV) →
    CP μ (fun (n : ℕ) ω => Real.sqrt n*
      Real.sqrt (bootVar causalMatchEstimated (firstSample Z n ω))) (Real.sqrt matchV)

/-- Supporting example for P001-T13; p. 233 (PDF p. 251), footnote 15 and
Table 6.3.1; hot deck: pp. 224–225; bootstrap: p. 131.
This is an independent mathematical failure example, not a whole version of the
printed qualified assurance. The uniform-score, independent-fair-sign design is
MCAR and MAR with overlap and mean outcome 50. Its nearest-neighbor hot-deck mean
is exactly unbiased and root-n tight. The scaled sampling variance tends to
3 log(3)-1/4, while the mean scaled bootstrap variance tends to the strictly
smaller displayed constant. The scaled bootstrap variances have bounded second
moments and are uniformly integrable. Neither the scaled variance nor the scaled
standard error is consistent. The iid experiment exists and contradicts the
auxiliary bias-only consistency implication. No conclusion is drawn about the
printed word "likely" or an empirical table entry. Matching uses replacement
and the existing tie rule; no respondents gives 50, and each ordered bootstrap
resample has its matches recomputed. The original target remains restricted. -/
def T13BootstrapFailureExampleStatement : Prop :=
  W2MatchingMarginals ∧ W2MatchingConditional ∧ W2MatchingConstants ∧
  (∀ u, (W2Response u = 0 → W2CensoredOutcome u = -99) ∧
    (W2Response u = 1 → W2CensoredOutcome u = W2HotOutcome u)) ∧
  (∀ᵐ u ∂matchingUnitLaw, (1/8 : ℝ) < u.1 ∧ u.1 < 1-1/8) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ × Bool × Bool), IID μ Z → μ.map (Z 0) = matchingUnitLaw →
    MatchingFailure μ Z false ∧
    W2RootNTight μ (fun n ω => hotDeck (firstSample Z n ω)) 50 ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      mean μ (fun ω => ((n : ℝ)*bootVar hotDeck (firstSample Z n ω))^2) ≤ C) ∧
    UniformIntegrable (fun (n : ℕ) ω => (n : ℝ)*bootVar hotDeck (firstSample Z n ω)) 1 μ ∧
    ¬ CP μ (fun (n : ℕ) ω => Real.sqrt n * Real.sqrt (bootVar hotDeck (firstSample Z n ω)))
      (Real.sqrt matchV)) ∧ W2MatchingRealization ∧
  ¬ W2HotDeckBiasOnlyCalibration.{u}

/-- Supporting example for P001-T15; pp. 264, 279–280 (PDF pp. 282,
297–298), Section 7.2.4 and footnote 20.
This is an independent mathematical failure example, not a whole version of the
printed qualified assurance. The bounded potential-outcome design is strongly
ignorable with overlap, uniform X on [0,1/2] and true propensity 1/4+X. Its clipped
additive intercept is consistent, uniformly estimating the score. Additive fits
preserve all distances, ties, matches and matching statistics, including every
bootstrap resample with its own refit. The weighted-sign representation gives
exact zero bias. The estimator is root-n tight, but its bootstrap has the displayed
smaller variance limit and inconsistent scaled variance and standard error.
The constants have the stated exact gap and decimals; the iid experiment exists.
Missing opposite arms use zero imputation. This contradicts the auxiliary bias-only
consistency implication, not the printed word "likely", any application estimate,
or the warning that score consistency alone need not give a root-n rate.
The original target remains restricted. -/
def T15BootstrapFailureExampleStatement : Prop :=
  W2MatchingMarginals ∧ W2MatchingConditional ∧ W2MatchingConstants ∧
  (∀ u, W2Observed u = W2Response u * W2Potential true u +
      (1-W2Response u)*W2Potential false u ∧
    |W2Potential false u| ≤ 1 ∧ |W2Potential true u| ≤ 1) ∧
  (∀ {n : ℕ} (s : Fin n → ℝ × Bool × Bool),
    (∀ x z : ℝ,
      |(estimatedMatchIntercept s+x)-(estimatedMatchIntercept s+z)| =
        |x-z| ∧ |(1/4+x)-(1/4+z)| = |x-z|) ∧
    (∀ (r : Fin n → Bool) (i : Fin n),
      nearestDonor (estimatedMatchScore s) r i = nearestDonor (fun j => (s j).1) r i) ∧
    causalMatchEstimated s = causalMatch s ∧
    (∀ a : Fin n → Fin n, causalMatchEstimated (resample s a) = causalMatch (resample s a)) ∧
    bootVar causalMatchEstimated s = bootVar causalMatch s) ∧
  (∀ {n : ℕ}, 0 < n → ∀ (p : Fin n → ℝ) (d e : Fin n → Bool),
    causalMatchEstimated (fun i => (p i,d i,e i)) =
      -(∑ j, donorReuseWeight p (fun i => !(d i)) j * noise (e j))/(n : ℝ)) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ × Bool × Bool), IID μ Z → μ.map (Z 0) = matchingUnitLaw →
    CP μ (fun n ω => estimatedMatchIntercept (firstSample Z n ω)) (1/4) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => prob μ
      {ω | ∃ x ∈ Set.Icc (0 : ℝ) (1/2), ε ≤
        |(estimatedMatchIntercept (firstSample Z n ω)+x)-(1/4+x)|}) atTop (nhds 0)) ∧
    W2EstimatedMatchingFailure μ Z ∧
    (∀ n ω, causalMatchEstimated (firstSample Z n ω) = causalMatch (firstSample Z n ω)) ∧
    W2RootNTight μ (fun n ω => causalMatchEstimated (firstSample Z n ω)) 0 ∧
    ¬ CP μ (fun (n : ℕ) ω => Real.sqrt n *
      Real.sqrt (bootVar causalMatchEstimated (firstSample Z n ω))) (Real.sqrt matchV)) ∧
  W2MatchingRealization ∧ ¬ W2EstimatedMatchBiasOnlyCalibration.{u}

def W2PlaceboPropensity (x : ℝ) : ℝ := 1/4+x^2/2
def W2BernoulliMass (p d : ℝ) : ℝ := if d = 1 then p else if d = 0 then 1-p else 0

/-- The full joint mass formula entails the uniform X law, independence of the
fair sign Z, and the conditional Bernoulli assignment. The conditional W formula
also specifies zero mass off its two-point support. -/
def W2PlaceboLawFacts : Prop :=
  (∀ x z d : ℝ,
    fprob placeboLaw (fun i => placeboX i=x ∧ placeboZ i=z ∧ placeboD i=d) =
      (if x ∈ ({-1,0,1} : Set ℝ) then (1/3 : ℝ) else 0) *
      (if z ∈ ({-1,1} : Set ℝ) then (1/2 : ℝ) else 0) *
        W2BernoulliMass (W2PlaceboPropensity x) d) ∧
  (∀ x ∈ ({-1,0,1} : Set ℝ), ∀ w d : ℝ,
    fprob placeboLaw (fun i => placeboX i=x ∧ placeboW i=w ∧ placeboD i=d) /
        fprob placeboLaw (fun i => placeboX i=x) =
      if w=x^2-1/2 ∨ w=x^2+1/2 then
        (1/2 : ℝ)*W2BernoulliMass (W2PlaceboPropensity x) d else 0)

def W2PlaceboMoments : Prop :=
  fmean placeboLaw placeboX = 0 ∧
  fmean placeboLaw (fun i => (placeboX i)^2) = 2/3 ∧
  fmean placeboLaw placeboD = 7/12 ∧
  fmean placeboLaw (fun i => placeboX i * placeboD i) = 0 ∧
  fmean placeboLaw placeboW = 2/3 ∧
  fmean placeboLaw (fun i => placeboX i * placeboW i) = 0 ∧
  fmean placeboLaw (fun i => (placeboW i-fmean placeboLaw placeboW)^2) = 17/36 ∧
  fmean placeboLaw (fun i => (placeboW i-fmean placeboLaw placeboW)*
    (placeboD i-fmean placeboLaw placeboD)) = 1/9

/-- Baseline (X,Z) is drawn before, independently of, a four-point assignment
seed. W under either intervention depends only on baseline variables. -/
def W2PlaceboStructuralLaw : Measure ((Fin 3 × Bool) × Fin 4) :=
  ((1/6 : ℝ≥0∞) • Measure.count).prod ((1/4 : ℝ≥0∞) • Measure.count)

def W2PlaceboStructuralAtom (v : (Fin 3 × Bool) × Fin 4) : Fin 12 :=
  ⟨v.1.1.val*4 + (if v.1.2 then 2 else 0) +
    (if v.2.val < (if v.1.1.val=1 then 1 else 3) then 1 else 0), by
    have hx := v.1.1.isLt
    split_ifs <;> omega⟩

def W2PlaceboInterventionW (b : Fin 3 × Bool) (_d : Bool) : ℝ :=
  ((b.1.val : ℝ)-1)^2 + noise b.2/2

def W2PlaceboInterventionY (b : Fin 3 × Bool) (d : Bool) : ℝ :=
  (if d then 3 else 2) + noise b.2

def W2PlaceboStructuralFacts : Prop :=
  IsProbabilityMeasure W2PlaceboStructuralLaw ∧
  W2PlaceboStructuralLaw.map W2PlaceboStructuralAtom = finiteLawMeasure placeboLaw ∧
  (∀ v : (Fin 3 × Bool) × Fin 4,
    placeboX (W2PlaceboStructuralAtom v) = (v.1.1.val : ℝ)-1 ∧
    placeboZ (W2PlaceboStructuralAtom v) = noise v.1.2 ∧
    placeboW (W2PlaceboStructuralAtom v) = W2PlaceboInterventionW v.1 false ∧
    W2PlaceboInterventionY v.1 false = 2+placeboZ (W2PlaceboStructuralAtom v) ∧
    W2PlaceboInterventionY v.1 true = 3+placeboZ (W2PlaceboStructuralAtom v)) ∧
  (∀ b, W2PlaceboInterventionW b false = W2PlaceboInterventionW b true)

/-- An actual array: six blocks of 40, with a 30/10 split at X=0 and a
10/30 split at X=±1, separately for each sign. -/
def W2PlaceboSample240 (i : Fin 240) : Fin 12 :=
  ⟨2*(i.val/40) + if i.val%40 < (if i.val/80=1 then 30 else 10) then 0 else 1, by
    have hi := i.isLt
    split_ifs <;> omega⟩

def W2PlaceboCounts (s : Fin 240 → Fin 12) : Prop :=
  ∀ j, (Finset.univ.filter (fun i => s i=j)).card =
    if placeboLaw.weight j = 1/8 then 30 else 10

def W2PlaceboSampleFacts (s : Fin 240 → Fin 12) : Prop :=
  let R : Matrix (Fin 240) (Fin 2) ℝ := fun i => ![1,placeboX (s i)]
  let F : Matrix (Fin 240) (Fin 3) ℝ := fun i => placeboRegressor (s i)
  let D : Fin 240 → ℝ := fun i => placeboD (s i)
  olsCoef R D = ![7/12,0] ∧ olsCoef F D = ![29/68,0,4/17] ∧
  olsRSS R D (olsCoef R D) = 175/3 ∧
  olsRSS F D (olsCoef F D) = 885/17 ∧
  placeboFStatistic (fun i (_ : Fin 1) => placeboX (s i))
    (fun i (_ : Fin 1) => placeboW (s i)) D = 5056/177

/-- P001-T17; p. 270 (PDF p. 288), Section 7.2.8.
The twelve-atom null law has a baseline-first causal realization with W unchanged
by treatment, the displayed conditional masses, overlap, conditional variance,
eight population moments, and unique restricted and full population fits.
For every iid realization, the conventional F and HC0 Wald statistics have the
displayed positive almost-sure limits after division by n, diverge, and reject
with probability tending to one at the stated critical values. An actual
240-observation exact-count sample exists; every ordering of it has the stated
OLS coefficients, residual sums and F=5056/177, rounding to 28.6.
The infinite iid experiment exists, so this is a realizable counterexample to
nominal size under conditional independence alone. -/
def T17WholeStatement : Prop :=
  T17Statement.{u} ∧ W2PlaceboLawFacts ∧ W2PlaceboStructuralFacts ∧ W2PlaceboMoments ∧
  (∃ s : Fin 240 → Fin 12, W2PlaceboCounts s) ∧
  (∀ s : Fin 240 → Fin 12, W2PlaceboCounts s → W2PlaceboSampleFacts s) ∧
  |(5056/177 : ℝ)-28.6| < 0.05 ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → Fin 12), IID μ Z → μ.map (Z 0)=finiteLawMeasure placeboLaw →
    (∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleF Z n ω) atTop atTop) ∧
    (∀ᵐ ω ∂μ, Tendsto (fun n => placeboSampleWald Z n ω) atTop atTop)) ∧
  (∃ μ : Measure (ℕ → Fin 12), IsProbabilityMeasure μ ∧
    IID μ (fun n ω => ω n) ∧ μ.map (fun ω => ω 0)=finiteLawMeasure placeboLaw)

/-- The ordinary fitted logs exist throughout a finite sample. This is a
sample-dependent event, not an all-sample positivity assumption. -/
def W2LogGood {Ω : Type*} {K τ : ℕ}
    (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (Θ : Set (Fin τ → ℝ))
    (n : ℕ) (ω : Ω) : Prop :=
  ∀ t ∈ Θ, ∀ i ∈ Finset.range n, 0 < g (Y i ω) (X i ω) t

/-- Uniform convergence of ordinary log likelihoods. The first clause controls
the real errors; the second records that the extended error is infinite when
some fitted log does not exist. Equivalently the extended uniform error tends
to zero in probability. This does not demand finite logs on every sample. -/
def W2UniformLogCP {Ω : Type*} [MeasurableSpace Ω] {K τ : ℕ}
    (μ : Measure Ω) (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (Θ : Set (Fin τ → ℝ)) : Prop :=
  W2UniformCP μ Θ (sampleLogLikelihood X Y g) (expectedLogLikelihood μ (X 0) (Y 0) g) ∧
  Tendsto (fun n => prob μ {ω | ¬ W2LogGood X Y g Θ n ω}) atTop (nhds 0)

/-- A compact finite-expected-log model problem. Maximization is required where
the fitted ordinary logs exist; the uniform extended-error hypothesis controls
the remaining samples. -/
structure W2MLProblem {Ω : Type u} [MeasurableSpace Ω] {K τ : ℕ}
    (μ : Measure Ω) (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ) where
  parameterSet : Set (Fin τ → ℝ)
  compact : IsCompact parameterSet
  truth_mem : θ ∈ parameterSet
  log_integrable : ∀ t ∈ parameterSet,
    Integrable (fun ω => Real.log (g (Y 0 ω) (X 0 ω) t)) μ
  log_exists : ∀ t ∈ parameterSet, ∀ᵐ ω ∂μ, 0 < g (Y 0 ω) (X 0 ω) t
  continuous : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) g) parameterSet
  unique : ∀ t ∈ parameterSet,
    expectedLogLikelihood μ (X 0) (Y 0) g t ≤ expectedLogLikelihood μ (X 0) (Y 0) g θ ∧
    (expectedLogLikelihood μ (X 0) (Y 0) g t = expectedLogLikelihood μ (X 0) (Y 0) g θ → t=θ)
  estimate : ℕ → Ω → Fin τ → ℝ
  measurable : ∀ n, Measurable (estimate n)
  values : ∀ n, 0 < n → ∀ᵐ ω ∂μ, estimate n ω ∈ parameterSet
  maximizes : ∀ n, 0 < n → ∀ᵐ ω ∂μ, W2LogGood X Y g parameterSet n ω →
    ∀ t ∈ parameterSet,
      sampleLogLikelihood X Y g n ω t ≤ sampleLogLikelihood X Y g n ω (estimate n ω)
  uniform : W2UniformLogCP μ X Y g parameterSet

/-- The compact argmax principle in the generality needed for part (ii). There
is no envelope at zero, no globally finite random supremum and no common
positive-density event in this principle. -/
def W2ArgmaxPrinciple : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {τ : ℕ} (Θ : Set (Fin τ → ℝ)), IsCompact Θ →
    ∀ θ ∈ Θ, ∀ L : (Fin τ → ℝ) → ℝ, ContinuousOn L Θ →
    (∀ t ∈ Θ, L t ≤ L θ ∧ (L t=L θ → t=θ)) →
    ∀ F : ℕ → Ω → (Fin τ → ℝ) → ℝ,
    ∀ T : ℕ → Ω → Fin τ → ℝ,
    (∀ n, Measurable (T n)) →
    (∀ n, 0 < n → ∀ᵐ ω ∂μ, T n ω ∈ Θ) →
    ∀ G : ℕ → Set Ω,
    Tendsto (fun n => prob μ (G n)ᶜ) atTop (nhds 0) →
    (∀ n, 0 < n → ∀ᵐ ω ∂μ, ω ∈ G n → ∀ t ∈ Θ, F n ω t ≤ F n ω (T n ω)) →
    W2UniformCP μ Θ F L → CP μ T θ

/-- Consistency of the actual log-criterion maximizers in the model problem. -/
def W2MLConsistency : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ)
    (B : W2MLProblem μ X Y g θ), CP μ B.estimate θ

def W2HessianCP {Ω : Type*} [MeasurableSpace Ω] {K τ : ℕ}
    (μ : Measure Ω) (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (U : Set (Fin τ → ℝ)) : Prop :=
  W2UniformCP μ {tjk : (Fin τ → ℝ) × Fin τ × Fin τ | tjk.1 ∈ U}
    (fun n ω tjk => sampleHessian X Y g n ω tjk.1 tjk.2.1 tjk.2.2)
    (fun tjk => populationHessian μ (X 0) (Y 0) g tjk.1 tjk.2.1 tjk.2.2)

/-- The canonical local regularity assumptions for normality. In particular the
centered score, information identity and continuity of expected Hessians are
assumptions, not consequences of pointwise C2 smoothness. QMD is absent here. -/
structure W2MLRegularity {Ω : Type u} [MeasurableSpace Ω] {K τ : ℕ}
    (μ : Measure Ω) (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ)
    (B : W2MLProblem μ X Y g θ) where
  radius : ℝ
  radius_pos : 0 < radius
  interior : Metric.ball θ radius ⊆ B.parameterSet
  regularSet : Set ((Fin K → ℝ) × ℝ)
  measurable_set : MeasurableSet regularSet
  full : (μ.map (fun ω => (X 0 ω,Y 0 ω))) regularSet = 1
  positive : ∀ xy ∈ regularSet, ∀ t ∈ B.parameterSet, 0 < g xy.2 xy.1 t
  sections : ∀ t ∈ B.parameterSet,
    Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t)
  smooth : ∀ xy ∈ regularSet, ContDiffOn ℝ 2
    (fun t => Real.log (g xy.2 xy.1 t)) (Metric.ball θ radius)
  score_l2 : ∀ j, MemLp (fun ω => modelScore g (Y 0 ω) (X 0 ω) θ j) 2 μ
  score_centered : ∀ j, mean μ (fun ω => modelScore g (Y 0 ω) (X 0 ω) θ j) = 0
  information_positive : (informationMatrix μ (X 0) (Y 0) g θ).PosDef
  information_identity : populationHessian μ (X 0) (Y 0) g θ =
    -informationMatrix μ (X 0) (Y 0) g θ
  hessian_continuous : ContinuousAt (populationHessian μ (X 0) (Y 0) g) θ
  hessian_integrable : ∀ t ∈ Metric.ball θ radius, ∀ j k,
    Integrable (fun ω => modelHessian g (Y 0 ω) (X 0 ω) t j k) μ
  hessian_uniform : W2HessianCP μ X Y g (Metric.ball θ radius)

/-- Normality for every measurable maximizer under the canonical explicit
regularities. The criterion, hence also this theorem, may be more general than a
mixture likelihood; specializing g to mixtureFamily gives the claimed result. -/
def W2MLNormality : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ),
    IID μ (fun i ω => (X i ω,Y i ω)) →
    ∀ (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ)
      (B : W2MLProblem μ X Y g θ), W2MLRegularity μ X Y g θ B →
    WeakLimit μ (fun n ω => Real.sqrt n • (B.estimate n ω-θ))
      (normalVectorLaw (informationMatrix μ (X 0) (Y 0) g θ)⁻¹)

/-- QMD of genuine dominated observation probabilities. The local integrability
clause expresses existence of the ordinary squared L2 residual, preventing an
undefined Bochner integral from masquerading as a zero remainder. Weighted score
terms vanish where the true density is zero. No finiteness assumption is made
on the chosen dominating measure. -/
def W2QMD {E : Type*} [MeasurableSpace E] {τ : ℕ} (ρ : Measure E)
    (f : (Fin τ → ℝ) → E → ℝ) (s : E → Fin τ → ℝ) (θ : Fin τ → ℝ) : Prop :=
  let R := fun t z => Real.sqrt (f t z)-Real.sqrt (f θ z)-
    (∑ j, (t j-θ j)*s z j)*Real.sqrt (f θ z)/2
  (∃ r : ℝ, 0 < r ∧ ∀ t, dist t θ < r → Integrable (fun z => (R t z)^2) ρ) ∧
  ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ t, dist t θ < r →
    (∫ z, (R t z)^2 ∂ρ) ≤ ε*(dist t θ)^2

/-- Information-bound conclusion for a fixed dominating observation measure.
Take E=(R^K)×R, ρ=ν_X⊗κ and f_t(x,y)=g_t(y|x) for the canonical model.
The probability guards say that these are actual observation laws. The claim
requires no s-finiteness of κ; neither does this formulation. -/
def W2InformationBound : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] {τ : ℕ} (ρ : Measure E)
    (f : (Fin τ → ℝ) → E → ℝ) (s : E → Fin τ → ℝ)
    (θ : Fin τ → ℝ) (δ : ℝ), 0 < δ →
    (∀ t ∈ Metric.ball θ δ, Measurable (f t)) →
    (∀ t ∈ Metric.ball θ δ, ∀ z, 0 ≤ f t z) →
    (∀ t ∈ Metric.ball θ δ,
      IsProbabilityMeasure (ρ.withDensity (fun z => ENNReal.ofReal (f t z)))) →
    ∀ [IsProbabilityMeasure (ρ.withDensity (fun z => ENNReal.ofReal (f θ z)))],
    (∀ j, MemLp (fun z => s z j) 2 (ρ.withDensity (fun z => ENNReal.ofReal (f θ z)))) →
    (∀ j, mean (ρ.withDensity (fun z => ENNReal.ofReal (f θ z))) (fun z => s z j) = 0) →
    W2QMD ρ f s θ →
    ∀ I : Matrix (Fin τ) (Fin τ) ℝ,
    (∀ j k, I j k = mean (ρ.withDensity (fun z => ENNReal.ofReal (f θ z)))
      (fun z => s z j*s z k)) → I.PosDef →
    ∀ (T : (n : ℕ) → (Fin n → E) → Fin τ → ℝ) (ψ : E → Fin τ → ℝ),
    RegularAL (fun t => ρ.withDensity (fun z => ENNReal.ofReal (f t z))) θ T ψ →
    ∀ a : Fin τ → ℝ, 0 ≤ ∑ j, ∑ k, a j*
      (covarianceMatrix (ρ.withDensity (fun z => ENNReal.ofReal (f θ z))) ψ j k-I⁻¹ j k)*a k

/-- Zero-weight nonidentification for genuine conditional model laws, without a
reference-measure finiteness assumption. -/
def W2MixtureNonidentification : Prop :=
  ∀ {M K τ : ℕ} (νX : Measure (Fin K → ℝ)) (κ : Measure ℝ)
    (p : (Fin τ → ℝ) → Fin M → ℝ)
    (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (θ θ' : Fin τ → ℝ), θ ≠ θ' → ∀ j : Fin M,
    p θ=p θ' → p θ j=0 →
    (∀ k, k ≠ j → ∀ y x, g k y x θ=g k y x θ') →
    ∀ [IsProbabilityMeasure (conditionalModelLaw νX κ (mixtureFamily p g) θ)],
    Integrable (fun xy : (Fin K → ℝ) × ℝ => Real.log (mixtureFamily p g xy.2 xy.1 θ))
      (conditionalModelLaw νX κ (mixtureFamily p g) θ) →
    (∀ y x, mixtureFamily p g y x θ=mixtureFamily p g y x θ') ∧
    conditionalModelLaw νX κ (mixtureFamily p g) θ=
      conditionalModelLaw νX κ (mixtureFamily p g) θ' ∧
    (∀ n, iidObservationLaw (conditionalModelLaw νX κ (mixtureFamily p g) θ) n=
      iidObservationLaw (conditionalModelLaw νX κ (mixtureFamily p g) θ') n) ∧
    mean (conditionalModelLaw νX κ (mixtureFamily p g) θ)
        (fun xy => Real.log (mixtureFamily p g xy.2 xy.1 θ)) =
      mean (conditionalModelLaw νX κ (mixtureFamily p g) θ')
        (fun xy => Real.log (mixtureFamily p g xy.2 xy.1 θ')) ∧
    (∀ T : (n : ℕ) → (Fin n → (Fin K → ℝ) × ℝ) → Fin τ → ℝ,
      (∀ n, Measurable (T n)) →
      ¬ (SampleCP (conditionalModelLaw νX κ (mixtureFamily p g) θ) T θ ∧
         SampleCP (conditionalModelLaw νX κ (mixtureFamily p g) θ') T θ'))

/-- P001-T12; p. 199 (PDF p. 217), Section 5.2.5, corrected subset sentence.
A freely variable zero-weight component makes the full vector unidentified:
the densities, observation laws, every iid sample law and finite expected logs
agree, and no estimator is consistent at both distinct vectors. Compactness,
continuity, unique identification and uniform positive-sample log-criterion
convergence imply consistency of every measurable maximizer. Under the explicit
common-set C2, centered L2 score, positive information, information identity,
continuous integrable expected Hessian and uniform sample-Hessian conditions,
each such interior ML maximizer has root-n limit N(0,I inverse). Separately, QMD
of the normalized fixed-dominator model implies that every regular asymptotically
linear estimator's influence covariance minus I inverse is positive semidefinite.
QMD is used only for this information bound. The argmax and local-normality
principles are given for arbitrary finite real criteria and specialize to the
fitted mixture; the information principle allows arbitrary dominating measures.
Thus unused free coordinates must be removed before a full-vector assertion. -/
def T12WholeStatement : Prop :=
  W2MixtureNonidentification ∧ W2MLConsistency.{u} ∧
    W2MLNormality.{u} ∧ W2InformationBound.{v}

end SAP.P001a
