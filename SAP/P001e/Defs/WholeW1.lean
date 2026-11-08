import Mathlib
import SAP.P001e.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e
universe u v
noncomputable section

/-- The finite normal density, parametrized by its standard deviation. -/
def W1normalDensity (m s y : ℝ) : ℝ :=
  Real.exp (-(y-m)^2/(2*s^2))/(s*Real.sqrt (2*Real.pi))

/-- A real-valued density of a law, including integrability and the version convention. -/
def W1HasPDF (ν : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  AEMeasurable f volume ∧ (∀ y, 0 ≤ f y) ∧ Integrable f volume ∧
    ν = volume.withDensity (fun y => ENNReal.ofReal (f y))

/-- P001-T77; p. 186 (PDF p. 204), footnote 5 after Definition 5.2.1.
The realized finite nonnegative likelihood is a function on the parameter set in
real coordinate space of the parameter's arity. A normal PDF at its mean equals
1/(s sqrt(2 pi)) for positive standard deviation s, and exceeds one whenever
s < 1/sqrt(2 pi). Thus PDF likelihood values need not lie in [0,1]. -/
def T77WholeStatement : Prop :=
  T77Statement.{u} ∧ ∀ m s : ℝ, 0 < s →
    Integrable (W1normalDensity m s) volume ∧
    (∀ y, 0 ≤ W1normalDensity m s y) ∧
    (∫ y, W1normalDensity m s y) = 1 ∧
    W1normalDensity m s m = 1/(s*Real.sqrt (2*Real.pi)) ∧
    (s < 1/Real.sqrt (2*Real.pi) → 1 < W1normalDensity m s m)

/-- P001-T78; p. 191 (PDF p. 209), footnote 10 in Example 5.2.4.
For a nonempty regression sample with an intercept, any least-squares minimizer
with positive residual sum Q jointly maximizes the normal log likelihood at
scale sqrt(Q/n). Its squared scale is Q/n. The residual sum and mean are zero,
so Q/n equals both the centered residual second moment and the plug-in variance.
No rank or uniqueness assumption is required. -/
def T78WholeStatement : Prop :=
  ∀ {n K : ℕ} (_hn : 0 < n) (X : Matrix (Fin n) (Fin (K+1)) ℝ)
    (Y : Fin n → ℝ) (b : Fin (K+1) → ℝ),
    (∀ i, X i 0 = 1) →
    (∀ c, residualSS X Y b ≤ residualSS X Y c) →
    0 < residualSS X Y b →
    let e := fun i => Y i - X.mulVec b i
    let m := (∑ i, e i)/(n : ℝ)
    0 < Real.sqrt (residualSS X Y b/(n : ℝ)) ∧
    (Real.sqrt (residualSS X Y b/(n : ℝ)))^2 = residualSS X Y b/(n : ℝ) ∧
    (∀ c s, 0 < s → gaussianLogLikelihood X Y c s ≤
      gaussianLogLikelihood X Y b (Real.sqrt (residualSS X Y b/(n : ℝ)))) ∧
    (∑ i, e i) = 0 ∧ m = 0 ∧
    (∑ i, (e i-m)^2)/(n : ℝ) = residualSS X Y b/(n : ℝ) ∧
    (∑ i, e i^2)/(n : ℝ)-m^2 = residualSS X Y b/(n : ℝ)

/-- The lower orthant with a common threshold for each covariate coordinate. -/
def W1orthant {K : ℕ} (x : Fin K → ℝ) : Set (Fin K → ℝ) :=
  {u | ∀ k, u k ≤ x k}

/-- The joint CDF of a law on the outcome and the covariate vector. -/
def W1jointCDF {K : ℕ} (ν : Measure (ℝ × (Fin K → ℝ)))
    (z : ℝ × (Fin K → ℝ)) : ℝ :=
  probability ν {w | w.1 ≤ z.1 ∧ w.2 ∈ W1orthant z.2}

/-- The domain of statistical functionals: actual joint CDFs of probability laws. -/
def W1JointCDF (K : ℕ) :=
  {F : (ℝ × (Fin K → ℝ)) → ℝ //
    ∃ ν : Measure (ℝ × (Fin K → ℝ)), IsProbabilityMeasure ν ∧ F = W1jointCDF ν}

/-- Applying a statistical functional to the fitted joint CDF defines the ML plug-in estimate. -/
def W1MLPlugin {K : ℕ} (T : W1JointCDF K → ℝ) (Fhat : W1JointCDF K) : ℝ := T Fhat

/-- Existence of the fitted maximizer is supplied; existence or a selection rule is not asserted. -/
def W1IsMLE {n K τ : ℕ} (Θ : Set (Fin τ → ℝ))
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (Y : Fin n → ℝ) (X : Fin n → Fin K → ℝ) (t : Fin τ → ℝ) : Prop :=
  t ∈ Θ ∧ ∀ s ∈ Θ, (∏ i, g (Y i) (X i) s) ≤ ∏ i, g (Y i) (X i) t

/-- The PMF lower-tail sum, allowing countably infinite support on the reals. -/
def W1pmfTail (p : PMF ℝ) (y : ℝ) : ℝ := ∑' v : ℝ, if v ≤ y then (p v).toReal else 0

/-- A normalized fitted law, its corrected sample formula, and its functional interpretation. -/
def W1FittedDisplay {n K : ℕ} (X : Fin n → Fin K → ℝ)
    (ν : Fin n → Measure ℝ) (H : Fin n → ℝ → ℝ) : Prop :=
  IsProbabilityMeasure (fittedJointLaw X ν) ∧
  ∃ Fhat : W1JointCDF K, Fhat.val = W1jointCDF (fittedJointLaw X ν) ∧
    (∀ y x, Fhat.val (y,x) =
      (∑ i, if X i ∈ W1orthant x then H i y else 0)/(n : ℝ)) ∧
    ∀ T : W1JointCDF K → ℝ, W1MLPlugin T Fhat = T Fhat

/-- Population CDF identities for a conditional law and its PMF or PDF versions. -/
def W1PopulationCDF : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K : ℕ} (Y : Ω → ℝ) (X : Ω → Fin K → ℝ), Measurable Y → Measurable X →
  ∃ F : W1JointCDF K,
    F.val = W1jointCDF (μ.map (fun ω => (Y ω, X ω))) ∧
    (∀ y x, F.val (y,x) = probability μ {ω | Y ω ≤ y ∧ X ω ∈ W1orthant x}) ∧
    (∀ y x,
      Integrable (fun ω => if X ω ∈ W1orthant x then
        probability (condDistrib Y X μ (X ω)) (Iic y) else 0) μ ∧
      F.val (y,x) = expectation μ (fun ω => if X ω ∈ W1orthant x then
        probability (condDistrib Y X μ (X ω)) (Iic y) else 0)) ∧
    (∀ p : (Fin K → ℝ) → PMF ℝ,
      (∀ᵐ x ∂(μ.map X), condDistrib Y X μ x = (p x).toMeasure) → ∀ y x,
      Integrable (fun ω => if X ω ∈ W1orthant x then W1pmfTail (p (X ω)) y else 0) μ ∧
      F.val (y,x) = expectation μ
        (fun ω => if X ω ∈ W1orthant x then W1pmfTail (p (X ω)) y else 0)) ∧
    (∀ f : ℝ → (Fin K → ℝ) → ℝ,
      (∀ᵐ x ∂(μ.map X), W1HasPDF (condDistrib Y X μ x) (fun v => f v x)) → ∀ y x,
      Integrable (fun ω => if X ω ∈ W1orthant x then (∫ v in Iic y, f v (X ω)) else 0) μ ∧
      F.val (y,x) = expectation μ
        (fun ω => if X ω ∈ W1orthant x then (∫ v in Iic y, f v (X ω)) else 0))

/-- The corrected fitted PMF display, using the same ML parameter in every summand. -/
def W1FittedPMF : Prop :=
  ∀ {n K τ : ℕ}, 0 < n → ∀ (Θ : Set (Fin τ → ℝ))
    (p : (Fin K → ℝ) → (Fin τ → ℝ) → PMF ℝ)
    (Y : Fin n → ℝ) (X : Fin n → Fin K → ℝ) (t : Fin τ → ℝ),
    W1IsMLE Θ (fun y x s => (p x s y).toReal) Y X t →
    W1FittedDisplay X (fun i => (p (X i) t).toMeasure) (fun i => W1pmfTail (p (X i) t))

/-- The corrected fitted PDF display, with normalized laws for the conditional PDF model. -/
def W1FittedPDF : Prop :=
  ∀ {n K τ : ℕ}, 0 < n → ∀ (Θ : Set (Fin τ → ℝ))
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (ν : (Fin K → ℝ) → (Fin τ → ℝ) → Measure ℝ),
    (∀ x t, t ∈ Θ → IsProbabilityMeasure (ν x t)) →
    (∀ x t, t ∈ Θ → W1HasPDF (ν x t) (fun y => g y x t)) →
    ∀ (Y : Fin n → ℝ) (X : Fin n → Fin K → ℝ) (t : Fin τ → ℝ),
    W1IsMLE Θ g Y X t →
    W1FittedDisplay X (fun i => ν (X i) t) (fun i y => ∫ v in Iic y, g v (X i) t)

/-- P001-T79; pp. 197–198 (PDF pp. 215–216), Definition 5.2.10.
The population joint CDF is the expectation of the covariate lower-orthant
indicator times the conditional lower-tail probability, expressed by a PMF sum
or PDF integral for the appropriate conditional-law version. Replacing that
expectation by the sample mean and using one attained ML parameter gives the
corrected fitted PMF and PDF displays. Each fitted display is a joint CDF of a
probability law, so applying any real statistical functional T defines T(Fhat).
Samples are nonempty; conditional laws and densities are read as versions. -/
def T79WholeStatement : Prop := W1PopulationCDF.{u} ∧ W1FittedPMF ∧ W1FittedPDF

/-- The respondent conditional mean used in the sharp bounds. -/
def W1respondentMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ystar R : Ω → ℝ) : ℝ :=
  (∫ ω in {ω | R ω = 1}, Ystar ω ∂μ)/probability μ {ω | R ω = 1}

/-- Whole sharp bounds with almost-sure support assumptions and endpoint formulas. -/
def W1MissingBounds : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y R : Ω → ℝ), Measurable Y → Measurable R → ∀ a b : ℝ, a ≤ b →
    (∀ᵐ ω ∂μ, Y ω ∈ Icc a b) → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < probability μ {ω | R ω = 0} → 0 < probability μ {ω | R ω = 1} →
    let Ys := fun ω => recordedOutcome (Y ω) (R ω)
    let m := W1respondentMean μ Ys R
    let L := m*probability μ {ω | R ω = 1}+a*probability μ {ω | R ω = 0}
    let U := m*probability μ {ω | R ω = 1}+b*probability μ {ω | R ω = 0}
    Integrable Y μ ∧ Integrable Ys μ ∧
    Integrable (fun ω => completeMissing (Ys ω) (R ω) a) μ ∧
    Integrable (fun ω => completeMissing (Ys ω) (R ω) b) μ ∧
    expectation μ (fun ω => completeMissing (Ys ω) (R ω) a) = L ∧
    expectation μ (fun ω => completeMissing (Ys ω) (R ω) b) = U ∧
    L ≤ expectation μ Y ∧ expectation μ Y ≤ U ∧
    ∀ c ∈ Icc L U, ∃ Y' : Ω → ℝ, Measurable Y' ∧
      (∀ᵐ ω ∂μ, Y' ω ∈ Icc a b) ∧ Integrable Y' μ ∧ expectation μ Y' = c ∧
      (fun ω => recordedOutcome (Y' ω) (R ω)) =ᵐ[μ] Ys ∧
      μ.map (fun ω => (recordedOutcome (Y' ω) (R ω), R ω)) =
        μ.map (fun ω => (Ys ω, R ω))

/-- Both completion vectors and their means, including the incorrect instruction's value. -/
def W1BoundsExample : Prop :=
  (fun i : Fin 6 => completeMissing (boundsRecorded i) (boundsResponse i) 0) = ![1,0,1,0,1,0] ∧
  (fun i : Fin 6 => completeMissing (boundsRecorded i) (boundsResponse i) 1) = ![1,1,1,0,1,1] ∧
  BoundsExample ∧
  ((∑ i : Fin 6, completeMissing (boundsRecorded i) (boundsResponse i) 0)/6 = 1/2 ∧
   (∑ i : Fin 6, completeMissing (boundsRecorded i) (boundsResponse i) 0)/6 ≠ 5/6)

/-- P001-T80; Example 6.1.2, pp. 209–210 (PDF pp. 227–228);
Theorem 6.1.3, pp. 210–211 (PDF pp. 228–229); sharpness prose, pp. 209 and 212.
An almost-surely [a,b]-valued outcome with binary response has mean between
respondent mean times response probability plus a or b times missingness
probability. The endpoints are the expectations of the lowest and highest
completions. Every value between them is attained with the same observable
joint law. Both response values have positive probability. The six printed
observations give completion vectors (1,0,1,0,1,0) and (1,1,1,0,1,1), with means
1/2 and 5/6; repeating the lowest-value instruction gives 1/2, unequal to 5/6. -/
def T80WholeStatement : Prop := W1MissingBounds.{u} ∧ W1BoundsExample

/-- P001-T83; Theorem 6.2.6, p. 226 (PDF p. 244), proof pp. 226–227.
For an integrable outcome and almost-surely binary response with both values
of positive probability, MAR given the covariates means conditional
independence and an almost-sure uniform positive lower bound on the true
response propensity. Then the recorded-outcome inverse-propensity weighted
variable is integrable, and its expectation equals both the population mean
and the expectation of the weighted uncensored outcome. Propensities are
measurable conditional-mean versions; all version bounds are almost sure. -/
def T83WholeStatement : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y R : Ω → ℝ), Measurable Y → Measurable R → Integrable Y μ →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < probability μ {ω | R ω = 0} → 0 < probability μ {ω | R ω = 1} →
    ∀ p : E → ℝ, IsConditionalMean μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) → CondIndependent μ X hX Y R →
    Integrable (fun ω => recordedOutcome (Y ω) (R ω)*R ω/p (X ω)) μ ∧
    expectation μ Y = expectation μ (fun ω => recordedOutcome (Y ω) (R ω)*R ω/p (X ω)) ∧
    expectation μ (fun ω => recordedOutcome (Y ω) (R ω)*R ω/p (X ω)) =
      expectation μ (fun ω => Y ω*R ω/p (X ω))

end
end SAP.P001e
