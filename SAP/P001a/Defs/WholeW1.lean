import Mathlib
import SAP.P001a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix Matrix.Norms.Elementwise

noncomputable section

universe u v

namespace SAP.P001a

/-- A PDF version of the uniform law with a hole at its mean. -/
def wholeHolePDF (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (-1 : ℝ) 1 ∧ x ≠ 0 then 1 / 2 else 0

/-- P001-T4; pp. 167–168 (PDF pp. 185–186), Definition 4.3.7.
Continuous local CEF representatives agree on an open set whenever they agree
Lebesgue almost everywhere there. Equality requires no derivative. Every existing
coordinate derivative at the covariate mean transfers, with the same value.
The positive-PDF neighborhood condition implies this version independence but
is not necessary, as the uniform PDF with a hole at its mean demonstrates. -/
def T4WholeStatement : Prop :=
  (∀ {K : ℕ} (U : Set (Fin K → ℝ)) (hU : IsOpen U)
    (m m' : U → ℝ) (hm : Continuous m) (hm' : Continuous m')
    (heq : ∀ᵐ x ∂(volume.restrict U), ∀ hx : x ∈ U, m ⟨x, hx⟩ = m' ⟨x, hx⟩),
    m = m' ∧ ∀ (x : U) (k : Fin K) (a : ℝ)
      (M M' : (Fin K → ℝ) → ℝ)
      (hM : ∀ y : U, M y = m y) (hM' : ∀ y : U, M' y = m' y),
      HasDerivAt (fun t => M (Function.update x.val k (x.val k + t))) a 0 →
      HasDerivAt (fun t => M' (Function.update x.val k (x.val k + t))) a 0 ∧
      partialAt M x.val k = partialAt M' x.val k) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K : ℕ} (X : Ω → Fin K → ℝ) (Y : Ω → ℝ) (hX : Measurable X)
    (hXi : ∀ k, Integrable (fun ω => X ω k) μ)
    (f : (Fin K → ℝ) → ℝ) (hf : HasVectorPDF (μ.map X) f)
    (U : Set (Fin K → ℝ)) (hU : IsOpen U)
    (hmean : (fun k => mean μ (fun ω => X ω k)) ∈ U)
    (hpositive : ∀ x ∈ U, 0 < f x)
    (m m' : (Fin K → ℝ) → ℝ) (hm : IsCEF μ X Y m) (hm' : IsCEF μ X Y m')
    (hc : ContinuousOn m U) (hc' : ContinuousOn m' U),
    Set.EqOn m m' U ∧ ∀ (k : Fin K) (a : ℝ),
      HasDerivAt (fun t => m (Function.update
        (fun j => mean μ (fun ω => X ω j)) k (mean μ (fun ω => X ω k) + t))) a 0 →
      HasDerivAt (fun t => m' (Function.update
        (fun j => mean μ (fun ω => X ω j)) k (mean μ (fun ω => X ω k) + t))) a 0 ∧
      partialAt m (fun j => mean μ (fun ω => X ω j)) k =
        partialAt m' (fun j => mean μ (fun ω => X ω j)) k) ∧
  (HasPDF (uniformLaw (-1) 1) wholeHolePDF ∧
    Integrable id (uniformLaw (-1) 1) ∧ mean (uniformLaw (-1) 1) id = 0 ∧
    wholeHolePDF 0 = 0 ∧
    ∀ m : ℝ → ℝ, ContinuousOn m (Set.Ioo (-1 : ℝ) 1) →
      m =ᵐ[uniformLaw (-1) 1] (fun _ => 0) →
      Set.EqOn m (fun _ => 0) (Set.Ioo (-1 : ℝ) 1) ∧ HasDerivAt m 0 0)

/-- A coefficient-measurable interpolating fit to one observation. -/
def wholeEndpointFit (xy : ℝ × ℝ) : Polynomial ℝ :=
  if xy.1 = 1 then Polynomial.C xy.2 else
    Polynomial.C (xy.2 / (xy.1 - 1)) * (Polynomial.X - Polynomial.C 1)

/-- P001-T5; pp. 168–169 (PDF pp. 186–187), Definition 4.3.9.
The printed claim is false: its unqualified supplementary endpoint bound fails
at t = n = J = 1. Under the independent uniform/Gaussian observation law the
displayed measurable degree-one least-squares selection interpolates every
observation and has endpoint tail probability zero, below the asserted quarter.
This refutes the endpoint supplement, not the separate local L2 lower limit. -/
def T5WholeStatement : Prop :=
  let ν := (uniformLaw 0 1).prod (gaussianReal 0 1)
  IsProbabilityMeasure ν ∧
  (∀ k : ℕ, Measurable (fun xy : ℝ × ℝ => (wholeEndpointFit xy).coeff k)) ∧
  (∀ xy : ℝ × ℝ, (wholeEndpointFit xy).natDegree ≤ 1 ∧
    (wholeEndpointFit xy).eval xy.1 = xy.2 ∧
    ∀ q : Polynomial ℝ, q.natDegree ≤ 1 →
      (xy.2 - (wholeEndpointFit xy).eval xy.1)^2 ≤ (xy.2 - q.eval xy.1)^2) ∧
  prob ν {xy | (1 / 4 : ℝ) < |(wholeEndpointFit xy).eval 1|} = 0 ∧
  ¬ (1 / 4 : ℝ) ≤ prob ν {xy | (1 / 4 : ℝ) < |(wholeEndpointFit xy).eval 1|}

/-- The local CEF is represented only on the almost-sure covariate domain. -/
def WholeLocalCEF {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) (m : ℝ → ℝ) : Prop :=
  Integrable Y μ ∧
  μ[Y | MeasurableSpace.comap X inferInstance] =ᵐ[μ] (fun ω => m (X ω))

/-- The correction's sampling, support, continuity and conditional variance assumptions.
Integrability of the squared residual makes its finite conditional expectation meaningful. -/
structure WholeSieveData {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : ℕ → Ω → ℝ) (a b V : ℝ) (m : ℝ → ℝ) : Prop where
  iid : IID μ (fun i ω => (X i ω, Y i ω))
  interval : a < b
  support : ∀ᵐ ω ∂μ, X 0 ω ∈ Set.Icc a b
  continuous : ContinuousOn m (Set.Icc a b)
  cef : WholeLocalCEF μ (X 0) (Y 0) m
  noise_integrable : Integrable (fun ω => (Y 0 ω - m (X 0 ω))^2) μ
  variance_bound : ∀ A : Set ℝ, MeasurableSet A →
    (∫ ω in (X 0) ⁻¹' A, (Y 0 ω - m (X 0 ω))^2 ∂μ) ≤
      V * prob μ ((X 0) ⁻¹' A)

/-- The finite supremum is over the compact covariate support, not all of ℝ. -/
def wholeSieveEnvelope (a b : ℝ) {K : ℕ} (p : Fin K → Polynomial ℝ) : ℝ :=
  sSup ((fun x => ∑ k, ((p k).eval x)^2) '' Set.Icc a b)

/-- Rayleigh-form definition of the smallest-eigenvalue lower bound. -/
def WholeGramGood {Ω : Type*} (X : ℕ → Ω → ℝ) (p : ℕ → Polynomial ℝ)
    (J : ℕ → ℕ) (c : ℝ) (n : ℕ) (ω : Ω) : Prop :=
  ∀ v : Fin (J n + 1) → ℝ, c * (∑ k, (v k)^2) ≤
    (∑ i ∈ Finset.range n, (∑ k : Fin (J n + 1), v k * (p k).eval (X i ω))^2) /
      (n : ℝ)

/-- P001-T6; pp. 168–169 (PDF pp. 186–187), Definition 4.3.9.
Polynomial least squares admits a measurable minimizing selection, including
singular designs. On compact support a continuous CEF and bounded conditional
variance give L2 consistency under growing degree, vanishing dimension/sample
ratio and a stable population-normalized Gram matrix. The attained support
supremum gives the general envelope rate. For uniform covariates on every
nondegenerate compact interval the envelope is at most K², the Euclidean
operator-norm deviation probability is at most 4(K³−K)/n, and the cubic rate
suffices for Gram stability. -/
def T6WholeStatement : Prop :=
  (∀ {Ω : Type u} [MeasurableSpace Ω] (X Y : ℕ → Ω → ℝ)
    (hm : ∀ i, Measurable (X i) ∧ Measurable (Y i)) (J : ℕ → ℕ),
    ∃ fit : ℕ → Ω → Polynomial ℝ, IsSieveLS X Y J fit ∧
      ∀ n k, Measurable (fun ω => (fit n ω).coeff k)) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ℕ → Ω → ℝ) (a b V : ℝ) (m : ℝ → ℝ)
    (h : WholeSieveData μ X Y a b V m)
    (p : ℕ → Polynomial ℝ) (hdeg : ∀ k, (p k).natDegree = k)
    (horth : ∀ j k, mean μ (fun ω => (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) =
      if j = k then 1 else 0)
    (J : ℕ → ℕ) (hJ : Tendsto J atTop atTop)
    (hrate : Tendsto (fun n => ((J n + 1 : ℕ) : ℝ) / n) atTop (nhds 0))
    (c : ℝ) (hc : 0 < c)
    (hgram : Tendsto (fun n => prob μ {ω | WholeGramGood X p J c n ω}) atTop (nhds 1))
    (fit : ℕ → Ω → Polynomial ℝ) (hfit : IsSieveLS X Y J fit),
    (∀ n ω, Integrable (fun x => ((fit n ω).eval x - m x)^2) (μ.map (X 0))) ∧
    CP μ (fun n ω => ∫ x, ((fit n ω).eval x - m x)^2 ∂(μ.map (X 0))) 0) ∧
  (∀ (a b : ℝ) (hab : a < b) {K : ℕ} (p : Fin K → Polynomial ℝ),
    ∃ x ∈ Set.Icc a b, wholeSieveEnvelope a b p = ∑ k, ((p k).eval x)^2 ∧
      ∀ y ∈ Set.Icc a b, (∑ k, ((p k).eval y)^2) ≤ wholeSieveEnvelope a b p) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (a b : ℝ) (hab : a < b)
    (hsupp : ∀ᵐ ω ∂μ, X 0 ω ∈ Set.Icc a b) (p : ℕ → Polynomial ℝ)
    (horth : ∀ j k, mean μ (fun ω => (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) =
      if j = k then 1 else 0)
    (J : ℕ → ℕ)
    (hrate : Tendsto (fun n => wholeSieveEnvelope a b (fun k : Fin (J n + 1) => p k) *
      ((J n + 1 : ℕ) : ℝ) / n) atTop (nhds 0)),
    Tendsto (fun n => prob μ {ω | WholeGramGood X p J (1 / 2) n ω}) atTop (nhds 1)) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (a b : ℝ) (hab : a < b)
    (hlaw : μ.map (X 0) = uniformLaw a b) (K n : ℕ) (hK : 0 < K) (hn : 0 < n)
    (p : Fin K → Polynomial ℝ) (hdeg : ∀ k, (p k).natDegree = k.val)
    (horth : ∀ j k, mean μ (fun ω => (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) =
      if j = k then 1 else 0),
    wholeSieveEnvelope a b p ≤ (K : ℝ)^2 ∧
    prob μ {ω | (1 / 2 : ℝ) < ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin K)) (sampleGram p X n ω - 1)‖} ≤
      4 * ((K : ℝ)^3 - K) / n) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hiid : IID μ X) (a b : ℝ) (hab : a < b)
    (hlaw : μ.map (X 0) = uniformLaw a b) (p : ℕ → Polynomial ℝ)
    (hdeg : ∀ k, (p k).natDegree = k)
    (horth : ∀ j k, mean μ (fun ω => (p j).eval (X 0 ω) * (p k).eval (X 0 ω)) =
      if j = k then 1 else 0)
    (J : ℕ → ℕ)
    (hrate : Tendsto (fun n => (((J n + 1 : ℕ) : ℝ)^3) / n) atTop (nhds 0)),
    Tendsto (fun n => prob μ {ω | WholeGramGood X p J (1 / 2) n ω}) atTop (nhds 1))

/-- A genuine conditional probability law with a chosen real density.
The kernel supplies the measurability presupposed by a conditional model even
when its reference measure is not s-finite. -/
structure WholeDensity (A : Type*) [MeasurableSpace A] (κ : Measure ℝ) where
  kernel : Kernel A ℝ
  markov : IsMarkovKernel kernel
  density : A → ℝ → ℝ
  measurable : Measurable (fun xy : A × ℝ => density xy.1 xy.2)
  nonnegative : ∀ x y, 0 ≤ density x y
  law : ∀ x, kernel x = κ.withDensity (fun y => ENNReal.ofReal (density x y))

attribute [instance] WholeDensity.markov

def wholeAverageKL {A : Type*} [MeasurableSpace A] (ν : Measure A) {κ : Measure ℝ}
    (F G : WholeDensity A κ) : ℝ≥0∞ :=
  ∫⁻ x, InformationTheory.klDiv (F.kernel x) (G.kernel x) ∂ν

def wholeSectionEntropy {A : Type*} [MeasurableSpace A] {κ : Measure ℝ}
    (F : WholeDensity A κ) (x : A) : ℝ :=
  ∫ y, F.density x y * Real.log (F.density x y) ∂κ

/-- Finite ordinary expected log density includes positivity under the true law. -/
def WholeFiniteLog {A : Type*} [MeasurableSpace A] (ν : Measure A) {κ : Measure ℝ}
    (F G : WholeDensity A κ) : Prop :=
  (∀ᵐ xy ∂(ν ⊗ₘ F.kernel), 0 < G.density xy.1 xy.2) ∧
  Integrable (fun xy : A × ℝ => Real.log (G.density xy.1 xy.2)) (ν ⊗ₘ F.kernel)

/-- A sample log criterion is minus infinity if any density factor vanishes. -/
def wholeSampleLog {Ω A T : Type*} [MeasurableSpace A] {κ : Measure ℝ}
    (X : ℕ → Ω → A) (Y : ℕ → Ω → ℝ) (G : T → WholeDensity A κ)
    (n : ℕ) (ω : Ω) (t : T) : EReal :=
  if ∀ i ∈ Finset.range n, 0 < (G t).density (X i ω) (Y i ω) then
    ((∑ i ∈ Finset.range n, Real.log ((G t).density (X i ω) (Y i ω))) / (n : ℝ) : ℝ)
  else ⊥

/-- Extended uniform discrepancy: no finiteness is imposed at n=0 or on bad events. -/
def wholeLogDiscrepancy {Ω A T : Type*} [MeasurableSpace A] {κ : Measure ℝ}
    (X : ℕ → Ω → A) (Y : ℕ → Ω → ℝ) (G : T → WholeDensity A κ)
    (M : T → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t : T, if ∀ i ∈ Finset.range n, 0 < (G t).density (X i ω) (Y i ω) then
    ENNReal.ofReal |(∑ i ∈ Finset.range n,
      Real.log ((G t).density (X i ω) (Y i ω))) / (n : ℝ) - M t| else ∞

/-- P001-T8; pp. 195–196 (PDF pp. 213–214), Theorem 5.2.8.
Averaged conditional KL equals finite iterated conditional entropy minus finite
expected log density. Its minimizers are precisely the expected-log maximizers.
Uniform convergence in probability of the positive-sample log criterion and
vanishing approximate maximization error give consistency at every separated
maximum; exact product maximizers are included. Compactness and a continuous
unique maximum imply separation. Consistency does not require finite entropy
or finite KL. A true model has zero KL, and uniqueness identifies its parameter.
All conditional laws are probability kernels; the reference measure is arbitrary. -/
def T8WholeStatement : Prop :=
  (∀ {A : Type u} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (κ : Measure ℝ) (F G : WholeDensity A κ)
    (hentropy : (∀ᵐ x ∂ν, Integrable (fun y => F.density x y *
      Real.log (F.density x y)) κ) ∧ Integrable (wholeSectionEntropy F) ν)
    (hlog : WholeFiniteLog ν F G),
    wholeAverageKL ν F G ≠ ∞ ∧
      (wholeAverageKL ν F G).toReal = (∫ x, wholeSectionEntropy F x ∂ν) -
        ∫ xy, Real.log (G.density xy.1 xy.2) ∂(ν ⊗ₘ F.kernel)) ∧
  (∀ {A : Type u} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (κ : Measure ℝ) (F : WholeDensity A κ) {τ : ℕ} (Θ : Set (Fin τ → ℝ))
    (G : Θ → WholeDensity A κ)
    (hentropy : (∀ᵐ x ∂ν, Integrable (fun y => F.density x y *
      Real.log (F.density x y)) κ) ∧ Integrable (wholeSectionEntropy F) ν)
    (hlog : ∀ t, WholeFiniteLog ν F (G t)),
    ∀ s : Θ,
      (∀ t, wholeAverageKL ν F (G s) ≤ wholeAverageKL ν F (G t)) ↔
      (∀ t, (∫ xy, Real.log ((G t).density xy.1 xy.2) ∂(ν ⊗ₘ F.kernel)) ≤
        ∫ xy, Real.log ((G s).density xy.1 xy.2) ∂(ν ⊗ₘ F.kernel))) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
    (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν] (κ : Measure ℝ)
    (F : WholeDensity (Fin K → ℝ) κ) (Θ : Set (Fin τ → ℝ))
    (G : Θ → WholeDensity (Fin K → ℝ) κ)
    (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) = ν ⊗ₘ F.kernel)
    (hlog : ∀ t, WholeFiniteLog ν F (G t))
    (tstar : Θ) (that : ℕ → Ω → Θ) (hm : ∀ n, Measurable (that n))
    (e : ℕ → Ω → ℝ) (hen : ∀ n, 0 < n → ∀ᵐ ω ∂μ, 0 ≤ e n ω)
    (he : CP μ e 0),
    let M := fun t : Θ => ∫ xy, Real.log ((G t).density xy.1 xy.2) ∂(ν ⊗ₘ F.kernel)
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : Θ,
      ε ≤ dist t tstar → M t ≤ M tstar - δ) →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => prob μ
      {ω | ENNReal.ofReal ε ≤ wholeLogDiscrepancy X Y G M n ω}) atTop (nhds 0)) →
    ((∀ n, 0 < n → ∀ᵐ ω ∂μ, ∀ t : Θ,
      (∏ i ∈ Finset.range n, (G t).density (X i ω) (Y i ω)) ≤
      ∏ i ∈ Finset.range n, (G (that n ω)).density (X i ω) (Y i ω)) ∨
    (∀ n, 0 < n → ∀ᵐ ω ∂μ, ∀ t : Θ,
      wholeSampleLog X Y G n ω t ≤ wholeSampleLog X Y G n ω (that n ω) +
        (e n ω : EReal))) → CP μ that tstar) ∧
  (∀ {E : Type u} [MetricSpace E] (Θ : Set E) (hc : IsCompact Θ)
    (θ : E) (hθ : θ ∈ Θ) (M : E → ℝ) (hM : ContinuousOn M Θ)
    (hu : ∀ t ∈ Θ, M t ≤ M θ ∧ (M t = M θ → t = θ)),
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Θ,
      ε ≤ dist t θ → M t ≤ M θ - δ) ∧
  (∀ {A : Type u} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    (κ : Measure ℝ) {τ : ℕ} (Θ : Set (Fin τ → ℝ))
    (G : Θ → WholeDensity A κ) (θ tstar : Θ)
    (hu : ∀ t, wholeAverageKL ν (G θ) (G tstar) ≤ wholeAverageKL ν (G θ) (G t) ∧
      (wholeAverageKL ν (G θ) (G t) = wholeAverageKL ν (G θ) (G tstar) → t = tstar)),
    wholeAverageKL ν (G θ) (G θ) = 0 ∧ tstar = θ ∧
      ∀ t, wholeAverageKL ν (G θ) (G t) = 0 ↔ t = θ)

/-- Included regressors, with the intercept in the first coordinate. -/
def wholeDesign {K L : ℕ} (x : Fin K → ℝ) (w : Fin L → ℝ) : Fin (K + L + 1) → ℝ :=
  Fin.cases 1 (Fin.addCases x w)

def wholeNullCoef {K L : ℕ} (γ : Fin (K + 1) → ℝ) : Fin (K + L + 1) → ℝ :=
  Fin.cases (γ 0) (Fin.addCases (fun k => γ k.succ) (fun _ : Fin L => 0))

def wholePlaceboSelector (K L : ℕ) : Matrix (Fin L) (Fin (K + L + 1)) ℝ :=
  fun l j => if j = (Fin.natAdd K l).succ then 1 else 0

def wholeRisk {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (Z : Ω → Fin p → ℝ) (D : Ω → ℝ) (b : Fin p → ℝ) : ℝ :=
  ∫ ω, (D ω - Z ω ⬝ᵥ b)^2 ∂μ

def wholeQ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (Z : Ω → Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => ∫ ω, Z ω j * Z ω k ∂μ

def wholeResidual {Ω : Type*} {p : ℕ} (Z : Ω → Fin p → ℝ)
    (D : Ω → ℝ) (b : Fin p → ℝ) (ω : Ω) : ℝ := D ω - Z ω ⬝ᵥ b

def wholeOmega {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (Z : Ω → Fin p → ℝ) (D : Ω → ℝ) (b : Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => ∫ ω, (wholeResidual Z D b ω)^2 * Z ω j * Z ω k ∂μ

def wholeSandwich {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (Z : Ω → Fin p → ℝ) (D : Ω → ℝ) (b : Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (wholeQ μ Z)⁻¹ * wholeOmega μ Z D b * ((wholeQ μ Z)⁻¹).transpose

def wholeRows {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ) (n : ℕ) (ω : Ω) :
    Matrix (Fin n) (Fin p) ℝ := fun i => Z i ω

def wholeBetaHat {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Fin p → ℝ :=
  olsCoef (wholeRows Z n ω) (fun i => D i ω)

def wholeEmpiricalQ {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (n : ℕ) (ω : Ω) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => (∑ i ∈ Finset.range n, Z i ω j * Z i ω k) / (n : ℝ)

def wholeMeat {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (u : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => (∑ i ∈ Finset.range n, (u i ω)^2 * Z i ω j * Z i ω k) / (n : ℝ)

def wholeFittedMeat {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Matrix (Fin p) (Fin p) ℝ :=
  wholeMeat Z (fun i ω => D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω) n ω

/-- HC0 in the original unnormalized matrix formula, with actual fitted residuals.
This is the same formula as `robustCov`, also allowing zero columns. -/
def wholeHC0 {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Matrix (Fin p) (Fin p) ℝ :=
  let A := wholeRows Z n ω
  let r := fun i : Fin n => D i ω - Z i ω ⬝ᵥ wholeBetaHat Z D n ω
  (A.transpose * A)⁻¹ * (A.transpose * Matrix.diagonal (fun i => (r i)^2) * A) *
    (A.transpose * A)⁻¹

def wholeRootError {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (n : ℕ) (ω : Ω) : Fin p → ℝ :=
  Real.sqrt n • (wholeBetaHat Z D n ω - b)

def wholeScoreSum {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) (n : ℕ) (ω : Ω) : Fin p → ℝ :=
  (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n,
    wholeResidual (Z i) (D i) b ω • Z i ω

def WholeTight {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (T : ℕ → Ω → E) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in atTop, prob μ {ω | C < ‖T n ω‖} ≤ η

/-- The maximum row norm squared divided by n, with a harmless empty-sample value. -/
def wholeMaxRow {Ω : Type*} {p : ℕ} (Z : ℕ → Ω → Fin p → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  if hn : 0 < n then
    ((Finset.range n).sup' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn)) (fun i => ‖Z i ω‖^2)) / n
  else 0

/-- Chi-square as the sum of independent squared standard normals. -/
def wholeChiSquare (L : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin L => gaussianReal 0 1)).map (fun z => ∑ l, (z l)^2)

def wholeWald {p L : ℕ} (R : Matrix (Fin L) (Fin p) ℝ)
    (b : Fin p → ℝ) (C : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (R.mulVec b) ⬝ᵥ (R * C * R.transpose)⁻¹.mulVec (R.mulVec b)

def wholeJointRegion {p L : ℕ} (R : Matrix (Fin L) (Fin p) ℝ)
    (b : Fin p → ℝ) (C : Matrix (Fin p) (Fin p) ℝ) (q : ℝ) : Set (Fin L → ℝ) :=
  {t | (R.mulVec b - t) ⬝ᵥ (R * C * R.transpose)⁻¹.mulVec (R.mulVec b - t) ≤ q}

/-- The population design assumptions do not include conditional independence or linearity. -/
structure WholePlaceboDesign {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ) : Prop where
  measurableX : Measurable X
  measurableW : Measurable W
  measurableD : Measurable D
  binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1
  supportD : 0 < prob μ {ω | D ω = 1} ∧ prob μ {ω | D ω = 1} < 1
  secondX : ∀ k, MemLp (fun ω => X ω k) 2 μ
  secondW : ∀ k, MemLp (fun ω => W ω k) 2 μ
  rank : IsUnit (wholeQ μ (fun ω => wholeDesign (X ω) (W ω))).det

structure WholePlaceboNull {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
    (γ : Fin (K + 1) → ℝ) : Prop extends WholePlaceboDesign μ X W D where
  ci : CI μ X measurableX W D
  cef : IsCEF μ X D (linearPredictor γ)

/-- The population CEF and the uniquely optimal coefficient vector. -/
def WholePlaceboPopulation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
    (γ : Fin (K + 1) → ℝ) : Prop :=
  IsCEF μ (fun ω => (X ω, W ω)) D (fun xw => linearPredictor γ xw.1) ∧
  ∀ b : Fin (K + L + 1) → ℝ,
    wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D (wholeNullCoef γ) ≤
      wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D b ∧
    (wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D b =
      wholeRisk μ (fun ω => wholeDesign (X ω) (W ω)) D (wholeNullCoef γ) ↔
      b = wholeNullCoef γ)

/-- Finite, non-default score and covariance quantities used by the OLS proof. -/
structure WholeScoreMoments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (Z : Ω → Fin p → ℝ) (D : Ω → ℝ) (b : Fin p → ℝ) : Prop where
  measurableZ : Measurable Z
  measurableD : Measurable D
  secondZ : ∀ j, MemLp (fun ω => Z ω j) 2 μ
  boundedResidual : ∀ᵐ ω ∂μ, |wholeResidual Z D b ω| ≤ 1
  orthogonal : ∀ j, mean μ (fun ω => Z ω j * wholeResidual Z D b ω) = 0
  secondScore : ∀ j, MemLp (fun ω => Z ω j * wholeResidual Z D b ω) 2 μ
  rank : IsUnit (wholeQ μ Z).det
  positiveQ : (wholeQ μ Z).PosSemidef
  positiveOmega : (wholeOmega μ Z D b).PosSemidef
  positiveSandwich : (wholeSandwich μ Z D b).PosSemidef

structure WholeGramLimits {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) : Prop where
  measurableBeta : ∀ n, Measurable (wholeBetaHat Z D n)
  measurableHC0 : ∀ n, Measurable (wholeHC0 Z D n)
  gram : CP μ (wholeEmpiricalQ Z) (wholeQ μ (Z 0))
  inverse : CP μ (fun n ω => (wholeEmpiricalQ Z n ω)⁻¹) (wholeQ μ (Z 0))⁻¹
  beta : CP μ (wholeBetaHat Z D) b
  trueMeat : CP μ (wholeMeat Z (fun i => wholeResidual (Z i) (D i) b))
    (wholeOmega μ (Z 0) (D 0) b)
  eventualRank : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, IsUnit (wholeEmpiricalQ Z n ω).det

/-- OLS limit law, correctly scaled HC0 consistency, and feasible joint inference. -/
def WholeOLSInference {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (Z : ℕ → Ω → Fin p → ℝ) (D : ℕ → Ω → ℝ) (b : Fin p → ℝ) : Prop :=
  CP μ (wholeBetaHat Z D) b ∧
  WeakLimit μ (wholeRootError Z D b) (normalVectorLaw (wholeSandwich μ (Z 0) (D 0) b)) ∧
  CP μ (fun n ω => (n : ℝ) • wholeHC0 Z D n ω) (wholeSandwich μ (Z 0) (D 0) b) ∧
  ∀ (L : ℕ) (hL : 0 < L) (R : Matrix (Fin L) (Fin p) ℝ)
    (hnull : R.mulVec b = 0)
    (hrank : IsUnit (R * wholeSandwich μ (Z 0) (D 0) b * R.transpose).det)
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1),
    ∃ q : ℝ, prob (wholeChiSquare L) (Set.Iic q) = 1 - α ∧
      CD μ (fun n ω => wholeWald R (wholeBetaHat Z D n ω) (wholeHC0 Z D n ω))
        (wholeChiSquare L) ∧
      Tendsto (fun n => prob μ {ω |
        q < wholeWald R (wholeBetaHat Z D n ω) (wholeHC0 Z D n ω)}) atTop (nhds α) ∧
      Tendsto (fun n => prob μ {ω |
        (0 : Fin L → ℝ) ∈ wholeJointRegion R (wholeBetaHat Z D n ω)
          (wholeHC0 Z D n ω) q}) atTop (nhds (1 - α))

/-- The added-linear-content interpretation, without a CEF specification. -/
def WholeLinearContent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ) : Prop :=
  let Z := fun ω => wholeDesign (X ω) (W ω)
  let b := (wholeQ μ Z)⁻¹.mulVec (fun j => ∫ ω, Z ω j * D ω ∂μ)
  (∀ a, wholeRisk μ Z D a = wholeRisk μ Z D b +
    (a - b) ⬝ᵥ (wholeQ μ Z).mulVec (a - b)) ∧
  ((∃ γ : Fin (K + 1) → ℝ, wholeRisk μ Z D (wholeNullCoef γ) = wholeRisk μ Z D b) ↔
    (wholePlaceboSelector K L).mulVec b = 0)

/-- P001-T18; p. 270 (PDF p. 288), Section 7.2.8.
Conditional independence and a linear treatment CEF preserve that CEF after
adding placebo covariates and make their uniquely optimal population
coefficients zero. Under iid sampling and the stated second moments and Gram
rank, actual OLS has its sandwich Gaussian limit and n times residual HC0
converges to that covariance. Every nonempty tested block with nonsingular
limiting covariance has a calibrated chi-square Wald test and its inverted
joint coefficient region. Without the CEF specification, zero placebo
coefficients mean no added linear predictive content; the explicit independent
placebo example instead has slope 4/17. -/
def T18WholeStatement : Prop :=
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
    (γ : Fin (K + 1) → ℝ) (h : WholePlaceboNull μ X W D γ),
    WholePlaceboPopulation μ X W D γ) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
    (h : WholePlaceboDesign μ X W D), WholeLinearContent μ X W D) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K L : ℕ} (X : ℕ → Ω → Fin K → ℝ) (W : ℕ → Ω → Fin L → ℝ)
    (D : ℕ → Ω → ℝ) (hiid : IID μ (fun i ω => (X i ω, W i ω, D i ω)))
    (γ : Fin (K + 1) → ℝ) (h : WholePlaceboNull μ (X 0) (W 0) (D 0) γ),
    WholeOLSInference μ (fun i ω => wholeDesign (X i ω) (W i ω)) D (wholeNullCoef γ)) ∧
  (FCondIndep placeboLaw placeboW placeboD placeboX ∧ (4 / 17 : ℝ) ≠ 0 ∧
    ∀ a b c : ℝ, placeboRisk (29 / 68) 0 (4 / 17) ≤ placeboRisk a b c ∧
      (placeboRisk a b c = placeboRisk (29 / 68) 0 (4 / 17) ↔
        a = 29 / 68 ∧ b = 0 ∧ c = 4 / 17))

end SAP.P001a
