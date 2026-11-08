import AronowAudit.P001.P001_Foundations

/-!
Statement-only literature contracts and conditional proposals for cond-P001g14.
No held theorem constant is used in a proposition. The source module is imported
for its existing data/model definitions only. These contracts are hypotheses,
not claims that the cited results have been proved in Lean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false

namespace AronowAudit.Literature

universe u v

/-- Bounded-continuous-test weak convergence on changing sample spaces. -/
def RowWeak {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {E : Type v} [TopologicalSpace E]
    (P : (n : ℕ) → Measure (Ω n)) (Z : (n : ℕ) → Ω n → E)
    [MeasurableSpace E] (G : Measure E) : Prop :=
  ∀ f : E → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Tendsto (fun (n : ℕ) => ∫ ω, f (Z n ω) ∂(P n)) atTop (nhds (∫ x, f x ∂G))

/-- Contiguity, with its measurable-event quantifier retained. -/
def Contiguous {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    (P Q : (n : ℕ) → Measure (Ω n)) : Prop :=
  ∀ A : (n : ℕ) → Set (Ω n), (∀ n, MeasurableSet (A n)) →
    Tendsto (fun n => (P n (A n)).toReal) atTop (nhds 0) →
    Tendsto (fun n => (Q n (A n)).toReal) atTop (nhds 0)

/-- A Gaussian vector in ordinary finite-coordinate notation. -/
def GaussianVector {d : ℕ} (a : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    Measure (Fin d → ℝ) :=
  (multivariateGaussian (WithLp.toLp 2 a) S).map (fun z => fun i => z i)

/-- Product law of a finite iid sample; independent of any statistical target. -/
def ProductLaw {E : Type u} [MeasurableSpace E] (P : Measure E) (n : ℕ) :
    Measure (Fin n → E) := Measure.pi (fun _ : Fin n => P)

/-- The ordinary finite-dimensional QMD condition. A nonnegative extended
integral prevents a nonintegrable residual from being assigned the real value 0.
The Euclidean squared length is written as the sum of coordinate squares. -/
def QMD {E : Type u} [MeasurableSpace E] {d : ℕ}
    (ρ : Measure E) (p : (Fin d → ℝ) → E → ℝ) (Θ : Set (Fin d → ℝ))
    (θ : Fin d → ℝ) (s : E → Fin d → ℝ) : Prop :=
  Measurable s ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t ∈ Θ, dist t θ < δ →
      (∫⁻ x, ENNReal.ofReal ((Real.sqrt (p t x) - Real.sqrt (p θ x) -
        (∑ j, (t j - θ j) * s x j) * Real.sqrt (p θ x) / 2)^2) ∂ρ) ≤
        ENNReal.ofReal (ε * ∑ j, (t j - θ j)^2)

/-- van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998,
Theorem 7.2, p. 94 (proof pp. 94–95), with QMD as equation (7.1), pp. 93–94.
The observation space and dominating measure are arbitrary. The complete local
parameter sequence h_n → h is retained. The vanishing zero-likelihood event
records the source's extended-log convention before using real logarithms.
No nonsingularity or pointwise differentiability assumption is imposed. -/
def QMDLAN : Prop :=
  ∀ (E : Type u) (mE : MeasurableSpace E) (d : ℕ)
    (ρ : @Measure E mE) (Θ : Set (Fin d → ℝ)) (θ : Fin d → ℝ)
    (p : (Fin d → ℝ) → E → ℝ) (s : E → Fin d → ℝ),
    letI : MeasurableSpace E := mE
    IsOpen Θ → θ ∈ Θ →
    (∀ t ∈ Θ, Measurable (p t)) →
    (∀ t ∈ Θ, ∀ x, 0 ≤ p t x) →
    (∀ t ∈ Θ, (∫⁻ x, ENNReal.ofReal (p t x) ∂ρ) = 1) →
    QMD ρ p Θ θ s →
    let P := ρ.withDensity (fun x => ENNReal.ofReal (p θ x))
    (∀ j, MemLp (fun x => s x j) 2 P) ∧
    (∀ j, (∫ x, s x j ∂P) = 0) ∧
    ∀ (hseq : ℕ → Fin d → ℝ) (h : Fin d → ℝ),
      Tendsto hseq atTop (nhds h) →
      let L := fun (n : ℕ) (z : Fin n → E) =>
        ∏ i, p (θ + (Real.sqrt n)⁻¹ • hseq n) (z i) / p θ (z i)
      Tendsto (fun n => ((ProductLaw P n) {z | L n z = 0}).toReal)
        atTop (nhds 0) ∧
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => ((ProductLaw P n) {z | ε ≤
          |Real.log (L n z) -
            ((Real.sqrt n)⁻¹ * ∑ i, ∑ j, h j * s (z i) j -
              (∫ x, (∑ j, h j * s x j)^2 ∂P) / 2)|}).toReal)
          atTop (nhds 0)

/-- van der Vaart, *Asymptotic Statistics*, 1998, Example 6.7 (Le Cam's
third lemma), pp. 90–91, including its footnote on log 0. Mutual contiguity
is the explicit intermediate conclusion in the published proof (p. 90),
obtained there from Lemma 6.4 / Example 6.5, pp. 88–89.
The full Gaussian block covariance may be singular. The first coordinate is
the log likelihood ratio; the remaining coordinates form the statistic.
RN derivatives denote the absolutely continuous part, as on pp. 85–87. -/
def GaussianThirdLemma : Prop :=
  ∀ (Ω : ℕ → Type u) (mΩ : (n : ℕ) → MeasurableSpace (Ω n)),
    letI : (n : ℕ) → MeasurableSpace (Ω n) := mΩ
    ∀ (P Q : (n : ℕ) → Measure (Ω n)) (k : ℕ)
      (Z : (n : ℕ) → Ω n → Fin k → ℝ)
      (a : Fin (k+1) → ℝ) (S : Matrix (Fin (k+1)) (Fin (k+1)) ℝ),
      (∀ n, IsProbabilityMeasure (P n)) →
      (∀ n, IsProbabilityMeasure (Q n)) →
      (∀ n, Measurable (Z n)) → S.PosSemidef → a 0 = -S 0 0 / 2 →
      Tendsto (fun n => (P n {ω | (Q n).rnDeriv (P n) ω = 0}).toReal)
        atTop (nhds 0) →
      RowWeak P (fun n ω => Fin.cons
        (Real.log (((Q n).rnDeriv (P n) ω).toReal)) (Z n ω)) (GaussianVector a S) →
      Contiguous P Q ∧ Contiguous Q P ∧
      RowWeak Q Z (GaussianVector (fun i => a i.succ + S i.succ 0)
        (fun i j => S i.succ j.succ))

/-- Arithmetic mean of a nonempty finite sample (totalized at size zero). -/
def FiniteMean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / (n : ℝ)

/-- Sample standard deviation using the divisor m, as in Bickel–Freedman
(1981), pp. 1196–1197. -/
def FiniteSD {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  Real.sqrt ((∑ i, (x i - FiniteMean x)^2) / (m : ℝ))

/-- Expectation under the exact uniform with-replacement resampling law.
There are n^m maps from a bootstrap sample of size m to the original n labels. -/
def ResamplingMean {n m : ℕ} (x : Fin n → ℝ) (g : (Fin m → ℝ) → ℝ) : ℝ :=
  (∑ a : Fin m → Fin n, g (fun i => x (a i))) / (n : ℝ)^m

/-- Bickel and Freedman, "Some Asymptotic Theory for the Bootstrap,"
*Annals of Statistics* 9(6), 1196–1217, 1981, Theorem 2.1(a,b), p. 1197.
Both sample sizes vary independently to infinity, and both the weak-limit
clause and resampled-standard-deviation clause are included. The statement
is over every real iid sequence with finite positive variance. -/
def IIDMeanBootstrap : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := mΩ
    ∀ (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (X : ℕ → Ω → ℝ),
      (∀ i, Measurable (X i)) → iIndepFun X μ →
      (∀ i, IdentDistrib (X i) (X 0) μ μ) → MemLp (X 0) 2 μ →
      0 < variance (X 0) μ →
      ∀ᵐ ω ∂μ,
        (∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
          Tendsto (fun nm : ℕ × ℕ => ResamplingMean (fun i : Fin nm.1 => X i ω)
            (fun y : Fin nm.2 → ℝ =>
              f (Real.sqrt nm.2 * (FiniteMean y -
                FiniteMean (fun i : Fin nm.1 => X i ω)))))
            atTop (nhds (∫ x, f x ∂(gaussianReal 0 (variance (X 0) μ).toNNReal)))) ∧
        (∀ ε : ℝ, 0 < ε →
          Tendsto (fun nm : ℕ × ℕ => ResamplingMean (fun i : Fin nm.1 => X i ω)
            (fun y : Fin nm.2 → ℝ =>
              if ε < |FiniteSD y - Real.sqrt (variance (X 0) μ)| then 1 else 0))
            atTop (nhds 0))

/-- Upper sample median, with zero-based rank floor(n/2). This is an
ordinary order statistic; it contains no heavy-tail law or target claim. -/
def UpperMedian {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ((List.ofFn x).mergeSort (fun a b => a ≤ b)).getD (n/2) 0

/-- Bickel and Freedman (1981), Proposition 5.1 and the explicit local-
derivative refinement immediately following it, p. 1208. This refinement
requires only a unique median and a positive derivative of F at that median;
no global density or tail moment is required. Both the marginal limit and
the almost-sure conditional weak limit are retained. A median is selected
by the upper order statistic (also the rank used in Ghosh et al. (1984),
p. 1131, alpha = floor(n/2)+1). -/
def MedianBootstrap : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := mΩ
    ∀ (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (X : ℕ → Ω → ℝ),
      (∀ i, Measurable (X i)) → iIndepFun X μ →
      (∀ i, IdentDistrib (X i) (X 0) μ μ) →
      ∀ (m a : ℝ), 0 < a →
        let F := fun x => (μ {ω | X 0 ω ≤ x}).toReal
        (F m = 1/2 ∧ (∀ x, x < m → F x < 1/2) ∧
          (∀ x, m < x → 1/2 < F x)) → HasDerivAt F a m →
        let G := gaussianReal 0 (1 / (4*a^2)).toNNReal
        (∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
          Tendsto (fun (n : ℕ) => ∫ ω,
            f (Real.sqrt n * (UpperMedian (fun i : Fin n => X i ω) - m)) ∂μ)
            atTop (nhds (∫ x, f x ∂G))) ∧
        (∀ᵐ ω ∂μ, ∀ f : ℝ → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
          Tendsto (fun n => ResamplingMean (fun i : Fin n => X i ω)
            (fun y : Fin n → ℝ => f (Real.sqrt n *
              (UpperMedian y - UpperMedian (fun i : Fin n => X i ω)))))
            atTop (nhds (∫ x, f x ∂G)))

/-- The empirical CDF of a finite sample. -/
def FiniteCDF {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, if x i ≤ t then (1 : ℝ) else 0) / (n : ℝ)

/-- Kolmogorov deviation; for n>0 the range is nonempty and bounded by 1. -/
def CDFDeviation {n : ℕ} (P : Measure ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (Set.range (fun t : ℝ => |FiniteCDF x t - (P (Set.Iic t)).toReal|))

/-- Devroye and Lugosi, *Combinatorial Methods in Density Estimation*,
Springer, 2001, Theorem 3.3 (Dvoretzky–Kiefer–Wolfowitz theorem), p. 22.
Its complete distribution-free expected-supremum bound is used, rather than
a sharp tail specialization. The universal constant is quantified outside
every sample space, law and positive sample size. Integrability is made
explicit; the deviation is measurable and bounded by 1. -/
def DKWExpectedSupremum : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := mΩ
      ∀ (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ (P : Measure ℝ), IsProbabilityMeasure P →
      ∀ (n : ℕ), 0 < n → ∀ (X : Fin n → Ω → ℝ),
        (∀ i, Measurable (X i)) → iIndepFun X μ →
        (∀ i, μ.map (X i) = P) →
        Integrable (fun ω => CDFDeviation P (fun i => X i ω)) μ ∧
        (∫ ω, CDFDeviation P (fun i => X i ω) ∂μ) ≤ c / Real.sqrt n

end AronowAudit.Literature

namespace AronowAudit.P001

universe u


/-- Conditional proposal; the complete held proposition is reproduced below. -/
def regular_local_alternative_score_identity_conditional_statement : Prop :=
  AronowAudit.Literature.QMDLAN.{0} → AronowAudit.Literature.GaussianThirdLemma.{0} →
  ∀ {K τ : ℕ}
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
  (hg : ∀ t ∈ Metric.ball θ δ, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hpos : ∀ t ∈ Metric.ball θ δ, ∀ y x, 0 ≤ g y x t)
  (hnorm : ∀ t ∈ Metric.ball θ δ, ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ)=1)
  (hqm : QuadraticMeanModel νX κ g θ)
  (hs2 : ∀ j, MemLp (fun xy : (Fin K → ℝ) × ℝ => modelScore g xy.2 xy.1 θ j)
    2 (conditionalModelLaw νX κ g θ))
  (hs0 : ∀ j, mean (conditionalModelLaw νX κ g θ)
    (fun xy => modelScore g xy.2 xy.1 θ j)=0)
  (I : Matrix (Fin τ) (Fin τ) ℝ)
  (hI : ∀ j k, I j k=mean (conditionalModelLaw νX κ g θ)
    (fun xy => modelScore g xy.2 xy.1 θ j*modelScore g xy.2 xy.1 θ k))
  (hpd : I.PosDef)
  (T : (n : ℕ) → (Fin n → (Fin K → ℝ) × ℝ) → Fin τ → ℝ)
  (ψ : (Fin K → ℝ) × ℝ → Fin τ → ℝ)
  (hregular : RegularAL (conditionalModelLaw νX κ g) θ T ψ),
  (∀ j k, mean (conditionalModelLaw νX κ g θ)
    (fun xy => ψ xy j*modelScore g xy.2 xy.1 θ k)=if j=k then 1 else 0) ∧
  ∀ a : Fin τ → ℝ, 0 ≤ ∑ j, ∑ k,
    a j*(covarianceMatrix (conditionalModelLaw νX κ g θ) ψ j k-I⁻¹ j k)*a k

/-- Conditional proposal; the complete held proposition is reproduced below. -/
def heavy_median_bootstrap_variance_counterexample_conditional_statement : Prop :=
  AronowAudit.Literature.MedianBootstrap.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (hlaw : μ.map (X 0)=heavyBootstrapLaw),
  CD μ (fun k ω => Real.sqrt (2*k+1)*sampleMedian (firstSample X (2*k+1) ω)) (gaussianReal 0 4) ∧
   BootstrapWeakCP μ X (fun k => 2*k+1) (fun {n} => @sampleMedian n) (gaussianReal 0 4) ∧
   (∀ n : ℕ,Odd n → 5 ≤ n → (3/16 : ℝ) ≤ prob μ {ω |
     5 < (n : ℝ)*bootVar sampleMedian (firstSample X n ω)}) ∧
   ¬ CP μ (fun k ω => ((2*k+1 : ℕ) : ℝ)*bootVar sampleMedian (firstSample X (2*k+1) ω)) 4

/-- Conditional proposal; the complete held proposition is reproduced below. -/
def regular_heavy_functional_bootstrap_weak_limit_conditional_statement : Prop :=
  AronowAudit.Literature.IIDMeanBootstrap.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (hlaw : μ.map (X 0)=heavyBootstrapLaw),
  BootstrapWeakCP μ X (fun k => 2*k+1) (fun {n} => @regularHeavyStatistic n) (gaussianReal 0 (1/4))

/-- Conditional proposal; the complete held proposition is reproduced below. -/
def bootstrap_median_primitive_moment_condition_conditional_statement : Prop :=
  AronowAudit.Literature.MedianBootstrap.{u} → AronowAudit.Literature.DKWExpectedSupremum.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
  (m : ℝ) (f : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
  (hf : (μ.map (X 0)).restrict (Metric.ball m δ) =
    (volume.restrict (Metric.ball m δ)).withDensity (fun x => ENNReal.ofReal (f x)))
  (hfn : ∀ x ∈ Metric.ball m δ, 0 ≤ f x)
  (hfm : AEMeasurable f (volume.restrict (Metric.ball m δ)))
  (hcont : ContinuousAt f m) (hpos : 0 < f m)
  (hmed : cdf μ (X 0) m=1/2 ∧
    (∀ x, x < m → cdf μ (X 0) x < 1/2) ∧
    (∀ x, m < x → 1/2 < cdf μ (X 0) x))
  (η : ℝ) (hη : 0 < η) (hmoment : Integrable (fun ω => |X 0 ω|^η) μ),
  CP μ (fun n ω => (n : ℝ)*bootVar sampleMedian (firstSample X n ω)) (1/(4*(f m)^2)) ∧
  CP μ (fun n ω => Real.sqrt n*Real.sqrt (bootVar sampleMedian (firstSample X n ω)))
    (1/(2*f m))

end AronowAudit.P001

#check @AronowAudit.Literature.QMDLAN
#print AronowAudit.Literature.QMDLAN
#print axioms AronowAudit.Literature.QMDLAN
#check @AronowAudit.Literature.GaussianThirdLemma
#print AronowAudit.Literature.GaussianThirdLemma
#print axioms AronowAudit.Literature.GaussianThirdLemma
#check @AronowAudit.Literature.IIDMeanBootstrap
#print AronowAudit.Literature.IIDMeanBootstrap
#print axioms AronowAudit.Literature.IIDMeanBootstrap
#check @AronowAudit.Literature.MedianBootstrap
#print AronowAudit.Literature.MedianBootstrap
#print axioms AronowAudit.Literature.MedianBootstrap
#check @AronowAudit.Literature.DKWExpectedSupremum
#print AronowAudit.Literature.DKWExpectedSupremum
#print axioms AronowAudit.Literature.DKWExpectedSupremum
#check @AronowAudit.P001.regular_local_alternative_score_identity_conditional_statement
#print axioms AronowAudit.P001.regular_local_alternative_score_identity_conditional_statement
#check @AronowAudit.P001.heavy_median_bootstrap_variance_counterexample_conditional_statement
#print axioms AronowAudit.P001.heavy_median_bootstrap_variance_counterexample_conditional_statement
#check @AronowAudit.P001.regular_heavy_functional_bootstrap_weak_limit_conditional_statement
#print axioms AronowAudit.P001.regular_heavy_functional_bootstrap_weak_limit_conditional_statement
#check @AronowAudit.P001.bootstrap_median_primitive_moment_condition_conditional_statement
#print axioms AronowAudit.P001.bootstrap_median_primitive_moment_condition_conditional_statement

-- Audit available project helpers, without using them as literature hypotheses.
#print axioms AronowAudit.P001.isCEF_condExp
#print axioms AronowAudit.P001.iid_sample_mean_chebyshev
#print axioms AronowAudit.P001.uniform_resampling_integral
#print axioms AronowAudit.P001.probability_convergence_continuous_at
#print axioms AronowAudit.P001.hot_deck_bootstrap_constant_inequalities
#print axioms AronowAudit.P001.iid_sample_mean_finite_moments
