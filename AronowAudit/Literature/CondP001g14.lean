import AronowAudit.P001.P001_Foundations

/-!
Literature statements for weak convergence, contiguity, and bootstrap resampling,
with a conditional application to a bounded transform of the mean.
The cited bootstrap result is an explicit hypothesis, not a theorem proved here.
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


/-- Product law of a finite iid sample; independent of any statistical target. -/
def ProductLaw {E : Type u} [MeasurableSpace E] (P : Measure E) (n : ℕ) :
    Measure (Fin n → E) := Measure.pi (fun _ : Fin n => P)


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


/-- The empirical CDF of a finite sample. -/
def FiniteCDF {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ i, if x i ≤ t then (1 : ℝ) else 0) / (n : ℝ)

/-- Kolmogorov deviation; for a probability measure P and n > 0, the range is nonempty and bounded by 1. -/
def CDFDeviation {n : ℕ} (P : Measure ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (Set.range (fun t : ℝ => |FiniteCDF x t - (P (Set.Iic t)).toReal|))


end AronowAudit.Literature

namespace AronowAudit.P001

universe u


/-- Bootstrap weak-limit statement conditional on the published iid mean
bootstrap theorem. -/
def regular_heavy_functional_bootstrap_weak_limit_conditional_statement : Prop :=
  AronowAudit.Literature.IIDMeanBootstrap.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X) (hlaw : μ.map (X 0)=heavyBootstrapLaw),
  BootstrapWeakCP μ X (fun k => 2*k+1) (fun {n} => @regularHeavyStatistic n) (gaussianReal 0 (1/4))


end AronowAudit.P001

