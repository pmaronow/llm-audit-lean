import Mathlib
import SAP.P001a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

universe u

namespace SAP.P001a

/-- The first component contains the covariates, the second the responses. -/
abbrev SieveDataW3 (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

/-- A polynomial represented by its first `d + 1` coefficients. -/
def coefficientPolynomialW3 {d : ℕ} (b : Fin (d + 1) → ℝ) : Polynomial ℝ :=
  ∑ k : Fin (d + 1), Polynomial.C (b k) * Polynomial.X ^ (k : ℕ)

/-- The main, three-quarter-power degree schedule. -/
def mainDegreeW3 (n : ℕ) : ℕ := Nat.floor ((n : ℝ) ^ (3 / 4 : ℝ))

/-- The separate supplementary schedule: the integer floor of the square root. -/
def endpointDegreeW3 (n : ℕ) : ℕ := Nat.sqrt n

/-- Pointwise squared-residual least squares, with coefficients that are Borel functions
of the first `n` observations. This includes singular and empty designs. -/
def BorelSieveLSW3 {Ω : Type*} (X Y : ℕ → Ω → ℝ) (J : ℕ → ℕ)
    (fit : ℕ → Ω → Polynomial ℝ) : Prop :=
  IsSieveLS X Y J fit ∧
  ∀ n : ℕ, ∃ b : SieveDataW3 n → (Fin (J n + 1) → ℝ), Measurable b ∧
    ∀ ω : Ω, fit n ω = coefficientPolynomialW3
      (b ((fun i : Fin n => X i ω), (fun i : Fin n => Y i ω)))

/-- Squared local Lebesgue L2 error about the zero conditional mean. Polynomial continuity
makes this integral finite for every sample and every finite `δ`. -/
def localRiskW3 {Ω : Type*} (fit : ℕ → Ω → Polynomial ℝ)
    (δ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ x in Set.Icc 0 δ, ((fit n ω).eval x) ^ 2

/-- The unit-interval uniform density, including the endpoints as a choice of version. -/
def unitDensityW3 (x : ℝ) : ℝ := if x ∈ Set.Icc (0 : ℝ) 1 then 1 else 0

open scoped ContDiff in
/-- The model facts making the counterexample admissible: independent uniform/Gaussian
coordinates, a smooth zero CEF, all integer moments, and the mass of every local region. -/
def SieveModelFactsW3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : ℕ → Ω → ℝ) : Prop :=
  μ.map (X 0) = uniformLaw 0 1 ∧
  μ.map (Y 0) = gaussianReal 0 1 ∧
  IndepFun (X 0) (Y 0) μ ∧
  HasPDF (μ.map (X 0)) unitDensityW3 ∧
  (∀ x : ℝ, 0 < unitDensityW3 x ↔ x ∈ Set.Icc (0 : ℝ) 1) ∧
  ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)) ∧
  IsCEF μ (X 0) (Y 0) (fun _ : ℝ => 0) ∧
  (∀ k : ℕ, Integrable (fun s => (X 0 s) ^ k) μ ∧
    Integrable (fun s => (Y 0 s) ^ k) μ) ∧
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → prob μ {s | X 0 s ∈ Set.Icc 0 δ} = δ

/-- The law of a finite iid sample, with designs and responses collected separately. -/
def finiteSampleLawW3 (n : ℕ) : Measure (SieveDataW3 n) :=
  (Measure.pi (fun _ : Fin n => uniformLaw 0 1)).prod
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))

/-- The endpoint assertion for a single finite iid experiment. Experiments at different
sample sizes need not be coupled. The coefficient statistic is Borel measurable. -/
def FiniteEndpointBoundW3 : Prop :=
  ∀ t : ℕ, 2 ≤ t → ∀ {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → SieveDataW3 (t ^ 2)),
    Measurable Z → μ.map Z = finiteSampleLawW3 (t ^ 2) →
    ∀ b : SieveDataW3 (t ^ 2) → (Fin (t + 1) → ℝ), Measurable b →
      (∀ ω : Ω, ∀ p : Polynomial ℝ, p.natDegree ≤ t →
        (∑ i : Fin (t ^ 2), ((Z ω).2 i -
          (coefficientPolynomialW3 (b (Z ω))).eval ((Z ω).1 i)) ^ 2) ≤
        ∑ i : Fin (t ^ 2), ((Z ω).2 i - p.eval ((Z ω).1 i)) ^ 2) →
      1 / 4 ≤ prob μ {ω | 1 / 4 < |(coefficientPolynomialW3 (b (Z ω))).eval 1|}

/-- P001-T5; pp. 168–169 (PDF pp. 186–187), Definition 4.3.9.
The squared-residual polynomial sieve with J_n = floor(n^(3/4)) satisfies J_n → infinity
and J_n/n → 0. For iid independent U[0,1] covariates and standard Gaussian outcomes,
the CEF is smooth and zero, all moments exist, and least-squares fits with Borel measurable
coefficients exist. Every such fit has, for every 0 < delta ≤ 1 and epsilon > 0, local squared L2
error exceeding epsilon with lower limiting probability at least 1/2 along n = t^4;
it therefore fails local L2 consistency on a region of positive probability mass.
For a separate degree-floor(sqrt(n)) sequence, fits with Borel measurable coefficients
also exist, and every such sequence satisfies Pr[|fit_(t^2)(1)| > 1/4] ≥ 1/4 for every
integer t ≥ 2, including experiments with no coupling across sample sizes. Thus the
printed rate condition is insufficient for the stated local
consistency; no assertion about consistency at slower degrees is made. The usual
measure-theoretic conditions are assumed. -/
def T5WholeStatement_W3 : Prop :=
  (Tendsto mainDegreeW3 atTop atTop ∧
  Tendsto (fun n : ℕ => (mainDegreeW3 (n + 1) : ℝ) / ((n : ℝ) + 1))
    atTop (nhds 0) ∧
  (∀ t : ℕ, endpointDegreeW3 (t ^ 2) = t) ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ℕ → Ω → ℝ),
    IID μ (fun i ω => (X i ω, Y i ω)) →
    μ.map (fun ω => (X 0 ω, Y 0 ω)) = (uniformLaw 0 1).prod (gaussianReal 0 1) →
    SieveModelFactsW3 μ X Y ∧
    (∃ fit : ℕ → Ω → Polynomial ℝ, BorelSieveLSW3 X Y mainDegreeW3 fit) ∧
    (∀ fit : ℕ → Ω → Polynomial ℝ, BorelSieveLSW3 X Y mainDegreeW3 fit →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        (∀ ε : ℝ, 0 < ε →
          1 / 2 ≤ Filter.liminf (fun t : ℕ =>
            prob μ {ω | ε < localRiskW3 fit δ (t ^ 4) ω}) atTop) ∧
        ¬ CP μ (localRiskW3 fit δ) 0) ∧
    (∃ fit : ℕ → Ω → Polynomial ℝ, BorelSieveLSW3 X Y endpointDegreeW3 fit) ∧
    (∀ fit : ℕ → Ω → Polynomial ℝ, BorelSieveLSW3 X Y endpointDegreeW3 fit →
      ∀ t : ℕ, 2 ≤ t →
        1 / 4 ≤ prob μ {ω | 1 / 4 < |(fit (t ^ 2) ω).eval 1|})) ∧
  FiniteEndpointBoundW3.{u}

end SAP.P001a
