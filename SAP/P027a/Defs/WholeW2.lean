import Mathlib
import SAP.P027a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

/-- Bias of the variance estimator for the population mean, with the population
and its outcomes held fixed and only the sample random. -/
def meanSamplingBias {U Ω : Type} [Fintype U] [Fintype Ω]
    (D : Design U Ω) (y : U → ℝ) : ℝ :=
  expect D (fun ω => htVarianceEstimator D y ω / (Fintype.card U : ℝ)^2) -
    variance D (htMean D y)

/-- The outcome average is outside the conditional sampling variance. Finite
second moments and zero off-diagonal cross moments are `UncorrelatedNoise`;
no common variance or independence assumption is added. -/
def WholeOutcomeAverage : Prop :=
  ∀ {U Ω Ξ : Type} [Fintype U] [Fintype Ω] [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (D : Design U Ω),
    Valid D → Positive D → 0 < Fintype.card U →
    ∀ x : U → ℝ, (∀ k, 1 ≤ x k) → ∀ (β : ℝ) (ε : U → Ξ → ℝ),
    UncorrelatedNoise μ ε →
      (∀ k, outcomeE μ (fun ξ => rawOutcomes x β ε ξ k) = β*x k) ∧
      (∀ k l, k ≠ l → outcomeE μ (fun ξ =>
        rawOutcomes x β ε ξ k * rawOutcomes x β ε ξ l) = β^2*x k*x l) ∧
      Integrable (fun ξ => biasA D (rawOutcomes x β ε ξ)) μ ∧
      Integrable (fun ξ => meanSamplingBias D (rawOutcomes x β ε ξ)) μ ∧
      outcomeE μ (fun ξ => biasA D (rawOutcomes x β ε ξ)) = β^2*biasA D x ∧
      0 ≤ outcomeE μ (fun ξ => biasA D (rawOutcomes x β ε ξ)) ∧
      outcomeE μ (fun ξ => meanSamplingBias D (rawOutcomes x β ε ξ)) =
        β^2*biasA D x/(Fintype.card U : ℝ)^2 ∧
      0 ≤ outcomeE μ (fun ξ => meanSamplingBias D (rawOutcomes x β ε ξ))

/-- Exact criterion for a fixed population, and its same-sign sufficient condition. -/
def WholePopulationwiseConservativity : Prop :=
  ∀ {U Ω : Type} [Fintype U] [Fintype Ω] (D : Design U Ω),
    Valid D → Positive D → 0 < Fintype.card U → ∀ y : U → ℝ,
      meanSamplingBias D y = biasA D y/(Fintype.card U : ℝ)^2 ∧
      (0 ≤ meanSamplingBias D y ↔ 0 ≤ biasA D y) ∧
      (((∀ k, 0 ≤ y k) ∨ (∀ k, y k ≤ 0)) → 0 ≤ meanSamplingBias D y)

/-- The concrete comparison in part (iv), including both outcome averages for
the eight-unit example and its downward-biased fixed outcome vector. -/
def WholeOutcomeWitness : Prop :=
  Valid random8 ∧ Positive random8 ∧ (∀ k, 1 ≤ randomSize8 k) ∧
    biasA random8 randomSize8 = 176 ∧
    (3/2 : ℝ)^2*biasA random8 randomSize8 = 396 ∧
    biasA random8 randomOutcome8 = -16 ∧
    meanSamplingBias random8 randomOutcome8 = -1/4 ∧
    (∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
      (ε : Fin 8 → Ξ → ℝ), UncorrelatedNoise μ ε →
      (∀ β : ℝ,
        outcomeE μ (fun ξ => biasA random8 (rawOutcomes randomSize8 β ε ξ)) =
          176*β^2 ∧
        outcomeE μ (fun ξ => meanSamplingBias random8
          (rawOutcomes randomSize8 β ε ξ)) = 176*β^2/64) ∧
      outcomeE μ (fun ξ => biasA random8 (rawOutcomes randomSize8 (3/2) ε ξ)) = 396)

/-- P027-T11, correction to Supplement Section C, p. A3: conditional on the
positive size vector, mean-zero errors with finite second moments and zero
cross moments give E[y_k y_l] = beta^2 x_k x_l for distinct units, E[A] =
beta^2 sum_Z x_k x_l >= 0, and average mean-scale sampling bias E[A]/N^2 >= 0.
The eight-unit coefficient is 176 (396 at beta = 3/2), whereas the displayed
fixed outcome vector has A = -16 and mean-scale bias -1/4. For each fixed
population conservativity is equivalent to A >= 0; outcomes all of one sign
suffice. Thus the average guarantee supplies no guarantee for every realized
population. The usual measure-theoretic conditions are assumed; the nonzero
population size is presupposed by the population mean. -/
def T11WholeStatement : Prop :=
  WholeOutcomeAverage ∧ WholePopulationwiseConservativity ∧ WholeOutcomeWitness

/-- Sum of the proposed certainty-unit probabilities. -/
def ppsCapSum {N : ℕ} (x : Fin N → ℝ) (c : ℝ) : ℝ :=
  ∑ k, min 1 (c*x k)

/-- The uniform probability law on the half-open unit interval. -/
def systematicStartLaw : Measure ℝ := volume.restrict (Set.Ico 0 1)

/-- The sampled subset as its Boolean membership function. -/
def systematicSample {N : ℕ} (π : Fin N → ℝ) (m : ℕ) (u : ℝ) : Fin N → Bool :=
  fun k => decide (systematicSelected π m u k)

/-- The actual ordered systematic design, including measurable indicators and
joint probabilities. The interval order is the order on `Fin N`. -/
def WholeSystematicLaw {N : ℕ} (π : Fin N → ℝ) (m : ℕ) : Prop :=
  IsProbabilityMeasure systematicStartLaw ∧
    (∀ u : ℝ, 0 ≤ u → u < 1 →
      (Finset.univ.filter (fun k => systematicSelected π m u k)).card = m) ∧
    (∀ k, MeasurableSet {u : ℝ | systematicSelected π m u k} ∧
      Integrable (fun u : ℝ => if systematicSelected π m u k then (1:ℝ) else 0)
        systematicStartLaw ∧
      (∫ u : ℝ, (if systematicSelected π m u k then (1:ℝ) else 0)
        ∂systematicStartLaw) = π k) ∧
    (∀ k l,
      Integrable (fun u : ℝ =>
        (if systematicSelected π m u k then (1:ℝ) else 0) *
        (if systematicSelected π m u l then (1:ℝ) else 0)) systematicStartLaw ∧
      (∫ u : ℝ, (if systematicSelected π m u k then (1:ℝ) else 0) *
        (if systematicSelected π m u l then (1:ℝ) else 0) ∂systematicStartLaw) =
        (systematicStartLaw
          ({u : ℝ | systematicSelected π m u k} ∩
           {u : ℝ | systematicSelected π m u l})).toReal)

def WholeCapRegularity : Prop :=
  ∀ {N : ℕ} (x : Fin N → ℝ), (∀ k, 0 < x k) →
    Continuous (ppsCapSum x) ∧ Monotone (ppsCapSum x) ∧ ppsCapSum x 0 = 0 ∧
    ∀ c : ℝ, (∑ k, 1/x k) ≤ c → ppsCapSum x c = N

def WholeSystematicConstruction : Prop :=
  ∀ {N : ℕ}, 2 ≤ N → ∀ m : ℕ, 0 < m → m < N →
    ∀ π : Fin N → ℝ, (∀ k, 0 < π k ∧ π k ≤ 1) →
    (∑ k, π k) = m → WholeSystematicLaw π m

/-- Sufficiency of the feasible printed formula, and an ordered design for a
capped vector for every positive size vector. -/
def WholePPSSpecializations : Prop :=
  ∀ {N : ℕ}, 2 ≤ N → ∀ m : ℕ, 0 < m → m < N →
    ∀ x : Fin N → ℝ, (∀ k, 0 < x k) →
      (((∀ k, (m:ℝ)*x k ≤ ∑ a, x a) →
        0 < (m:ℝ)/(∑ a, x a) ∧ WholeSystematicLaw (printedPPS m x) m)) ∧
      (∃ c : ℝ, 0 < c ∧ ppsCapSum x c = m ∧
        WholeSystematicLaw (fun k => min 1 (c*x k)) m)

def certaintyProb8 (k : Fin 8) : ℝ := min 1 ((1/7 : ℝ)*invalidSize8 k)

/-- The seven half-open start cells, with zero-based index `g`. -/
def certaintyCell8 (g : Fin 7) : Set ℝ := Set.Ico ((g:ℝ)/7) (((g:ℝ)+1)/7)

def WholeCertainty8 : Prop :=
  Valid certainty8 ∧ Positive certainty8 ∧
    (∑ k, certaintyProb8 k) = 2 ∧
    (∀ k, certaintyProb8 k = if k = 0 then 1 else 1/7) ∧
    (∀ k, pi certainty8 k = certaintyProb8 k) ∧
    (∀ k l, joint certainty8 k l = if k = l then pi certainty8 k else
      if k = 0 ∨ l = 0 then 1/7 else 0) ∧
    (∑ k, min 1 (printedPPS 2 invalidSize8 k)) = 51/37 ∧
    (51/37 : ℝ) ≠ 2 ∧
    (∀ (g : Fin 7) (u : ℝ), u ∈ certaintyCell8 g →
      systematicSample certaintyProb8 2 u = certainty8.selected g) ∧
    (∀ g : Fin 7, (systematicStartLaw (certaintyCell8 g)).toReal = 1/7) ∧
    (∀ F : (Fin 8 → Bool) → ℝ,
      Integrable (fun u => F (systematicSample certaintyProb8 2 u)) systematicStartLaw ∧
      (∫ u, F (systematicSample certaintyProb8 2 u) ∂systematicStartLaw) =
        expect certainty8 (fun g => F (certainty8.selected g)))

/-- The unoffset NB vector `v` is accepted precisely when the printed formula
for the offset sizes `1 + v_k` is feasible. The pointwise inequalities are
equivalent to m times the maximum size being at most the total size. -/
def feasibleSizeVectors (N m : ℕ) : Set (Fin N → ℕ) :=
  {v | ∀ k, (m:ℝ)*(1+(v k:ℝ)) ≤ ∑ a, (1+(v a:ℝ))}

def acceptedSizeLaw (N m : ℕ) : Measure (Fin N → ℕ) :=
  ProbabilityTheory.cond (nbProductLawN N) (feasibleSizeVectors N m)

/-- Independent repetitions of a full size vector, retaining the independence
within each full vector already specified by `nbProductLawN`. -/
def redrawSizeSequenceLaw (N : ℕ) : Measure (ℕ → (Fin N → ℕ)) :=
  Measure.infinitePi (fun _ : ℕ => nbProductLawN N)

/-- First feasible full vector. The default on sequences with no acceptance is
explicit; the whole statement proves that these sequences have probability zero. -/
def redrawSizeOutput (N m : ℕ) (w : ℕ → (Fin N → ℕ)) : Fin N → ℕ :=
  if h : ∃ n, w n ∈ feasibleSizeVectors N m then w (Nat.find h) else fun _ => 0

def WholeRedrawRecipe : Prop :=
  ∀ {N : ℕ}, 2 ≤ N → ∀ m : ℕ, 0 < m → m < N →
    IsProbabilityMeasure (nbProductLawN N) ∧
    0 < nbProductLawN N (feasibleSizeVectors N m) ∧
    IsProbabilityMeasure (acceptedSizeLaw N m) ∧
    (∀ B : Set (Fin N → ℕ), MeasurableSet B →
      (acceptedSizeLaw N m B).toReal =
        (nbProductLawN N (B ∩ feasibleSizeVectors N m)).toReal /
          (nbProductLawN N (feasibleSizeVectors N m)).toReal) ∧
    IsProbabilityMeasure (redrawSizeSequenceLaw N) ∧
    (∀ᵐ w ∂redrawSizeSequenceLaw N, ∃ n, w n ∈ feasibleSizeVectors N m) ∧
    Measurable (redrawSizeOutput N m) ∧
    (redrawSizeSequenceLaw N).map (redrawSizeOutput N m) = acceptedSizeLaw N m

/-- P027-T13, correction to the PPS display in Supplement Section C, p. A3:
for N >= 2, positive sizes and 0 < m < N, the printed probabilities require
m max(x) <= sum(x). The cap-sum map is continuous, nondecreasing, starts at
zero and eventually equals N; a positive cap multiplier gives sum m. Under
feasibility, m/sum(x) retains the printed formula. Ordered intervals with
these probabilities and a uniform start in [0,1) give exactly m distinct
units, the prescribed marginals and the intersection-measure joint probabilities.
For sizes (30,1,1,1,1,1,1,1), m = 2, redistribution gives (1,1/7,...,1/7):
the same continuous design draws each {1,j} with probability 1/7, with the
stated joints, whereas naive capping sums to 51/37 != 2. The formula-preserving
recipe independently redraws full offset-NB vectors until feasibility;
acceptance has positive probability, termination is almost sure and the output
law is the original law restricted to feasibility and normalized. The alternative
retains the original size law and uses the capped ordered design and its joints.
The usual measure-theoretic conditions are assumed. No assertion about which
recipe generated the unavailable simulation runs is made. -/
def T13WholeStatement : Prop :=
  PPSFeasibility ∧ WholeCapRegularity ∧ WholeSystematicConstruction ∧
    WholePPSSpecializations ∧ WholeCertainty8 ∧ WholeRedrawRecipe

end
end SAP.P027a
