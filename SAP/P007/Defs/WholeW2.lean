import Mathlib
import SAP.P007.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P007

open MeasureTheory
open scoped BigOperators

universe uW2

/-- The probability of an array event on an arbitrary underlying probability
space. Uses of this definition below require a probability measure and a
measurable array, so all these real probabilities are finite and well defined. -/
noncomputable def eventOnW2 {Ω : Type uW2} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (M : Ω → Array n k) (P : Array n k → Prop) : ℝ :=
  μ.real {ω | P (M ω)}

/-- The probability that the first j cells of row i are observed. -/
noncomputable def survivalOnW2 {Ω : Type uW2} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (M : Ω → Array n k) (i : Fin n) (j : ℕ) : ℝ :=
  eventOnW2 μ M (fun x => prefixObserved (x i) j)

/-- Assumption 2 on the underlying probability space, including q=0 and the
printed proviso that later conditional ratios are required only at positive
conditioning probabilities. -/
noncomputable def observationBoundOnW2 {Ω : Type uW2} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (M : Ω → Array n k) (q : ℝ) : Prop :=
  0 ≤ q ∧ q < 1 ∧ ∀ i,
    (0 < k → survivalOnW2 μ M i 1 ≤ q) ∧
    ∀ j, 1 ≤ j → j < k → 0 < survivalOnW2 μ M i j →
      survivalOnW2 μ M i (j + 1) / survivalOnW2 μ M i j ≤ q

/-- Full mutual independence of row vectors on the underlying probability
space, tested against every row event. Row spaces are finite and discrete, so
every event tested here is measurable when the array is measurable. -/
noncomputable def rowsIndependentOnW2 {Ω : Type uW2} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (M : Ω → Array n k) : Prop :=
  ∀ E : Fin n → Row k → Prop,
    eventOnW2 μ M (fun x => ∀ i, E i (x i)) =
      ∏ i, eventOnW2 μ M (fun x => E i (x i))

/-- Full mutual independence of every cell of a finite joint law. Allowing an
arbitrary Boolean event at each coordinate includes every subfamily, by taking
the sure event at unused coordinates; this is not pairwise independence. -/
noncomputable def cellsIndependentW2 {n k : ℕ} (L : Law (Array n k)) : Prop :=
  ∀ E : Fin n → Fin k → Bool → Prop,
    probability L (fun x => ∀ i j, E i j (x i j)) =
      ∏ i, ∏ j, probability L (fun x => E i j (x i j))

/-- Full mutual independence of the n*k cells on the underlying probability
space. As for rows, every Boolean event is measurable, and arbitrary events at
all coordinates test independence of all subfamilies. -/
noncomputable def cellsIndependentOnW2 {Ω : Type uW2} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (M : Ω → Array n k) : Prop :=
  ∀ E : Fin n → Fin k → Bool → Prop,
    eventOnW2 μ M (fun x => ∀ i j, E i j (x i j)) =
      ∏ i, ∏ j, eventOnW2 μ M (fun x => E i j (x i j))

/-- An exact finite joint distribution of a measurable Boolean array: every
event probability and every real statistic's expectation agree. Integrability
is explicitly included; finite range and a probability measure ensure it. -/
def lawRealizesW2 {Ω : Type uW2} [MeasurableSpace Ω] {n k : ℕ}
    (μ : Measure Ω) (M : Ω → Array n k) (L : Law (Array n k)) : Prop :=
  (∀ P : Array n k → Prop, probability L P = eventOnW2 μ M P) ∧
  ∀ f : Array n k → ℝ,
    Integrable (fun ω => f (M ω)) μ ∧
      (∫ ω, f (M ω) ∂μ) = expectation L f

/-- P007-T10; corrected Figure 5 and its discussion, Supplement pp. 2-3.
The usual measure-theoretic conditions are assumed. For positive integers n,k
and any measurable missingness array on a probability space, Assumption 2 gives
E[D_i]=1-s_ik >= b_k and E[F_n]=(sum_i (1-s_ik))/n >= b_k, where
b_k=1-q^k is independent of n. These conclusions require no row independence.
Every law with mutually independent cells of observation probability q satisfies
Assumptions 1 and 2 and attains E[F_n]=b_k; a normalized independent-cell law
exists for every q in [0,1). The all-deletion lower bound is b_k^n, equals b_k
at n=1, and is strictly smaller for n>=2 and 0<q<1, when 0<b_k<1.
On the entire domain q in [0,1), the bounds coincide if and only if n=1 or q=0;
at q=0 both bounds are one. -/
def T10WholeStatement_W2 : Prop :=
  (∀ (Ω : Type uW2) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (n k : ℕ), 0 < n → 0 < k → ∀ M : Ω → Array n k, Measurable M →
      ∀ q : ℝ, observationBoundOnW2 μ M q →
      (∀ i : Fin n,
        Integrable (fun ω => deletedIndicator (M ω) i) μ ∧
        (∫ ω, deletedIndicator (M ω) i ∂μ) = 1 - survivalOnW2 μ M i k ∧
        fractionBound q k ≤ ∫ ω, deletedIndicator (M ω) i ∂μ) ∧
      (Integrable (fun ω => deletedFraction (M ω)) μ ∧
        (∫ ω, deletedFraction (M ω) ∂μ) =
          (∑ i, (1 - survivalOnW2 μ M i k)) / n ∧
        fractionBound q k ≤ ∫ ω, deletedFraction (M ω) ∂μ)) ∧
  (∀ (Ω : Type uW2) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (n k : ℕ), 0 < n → 0 < k → ∀ M : Ω → Array n k, Measurable M →
      ∀ q : ℝ, 0 ≤ q → q < 1 → cellsIndependentOnW2 μ M →
      (∀ i j, eventOnW2 μ M (fun x => x i j = false) = q) →
      rowsIndependentOnW2 μ M ∧ observationBoundOnW2 μ M q ∧
        (∫ ω, deletedFraction (M ω) ∂μ) = fractionBound q k) ∧
  (∀ (n k : ℕ), 0 < n → 0 < k → ∀ q : ℝ, 0 ≤ q → q < 1 →
      ∃ L : Law (Array n k), L.weight = equalWeights n k q ∧
        cellsIndependentW2 L ∧ rowIndependent L ∧ observationBound L q ∧
        (∀ i j, probability L (fun x => x i j = false) = q) ∧
        expectation L deletedFraction = fractionBound q k) ∧
  (∀ (n k : ℕ), 0 < n → 0 < k → ∀ q : ℝ, 0 ≤ q → q < 1 →
      lowerBound n q k = (fractionBound q k)^n ∧
      lowerBound 1 q k = fractionBound q k ∧
      (0 < q → 2 ≤ n →
        0 < fractionBound q k ∧ fractionBound q k < 1 ∧
          lowerBound n q k < fractionBound q k) ∧
      (lowerBound n q k = fractionBound q k ↔ n = 1 ∨ q = 0) ∧
      (q = 0 → fractionBound q k = 1 ∧ lowerBound n q k = 1))

end SAP.P007
