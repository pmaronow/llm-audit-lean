import Mathlib
import SAP.P013b.Defs.Part11

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013b

open MeasureTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- The `(i,j)` entry of the same-exposure simulation matrix with identity
smoothing. The number of replicates is `R = n + 1`, so the denominator is
`R + 1 = n + 2` and is always positive. -/
def t20SmoothedEntry {Ω A : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d : Fin K) (Z : ℕ → A → Ω) (a : A)
    (n : ℕ) (i j : Fin N) : ℝ :=
  ((∑ r ∈ range (n + 1),
    indicator F.exposure i d (Z r a) * indicator F.exposure j d (Z r a)) +
      (if i = j then 1 else 0)) / (n + 2 : ℝ)

/-- The `(i,j)` entry of the cross-exposure simulation matrix, using the
same positive number `R = n + 1` of replicates and no smoothing. -/
def t20CrossEntry {Ω A : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d e : Fin K) (Z : ℕ → A → Ω) (a : A)
    (n : ℕ) (i j : Fin N) : ℝ :=
  (∑ r ∈ range (n + 1),
    indicator F.exposure i d (Z r a) * indicator F.exposure j e (Z r a)) /
      (n + 1 : ℝ)

/-- Both printed matrix limits, entrywise on a fixed finite population.
Indexing by `R = n + 1` omits only the undefined zero-replicate cross ratio. -/
def T20MatrixLimits {Ω A : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (d e : Fin K) (Z : ℕ → A → Ω) (a : A) : Prop :=
  ∀ i j : Fin N,
    Tendsto (fun n : ℕ => t20SmoothedEntry F d Z a n i j) atTop
      (𝓝 (jointPi F i j d d)) ∧
    Tendsto (fun n : ℕ => t20CrossEntry F d e Z a n i j) atTop
      (𝓝 (jointPi F i j d e))

/-- Repeating one fair draw refutes the marginal-law-only interpretation of
replication. This is an illustration of the need for independence, not a
refutation of the independent-replicate proposition.
P013-T20; Proposition 3.1, p. 1917 (PDF p. 6), Appendix A.1, p. 1938 (PDF p. 27).
In a one-unit design with
two equiprobable assignments, own-assignment exposure, and zero potential
outcomes, repeat one fair binary assignment forever. Every replicate is
measurable and has exactly the design law, and both exposure probabilities are
strictly between zero and one. The exact same-exposure diagonal is 1/2, but its
smoothed estimate tends to 1 or 0 at every sample point. The cross-exposure
entry and its exact target are zero. The same-exposure limit fails everywhere,
the failure of the conjunction has probability one, and the claimed
almost-sure conjunction is false. Replicate counts are `R = n + 1 > 0`.
The independent-draw result is stated separately in T20Statement. -/
def T20WholeStatement : Prop :=
  ∃ (P : Design (Fin 2)) (F : Population P 1 2) (Z : ℕ → Fin 2 → Fin 2),
    (∀ z, P.weight z = (1 / 2 : ℝ)) ∧
    (∀ z i, F.exposure z i = z) ∧
    (∀ i d, F.outcome i d = 0) ∧
    (∀ d, Positivity F d) ∧
    IsProbabilityMeasure (designMeasure P) ∧
    (∀ r, Measurable (Z r)) ∧
    (∀ r, Measure.map (Z r) (designMeasure P) = designMeasure P) ∧
    (∀ r b, Z r b = b) ∧
    jointPi F 0 0 0 0 = (1 / 2 : ℝ) ∧
    jointPi F 0 0 0 1 = 0 ∧
    (∀ b n, t20CrossEntry F 0 1 Z b n 0 0 = 0) ∧
    (∀ b, Tendsto (fun n : ℕ => t20SmoothedEntry F 0 Z b n 0 0) atTop
      (𝓝 (if b = 0 then (1 : ℝ) else 0))) ∧
    (∀ b, ¬ Tendsto (fun n : ℕ => t20SmoothedEntry F 0 Z b n 0 0) atTop
      (𝓝 (jointPi F 0 0 0 0))) ∧
    (∀ᵐ b ∂designMeasure P, ¬ T20MatrixLimits F 0 1 Z b) ∧
    ¬ (∀ᵐ b ∂designMeasure P, T20MatrixLimits F 0 1 Z b)

end

end SAP.P013b
