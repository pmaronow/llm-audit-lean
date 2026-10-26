import AronowAudit.P006.Wave1.BinaryExperimentBlueprint

/-!
# P006-T27: refutation of printed TT alignment

Propositions 9 and 3 as printed (PDF pp. 5, 17–18) assert TT alignment under
fixed-query unbiasedness only. `Target` is the negation of this assertion for
types in universe 0.

The one-unit experiment `E27` has the random baseline
`μhat π ω x = estA (X ω) x`: its mean is `0 = μ0 x` at every fixed query `x`,
but it equals `1` at the unit's own covariate. With
`PiSet = {π | Admissible π}`, the actual rewards are `expectedTT π = -(π false + π true)/4` and
`V π = (π false + π true)/4`, so the first printed clause fails at `π ≡ 1` (`-1/2 ≠ 1/2`).
The sample space is `Ω = Fin 1 → Bool × Bool`.
-/

set_option autoImplicit false

namespace AronowAudit.P006.Wave1.TTAlignment

open AronowAudit.P006 AronowAudit.P006.Wave1.BinaryExperiment MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-! Printed assertion -/

/-- P006-T27: the negation of the printed TT alignment assertion
(Propositions 9 and 3), for types in universe 0. -/
def Target : Prop :=
  ¬ ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n),
      Standing E → ∀ (PiSet : Set (C → ℝ)), (∀ π ∈ PiSet, Admissible π) →
      PointwiseUnbiased E PiSet →
      (∀ π ∈ PiSet, E.expectedTT π = (n : ℝ) * E.V π) ∧
      (∀ π, IsBest PiSet E.expectedTT π ↔ IsBest PiSet E.V π) ∧
      (∀ π, IsBest PiSet E.expectedTT π → regret PiSet E.V π = 0) ∧
      (PiSet = {π | Admissible π} → IsBest PiSet E.expectedTT (positiveRule E.τ))

/-- The one-unit witness experiment, using witness A of P006-T4. -/
def E27 : Experiment (Fin 1 → Bool × Bool) Bool 1 :=
  binExp 1 (by norm_num) (fun _ => 1 / 2) (fun _ ω x => estA (ω 0).1 x)

/-- An explicit-witness formulation of `Target`. -/
def Witness : Prop :=
  ∃ (E : Experiment (Fin 1 → Bool × Bool) Bool 1) (PiSet : Set (Bool → ℝ)),
    Standing E ∧ (∀ π ∈ PiSet, Admissible π) ∧ PointwiseUnbiased E PiSet ∧
    ¬ ((∀ π ∈ PiSet, E.expectedTT π = (1 : ℝ) * E.V π) ∧
       (∀ π, IsBest PiSet E.expectedTT π ↔ IsBest PiSet E.V π) ∧
       (∀ π, IsBest PiSet E.expectedTT π → regret PiSet E.V π = 0) ∧
       (PiSet = {π | Admissible π} → IsBest PiSet E.expectedTT (positiveRule E.τ)))

/-! Fixed-query unbiasedness and reward identities -/

/-- Fixed-query unbiasedness of the witness baseline, with integrability:
for each fixed query x, the event X=x has probability 1/2 regardless of π,
so the two estimator values ±1 have mean zero. Integrability follows from
`Integrable.of_finite`; the mean follows from `BinaryExperiment.S2`. -/
def S1 : Prop :=
  ∀ π : Bool → ℝ, Admissible π → ∀ x : Bool,
    Integrable (fun ω => E27.μhat π ω x) (E27.law π) ∧ ∫ ω, E27.μhat π ω x ∂E27.law π = 0

/-- The actual reward and welfare functionals: the estimator evaluated at
the unit's own covariate equals 1 in every state, giving expected TT reward
−(π false + π true)/4 and welfare (π false + π true)/4.
The finite expectation identity `BinaryExperiment.S2` and reindexing by
`Equiv.funUnique (Fin 1) (Bool × Bool)` reduce both expectations to finite sums;
the single-unit TT sum reduces by `Fin.sum_univ_one`. -/
def S2 : Prop :=
  ∀ π : Bool → ℝ, Admissible π →
    E27.expectedTT π = -(π false + π true) / 4 ∧ E27.V π = (π false + π true) / 4

/-! Implications of the binary experiment identities -/

/-- Fixed-query unbiasedness from the binary experiment identities. -/
def N1 : Prop := BinaryExperiment.S1 → BinaryExperiment.S2 → S1
/-- Reward and welfare formulas from the binary experiment identities. -/
def N2 : Prop := BinaryExperiment.S1 → BinaryExperiment.S2 → S2

/-! Refutation -/

/-- The witness experiment contradicts the printed alignment assertion. -/
theorem assemble_witness (b1 : BinaryExperiment.N1) (b2 : BinaryExperiment.N2)
    (b3 : BinaryExperiment.N3) (b4 : BinaryExperiment.N4) (b5 : BinaryExperiment.N5)
    (h1 : N1) (h2 : N2) : Witness := by
  have s2b : BinaryExperiment.S2 := b2 b1
  have hU : S1 := h1 b1 s2b
  have hV : S2 := h2 b1 s2b
  refine ⟨E27, {π | Admissible π},
    standing_of b1 b3 b4 b5 1 (by norm_num) (fun _ => 1 / 2) (fun _ ω x => estA (ω 0).1 x),
    fun _ h => h, fun π hπ x => hU π hπ x, ?_⟩
  rintro ⟨hTT, -⟩
  have hone : Admissible (fun _ : Bool => (1 : ℝ)) :=
    ⟨measurable_const, fun _ => by norm_num⟩
  have h := hTT _ hone
  rw [(hV _ hone).1, (hV _ hone).2] at h
  norm_num at h

/-- The explicit witness implies `Target`. -/
theorem assemble (b1 : BinaryExperiment.N1) (b2 : BinaryExperiment.N2)
    (b3 : BinaryExperiment.N3) (b4 : BinaryExperiment.N4) (b5 : BinaryExperiment.N5)
    (h1 : N1) (h2 : N2) : Target := by
  intro hall
  obtain ⟨E, PiSet, hS, hP, hU, hneg⟩ := assemble_witness b1 b2 b3 b4 b5 h1 h2
  have h := hall E hS PiSet hP hU
  exact hneg (by simpa using h)

end

end AronowAudit.P006.Wave1.TTAlignment
