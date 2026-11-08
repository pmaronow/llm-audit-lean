import AronowAudit.P006.Wave1.BinaryExperimentBlueprint

/-!
# Blueprint: P006-T27, refutation of `T27_printed_TT_alignment`

Wave 1, group P005-P006-P017-P023-P046-P047. Resolution `refute` (mapper §5, accepted by both
referees with no fixes).

The frozen record `AronowAudit.P006.T27_printed_TT_alignment`
(P006_CounterfactualMetrics.lean, line 877) asserts Propositions 9 and 3 as printed (PDF
pp. 5, 17–18) under fixed-query unbiasedness only. `Target` is the negation of its universe-0
instance (checked by `rfl`).

Witness (mapper): the one-unit experiment `BinaryExperiment.binExp 1 _ (fun _ => 1/2) μhat`
with the random baseline `μhat π ω x = estA (X ω) x` (witness A of T4): its mean is `0 = μ0 x`
at every fixed query `x`, but it equals `1` at the unit's own covariate. With
`PiSet = {π | Admissible π}`, the actual rewards are `expectedTT π = -(π false + π true)/4` and
`V π = (π false + π true)/4`, so the first printed clause fails at `π ≡ 1` (`-1/2 ≠ 1/2`).
The mapper used `Ω = Bool × Bool`; here `Ω = Fin 1 → Bool × Bool` (same law).

Writers: prove `theorem nk_proof : Nk` in `AronowAudit/P006/Wave1/TTAlignment/Nk.lean`.
The shared nodes `BinaryExperiment.N1`–`N5` are proved in `AronowAudit/P006/Wave1/BinaryExperiment/`.
-/

set_option autoImplicit false

namespace AronowAudit.P006.Wave1.TTAlignment

open AronowAudit.P006 AronowAudit.P006.Wave1.BinaryExperiment MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-! ## Frozen target -/

/-- **Target (P006-T27).** The exact negation of the frozen printed contract
`T27_printed_TT_alignment` (Propositions 9 and 3 as printed), universe-0 instance. -/
def Target : Prop :=
  ¬ ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n),
      Standing E → ∀ (PiSet : Set (C → ℝ)), (∀ π ∈ PiSet, Admissible π) →
      PointwiseUnbiased E PiSet →
      (∀ π ∈ PiSet, E.expectedTT π = (n : ℝ) * E.V π) ∧
      (∀ π, IsBest PiSet E.expectedTT π ↔ IsBest PiSet E.V π) ∧
      (∀ π, IsBest PiSet E.expectedTT π → regret PiSet E.V π = 0) ∧
      (PiSet = {π | Admissible π} → IsBest PiSet E.expectedTT (positiveRule E.τ))

/-- The one-unit witness experiment (mapper §5, witness A of T4). -/
def E27 : Experiment (Fin 1 → Bool × Bool) Bool 1 :=
  binExp 1 (by norm_num) (fun _ => 1 / 2) (fun _ ω x => estA (ω 0).1 x)

/-- The mapper's explicit-witness statement (stronger presentation of `Target`). -/
def Witness : Prop :=
  ∃ (E : Experiment (Fin 1 → Bool × Bool) Bool 1) (PiSet : Set (Bool → ℝ)),
    Standing E ∧ (∀ π ∈ PiSet, Admissible π) ∧ PointwiseUnbiased E PiSet ∧
    ¬ ((∀ π ∈ PiSet, E.expectedTT π = (1 : ℝ) * E.V π) ∧
       (∀ π, IsBest PiSet E.expectedTT π ↔ IsBest PiSet E.V π) ∧
       (∀ π, IsBest PiSet E.expectedTT π → regret PiSet E.V π = 0) ∧
       (PiSet = {π | Admissible π} → IsBest PiSet E.expectedTT (positiveRule E.τ)))

/-! ## Node statements -/

/-- **Statement S1** (mapper §5 step 1, "For each fixed query x, the event X=x has probability
1/2 regardless of π; therefore the two estimator values ±1 have mean zero"): fixed-query
unbiasedness of the witness baseline, with integrability. Use `BinaryExperiment.S2` and
`Integrable.of_finite`. -/
def S1 : Prop :=
  ∀ π : Bool → ℝ, Admissible π → ∀ x : Bool,
    Integrable (fun ω => E27.μhat π ω x) (E27.law π) ∧ ∫ ω, E27.μhat π ω x ∂E27.law π = 0

/-- **Statement S2** (mapper §5 step 2, "μhatπ(ω,X(ω))=1 on every state ... E.expectedTT(π)=
E[T(1/2-1)]=-(u+v)/4, E.V(π)=E[T(1/2-0)]=(u+v)/4"): the actual reward and welfare functionals.
Use `BinaryExperiment.S2`, `oneTT_formula`/`witnesses_AB_formula` arithmetic, and
`Fin.sum_univ_one` with the reindexing `Fintype.sum_equiv (Equiv.funUnique (Fin 1) _)` of
`Fin 1 → Bool × Bool`. -/
def S2 : Prop :=
  ∀ π : Bool → ℝ, Admissible π →
    E27.expectedTT π = -(π false + π true) / 4 ∧ E27.V π = (π false + π true) / 4

/-! ## Nodes -/

/-- Node N1: may use the shared statements `BinaryExperiment.S1`, `BinaryExperiment.S2`. -/
def N1 : Prop := BinaryExperiment.S1 → BinaryExperiment.S2 → S1
/-- Node N2: may use the shared statements `BinaryExperiment.S1`, `BinaryExperiment.S2`. -/
def N2 : Prop := BinaryExperiment.S1 → BinaryExperiment.S2 → S2

/-! ## Assembly -/

/-- **Witness assembly.** -/
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

/-- **Assembly.** The nodes suffice for the refutation. -/
theorem assemble (b1 : BinaryExperiment.N1) (b2 : BinaryExperiment.N2)
    (b3 : BinaryExperiment.N3) (b4 : BinaryExperiment.N4) (b5 : BinaryExperiment.N5)
    (h1 : N1) (h2 : N2) : Target := by
  intro hall
  obtain ⟨E, PiSet, hS, hP, hU, hneg⟩ := assemble_witness b1 b2 b3 b4 b5 h1 h2
  have h := hall E hS PiSet hP hU
  exact hneg (by simpa using h)

/-- Fidelity check: `Target` is literally the negation of the universe-0 instance of the frozen
statement `AronowAudit.P006.T27_printed_TT_alignment` (only its type is read). -/
example : Target = ¬ (type_of% @AronowAudit.P006.T27_printed_TT_alignment.{0, 0}) := rfl

end

end AronowAudit.P006.Wave1.TTAlignment
