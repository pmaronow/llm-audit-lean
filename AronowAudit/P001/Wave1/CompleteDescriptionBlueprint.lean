import AronowAudit.P001.P001_Foundations

/-!
# Counterexample to complete description implying ignorability (P001-T105)

The assertion under consideration is that, on every probability space, for
measurable covariates `X`, treatment `D`, and voter preference `U`, and any
vote-share rule `m (X, d, U)` measurable and valued in `[0,100]` for `d = 0, 1`,
the potential-outcome pair `(m(X,0,U), m(X,1,U))` is conditionally independent
of `D` given `X`. `Target` is the negation of this assertion in universe 0.

The witness is `Ω = Fin 4` with masses `(3/8, 1/8, 1/8, 3/8)`, `E = ℝ`,
`X = 0`, `U = electorateU = (0,0,1,1)`, `D = electorateD = (0,1,0,1)`,
and `m x d u = 20 + 40u + 5d`. The pair equals `(60,65)` on atoms `2, 3`
(mass `1/2`), and `D = 1` on atoms `1, 3` (mass `1/2`), but both hold only
on atom `3` (mass `3/8 ≠ 1/4`). With constant `X`, conditional independence
implies ordinary independence of events (`N1`). `N2` gives these event probabilities.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.CompleteDescription

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Negation of the universal assertion that a measurable bounded vote-share
rule implies conditional ignorability (universe 0). -/
def Target : Prop :=
  ¬ ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X) (D U : Ω → ℝ),
    Measurable D → Measurable U → ∀ (m : E → ℝ → ℝ → ℝ),
    Measurable (fun ω => m (X ω) 0 (U ω)) → Measurable (fun ω => m (X ω) 1 (U ω)) →
    (∀ ω, m (X ω) 0 (U ω) ∈ Set.Icc (0 : ℝ) 100 ∧ m (X ω) 1 (U ω) ∈ Set.Icc (0 : ℝ) 100) →
    CI μ X hX (fun ω => (m (X ω) 0 (U ω), m (X ω) 1 (U ω))) D

/-- The witness law on `Fin 4`: masses `3/8, 1/8, 1/8, 3/8`. -/
abbrev electorateLaw : Measure (Fin 4) := finiteLawMeasure binaryJoint

/-- The witness vote-share rule `m(x, d, u) = 20 + 40u + 5d`. -/
def voteRule : ℝ → ℝ → ℝ → ℝ := fun _ d u => 20 + 40 * u + 5 * d

/-- The potential-outcome pair `(m(X,0,U), m(X,1,U))` of the witness, with `X = 0`. -/
def potentialPair : Fin 4 → ℝ × ℝ :=
  fun i => (voteRule 0 0 (electorateU i), voteRule 0 1 (electorateU i))

/-- For a constant covariate, `CI` implies ordinary product factorization of
event probabilities. The covariate generates the trivial sigma-field, so each
conditional expectation of an indicator is its probability almost everywhere.
An a.e. equality of constants on a probability space is an equality; integrating
the indicators therefore gives the product equation. -/
def N1 : Prop :=
  ∀ {Ω E F G : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace G] (μ : Measure Ω) [IsProbabilityMeasure μ] (e : E)
    (Y : Ω → F) (Z : Ω → G), Measurable Y → Measurable Z →
    CI μ (fun _ => e) measurable_const Y Z →
    ∀ (A : Set F) (B : Set G), MeasurableSet A → MeasurableSet B →
      (μ (Y ⁻¹' A ∩ Z ⁻¹' B)).toReal = (μ (Y ⁻¹' A)).toReal * (μ (Z ⁻¹' B)).toReal

/-- The witness law is a probability measure and the intersection and marginal
event probabilities are `3/8`, `1/2`, `1/2`.
Atoms `0,1,2,3` have positive masses `(3/8,1/8,1/8,3/8)` summing to one;
the intersection is atom `3`. The finite atomic law permits direct summation,
with the preimages computed from `electorateU`, `electorateD`. -/
def N2 : Prop :=
  IsProbabilityMeasure electorateLaw ∧
    (electorateLaw (potentialPair ⁻¹' {(60, 65)} ∩ electorateD ⁻¹' {1})).toReal = 3/8 ∧
    (electorateLaw (potentialPair ⁻¹' {(60, 65)})).toReal = 1/2 ∧
    (electorateLaw (electorateD ⁻¹' {1})).toReal = 1/2

/-- Every real function on `Fin 4` is measurable (discrete σ-algebra). -/
theorem fin4_measurable {β : Type} [MeasurableSpace β] (f : Fin 4 → β) : Measurable f :=
  measurable_of_countable f

/-- The witness respects the `[0,100]` bounds of the contract at every atom. -/
theorem voteRule_bounds (i : Fin 4) :
    voteRule 0 0 (electorateU i) ∈ Set.Icc (0 : ℝ) 100 ∧
      voteRule 0 1 (electorateU i) ∈ Set.Icc (0 : ℝ) 100 := by
  fin_cases i <;> norm_num [voteRule, electorateU]

/-- Specializing the universal assertion to the electorate witness, `N1`
turns its `CI` conclusion into `3/8 = (1/2)(1/2)`, contradicting `N2`. -/
theorem assemble (h1 : N1) (h2 : N2) : Target := by
  intro H
  obtain ⟨hprob, hAB, hA, hB⟩ := h2
  have hci := @H (Fin 4) ℝ _ _ electorateLaw hprob (fun _ => (0 : ℝ)) measurable_const
    electorateD electorateU (fin4_measurable _) (fin4_measurable _) voteRule
    (fin4_measurable _) (fin4_measurable _) voteRule_bounds
  have key := @h1 (Fin 4) ℝ (ℝ × ℝ) ℝ _ _ _ _ electorateLaw hprob 0 potentialPair
    electorateD (fin4_measurable _) (fin4_measurable _) hci {(60, 65)} {1}
    (measurableSet_singleton _) (measurableSet_singleton _)
  rw [hAB, hA, hB] at key
  norm_num at key

end

end AronowAudit.P001.Wave1.CompleteDescription
