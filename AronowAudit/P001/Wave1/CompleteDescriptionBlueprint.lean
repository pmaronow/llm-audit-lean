import AronowAudit.P001.P001_Foundations

/-!
# Blueprint: refutation of `AronowAudit.P001.printed_complete_description_implies_ignorability`

Record 4 of group P001a: P001-T105 /
`AronowAudit.P001.printed_complete_description_implies_ignorability`; resolution `refute`.
Frozen contract (P001_Foundations.lean:5149): on every probability space, for measurable
covariates `X`, treatment `D` and voter preference `U`, and any vote-share rule
`m (X, d, U)` measurable and valued in `[0,100]` for `d = 0, 1`, the potential-outcome pair
`(m(X,0,U), m(X,1,U))` is conditionally independent (`CI`) of `D` given `X`.

`Target` is the negation of exactly that contract with `Ω E : Type` (universe 0); the
`example` checks by `Iff.rfl` that it is the negation of the frozen type at universe 0.

Witness (paper proof, record 4): `Ω = Fin 4` with masses `(3/8, 1/8, 1/8, 3/8)`
(`finiteLawMeasure binaryJoint`), `E = ℝ`, `X = 0`, `U = electorateU = (0,0,1,1)`,
`D = electorateD = (0,1,0,1)`, `m x d u = 20 + 40u + 5d`. The pair equals `(60,65)` on
atoms `2, 3` (mass `1/2`), `D = 1` on atoms `1, 3` (mass `1/2`), but both hold only on
atom `3` (mass `3/8 ≠ 1/4`). With constant `X`, `CI` reduces to ordinary independence of
events (node `N1`). The information-completeness interpretation (voters use only the
leaflet and their own preferences) is the validator's model fixed in the dossier; it is
verified separately by the proved `electorate_information_complete` and is not part of the
frozen Lean contract.

Writers prove `theorem nk_proof : Nk` in
`AronowAudit/P001/Wave1/CompleteDescription/Nk.lean`.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.CompleteDescription

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The frozen statement to be resolved: the negation of the exact recorded contract
`printed_complete_description_implies_ignorability` (universe 0). -/
def Target : Prop :=
  ¬ ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X) (D U : Ω → ℝ),
    Measurable D → Measurable U → ∀ (m : E → ℝ → ℝ → ℝ),
    Measurable (fun ω => m (X ω) 0 (U ω)) → Measurable (fun ω => m (X ω) 1 (U ω)) →
    (∀ ω, m (X ω) 0 (U ω) ∈ Set.Icc (0 : ℝ) 100 ∧ m (X ω) 1 (U ω) ∈ Set.Icc (0 : ℝ) 100) →
    CI μ X hX (fun ω => (m (X ω) 0 (U ω), m (X ω) 1 (U ω))) D

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration, universe 0).
Only the frozen theorem's *type* is read; its `sorry` proof is never used. -/
example : Target ↔
    ¬ (type_of% @AronowAudit.P001.printed_complete_description_implies_ignorability.{0, 0}) :=
  Iff.rfl

/-- The witness law on `Fin 4`: masses `3/8, 1/8, 1/8, 3/8`. -/
abbrev electorateLaw : Measure (Fin 4) := finiteLawMeasure binaryJoint

/-- The witness vote-share rule `m(x, d, u) = 20 + 40u + 5d`. -/
def voteRule : ℝ → ℝ → ℝ → ℝ := fun _ d u => 20 + 40 * u + 5 * d

/-- The potential-outcome pair `(m(X,0,U), m(X,1,U))` of the witness, with `X = 0`. -/
def potentialPair : Fin 4 → ℝ × ℝ :=
  fun i => (voteRule 0 0 (electorateU i), voteRule 0 1 (electorateU i))

/-- **Node N1** (paper proof, record 4, third paragraph: "Conditioning on the constant X
leaves unconditional probabilities unchanged: σ(X) is the trivial sigma-field, so each
conditional expectation of an indicator is its probability almost everywhere ... If CI held,
its definition at these measurable sets would give 3/8=(1/2)(1/2)"). For a constant
covariate, `CI` implies ordinary product factorization of event probabilities.
Suggested route: `MeasurableSpace.comap_const` (comap of a constant map is `⊥`),
`MeasureTheory.condExp_bot` (`μ[f|⊥] = fun _ => ∫ f ∂μ` for a probability measure), then an
a.e. equality of constants on a probability space is an equality
(`Filter.EventuallyEq.eventually`, `ae_neBot`/`Filter.Eventually.exists`); finally
`integral_indicator_one`-type lemmas: `∫ (if ω ∈ S then 1 else 0) = μ.real S`
(`integral_ite`, `integral_indicator`, `Measure.real`). -/
def N1 : Prop :=
  ∀ {Ω E F G : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace G] (μ : Measure Ω) [IsProbabilityMeasure μ] (e : E)
    (Y : Ω → F) (Z : Ω → G), Measurable Y → Measurable Z →
    CI μ (fun _ => e) measurable_const Y Z →
    ∀ (A : Set F) (B : Set G), MeasurableSet A → MeasurableSet B →
      (μ (Y ⁻¹' A ∩ Z ⁻¹' B)).toReal = (μ (Y ⁻¹' A)).toReal * (μ (Z ⁻¹' B)).toReal

/-- **Node N2** (paper proof, record 4, first and third paragraphs: "On atoms i=0,1,2,3
assign masses (3/8,1/8,1/8,3/8), all positive with sum one ... P(A)=1/2, P(B)=1/2, but
P(A∩B)=3/8 (atom 3)"). The witness law is a probability measure and the three event
probabilities are `3/8`, `1/2`, `1/2`.
Suggested route: `finiteLawMeasure`, `Measure.coe_finset_sum`/`Measure.finset_sum_apply`,
`Measure.smul_apply`, `Measure.dirac_apply'` (all sets of `Fin 4` are measurable),
`Fin.sum_univ_four`, `binaryJoint` weights `![3/8,1/8,1/8,3/8]`, `ENNReal.ofReal` arithmetic
via `ENNReal.toReal_sum`/`ENNReal.toReal_ofReal`; the preimages are computed by
`fin_cases`/`decide` on `electorateU`, `electorateD`. -/
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

/-- The nodes suffice: specialize the frozen contract to the electorate witness; `N1`
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

/-- Nonvacuity record: every hypothesis of the frozen contract holds at the witness
(measurability is automatic on `Fin 4`; the bounds are `voteRule_bounds`), and both
treatment arms have positive mass `1/2` (given `N2`). -/
example (h2 : N2) :
    IsProbabilityMeasure electorateLaw ∧ Measurable electorateD ∧ Measurable electorateU ∧
    (∀ i, voteRule 0 0 (electorateU i) ∈ Set.Icc (0 : ℝ) 100 ∧
      voteRule 0 1 (electorateU i) ∈ Set.Icc (0 : ℝ) 100) ∧
    (electorateLaw (electorateD ⁻¹' {1})).toReal = 1/2 :=
  ⟨h2.1, fin4_measurable _, fin4_measurable _, voteRule_bounds, h2.2.2.2⟩

end

end AronowAudit.P001.Wave1.CompleteDescription
