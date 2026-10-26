import AronowAudit.P001.P001_Foundations

/-!
# Total probability over finite or countable partitions (P001-T24)

Theorem 1.1.13 (Law of Total Probability), p. 12 (PDF p. 30), with footnote 12
allowing finite or countably infinite partitions; the strict positivity requirement
`P(Aᵢ) > 0`; the partition remark, p. 13 (PDF p. 31);
and Definition 1.1.8 (conditional probability only for `P(A) > 0`), p. 10.

The partition may be indexed by any countable type. The conclusions include the
binary complement decomposition and the nonemptiness criterion for `{C, Cᶜ}`.
The weak inequality `0 ≤ P(∅)` does not supply the positivity required by Definition 1.1.8.
-/

namespace AronowAudit.P001.Wave1.TotalProbabilityCountable

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u v

/-- Total probability and the complement partition: for a nonempty
measurable partition indexed by any countable type, (i) `P(B) = ∑ᵢ P(B ∩ Aᵢ)`; (ii) with
strictly positive cell masses, `P(B) = ∑ᵢ P(B|Aᵢ)P(Aᵢ)`; (iii) for every measurable `C`,
`{C, Cᶜ}` has two nonempty cells iff `C ≠ ∅, Ω`, and `P(B) = P(B ∩ C) + P(B ∩ Cᶜ)`;
(iv) `P(∅) ≥ 0` holds but `P(∅) > 0` fails. -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type v} [Countable ι] (A : ι → Set Ω),
    (∀ i, MeasurableSet (A i)) → (∀ i, (A i).Nonempty) →
    Pairwise (fun i j => Disjoint (A i) (A j)) → (⋃ i, A i) = Set.univ →
    ∀ (B : Set Ω), MeasurableSet B →
    (prob μ B = ∑' i, prob μ (B ∩ A i)) ∧
    ((∀ i, 0 < prob μ (A i)) →
      prob μ B = ∑' i, (prob μ (B ∩ A i) / prob μ (A i)) * prob μ (A i)) ∧
    (∀ C : Set Ω, MeasurableSet C →
      ((C.Nonempty ∧ Cᶜ.Nonempty) ↔ C ≠ ∅ ∧ C ≠ Set.univ) ∧
      prob μ B = prob μ (B ∩ C) + prob μ (B ∩ Cᶜ)) ∧
    (0 ≤ prob μ (∅ : Set Ω) ∧ ¬ 0 < prob μ (∅ : Set Ω))

/-- For measurable `C` and arbitrary `B`, measurable-set splitting gives the binary
probability formula, including `C = ∅` and `C = Ω` (Example 1.1.11, p. 13).
`B` need not be measurable. -/
def N1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B C : Set Ω), MeasurableSet C →
    prob μ B = prob μ (B ∩ C) + prob μ (B ∩ Cᶜ)

/-- The countable partition identity, the nonemptiness criterion, `N1`, and
`P(∅) = 0` give the four conclusions. -/
theorem assemble (h1 : N1.{u}) : Target.{u, v} := by
  intro Ω _ μ _ ι _ A hA hne hdis hcover B hB
  obtain ⟨hsum, hcond⟩ := total_probability_partition μ A hA hne hdis hcover B hB
  refine ⟨hsum, hcond, fun C hC => ⟨two_event_partition_nonempty C, h1 μ B C hC⟩, ?_⟩
  simp [prob]

/- Satisfiable instance of the hypotheses: `Ω = Bool` with the full
σ-algebra and mass `1/2` at each point, `ι = Bool`, `A i = {i}`, `B = {true}`; the cells are
measurable, nonempty, disjoint, cover `Ω` and have positive mass. For a nonempty null cell:
the unit-uniform law on `ℝ` with cells `{0}` and `ℝ \ {0}`. -/

end
end AronowAudit.P001.Wave1.TotalProbabilityCountable
