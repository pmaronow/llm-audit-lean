import AronowAudit.P001.P001_Foundations

/-!
# P001-T32: a continuous random variable whose range contains no interval

Section 1.2.4, p. 24 (PDF p. 42), paragraph before Definition 1.2.14, corrected:
a continuous random variable has uncountable range and uncountable sample space,
and its range need not contain an interval of positive length.

Take the sample space to be the subtype `C = [0, 1/2] \ ℚ` itself, with law
`ν = 2 • volume.comap (↑)`. The inclusion has range exactly `C` and density
`2 · 1_C`. In contrast, the identity on all of `ℝ` has range `ℝ` even when its
law is concentrated on `C`.
-/

namespace AronowAudit.P001.Wave1.IrrationalRange

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

/-- (i) Every real random variable with a PDF has null fibres, uncountable range and uncountable sample space; (ii) for
`C = [0,1/2] \ ℚ` there is a probability law on the subtype `C` whose inclusion is a measurable
random variable with range exactly `C`, density `2 · 1_C`, and no nondegenerate closed
interval inside its range. -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ), Measurable X → ∀ (f : ℝ → ℝ), HasPDF (μ.map X) f →
    (∀ t : ℝ, μ {ω | X ω = t} = 0) ∧
    ¬ (Set.range X).Countable ∧ ¬ Countable Ω ∧
    (let C : Set ℝ := Set.Icc (0 : ℝ) (1 / 2) \ Set.range (fun q : ℚ => (q : ℝ))
     ∃ ν : Measure C,
       MeasurableSet C ∧ volume C = 1 / 2 ∧ IsProbabilityMeasure ν ∧
       Measurable (fun x : C => (x : ℝ)) ∧
       Set.range (fun x : C => (x : ℝ)) = C ∧
       HasPDF (ν.map (fun x : C => (x : ℝ))) (fun x => if x ∈ C then 2 else 0) ∧
       ¬ C.Countable ∧ ¬ Countable C ∧
       ∀ a b : ℝ, a < b → ¬ Set.Icc a b ⊆ Set.range (fun x : C => (x : ℝ)))

/-- The set `C = [0, 1/2] \ ℚ` (the irrationals of `[0, 1/2]`). -/
def irrHalf : Set ℝ := Set.Icc (0 : ℝ) (1 / 2) \ Set.range (fun q : ℚ => (q : ℝ))

/-- The sample-space law on the subtype `C`: twice the pullback of Lebesgue measure along the
inclusion. -/
def irrHalfLaw : Measure irrHalf := (2 : ℝ≥0∞) • volume.comap (fun x : irrHalf => (x : ℝ))

/-- The density `2 · 1_C`, written exactly as in `Target` (with the set spelled out) so that
its `Decidable` instance (`Set.decidableSdiff`) is the one elaborated in `Target`; then
`fun x => if x ∈ C then 2 else 0` in `Target` is definitionally `irrHalfDensity`. -/
def irrHalfDensity (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (0 : ℝ) (1 / 2) \ Set.range (fun q : ℚ => (q : ℝ)) then 2 else 0

/-- The rationals are countable, Borel and Lebesgue-null, hence `C` is Borel and
`λ(C) = λ([0,1/2]) = 1/2`. For `a < b`, a rational `q ∈ (a,b)` lies in `[a,b]` but not in
`C`. -/
def N1 : Prop :=
  MeasurableSet irrHalf ∧ volume irrHalf = 1 / 2 ∧
    ∀ a b : ℝ, a < b → ¬ Set.Icc a b ⊆ irrHalf

/-- For every Borel `A`, `(ν map j)(A) = 2 λ(A ∩ C)`; this is exactly
the measure with density `2 · 1_C`, by `map_comap_subtype_coe`. The `if` in
`irrHalfDensity` carries the instance `Set.decidableSdiff`, while an `if x ∈ irrHalf` written
in a file with the local classical instance carries another; relate them with
`simp only [irrHalfDensity, irrHalf]`/`split_ifs`/`by_cases`, never `rfl`. -/
def N2 : Prop :=
  irrHalfLaw.map (fun x : irrHalf => (x : ℝ)) =
    volume.withDensity (fun x => ENNReal.ofReal (irrHalfDensity x))

/-- The subtype law is a probability measure: `ν(C) = 2 λ(C) = 1`. -/
def N3 : Prop := IsProbabilityMeasure irrHalfLaw

/-- The density is Borel, nonnegative and integrable, with integral `2 λ(C) = 1`.
This proposition supplies the measurability and integrability clauses of `HasPDF`. -/
def N4 : Prop := AEMeasurable irrHalfDensity volume ∧ Integrable irrHalfDensity volume

/-- The four propositions imply `Target`. Clause (i) follows from
`continuous_rv_range_uncountable`; the range of the inclusion is `Subtype.range_coe`; `C` is uncountable because a countable set is
Lebesgue-null while `λ(C) = 1/2`; the type-level statement is `Set.countable_coe_iff`. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) : Target.{u} := by
  intro Ω _ μ _ X hX f hf
  obtain ⟨g1, g2, g3⟩ := continuous_rv_range_uncountable μ X hX f hf
  refine ⟨g1, g2, g3, ?_⟩
  obtain ⟨hC, hvol, hint⟩ := h1
  have hunc : ¬ irrHalf.Countable := fun hc => by
    have h0 := hc.measure_zero volume
    rw [hvol] at h0
    norm_num at h0
  have hdens : ∀ x, 0 ≤ irrHalfDensity x := fun x => by
    unfold irrHalfDensity
    split_ifs <;> norm_num
  refine ⟨irrHalfLaw, hC, hvol, h3, measurable_subtype_coe, Subtype.range_coe,
    ⟨h4.1, hdens, h4.2, h2⟩, hunc,
    fun h => hunc (Set.countable_coe_iff.mp h), ?_⟩
  intro a b hab
  rw [Subtype.range_coe]
  exact hint a b hab

/- Satisfiable instance of the general hypotheses: `Ω = ℝ` with the unit-uniform
law, `X = id`, `f = 1_{[0,1]}`; alternatively the witness itself, `Ω = C`, `μ = irrHalfLaw`,
`X = (↑)`, `f = 2 · 1_C` (by N2–N4). -/

end
end AronowAudit.P001.Wave1.IrrationalRange
