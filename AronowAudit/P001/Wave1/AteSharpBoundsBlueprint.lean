import AronowAudit.P001.P001_Foundations

/-!
# Blueprint: sharp ATE bounds with the printed endpoints, paper support (P001-T114)

Record 15 of group P001a: P001-T114 / held `AronowAudit.P001.ate_sharp_bounds_and_width`;
resolution `repair_and_prove`. Theorem 7.1.7 (p. 241, proof pp. 241-242), width
pp. 242-243, sharpness p. 244. The held theorem (:4338) is proved but constrains null points
(pointwise bounds and binary values), allows a constant `D`, uses imputed endpoint integrals
and demands pointwise equality of the observed outcome. The repair (mapper's
`ate_sharp_paper_bounds_same_observable_law`): a.e. bounds and binary values, both arms in
support (`hD0`, `hD1`), the printed conditional-arm endpoints `L`, `U`, the width `b - a`,
and sharpness at every `c ∈ [L, U]` with the same observable joint law of `(Y, D)`.

Write `l = ateLower Y D a b`, `u = ateUpper Y D a b` (imputed endpoints, :508, :510).
Nodes: `N1` (imputed means are the printed endpoints), `N2` (interval and width),
`N3` (every value is attained with the same observable law). The held proof (:4338) and the
lower-endpoint helper `bound_endpoint_formula` (:10304, pointwise binary) are patterns only.
Writers prove `theorem nk_proof : Nk` in `AronowAudit/P001/Wave1/AteSharpBounds/Nk.lean`.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.AteSharpBounds

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The frozen statement the record is resolved by (mapper's
`AronowAudit.P001.Wave1.ate_sharp_paper_bounds_same_observable_law`). -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : Ω → ℝ), Measurable Y0 → Measurable Y1 → Measurable D → ∀ (a b : ℝ),
    (∀ᵐ ω ∂μ, Y0 ω ∈ Set.Icc a b ∧ Y1 ω ∈ Set.Icc a b) →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    0 < prob μ {ω | D ω = 0} → 0 < prob μ {ω | D ω = 1} →
    let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
    let L := conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} + a * prob μ {ω | D ω = 0} -
      (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} + b * prob μ {ω | D ω = 1})
    let U := conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} + b * prob μ {ω | D ω = 0} -
      (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} + a * prob μ {ω | D ω = 1})
    mean μ (fun ω => Y1 ω - Y0 ω) ∈ Set.Icc L U ∧ U - L = b - a ∧
    ∀ c ∈ Set.Icc L U, ∃ Z0 Z1 : Ω → ℝ,
      Measurable Z0 ∧ Measurable Z1 ∧
      (∀ᵐ ω ∂μ, Z0 ω ∈ Set.Icc a b ∧ Z1 ω ∈ Set.Icc a b) ∧
      μ.map (fun ω => (observedOutcome (Z0 ω) (Z1 ω) (D ω), D ω)) =
        μ.map (fun ω => (Y ω, D ω)) ∧
      mean μ (fun ω => Z1 ω - Z0 ω) = c

/-- **Node N1** (paper proof, record 15, first two paragraphs: "By the definition of
conditionalMeanAt, E[Y1_{D=d}]=E[Y|D=d]P_d; the cancellation is legitimate because P_d>0
... Integrating the event decompositions and using the conditional-arm identities gives
E[l]=L and E[u]=U, with exactly the printed formulas"; "Shared lemmas" item 8). For any
integrable observed outcome and a.e. binary `D` with both arms of positive mass, the imputed
endpoint means are the printed conditional-arm endpoints.
Suggested route: follow `bound_endpoint_formula` (:10304) but with a.e. binary `D`:
`D = 1_{D=1}` and `1 - D = 1_{D=0}` a.e.; `integral_congr_ae`, `integral_indicator`,
`integral_add`/`integral_sub`/`integral_mul_left`; `conditionalMeanAt` (:690) times
`prob` cancels by `div_mul_cancel₀` with `hD0.ne'`, `hD1.ne'`. -/
def N1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y D : Ω → ℝ), Integrable Y μ → Measurable D → (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    0 < prob μ {ω | D ω = 0} → 0 < prob μ {ω | D ω = 1} → ∀ (a b : ℝ),
    mean μ (fun ω => ateLower (Y ω) (D ω) a b) =
        conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} + a * prob μ {ω | D ω = 0} -
          (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} + b * prob μ {ω | D ω = 1}) ∧
    mean μ (fun ω => ateUpper (Y ω) (D ω) a b) =
        conditionalMeanAt μ D Y 1 * prob μ {ω | D ω = 1} + b * prob μ {ω | D ω = 0} -
          (conditionalMeanAt μ D Y 0 * prob μ {ω | D ω = 0} + a * prob μ {ω | D ω = 1})

/-- **Node N2** (paper proof, record 15, first two paragraphs: "There is a probability-one
set on which Y0,Y1∈[a,b] and D∈{0,1}. It is nonempty, so a≤b ... Splitting into D=0 and
D=1 shows l≤Y1-Y0≤u almost surely ... Also u-l=b-a almost surely, so U-L=E[b-a]=b-a").
Integrability of the observed outcome, interval membership and width for the imputed
endpoints, under a.e. bounds and a.e. binary `D`.
Suggested route: the held proof (:4338) with every pointwise step replaced by
`filter_upwards [hbound, hbinary]`; `Integrable.of_bound` with the a.e. bound;
`integral_mono_ae`; `integral_congr_ae` for `u - l = b - a`. -/
def N2 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : Ω → ℝ), Measurable Y0 → Measurable Y1 → Measurable D → ∀ (a b : ℝ),
    (∀ᵐ ω ∂μ, Y0 ω ∈ Set.Icc a b ∧ Y1 ω ∈ Set.Icc a b) →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    Integrable (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) μ ∧
    mean μ (fun ω => Y1 ω - Y0 ω) ∈ Set.Icc
      (mean μ (fun ω => ateLower (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b))
      (mean μ (fun ω => ateUpper (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b)) ∧
    mean μ (fun ω => ateUpper (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b) -
      mean μ (fun ω => ateLower (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b) = b - a

/-- **Node N3** (paper proof, record 15, third paragraph: "Fix c∈[L,U] and set q=a+c-L ...
Z0=Y0(1-D)+(a+b-q)D, Z1=Y1D+q(1-D) ... both completions lie in [a,b] almost surely, and
their observed outcome agrees almost surely with Y, with D unchanged. The measurable
observable pairs therefore have the same pushforward law ... Hence E[Z1-Z0]=L+(c-L)=c. This
works without division by b-a"). Every value between the imputed endpoint means is the ATE
of a bounded completion with the same observable law.
Suggested route: the held construction (:4338, its two completions) with a.e. reasoning;
`Measure.map_congr` for a.e.-equal measurable maps (`Measurable.prodMk`); `a ≤ b` from the
a.e. bounds on a probability space; `integral_congr_ae` and `integral_add` for the mean. -/
def N3 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : Ω → ℝ), Measurable Y0 → Measurable Y1 → Measurable D → ∀ (a b : ℝ),
    (∀ᵐ ω ∂μ, Y0 ω ∈ Set.Icc a b ∧ Y1 ω ∈ Set.Icc a b) →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    ∀ c ∈ Set.Icc
      (mean μ (fun ω => ateLower (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b))
      (mean μ (fun ω => ateUpper (observedOutcome (Y0 ω) (Y1 ω) (D ω)) (D ω) a b)),
    ∃ Z0 Z1 : Ω → ℝ,
      Measurable Z0 ∧ Measurable Z1 ∧
      (∀ᵐ ω ∂μ, Z0 ω ∈ Set.Icc a b ∧ Z1 ω ∈ Set.Icc a b) ∧
      μ.map (fun ω => (observedOutcome (Z0 ω) (Z1 ω) (D ω), D ω)) =
        μ.map (fun ω => (observedOutcome (Y0 ω) (Y1 ω) (D ω), D ω)) ∧
      mean μ (fun ω => Z1 ω - Z0 ω) = c

/-- The nodes suffice: `N2` gives integrability, interval and width for the imputed
endpoints, `N1` identifies them with the printed `L`, `U`, and `N3` gives sharpness. -/
theorem assemble (h1 : N1.{u}) (h2 : N2.{u}) (h3 : N3.{u}) : Target.{u} := by
  intro Ω _ μ _ Y0 Y1 D hY0 hY1 hD a b hbound hbin hD0 hD1 Y L U
  obtain ⟨hYi, hmem, hwidth⟩ := h2 μ Y0 Y1 D hY0 hY1 hD a b hbound hbin
  obtain ⟨hl, hu⟩ := h1 μ Y D hYi hD hbin hD0 hD1 a b
  have hl' : mean μ (fun ω => ateLower (Y ω) (D ω) a b) = L := hl
  have hu' : mean μ (fun ω => ateUpper (Y ω) (D ω) a b) = U := hu
  refine ⟨?_, ?_, ?_⟩
  · rw [← hl', ← hu']; exact hmem
  · rw [← hl', ← hu']; exact hwidth
  · intro c hc
    rw [← hl', ← hu'] at hc
    exact h3 μ Y0 Y1 D hY0 hY1 hD a b hbound hbin c hc

end

end AronowAudit.P001.Wave1.AteSharpBounds
