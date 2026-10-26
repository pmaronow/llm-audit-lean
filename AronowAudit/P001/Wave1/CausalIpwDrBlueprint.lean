import AronowAudit.P001.Wave1.MarSelectionBlueprint

/-!
# IPW and double robustness under strong ignorability (P001-T117)

Theorem 7.2.5 (p. 265, proof pp. 265-266) and Theorem 7.2.8
(pp. 267-268, proof pp. 268-269). IPW follows from strong ignorability;
the nuisance functions and both correctness alternatives are quantified inside
the double-robustness conjunct. The statement includes `Supp[D] = {0,1}`
and a.e. binary values, overlap, and bounds.

The shared arm identity is applied with `U = (Y0, Y1)` to the treated arm
(`R = D`, propensity `p`, `V = Y1`, `Z = Y`) and to the control arm
(`R = 1 - D`, propensity `1 - p`, weight `1 - q`, `V = Y0`, `Z = Y`).
IPW is the case `m = 0`, `q = p` of the second correctness alternative.
`N1` transfers conditional independence to `1 - D`, and `N2` transfers
the propensity CEF to `1 - D`.
-/

set_option autoImplicit false

universe u v w

namespace AronowAudit.P001.Wave1.CausalIpwDr

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- IPW and double robustness with both treatment arms in support and
a.e. binary values, overlap, and bounds. -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin K → ℝ) (hX : Measurable X) (Y0 Y1 D : Ω → ℝ),
    Measurable Y0 → Measurable Y1 → Measurable D → Integrable Y0 μ → Integrable Y1 μ →
    (∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) →
    0 < prob μ {ω | D ω = 0} → 0 < prob μ {ω | D ω = 1} →
    ∀ (p : (Fin K → ℝ) → ℝ), IsCEF μ X D p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) ∧ p (X ω) < 1 - ε) →
    CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D →
    let Y := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
    mean μ (fun ω => Y1 ω - Y0 ω) =
      mean μ (fun ω => Y ω * D ω / p (X ω) - Y ω * (1 - D ω) / (1 - p (X ω))) ∧
    (∀ m0 m1 q : (Fin K → ℝ) → ℝ,
      Measurable m0 → Measurable m1 → Measurable q →
      Integrable (m0 ∘ X) μ → Integrable (m1 ∘ X) μ →
      ((IsCEF (μ.restrict {ω | D ω = 0}) X Y m0 ∧
        IsCEF (μ.restrict {ω | D ω = 1}) X Y m1 ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < q (X ω) ∧ q (X ω) < 1 - η) ∨
        q ∘ X =ᵐ[μ] p ∘ X) →
      mean μ (fun ω => Y1 ω - Y0 ω) =
        mean μ (fun ω => m1 (X ω) + D ω * (Y ω - m1 (X ω)) / q (X ω) -
          m0 (X ω) - (1 - D ω) * (Y ω - m0 (X ω)) / (1 - q (X ω))))

/-- Conditional independence of `U` and `D` given `X` passes to `1 - D`.
Proof outline: unfold `CI`; for measurable `B`, `{1 - D ∈ B} = {D ∈ B'}` with
`B' = (fun d => 1 - d) ⁻¹' B` measurable. The indicator functions agree
pointwise, so conditional-expectation congruence gives the factorization. -/
def N1 : Prop :=
  ∀ {Ω : Type u} {E : Type v} {F : Type w} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) (X : Ω → E) (hX : Measurable X) (U : Ω → F)
    (D : Ω → ℝ), CI μ X hX U D → CI μ X hX U (fun ω => 1 - D ω)

/-- The propensity CEF passes to `1 - D` with propensity `1 - p`.
Proof outline: measurability of `1 - p`, linearity of set integrals,
and integrability of constants give the required event-integral identity. -/
def N2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ) (p : E → ℝ),
    IsCEF μ X D p → IsCEF μ X (fun ω => 1 - D ω) (fun x => 1 - p x)

/-- Four applications of the shared arm identity (two for IPW with
`m = 0`, `q = p`; two for DR), using `N1`, `N2` for the control arm,
and then linearity give the result. -/
theorem assemble (hS : MarSelection.AllShared.{u, 0, 0}) (h1 : N1.{u, 0, 0})
    (h2 : N2.{u, 0}) : Target.{u} := by
  intro Ω _ K μ _ X hX Y0 Y1 D hY0 hY1 hD hi0 hi1 hbin _ _ p hp hpos hCI Y
  obtain ⟨ε, hε, hεp⟩ := hpos
  have hU : Measurable (fun ω => (Y0 ω, Y1 ω)) := hY0.prodMk hY1
  have hYm : Measurable Y := by
    change Measurable (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω))
    unfold observedOutcome; fun_prop
  have hbin0 : ∀ᵐ ω ∂μ, 1 - D ω = 0 ∨ 1 - D ω = 1 :=
    hbin.mono fun ω h => by rcases h with h | h <;> simp [h]
  have hCI0 := h1 μ X hX (fun ω => (Y0 ω, Y1 ω)) D hCI
  have hp0 := h2 μ X D p hp
  have hD0m : Measurable (fun ω => 1 - D ω) := measurable_const.sub hD
  have hpos1 : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) := ⟨ε, hε, hεp.mono fun ω h => h.1⟩
  have hpos0 : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < (fun x => 1 - p x) (X ω) :=
    ⟨ε, hε, hεp.mono fun ω h => by simp only; linarith [h.2]⟩
  have hZ1 : ∀ᵐ ω ∂μ, D ω = 1 → Y ω = (fun z : (Fin K → ℝ) × ℝ × ℝ => z.2.2) (X ω, (Y0 ω, Y1 ω)) :=
    Filter.Eventually.of_forall fun ω h => by simp [Y, observedOutcome, h]
  have hZ0 : ∀ᵐ ω ∂μ, 1 - D ω = 1 →
      Y ω = (fun z : (Fin K → ℝ) × ℝ × ℝ => z.2.1) (X ω, (Y0 ω, Y1 ω)) :=
    Filter.Eventually.of_forall fun ω h => by
      have h0 : D ω = 0 := by linarith
      simp [Y, observedOutcome, h0]
  have hset : {ω | 1 - D ω = 1} = {ω | D ω = 0} := by
    ext ω; simp only [Set.mem_ofPred_eq, sub_eq_self]
  have hg1 : Measurable (fun z : (Fin K → ℝ) × ℝ × ℝ => z.2.2) := measurable_snd.snd
  have hg0 : Measurable (fun z : (Fin K → ℝ) × ℝ × ℝ => z.2.1) := measurable_snd.fst
  have hp1m : Measurable p := hp.1
  have hp0m : Measurable (fun x => 1 - p x) := measurable_const.sub hp.1
  -- treated and control arm identities for arbitrary nuisances
  have arm1 := fun (m q : (Fin K → ℝ) → ℝ) (hm : Measurable m) (hq : Measurable q)
      (hmi : Integrable (m ∘ X) μ) hcase =>
    MarSelection.armMean_of hS μ X hX (fun ω => (Y0 ω, Y1 ω)) D (fun z => z.2.2) Y p m q
      hU hD hg1 hYm hbin hCI hp hpos1 hi1 hZ1 hm hq hmi hcase
  have arm0 := fun (m q : (Fin K → ℝ) → ℝ) (hm : Measurable m) (hq : Measurable q)
      (hmi : Integrable (m ∘ X) μ) hcase =>
    MarSelection.armMean_of hS μ X hX (fun ω => (Y0 ω, Y1 ω)) (fun ω => 1 - D ω)
      (fun z => z.2.1) Y (fun x => 1 - p x) m q hU hD0m hg0 hYm hbin0 hCI0 hp0 hpos0 hi0
      hZ0 hm hq hmi hcase
  have hτ : mean μ (fun ω => Y1 ω - Y0 ω) = ∫ ω, Y1 ω ∂μ - ∫ ω, Y0 ω ∂μ :=
    integral_sub hi1 hi0
  have h0int : Integrable ((fun _ : Fin K → ℝ => (0 : ℝ)) ∘ X) μ := integrable_const _
  refine ⟨?_, ?_⟩
  · -- IPW: `m = 0`, `q = p` (resp. `1 - p`), second alternative
    obtain ⟨hI1, hE1⟩ := arm1 (fun _ => 0) p measurable_const hp1m h0int
      (Or.inr Filter.EventuallyEq.rfl)
    obtain ⟨hI0, hE0⟩ := arm0 (fun _ => 0) (fun x => 1 - p x) measurable_const hp0m h0int
      (Or.inr Filter.EventuallyEq.rfl)
    rw [hτ, ← hE1, ← hE0, ← integral_sub hI1 hI0]
    unfold mean
    congr 1
    funext ω
    simp only [sub_zero, zero_add]
    ring
  · intro m0 m1 q hm0 hm1 hq hmi0 hmi1 hcorrect
    have hq0m : Measurable (fun x => 1 - q x) := measurable_const.sub hq
    have hcase1 : (IsCEF (μ.restrict {ω | D ω = 1}) X Y m1 ∧
        ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂μ, c ≤ q (X ω)) ∨ q ∘ X =ᵐ[μ] p ∘ X := by
      rcases hcorrect with ⟨-, hc1, η, hη, hqη⟩ | h
      · exact Or.inl ⟨hc1, η, hη, hqη.mono fun ω h => h.1.le⟩
      · exact Or.inr h
    have hcase0 : (IsCEF (μ.restrict {ω | 1 - D ω = 1}) X Y m0 ∧
        ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂μ, c ≤ (fun x => 1 - q x) (X ω)) ∨
        (fun x => 1 - q x) ∘ X =ᵐ[μ] (fun x => 1 - p x) ∘ X := by
      rcases hcorrect with ⟨hc0, -, η, hη, hqη⟩ | h
      · refine Or.inl ⟨?_, η, hη, hqη.mono fun ω h => ?_⟩
        · rw [hset]; exact hc0
        · simp only; linarith [h.2]
      · exact Or.inr (h.mono fun ω h => by simp only [Function.comp] at h ⊢; rw [h])
    obtain ⟨hI1, hE1⟩ := arm1 m1 q hm1 hq hmi1 hcase1
    obtain ⟨hI0, hE0⟩ := arm0 m0 (fun x => 1 - q x) hm0 hq0m hmi0 hcase0
    rw [hτ, ← hE1, ← hE0, ← integral_sub hI1 hI0]
    unfold mean
    congr 1
    funext ω
    ring

end

end AronowAudit.P001.Wave1.CausalIpwDr
