import AronowAudit.P001.Wave1.MarSelection.N1
import AronowAudit.P001.Wave1.MarSelection.N2
import AronowAudit.P001.Wave1.MarSelection.N3
import AronowAudit.P001.Wave1.MarSelection.N4
import AronowAudit.P001.Wave1.MarSelection.N5
import AronowAudit.P001.Wave1.MarDiscreteBlueprint
import AronowAudit.P001.Wave1.CausalIpwDr.N1
import AronowAudit.P001.Wave1.CausalIpwDr.N2
import AronowAudit.P001.Wave1.MarBalance.N1
import AronowAudit.P001.Wave1.MarBalance.N2

/-! P001-T116: L1 identification and the moment-free propensity-score theorem. -/

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableDecideP001T116 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false
set_option linter.unusedVariables false

/-- Apply the proved selection transfer to D and to 1-D, retaining the supplied
arm regression versions on the arbitrary covariate space. -/
lemma DecideP001T116_arm_cefs {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1) (hD : Measurable D)
   (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ) (hbinary : ∀ ω,D ω=0 ∨ D ω=1)
   (p : E → ℝ) (hp : IsCEF μ X D p) (ε : ℝ) (hε : 0 < ε)
   (hpos : ∀ ω,ε < p (X ω) ∧ p (X ω) < 1-ε)
   (hCI : CI μ X hX (fun ω => (Y0 ω,Y1 ω)) D)
   (m0 m1 : E → ℝ)
   (hm0 : IsCEF (μ.restrict {ω | D ω=0}) X (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m0)
   (hm1 : IsCEF (μ.restrict {ω | D ω=1}) X (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m1)
   (hmi0 : Integrable (m0 ∘ X) μ) (hmi1 : Integrable (m1 ∘ X) μ) :
   IsCEF μ X Y0 m0 ∧ IsCEF μ X Y1 m1 := by
  have hU : Measurable (fun ω => (Y0 ω, Y1 ω)) := h0.prodMk h1
  have hbin : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1 := ae_of_all μ hbinary
  have hbin0 : ∀ᵐ ω ∂μ, 1 - D ω = 0 ∨ 1 - D ω = 1 :=
    hbin.mono fun ω h => by rcases h with h | h <;> simp [h]
  have hCI0 := CausalIpwDr.n1_proof μ X hX (fun ω => (Y0 ω, Y1 ω)) D hCI
  have hp0 := CausalIpwDr.n2_proof μ X D p hp
  have hD0 : Measurable (fun ω => 1 - D ω) := measurable_const.sub hD
  have hpos1 : ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < p (X ω) :=
    ⟨ε, hε, ae_of_all μ (fun ω => (hpos ω).1)⟩
  have hpos0 : ∃ η : ℝ, 0 < η ∧ ∀ᵐ ω ∂μ, η < (fun x => 1 - p x) (X ω) :=
    ⟨ε, hε, ae_of_all μ (fun ω => by linarith [(hpos ω).2])⟩
  have hobs1 : ∀ᵐ ω ∂μ, D ω = 1 →
      observedOutcome (Y0 ω) (Y1 ω) (D ω) =
        (fun z : E × ℝ × ℝ => z.2.2) (X ω, (Y0 ω, Y1 ω)) :=
    ae_of_all μ (fun ω h => by simp [observedOutcome, h])
  have hobs0 : ∀ᵐ ω ∂μ, 1 - D ω = 1 →
      observedOutcome (Y0 ω) (Y1 ω) (D ω) =
        (fun z : E × ℝ × ℝ => z.2.1) (X ω, (Y0 ω, Y1 ω)) :=
    ae_of_all μ (fun ω h => by
      have hd : D ω = 0 := by linarith
      simp [observedOutcome, hd])
  have hset : {ω | 1 - D ω = 1} = {ω | D ω = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, sub_eq_self]
  have hm0' : IsCEF (μ.restrict {ω | 1 - D ω = 1}) X
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m0 := by
    rw [hset]
    exact hm0
  constructor
  · exact MarSelection.n5_proof MarSelection.n1_proof MarSelection.n4_proof
      MarSelection.n3_proof MarSelection.n2_proof μ X hX
      (fun ω => (Y0 ω, Y1 ω)) (fun ω => 1 - D ω) (fun z => z.2.1)
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) (fun x => 1 - p x) m0
      hU hD0 measurable_snd.fst hbin0 hCI0 hp0 hpos0 hi0 hobs0 hm0' hmi0
  · exact MarSelection.n5_proof MarSelection.n1_proof MarSelection.n4_proof
      MarSelection.n3_proof MarSelection.n2_proof μ X hX
      (fun ω => (Y0 ω, Y1 ω)) D (fun z => z.2.2)
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) p m1
      hU hD measurable_snd.snd hbin hCI hp hpos1 hi1 hobs1 hm1 hmi1

/-- An event-wise tower argument reduces conditional independence to the propensity
score for an arbitrary measurable outcome space. The proof uses only outcome events. -/
lemma DecideP001T116_reduce_ci {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (U : Ω → F) (D : Ω → ℝ)
    (p : E → ℝ) (hp : IsCEF μ X D p) (hD : Measurable D)
    (hbinary : ∀ ω, D ω = 0 ∨ D ω = 1) (hCI : CI μ X hX U D) :
    CI μ (p ∘ X) (hp.1.comp hX) U D := by
  let S : Ω → ℝ := p ∘ X
  have hG : (MeasurableSpace.comap X inferInstance) ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hXm : Measurable[(MeasurableSpace.comap X inferInstance)] X := comap_measurable X
  have hHG : (MeasurableSpace.comap S inferInstance) ≤ (MeasurableSpace.comap X inferInstance) := (hp.1.comp hXm).comap_le
  have hH : (MeasurableSpace.comap S inferInstance) ≤ ‹MeasurableSpace Ω› := (hp.1.comp hX).comap_le
  intro A B hA hB
  let I : Ω → ℝ := (U ⁻¹' A).indicator (fun _ => 1)
  let J : Ω → ℝ := (D ⁻¹' B).indicator (fun _ => 1)
  let f : ℝ → ℝ := fun s => (if (0 : ℝ) ∈ B then 1 - s else 0) +
    (if (1 : ℝ) ∈ B then s else 0)
  let r : Ω → ℝ := f ∘ S
  have hfm : Measurable f := by
    dsimp [f]
    split_ifs <;> fun_prop
  have hrm : StronglyMeasurable[(MeasurableSpace.comap S inferInstance)] r := (hfm.comp (comap_measurable S)).stronglyMeasurable
  have hb : μ[J | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] r := MarBalance.n1_proof μ X D p hX hD (ae_of_all μ hbinary) hp B hB
  have hri : Integrable r μ := integrable_condExp.congr hb
  have hrfix : μ[r | (MeasurableSpace.comap S inferInstance)] = r := condExp_of_stronglyMeasurable hH hrm hri
  have hJH : μ[J | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] r := by
    calc
      μ[J | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] μ[μ[J | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] := (condExp_condExp_of_le hHG hG).symm
      _ =ᵐ[μ] μ[r | (MeasurableSpace.comap S inferInstance)] := condExp_congr_ae hb
      _ =ᵐ[μ] r := Filter.Eventually.of_forall (congrFun hrfix)
  have hjoin : (fun ω => if U ω ∈ A ∧ D ω ∈ B then (1 : ℝ) else 0) = I * J := by
    funext ω
    by_cases hωA : U ω ∈ A <;> by_cases hωB : D ω ∈ B <;>
      simp [I, J, Set.indicator, hωA, hωB]
  have hci : μ[I * J | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] μ[I | (MeasurableSpace.comap X inferInstance)] * μ[J | (MeasurableSpace.comap X inferInstance)] := by
    rw [← hjoin]
    exact hCI A B hA hB
  have hinner : μ[I * J | (MeasurableSpace.comap X inferInstance)] =ᵐ[μ] r * μ[I | (MeasurableSpace.comap X inferInstance)] := by
    filter_upwards [hci, hb] with ω hω hωb
    change (μ[I * J | (MeasurableSpace.comap X inferInstance)]) ω = r ω * (μ[I | (MeasurableSpace.comap X inferInstance)]) ω
    calc
      (μ[I * J | (MeasurableSpace.comap X inferInstance)]) ω = (μ[I | (MeasurableSpace.comap X inferInstance)]) ω * (μ[J | (MeasurableSpace.comap X inferInstance)]) ω := hω
      _ = r ω * (μ[I | (MeasurableSpace.comap X inferInstance)]) ω := by rw [hωb]; ring
  -- Integrability of the product follows from its equality to a conditional
  -- expectation, so no outcome moment or separate bound on U is needed.
  have hinneri : Integrable (r * μ[I | (MeasurableSpace.comap X inferInstance)]) μ := integrable_condExp.congr hinner
  have hpull : μ[r * μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] r * μ[μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] :=
    condExp_mul_of_stronglyMeasurable_left hrm hinneri integrable_condExp
  have htowerI : μ[μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] μ[I | (MeasurableSpace.comap S inferInstance)] := condExp_condExp_of_le hHG hG
  have hproduct : μ[I * J | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] r * μ[I | (MeasurableSpace.comap S inferInstance)] := by
    calc
      μ[I * J | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ] μ[μ[I * J | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] := (condExp_condExp_of_le hHG hG).symm
      _ =ᵐ[μ] μ[r * μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] := condExp_congr_ae hinner
      _ =ᵐ[μ] r * μ[μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)] := hpull
      _ =ᵐ[μ] r * μ[I | (MeasurableSpace.comap S inferInstance)] := by
        filter_upwards [htowerI] with ω hω
        change r ω * (μ[μ[I | (MeasurableSpace.comap X inferInstance)] | (MeasurableSpace.comap S inferInstance)]) ω = r ω * (μ[I | (MeasurableSpace.comap S inferInstance)]) ω
        rw [hω]
  change μ[(fun ω => if U ω ∈ A ∧ D ω ∈ B then (1 : ℝ) else 0) | (MeasurableSpace.comap S inferInstance)] =ᵐ[μ]
    μ[I | (MeasurableSpace.comap S inferInstance)] * μ[J | (MeasurableSpace.comap S inferInstance)]
  rw [hjoin]
  filter_upwards [hproduct, hJH] with ω hω hωJ
  change (μ[I * J | (MeasurableSpace.comap S inferInstance)]) ω = (μ[I | (MeasurableSpace.comap S inferInstance)]) ω * (μ[J | (MeasurableSpace.comap S inferInstance)]) ω
  rw [hω]
  change r ω * (μ[I | (MeasurableSpace.comap S inferInstance)]) ω = (μ[I | (MeasurableSpace.comap S inferInstance)]) ω * (μ[J | (MeasurableSpace.comap S inferInstance)]) ω
  rw [hωJ]
  ring


theorem strong_ignorability_l1_identification
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1)
    (hD : Measurable D) (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ)
    (hbinary : ∀ ω, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsCEF μ X D p) (ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ ω, ε < p (X ω) ∧ p (X ω) < 1 - ε)
    (hCI : CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D)
    (m0 m1 : E → ℝ)
    (hm0 : IsCEF (μ.restrict {ω | D ω = 0}) X
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m0)
    (hm1 : IsCEF (μ.restrict {ω | D ω = 1}) X
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m1)
    (hmi0 : Integrable (m0 ∘ X) μ) (hmi1 : Integrable (m1 ∘ X) μ) :
    IsCEF μ X (fun ω => Y1 ω - Y0 ω) (fun x => m1 x - m0 x) ∧
    mean μ (fun ω => Y1 ω - Y0 ω) =
      mean μ (fun ω => m1 (X ω) - m0 (X ω)) := by
  obtain ⟨hc0, hc1⟩ := DecideP001T116_arm_cefs μ X hX Y0 Y1 D h0 h1 hD
    hi0 hi1 hbinary p hp ε hε hpos hCI m0 m1 hm0 hm1 hmi0 hmi1
  have hcef : IsCEF μ X (fun ω => Y1 ω - Y0 ω) (fun x => m1 x - m0 x) := by
    refine ⟨hc1.1.sub hc0.1, hi1.sub hi0, hmi1.sub hmi0, ?_⟩
    intro A hA
    change (∫ ω in X ⁻¹' A, Y1 ω - Y0 ω ∂μ) =
      ∫ ω in X ⁻¹' A, (m1 ∘ X) ω - (m0 ∘ X) ω ∂μ
    rw [integral_sub hi1.integrableOn hi0.integrableOn,
      integral_sub hmi1.integrableOn hmi0.integrableOn,
      hc1.2.2.2 A hA, hc0.2.2.2 A hA]
    rfl
  exact ⟨hcef, MarDiscrete.mean_eq_of_isCEF μ X _ _ hcef⟩

theorem strong_ignorability_propensity_score_moment_free
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1)
    (hD : Measurable D) (hbinary : ∀ ω, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsCEF μ X D p) (ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ ω, ε < p (X ω) ∧ p (X ω) < 1 - ε)
    (hCI : CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D) :
    CI μ (p ∘ X) (hp.1.comp hX) D X ∧
    CI μ (p ∘ X) (hp.1.comp hX) (fun ω => (Y0 ω, Y1 ω)) D ∧
    IsCEF μ (p ∘ X) D id ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ ω ∂μ, δ < (p ∘ X) ω ∧ (p ∘ X) ω < 1 - δ) := by
  obtain ⟨hbal, hself⟩ := MarBalance.n2_proof MarBalance.n1_proof
    MarSelection.n1_proof μ X hX D p hp hD (ae_of_all μ hbinary)
  exact ⟨hbal,
    DecideP001T116_reduce_ci μ X hX (fun ω => (Y0 ω, Y1 ω)) D p hp hD hbinary hCI,
    hself, ε, hε, ae_of_all μ hpos⟩

/-- Identification and the moment-free propensity-score theorem, with independent domains. -/
theorem strong_ignorability_repaired :
    (∀ {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1)
    (hD : Measurable D) (hi0 : Integrable Y0 μ) (hi1 : Integrable Y1 μ)
    (hbinary : ∀ ω, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsCEF μ X D p) (ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ ω, ε < p (X ω) ∧ p (X ω) < 1 - ε)
    (hCI : CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D)
    (m0 m1 : E → ℝ)
    (hm0 : IsCEF (μ.restrict {ω | D ω = 0}) X
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m0)
    (hm1 : IsCEF (μ.restrict {ω | D ω = 1}) X
      (fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)) m1)
    (hmi0 : Integrable (m0 ∘ X) μ) (hmi1 : Integrable (m1 ∘ X) μ),
    IsCEF μ X (fun ω => Y1 ω - Y0 ω) (fun x => m1 x - m0 x) ∧
    mean μ (fun ω => Y1 ω - Y0 ω) =
      mean μ (fun ω => m1 (X ω) - m0 (X ω))) ∧
    (∀ {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y0 Y1 D : Ω → ℝ) (h0 : Measurable Y0) (h1 : Measurable Y1)
    (hD : Measurable D) (hbinary : ∀ ω, D ω = 0 ∨ D ω = 1)
    (p : E → ℝ) (hp : IsCEF μ X D p) (ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ ω, ε < p (X ω) ∧ p (X ω) < 1 - ε)
    (hCI : CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D),
    CI μ (p ∘ X) (hp.1.comp hX) D X ∧
    CI μ (p ∘ X) (hp.1.comp hX) (fun ω => (Y0 ω, Y1 ω)) D ∧
    IsCEF μ (p ∘ X) D id ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ ω ∂μ, δ < (p ∘ X) ω ∧ (p ∘ X) ω < 1 - δ)) := by
  exact ⟨@strong_ignorability_l1_identification,
    @strong_ignorability_propensity_score_moment_free⟩


universe u v w z

end

end AronowAudit.P001.Wave1
