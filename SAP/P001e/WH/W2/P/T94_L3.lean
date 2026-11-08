import SAP.P001e.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.WH.W2.P.T94_L3

open SAP.P001e
universe u v

lemma complement_conditionalMean {Ω : Type u} {E : Type v}
    [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → E) (D : Ω → ℝ) (p : E → ℝ)
    (h : IsConditionalMean μ X D p) :
    IsConditionalMean μ X (fun ω => 1-D ω) (fun x => 1-p x) := by
  rcases h with ⟨hp, hDi, hpi, hcef⟩
  refine ⟨measurable_const.sub hp, (integrable_const (1:ℝ)).sub hDi,
    (integrable_const (1:ℝ)).sub hpi, ?_⟩
  intro A hA
  have hD := hcef A hA
  calc
    (∫ ω in X ⁻¹' A, (1-D ω) ∂μ) =
        (∫ ω in X ⁻¹' A, (1:ℝ) ∂μ) - ∫ ω in X ⁻¹' A, D ω ∂μ := by
      exact integral_sub (integrable_const (1:ℝ)).integrableOn hDi.integrableOn
    _ = (∫ ω in X ⁻¹' A, (1:ℝ) ∂μ) - ∫ ω in X ⁻¹' A, p (X ω) ∂μ := by
      rw [hD]
    _ = ∫ ω in X ⁻¹' A, (1-p (X ω)) ∂μ := by
      symm
      exact integral_sub (integrable_const (1:ℝ)).integrableOn hpi.integrableOn

end SAP.P001e.WH.W2.P.T94_L3

theorem SAP.P001e.WH.W2.T94_L3_proof : SAP.P001e.WH.W2.T94_L3 := by
  intro hT94 Ω _μspace μ _ K X D Y0 Y1 p model F hm hi d hd
  let U : Ω → ℝ × ℝ := fun ω => (Y0 ω,Y1 ω)
  let Y : Ω → ℝ := fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)
  have hU : Measurable U := model.hY0.prodMk model.hY1
  have hU1 : Measurable (fun z : (Fin K → ℝ) × (ℝ × ℝ) => z.2.2) :=
    measurable_snd.comp measurable_snd
  have hU0 : Measurable (fun z : (Fin K → ℝ) × (ℝ × ℝ) => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hF0i : Integrable (fun ω => F (0,X ω)) μ := hi 0 (by simp)
  have hF1i : Integrable (fun ω => F (1,X ω)) μ := hi 1 (by simp)
  have hobs0 := hT94 μ X model.hX D Y model.hD F hm 0 hF0i
  have hobs1 := hT94 μ X model.hX D Y model.hD F hm 1 hF1i
  have hpos := model.overlap
  have htreated : IsConditionalMean μ X Y1 (fun x => F (1,x)) := by
    have hCEF : AronowAudit.P001.IsCEF (μ.restrict {ω | D ω=1}) X Y
        (fun x => F (1,x)) := by
      simpa only [SAP.P001e.Bridge.IsConditionalMean_eq] using hobs1
    have htr := AronowAudit.P001.Wave1.MarSelection.n5_proof
      AronowAudit.P001.Wave1.MarSelection.n1_proof
      AronowAudit.P001.Wave1.MarSelection.n4_proof
      AronowAudit.P001.Wave1.MarSelection.n3_proof
      AronowAudit.P001.Wave1.MarSelection.n2_proof
      μ X model.hX U D (fun z => z.2.2) Y p (fun x => F (1,x))
      hU model.hD hU1 model.binary model.independent model.propensity
      (by
        obtain ⟨ε,hε,hεp⟩ := hpos
        refine ⟨ε,hε,?_⟩
        filter_upwards [hεp] with ω hω
        exact hω.1)
      model.hi1
      (Filter.Eventually.of_forall fun ω hω => by
        simp [Y, U, realizedOutcome, hω])
      hCEF hF1i
    exact htr
  have hcomplement : IsConditionalMean μ X (fun ω => 1-D ω)
      (fun x => 1-p x) := SAP.P001e.WH.W2.P.T94_L3.complement_conditionalMean μ X D p model.propensity
  have hR0 : Measurable (fun ω => 1-D ω) := measurable_const.sub model.hD
  have hR0bin : ∀ᵐ ω ∂μ, (1-D ω=0 ∨ 1-D ω=1) := by
    filter_upwards [model.binary] with ω hω
    rcases hω with hω | hω
    · right
      rw [hω]
      norm_num
    · left
      rw [hω]
      norm_num
  have hCI0 : AronowAudit.P001.CI μ X model.hX U (fun ω => 1-D ω) := by
    intro A B hA hB
    let B' : Set ℝ := (fun r : ℝ => 1-r) ⁻¹' B
    have hB' : MeasurableSet B' := hB.preimage (measurable_const.sub measurable_id)
    simpa [AronowAudit.P001.CI, SAP.P001e.CondIndependent, B', Set.mem_preimage]
      using model.independent A B' hA hB'
  have hcontrol : IsConditionalMean μ X Y0 (fun x => F (0,x)) := by
    have hset : {ω | 1-D ω=1} = {ω | D ω=0} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;> linarith
    have hCEF : AronowAudit.P001.IsCEF (μ.restrict {ω | 1-D ω=1}) X Y
        (fun x => F (0,x)) := by
      rw [hset]
      simpa only [SAP.P001e.Bridge.IsConditionalMean_eq] using hobs0
    have hcon := AronowAudit.P001.Wave1.MarSelection.n5_proof
      AronowAudit.P001.Wave1.MarSelection.n1_proof
      AronowAudit.P001.Wave1.MarSelection.n4_proof
      AronowAudit.P001.Wave1.MarSelection.n3_proof
      AronowAudit.P001.Wave1.MarSelection.n2_proof
      μ X model.hX U (fun ω => 1-D ω) (fun z => z.2.1) Y
      (fun x => 1-p x) (fun x => F (0,x))
      hU hR0 hU0 hR0bin hCI0 hcomplement
      (by
        obtain ⟨ε,hε,hεp⟩ := hpos
        refine ⟨ε,hε, ?_⟩
        filter_upwards [hεp] with ω hω
        linarith [hω.2])
      model.hi0
      (Filter.Eventually.of_forall fun ω hω => by
        have hd0 : D ω=0 := by linarith
        simp [Y, U, realizedOutcome, hd0])
      hCEF hF0i
    exact hcon
  have hzero : IsConditionalMean μ X Y0 (fun x => F (0,x)) := hcontrol
  have hone : IsConditionalMean μ X Y1 (fun x => F (1,x)) := htreated
  rcases Set.mem_insert_iff.mp hd with hd0 | hd1
  · subst d
    simpa using hzero
  · have hd1' : d=1 := Set.mem_singleton_iff.mp hd1
    subst d
    simpa using hone


