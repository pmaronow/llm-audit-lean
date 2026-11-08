import SAP.P001e.Defs.WholeW2
import SAP.P001e.Bridge
import AronowAudit.P001.Wave1.MarSelection.N1
import AronowAudit.P001.Wave1.MarSelection.N2
import AronowAudit.P001.Wave1.MarSelection.N3
import AronowAudit.P001.Wave1.MarSelection.N4
import AronowAudit.P001.Wave1.MarSelection.N5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.WH.W2
universe u v
noncomputable section

/-- A measurable function of the conditioning variable is its own CEF. -/
theorem conditionalMean_of_eq {Ω : Type u} {E : Type v}
    [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) (X : Ω → E)
    (Y : Ω → ℝ) (m : E → ℝ) (hm : Measurable m) (hi : Integrable Y μ)
    (he : Y=m ∘ X) : IsConditionalMean μ X Y m := by
  subst Y
  exact ⟨hm, hi, hi, fun _ _ => rfl⟩

/-- Conditional expectation followed by measurable factorization constructs a CEF,
including for the zero measure and arbitrary measurable covariate spaces. -/
theorem exists_conditionalMean {Ω : Type u} {E : Type v}
    [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → E) (hX : Measurable X) (Y : Ω → ℝ) (hi : Integrable Y μ) :
    ∃ m : E → ℝ, IsConditionalMean μ X Y m := by
  obtain ⟨m, hm, he⟩ :=
    (stronglyMeasurable_condExp (μ := μ) (f := Y)
      (m := MeasurableSpace.comap X inferInstance)).exists_eq_measurable_comp
  refine ⟨m, hm.measurable, hi, ?_, ?_⟩
  · rw [← he]
    exact integrable_condExp
  · intro A hA
    change (∫ ω in X ⁻¹' A, Y ω ∂μ)=∫ ω in X ⁻¹' A, (m ∘ X) ω ∂μ
    rw [← he]
    exact (setIntegral_condExp hX.comap_le hi ⟨A,hA,rfl⟩).symm

/-- Integrating a CEF over the whole covariate space gives the population mean. -/
theorem mean_of_conditionalMean {Ω : Type u} {E : Type v}
    [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) (X : Ω → E)
    (Y : Ω → ℝ) (m : E → ℝ) (hm : IsConditionalMean μ X Y m) :
    expectation μ Y=expectation μ (m ∘ X) := by
  simpa [expectation] using hm.2.2.2 Set.univ MeasurableSet.univ

/-- Apply the already proved selection nodes, with a scalar outcome. -/
theorem mar_transfer {Ω : Type u} {E : Type v}
    [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Measurable X) (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R)
    (hi : Integrable Y μ) (hb : ∀ᵐ ω ∂μ, R ω=0 ∨ R ω=1)
    (p m : E → ℝ) (hp : IsConditionalMean μ X R p)
    (hpos : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω))
    (hind : CondIndependent μ X hX Y R)
    (hm : IsConditionalMean (μ.restrict {ω | R ω=1}) X Y m)
    (hmi : Integrable (m ∘ X) μ) : IsConditionalMean μ X Y m := by
  exact AronowAudit.P001.Wave1.MarSelection.n5_proof
    AronowAudit.P001.Wave1.MarSelection.n1_proof
    AronowAudit.P001.Wave1.MarSelection.n4_proof
    AronowAudit.P001.Wave1.MarSelection.n3_proof
    AronowAudit.P001.Wave1.MarSelection.n2_proof
    μ X hX Y R (fun z => z.2) Y p m hY hR measurable_snd hb hind hp hpos hi
    (ae_of_all _ (fun _ _ => rfl)) hm hmi

/-- Binary consistency gives an integrable observed outcome without second moments. -/
theorem potential_observed_integrable {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) {K : ℕ} (X : Ω → Fin K → ℝ) (D Y0 Y1 : Ω → ℝ)
    (p : (Fin K → ℝ) → ℝ) (h : WholePotentialModel μ X D Y0 Y1 p) :
    Integrable (fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)) μ := by
  have hb : ∀ᵐ ω ∂μ, ‖D ω‖ ≤ (1 : ℝ) := by
    filter_upwards [h.binary] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  have hc : ∀ᵐ ω ∂μ, ‖1-D ω‖ ≤ (1 : ℝ) := by
    filter_upwards [h.binary] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  convert (h.hi1.bdd_mul h.hD.aestronglyMeasurable hb).add
    (h.hi0.bdd_mul (measurable_const.sub h.hD).aestronglyMeasurable hc) using 1
  ext ω
  simp only [realizedOutcome, Pi.add_apply, Pi.sub_apply]
  ring

/-- Certified cell-level algebra, reproduced from the package Solution using its
three proved finite-sum donors. -/
theorem cell85 : T85Statement.{u} := by
  intro E _ _ N r q n hn hN hr hq htotal
  have hn0 : n ≠ 0 := hn.ne'
  have hcrit := AronowAudit.P001.missing_ipw_saturation_necessary N r q hN hr hq
  refine ⟨?_,?_,?_⟩
  · intro S
    exact (AronowAudit.P001.missing_ipw_difference_and_stabilization
      N r S q n hn hN hr htotal).1
  · constructor
    · intro he
      apply hcrit.mp
      intro S
      exact (div_left_inj' hn0).mp (he S)
    · intro hs S
      exact congrArg (fun z : ℝ => z/n) (hcrit.mpr hs S)
  · intro hs
    have hqeq : q=fun x => r x/N x := funext hs
    have hd : cellWeightMean r q n=1 := by
      rw [hqeq]
      exact (AronowAudit.P001.missing_ipw_difference_and_stabilization
        N r (fun _ => 0) q n hn hN hr htotal).2
    refine ⟨hd,fun S => ?_⟩
    have he : cellIPW S q n=cellPlugIn N r S n :=
      congrArg (fun z : ℝ => z/n) (hcrit.mpr hs S)
    exact ⟨he,by rw [cellStabilized,hd,div_one,he]⟩

end
end SAP.P001e.WH.W2
