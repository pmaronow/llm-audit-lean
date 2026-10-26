import AronowAudit.P001.P001_Foundations

/-! Refutations of the printed uniform-positivity converse and the universal
positive-variance normal-limit claim for plug-in estimators. -/
namespace AronowAudit.P001.PrintedConfidence
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal
local instance (p : Prop) : Decidable p := Classical.propDecidable p
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
universe u

/-- Actual iid observations in every sample-space universe. -/
def liftStreamLaw {E : Type} [MeasurableSpace E] (ν : Measure E) :
    Measure (ℕ → ULift.{u} E) :=
  Measure.infinitePi (fun _ : ℕ => ν.map (ULift.up : E → ULift.{u} E))

instance liftStreamLaw_probability {E : Type} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] : IsProbabilityMeasure (liftStreamLaw.{u} ν) := by
  dsimp [liftStreamLaw]
  infer_instance

def streamObservation {E : Type} (i : ℕ) (ω : ℕ → ULift.{u} E) : E := (ω i).down

set_option backward.isDefEq.respectTransparency false in
theorem lift_stream_iid {E : Type} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] :
    IID (liftStreamLaw.{u} ν) streamObservation ∧
      (liftStreamLaw.{u} ν).map (streamObservation 0) = ν := by
  let baseLaw : Measure (ULift.{u} E) := ν.map ULift.up
  have hcoord (i : ℕ) : (liftStreamLaw.{u} ν).map (fun ω => ω i) = baseLaw :=
    Measure.infinitePi_map_eval (fun _ : ℕ => baseLaw) i
  have hm (i : ℕ) : Measurable (fun ω : ℕ → ULift.{u} E => ω i) := measurable_pi_apply i
  have hobs (i : ℕ) : Measurable (streamObservation (E := E) i) :=
    measurable_down.comp (hm i)
  have hlaw (i : ℕ) : (liftStreamLaw.{u} ν).map (streamObservation i) = ν := by
    change (liftStreamLaw.{u} ν).map (ULift.down ∘ (fun ω => ω i)) = ν
    rw [← Measure.map_map measurable_down (hm i),hcoord]
    dsimp [baseLaw]
    rw [Measure.map_map measurable_down measurable_up]
    change ν.map id = ν
    exact Measure.map_id
  refine ⟨⟨hobs,?_,?_⟩,hlaw 0⟩
  · exact iIndepFun_infinitePi (fun _ : ℕ => measurable_down)
  · intro i
    exact ⟨(hobs i).aemeasurable,(hobs 0).aemeasurable,(hlaw i).trans (hlaw 0).symm⟩

/-- Universal closure of the printed countable-overlap assertion. -/
def PrintedOverlapUniformPositivityConverse : Prop :=
  ∀ (t c : ℕ → ℝ), (∀ k,0 ≤ t k) → (∀ k,0 ≤ c k) →
    Summable t → Summable c → 0 < ∑' k,t k → 0 < ∑' k,c k →
    (∑' k,t k)+(∑' k,c k)=1 →
    ({k | 0 < t k}={k | 0 < c k} ↔ ∃ ε : ℝ,0 < ε ∧ ∀ k,0 < t k+c k →
      ε < t k/(t k+c k) ∧ t k/(t k+c k) < 1-ε)

theorem printed_overlap_uniform_positivity_converse_refuted :
    ¬ PrintedOverlapUniformPositivityConverse := by
  intro h
  obtain ⟨hst,hsc,hmt,hmc,hpos,hbad⟩ := complete_overlap_without_uniform_positivity
  have heq : {k | 0 < overlapT k} = {k | 0 < overlapC k} := by
    ext k
    exact iff_of_true (hpos k).1 (hpos k).2.1
  have hh := (h overlapT overlapC (fun k => (hpos k).1.le)
    (fun k => (hpos k).2.1.le) hst hsc (by rw [hmt]; norm_num)
    (by rw [hmc]; norm_num) (by rw [hmt,hmc]; norm_num)).mp heq
  obtain ⟨ε,hε,hbound⟩ := hh
  apply hbad
  refine ⟨ε,hε,fun k => ?_⟩
  simpa only [overlapPropensity] using hbound k (add_pos (hpos k).1 (hpos k).2.1)

/-- Universal closure in every sample-space universe. -/
def PrintedPluginPositiveNormalLimit : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), IID μ X → ∀ T : (ℝ → ℝ) → ℝ,
    CDFHadamard T (cdf μ (X 0)) →
    ∃ φ : ℝ,0 < φ ∧ CD μ
      (fun n ω => Real.sqrt n*(T (cdf (empirical X n ω) id)-T (cdf μ (X 0))))
      (gaussianReal 0 ⟨φ^2,sq_nonneg _⟩)

/-- Even genuine nondegenerate iid Gaussian data do not rescue a constant functional. -/
theorem printed_plugin_positive_normal_limit_refuted :
    ¬ PrintedPluginPositiveNormalLimit.{u} := by
  intro h
  let μ := liftStreamLaw.{u} (gaussianReal 0 1)
  let X : ℕ → (ℕ → ULift.{u} ℝ) → ℝ := streamObservation
  have hiid : IID μ X := (lift_stream_iid.{u} (gaussianReal 0 1)).1
  obtain ⟨φ,hφ,hCD⟩ := h μ X hiid (fun _ => (7 : ℝ))
    (constant_cdf_functional_hadamard _)
  have hv : (0 : ℝ≥0) < ⟨φ^2,sq_nonneg φ⟩ := by
    exact_mod_cast (sq_pos_of_pos hφ)
  apply (constant_plugin_degenerate μ).2 ⟨φ^2,sq_nonneg φ⟩ hv
  simpa only [sub_self,mul_zero] using hCD

end
end AronowAudit.P001.PrintedConfidence
