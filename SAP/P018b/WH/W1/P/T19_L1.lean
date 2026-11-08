import SAP.P018b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section
namespace SAP.P018b.WH.W1.P.T19_L1

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

abbrev RareUnit := AronowAudit.P018.RareUnit

/-- Flip both fair signs while keeping the sampled design coordinates. -/
def flipUnit (u : RareUnit) : RareUnit :=
  ⟨u.m, u.label, !u.A, !u.B⟩

theorem flipUnit_involutive : Function.Involutive flipUnit := by
  intro u
  cases u
  simp [flipUnit]

theorem signValue_flip (b : Bool) : SAP.P018b.signValue (!b) =
    -SAP.P018b.signValue b := by
  cases b <;> norm_num [SAP.P018b.signValue]

theorem flipUnit_measurable : Measurable flipUnit := by
  exact measurable_of_countable _

theorem flipUnit_measurePreserving : MeasurePreserving flipUnit AronowAudit.P018.rareLaw AronowAudit.P018.rareLaw := by
  classical
  haveI : Countable RareUnit := AronowAudit.P018.Wave1.TailB_rare_countable
  refine ⟨flipUnit_measurable, ?_⟩
  apply ext_of_measurableAtoms
  intro u
  rw [measurableAtom_of_measurableSingletonClass]
  rw [Measure.map_apply flipUnit_measurable (measurableSet_singleton u)]
  have hp : flipUnit ⁻¹' ({u} : Set RareUnit) = {flipUnit u} := by
    ext v
    constructor
    · intro hv
      have huv : flipUnit v = u := Set.mem_singleton_iff.mp hv
      have hv' : v = flipUnit u := by
        calc
          v = flipUnit (flipUnit v) := (flipUnit_involutive v).symm
          _ = flipUnit u := congrArg flipUnit huv
      exact Set.mem_singleton_iff.mpr hv'
    · intro hv
      have hvu : v = flipUnit u := Set.mem_singleton_iff.mp hv
      subst v
      exact flipUnit_involutive u
  rw [hp, AronowAudit.P018.Wave1.TailB_rare_atom, AronowAudit.P018.Wave1.TailB_rare_atom]
  rfl

def flipSample {N : ℕ} (ω : Fin N → RareUnit) : Fin N → RareUnit :=
  fun i => flipUnit (ω i)

theorem flipSample_involutive {N : ℕ} : Function.Involutive (@flipSample N) := by
  intro ω
  funext i
  exact flipUnit_involutive (ω i)

theorem flipSample_measurable {N : ℕ} : Measurable (@flipSample N) := by
  apply measurable_pi_iff.mpr
  intro i
  exact flipUnit_measurable.comp (measurable_pi_apply i)

/-- The rare sample product measure is invariant under the simultaneous flip. -/
theorem flipSample_measurePreserving (N : ℕ) :
    MeasurePreserving (@flipSample N)
      (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw))
      (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw)) := by
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  exact measurePreserving_pi _ _ (fun _ => flipUnit_measurePreserving)

theorem rareDesign_flip {N : ℕ} (ω : Fin N → RareUnit)
    (d : AronowAudit.P018.Dyad N) (t : Fin 2) :
    repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (flipSample ω) d t =
      repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω d t := by
  simp [flipSample, repeatedX, wholeRareKernel, SAP.P018b.WH.W1.rareModel,
    wholeRareS, wholeRareSmall, flipUnit] <;> rfl

theorem rareSmall_flip (u v : RareUnit) :
    wholeRareSmall SAP.P018b.WH.W1.rareModel (flipUnit u) (flipUnit v) =
      wholeRareSmall SAP.P018b.WH.W1.rareModel u v := by
  simp [wholeRareSmall, SAP.P018b.WH.W1.rareModel, flipUnit]

theorem rareSignal_flip (u v : RareUnit) :
    wholeRareA SAP.P018b.WH.W1.rareModel (flipUnit u) (flipUnit v) =
      -wholeRareA SAP.P018b.WH.W1.rareModel u v := by
  simp only [wholeRareA, rareSmall_flip]
  have hA₁ : SAP.P018b.WH.W1.rareModel.A (flipUnit u) =
      !SAP.P018b.WH.W1.rareModel.A u := rfl
  have hA₂ : SAP.P018b.WH.W1.rareModel.A (flipUnit v) =
      !SAP.P018b.WH.W1.rareModel.A v := rfl
  rw [hA₁, hA₂, signValue_flip, signValue_flip]
  split_ifs <;> ring

theorem rareKernelResponse_flip {N : ℕ} (d : AronowAudit.P018.Dyad N) (t : Fin 2)
    (u v : RareUnit) :
    (wholeRareKernel SAP.P018b.WH.W1.rareModel).Y N d t (flipUnit u) (flipUnit v) =
      -(wholeRareKernel SAP.P018b.WH.W1.rareModel).Y N d t u v := by
  simp only [wholeRareKernel]
  have hB₁ : SAP.P018b.signValue (SAP.P018b.WH.W1.rareModel.B (flipUnit u)) =
      -SAP.P018b.signValue (SAP.P018b.WH.W1.rareModel.B u) := by
    simp [SAP.P018b.WH.W1.rareModel, flipUnit, signValue_flip]
  have hB₂ : SAP.P018b.signValue (SAP.P018b.WH.W1.rareModel.B (flipUnit v)) =
      -SAP.P018b.signValue (SAP.P018b.WH.W1.rareModel.B v) := by
    simp [SAP.P018b.WH.W1.rareModel, flipUnit, signValue_flip]
  rw [hB₁, hB₂, rareSignal_flip]
  by_cases ht : t.val = 0 <;> simp [ht] <;> ring

theorem rareResponse_flip {N : ℕ} (ω : Fin N → RareUnit)
    (d : AronowAudit.P018.Dyad N) (t : Fin 2) :
    repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) (flipSample ω) d t =
      -repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω d t := by
  simp only [repeatedY, flipSample]
  exact rareKernelResponse_flip d t _ _

theorem rareDesign_measurable {N : ℕ} (d : AronowAudit.P018.Dyad N) (t : Fin 2) :
    Measurable (fun ω : Fin N → RareUnit =>
      repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω d t) := by
  apply measurable_pi_iff.mpr
  intro j
  have hm : Measurable (fun uv : RareUnit × RareUnit =>
      (wholeRareKernel SAP.P018b.WH.W1.rareModel).X N d t uv.1 uv.2 j) :=
    measurable_of_countable _
  have hp : Measurable (fun ω : Fin N → RareUnit =>
      (ω (AronowAudit.P018.firstUnit d), ω (AronowAudit.P018.secondUnit d))) :=
    (measurable_pi_apply (AronowAudit.P018.firstUnit d)).prodMk
      (measurable_pi_apply (AronowAudit.P018.secondUnit d))
  exact hm.comp hp

theorem rareWholeDesign_measurable {N : ℕ} :
    Measurable (fun ω : Fin N → RareUnit =>
      repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω) := by
  apply measurable_pi_iff.mpr
  intro d
  apply measurable_pi_iff.mpr
  intro t
  exact rareDesign_measurable d t

theorem rareResponse_measurable {N : ℕ} (d : AronowAudit.P018.Dyad N) (t : Fin 2) :
    Measurable (fun ω : Fin N → RareUnit =>
      repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω d t) := by
  have hm : Measurable (fun uv : RareUnit × RareUnit =>
      (wholeRareKernel SAP.P018b.WH.W1.rareModel).Y N d t uv.1 uv.2) :=
    measurable_of_countable _
  have hp : Measurable (fun ω : Fin N → RareUnit =>
      (ω (AronowAudit.P018.firstUnit d), ω (AronowAudit.P018.secondUnit d))) :=
    (measurable_pi_apply (AronowAudit.P018.firstUnit d)).prodMk
      (measurable_pi_apply (AronowAudit.P018.secondUnit d))
  exact hm.comp hp

theorem rareResponse_integrable {N : ℕ} (d : AronowAudit.P018.Dyad N) (t : Fin 2) :
    Integrable (fun ω : Fin N → RareUnit =>
      repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω d t)
      (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw)) := by
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  let f : (Fin N → RareUnit) → ℝ := fun ω =>
    repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω d t
  have hbound : ∀ ω, |f ω| ≤ 4 := by
    intro ω
    exact (SAP.P018b.WH.W1.rareModel_bounds.2 N d t (ω (AronowAudit.P018.firstUnit d))
      (ω (AronowAudit.P018.secondUnit d)))
  have hmem : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw)),
      f ω ∈ Set.Icc (-4) 4 := by
    filter_upwards [] with ω
    exact abs_le.mp (hbound ω)
  exact memLp_one_iff_integrable.1
    (memLp_of_bounded (a := -4) (b := 4) hmem
      (rareResponse_measurable d t).aestronglyMeasurable 1)

theorem rareResponse_integral_on_design_set_zero {N : ℕ}
    (d : AronowAudit.P018.Dyad N) (t : Fin 2)
    (s : Set (Fin N → RareUnit))
    (hs : MeasurableSet[MeasurableSpace.comap
      (fun ω : Fin N → RareUnit =>
        repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω) inferInstance] s) :
    (∫ ω in s, repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω d t
      ∂Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw)) = 0 := by
  classical
  let μ : Measure (Fin N → RareUnit) := Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw)
  let X : (Fin N → RareUnit) → (d : AronowAudit.P018.Dyad N) →
      Fin ((wholeRareKernel SAP.P018b.WH.W1.rareModel).T N d) → AronowAudit.P018.Vec 2 :=
    fun ω => repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω
  let f : (Fin N → RareUnit) → ℝ := fun ω =>
    repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω d t
  have hXmeas : Measurable X := rareWholeDesign_measurable
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  have hpres := flipSample_measurePreserving N
  let e := MeasurableEquiv.ofInvolutive (@flipSample N) flipSample_involutive flipSample_measurable
  have hset : ∀ ω, (flipSample ω ∈ X ⁻¹' B) ↔ ω ∈ X ⁻¹' B := by
    intro ω
    change repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (flipSample ω) ∈ B ↔
      repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω ∈ B
    have hdesign : repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) (flipSample ω) =
        repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω := by
      funext q r
      simpa only [wholeRareKernel] using rareDesign_flip ω q r
    rw [hdesign]
  have hindicator_neg :
      (fun ω => (X ⁻¹' B).indicator f (flipSample ω)) =
        fun ω => -((X ⁻¹' B).indicator f ω) := by
    funext ω
    by_cases hω : ω ∈ X ⁻¹' B
    · have hflip : flipSample ω ∈ X ⁻¹' B := (hset ω).2 hω
      simp [Set.indicator, hω, hflip, f, rareResponse_flip]
    · have hflip : flipSample ω ∉ X ⁻¹' B := by
        intro hh
        exact hω ((hset ω).1 hh)
      simp [Set.indicator, hω, hflip]
  have hfi : Integrable f μ := rareResponse_integrable d t
  have hfi' : Integrable ((X ⁻¹' B).indicator f) μ :=
    hfi.indicator (hXmeas hB)
  have hcomp :
      (∫ ω, (X ⁻¹' B).indicator f (flipSample ω) ∂μ) =
        ∫ ω, (X ⁻¹' B).indicator f ω ∂μ := by
    simpa [μ] using hpres.integral_comp e.measurableEmbedding
      (fun ω => (X ⁻¹' B).indicator f ω)
  have hnegint :
      (∫ ω, -((X ⁻¹' B).indicator f ω) ∂μ) =
        -(∫ ω, (X ⁻¹' B).indicator f ω ∂μ) := by
    simpa only [Pi.neg_apply] using (integral_neg (fun ω => (X ⁻¹' B).indicator f ω))
  rw [hindicator_neg, hnegint] at hcomp
  have hz : (∫ ω, (X ⁻¹' B).indicator f ω ∂μ) = 0 := by linarith
  change (∫ ω in X ⁻¹' B, f ω ∂μ) = 0
  rw [← integral_indicator (hXmeas hB)]
  simpa [f, μ] using hz

theorem condExp_zero_of_setIntegral_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : @Measure Ω mΩ) (m : MeasurableSpace Ω)
    (hm : m ≤ mΩ)
    (hσ : SigmaFinite (μ.trim hm))
    (f : Ω → ℝ) (hfi : Integrable f μ)
    (hzero : ∀ s, MeasurableSet[m] s → μ s < ∞ →
      (∫ x in s, f x ∂μ) = 0) :
    condExp m μ f =ᵐ[μ] 0 := by
  letI := hσ
  symm
  have h0 : Integrable (fun _ : Ω => (0 : ℝ)) μ := by
    exact integrable_zero Ω ℝ μ
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hfi
    (fun s _ _ => ?_) ?_ aestronglyMeasurable_const
  · change IntegrableOn (fun _ : Ω => (0 : ℝ)) s μ
    exact h0.integrableOn
  intro s hs hμs
  calc
    (∫ x in s, (fun _ : Ω => (0 : ℝ)) x ∂μ) = 0 := by simp
    _ = ∫ x in s, f x ∂μ := (hzero s hs hμs).symm

end SAP.P018b.WH.W1.P.T19_L1

namespace SAP.P018b.WH.W1.P.T19_L1
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem rareConditionalMean_one {N : ℕ} (d : AronowAudit.P018.Dyad N) (t : Fin 2) :
    MeasureTheory.condExp
      (MeasurableSpace.comap
        (fun ω : Fin N → RareUnit =>
          repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω) inferInstance)
      (repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N)
      (fun ω => repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω d t)
      =ᵐ[repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N] 0 := by
  classical
  letI : IsProbabilityMeasure AronowAudit.P018.rareLaw :=
    AronowAudit.P018.Wave1.TailB_rare_probability
  have hle : MeasurableSpace.comap
      (fun ω : Fin N → RareUnit =>
        repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω) inferInstance ≤
      (inferInstance : MeasurableSpace (Fin N → RareUnit)) :=
    (rareWholeDesign_measurable (N := N)).comap_le
  letI : IsProbabilityMeasure (repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => AronowAudit.P018.rareLaw))
    infer_instance
  have hfiniteTrim : IsFiniteMeasure
      ((repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N).trim hle) :=
    isFiniteMeasure_trim hle
  have hσ : SigmaFinite
      ((repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N).trim hle) := inferInstance
  have hfi : Integrable
      (fun ω => repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω d t)
      (repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N) := by
    simpa [repeatedLaw, wholeRareKernel, SAP.P018b.WH.W1.rareModel] using
      rareResponse_integrable d t
  exact condExp_zero_of_setIntegral_zero
    (repeatedLaw (wholeRareKernel SAP.P018b.WH.W1.rareModel) N)
    (MeasurableSpace.comap
      (fun ω : Fin N → RareUnit =>
        repeatedX (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω) inferInstance) hle hσ
    (fun ω => repeatedY (wholeRareKernel SAP.P018b.WH.W1.rareModel) ω d t) hfi
    (fun s hs _ => by
      simpa [repeatedLaw, wholeRareKernel, SAP.P018b.WH.W1.rareModel] using
        rareResponse_integral_on_design_set_zero d t s hs)

theorem rareConditionalMean_aux : wholeRareConditionalMean SAP.P018b.WH.W1.rareModel := by
  intro N d t
  exact rareConditionalMean_one d t

end SAP.P018b.WH.W1.P.T19_L1

namespace SAP.P018b.WH.W1
theorem T19_L1_proof : T19_L1 :=
  SAP.P018b.WH.W1.P.T19_L1.rareConditionalMean_aux
end SAP.P018b.WH.W1
end
