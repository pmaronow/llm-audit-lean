import SAP.P029b.WH.W2.Leaves
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.IdentDistrib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P029b.WH.W2.P.T27_L1

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Set

noncomputable section

lemma measure_preimage_of_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → CancelAtomW2)
    (hf : MeasurePreserving f μ cancelLawW2) (s : Set CancelAtomW2)
    (hs : MeasurableSet s) : μ (f ⁻¹' s) = cancelLawW2 s := by
  rw [← hf.map_eq, Measure.map_apply hf.measurable hs]

lemma mP_preimage_of_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → CancelAtomW2)
    (hf : MeasurePreserving f μ cancelLawW2) (s : Set CancelAtomW2)
    (hs : MeasurableSet s) :
    mP μ (f ⁻¹' s) = mP cancelLawW2 s := by
  unfold mP
  rw [measure_preimage_of_preserving μ f hf s hs]

lemma setIntegral_preimage_of_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → CancelAtomW2)
    (hf : MeasurePreserving f μ cancelLawW2) (s : Set CancelAtomW2)
    (hs : MeasurableSet s) (g : CancelAtomW2 → ℝ) :
    ∫ ω in f ⁻¹' s, g (f ω) ∂μ = ∫ a in s, g a ∂cancelLawW2 := by
  have hpre : MeasurableSet (f ⁻¹' s) := hf.measurable hs
  have hind : Measurable (Set.indicator s g) := Measurable.of_discrete
  calc
    ∫ ω in f ⁻¹' s, g (f ω) ∂μ =
        ∫ ω, Set.indicator (f ⁻¹' s) (g ∘ f) ω ∂μ := by
          symm
          exact integral_indicator hpre
    _ = ∫ ω, Set.indicator s g (f ω) ∂μ := by
          congr 1
    _ = ∫ a, Set.indicator s g a ∂(Measure.map f μ) := by
          rw [← integral_map hf.measurable.aemeasurable hind.aestronglyMeasurable]
    _ = ∫ a, Set.indicator s g a ∂cancelLawW2 := by rw [hf.map_eq]
    _ = ∫ a in s, g a ∂cancelLawW2 := integral_indicator hs

lemma mCE_preimage_of_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → CancelAtomW2)
    (hf : MeasurePreserving f μ cancelLawW2) (s : Set CancelAtomW2)
    (hs : MeasurableSet s) (g : CancelAtomW2 → ℝ) :
    mCE μ (g ∘ f) (f ⁻¹' s) = mCE cancelLawW2 g s := by
  unfold mCE
  change (∫ ω in f ⁻¹' s, g (f ω) ∂μ) / mP μ (f ⁻¹' s) =
    (∫ a in s, g a ∂cancelLawW2) / mP cancelLawW2 s
  rw [setIntegral_preimage_of_preserving μ f hf s hs g,
    mP_preimage_of_preserving μ f hf s hs]

lemma iv_preimage_of_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → CancelAtomW2)
    (hf : MeasurePreserving f μ cancelLawW2)
    (hiv : IVAssumptions cancelLawW2 cancelUnitW2 Prod.snd) :
    IVAssumptions μ (fun ω => cancelUnitW2 (f ω)) (fun ω => (f ω).2) := by
  rcases hiv with ⟨hxm, hd0m, hd1m, hy0m, hy1m, hZm, hy0int, hy1int,
    hInd, hpos, hlt, hdef, hdiff⟩
  have htuple : Measurable (fun a : CancelAtomW2 =>
      ((cancelUnitW2 a).x, (cancelUnitW2 a).d0, (cancelUnitW2 a).d1,
        (cancelUnitW2 a).y0, (cancelUnitW2 a).y1)) := Measurable.of_discrete
  have hpairmeas : Measurable (fun a : CancelAtomW2 =>
      (a.2, ((cancelUnitW2 a).x, (cancelUnitW2 a).d0, (cancelUnitW2 a).d1,
        (cancelUnitW2 a).y0, (cancelUnitW2 a).y1))) := Measurable.of_discrete
  have hZmeas : Measurable (Prod.snd : CancelAtomW2 → Bool) := Measurable.of_discrete
  have hZpull : μ.map (fun ω => (f ω).2) = cancelLawW2.map Prod.snd := by
    change μ.map ((Prod.snd : CancelAtomW2 → Bool) ∘ f) = _
    rw [← Measure.map_map hZmeas hf.measurable, hf.map_eq]
  have hTuplepull : μ.map (fun ω =>
      ((cancelUnitW2 (f ω)).x, (cancelUnitW2 (f ω)).d0, (cancelUnitW2 (f ω)).d1,
        (cancelUnitW2 (f ω)).y0, (cancelUnitW2 (f ω)).y1)) =
      cancelLawW2.map (fun a =>
        ((cancelUnitW2 a).x, (cancelUnitW2 a).d0, (cancelUnitW2 a).d1,
          (cancelUnitW2 a).y0, (cancelUnitW2 a).y1)) := by
    change μ.map ((fun a : CancelAtomW2 =>
      ((cancelUnitW2 a).x, (cancelUnitW2 a).d0, (cancelUnitW2 a).d1,
        (cancelUnitW2 a).y0, (cancelUnitW2 a).y1)) ∘ f) = _
    rw [← Measure.map_map htuple hf.measurable, hf.map_eq]
  have hpair : μ.map (fun ω =>
      ((f ω).2, ((cancelUnitW2 (f ω)).x, (cancelUnitW2 (f ω)).d0,
        (cancelUnitW2 (f ω)).d1, (cancelUnitW2 (f ω)).y0, (cancelUnitW2 (f ω)).y1))) =
      (μ.map (fun ω => (f ω).2)).prod
        (μ.map (fun ω => ((cancelUnitW2 (f ω)).x, (cancelUnitW2 (f ω)).d0,
          (cancelUnitW2 (f ω)).d1, (cancelUnitW2 (f ω)).y0, (cancelUnitW2 (f ω)).y1))) := by
    calc
      _ = cancelLawW2.map (fun a =>
          (a.2, ((cancelUnitW2 a).x, (cancelUnitW2 a).d0, (cancelUnitW2 a).d1,
            (cancelUnitW2 a).y0, (cancelUnitW2 a).y1))) := by
          change μ.map ((fun a : CancelAtomW2 =>
            (a.2, ((cancelUnitW2 a).x, (cancelUnitW2 a).d0, (cancelUnitW2 a).d1,
              (cancelUnitW2 a).y0, (cancelUnitW2 a).y1))) ∘ f) = _
          rw [← Measure.map_map hpairmeas hf.measurable, hf.map_eq]
      _ = (cancelLawW2.map Prod.snd).prod (cancelLawW2.map fun a =>
          ((cancelUnitW2 a).x, (cancelUnitW2 a).d0, (cancelUnitW2 a).d1,
            (cancelUnitW2 a).y0, (cancelUnitW2 a).y1)) :=
          hInd.map_prod_eq_prod_map_map hZmeas.aemeasurable htuple.aemeasurable
      _ = _ := by
          rw [hZpull, hTuplepull]
  have hIndPull : IndepFun (fun ω => (f ω).2)
      (fun ω => ((cancelUnitW2 (f ω)).x, (cancelUnitW2 (f ω)).d0,
        (cancelUnitW2 (f ω)).d1, (cancelUnitW2 (f ω)).y0,
        (cancelUnitW2 (f ω)).y1)) μ :=
    (indepFun_iff_map_prod_eq_prod_map_map (μ := μ)
      (Measurable.aemeasurable (hZmeas.comp hf.measurable))
      (Measurable.aemeasurable (htuple.comp hf.measurable))).2 hpair
  have htrue : mP μ (f ⁻¹' {a | a.2 = true}) =
      mP cancelLawW2 {a | a.2 = true} :=
    mP_preimage_of_preserving μ f hf _ MeasurableSet.of_discrete
  have hdefmap : μ (f ⁻¹' {a | (cancelUnitW2 a).defier}) =
      cancelLawW2 {a | (cancelUnitW2 a).defier} :=
    measure_preimage_of_preserving μ f hf _ MeasurableSet.of_discrete
  let receiptBit : CancelAtomW2 → ℝ :=
    fun a => bit ((cancelUnitW2 a).receipt a.2)
  have hreceiptTrue : mCE μ (receiptBit ∘ f) (f ⁻¹' {a | a.2 = true}) =
      mCE cancelLawW2 receiptBit {a | a.2 = true} :=
    mCE_preimage_of_preserving μ f hf _ MeasurableSet.of_discrete receiptBit
  have hreceiptFalse : mCE μ (receiptBit ∘ f) (f ⁻¹' {a | a.2 = false}) =
      mCE cancelLawW2 receiptBit {a | a.2 = false} :=
    mCE_preimage_of_preserving μ f hf _ MeasurableSet.of_discrete receiptBit
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hIndPull, ?_, ?_, ?_, ?_⟩
  · exact hxm.comp hf.measurable
  · exact hd0m.comp hf.measurable
  · exact hd1m.comp hf.measurable
  · exact hy0m.comp hf.measurable
  · exact hy1m.comp hf.measurable
  · exact hZm.comp hf.measurable
  · exact hf.integrable_comp_of_integrable hy0int
  · exact hf.integrable_comp_of_integrable hy1int
  · rw [show {ω | (f ω).2 = true} = f ⁻¹' {a | a.2 = true} by rfl, htrue]
    exact hpos
  · rw [show {ω | (f ω).2 = true} = f ⁻¹' {a | a.2 = true} by rfl, htrue]
    exact hlt
  · change μ (f ⁻¹' {a | (cancelUnitW2 a).defier}) = 0
    rw [hdefmap]
    exact hdef
  · rw [show (fun ω => bit ((cancelUnitW2 (f ω)).receipt ((f ω).2))) =
        receiptBit ∘ f by rfl,
      show {ω | (f ω).2 = true} = f ⁻¹' {a | a.2 = true} by rfl,
      show {ω | (f ω).2 = false} = f ⁻¹' {a | a.2 = false} by rfl,
      hreceiptTrue, hreceiptFalse]
    exact hdiff

end
end SAP.P029b.WH.W2.P.T27_L1

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Set

noncomputable section

theorem SAP.P029b.WH.W2.T27_L1_proof : SAP.P029b.WH.W2.T27_L1 := by
  intro hpop
  rcases hpop with ⟨hIV, _, _, hATE, _⟩
  have hbase : IsProbabilityMeasure cancelLawW2 := by infer_instance
  letI : IsProbabilityMeasure cancelLawW2 := hbase
  have hprob : IsProbabilityMeasure cancelSampleLawW2 := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => cancelLawW2))
    infer_instance
  have hind : iIndepFun
      (fun i (ω : CancelSpaceW2) =>
        jointVariables (cancelDrawW2 i) (cancelZW2 i) ω) cancelSampleLawW2 := by
    change iIndepFun (fun i ω => jointVariables cancelUnitW2 Prod.snd (ω i))
      (Measure.infinitePi (fun _ : ℕ => cancelLawW2))
    exact ProbabilityTheory.iIndepFun_infinitePi
        (P := fun _ : ℕ => cancelLawW2)
        (X := fun _ => jointVariables cancelUnitW2 Prod.snd)
        (mX := fun _ => (Measurable.of_discrete :
          Measurable (jointVariables cancelUnitW2 Prod.snd)))
  refine ⟨hprob, hind, ?_, ?_, ?_⟩
  · intro i
    have hID : IdentDistrib (Function.eval i) (Function.eval 0)
        cancelSampleLawW2 cancelSampleLawW2 := by
      refine ⟨(measurable_pi_apply i).aemeasurable,
        (measurable_pi_apply 0).aemeasurable, ?_⟩
      simp [cancelSampleLawW2, Measure.infinitePi_map_eval]
    have hj : Measurable (jointVariables cancelUnitW2 Prod.snd) := Measurable.of_discrete
    change IdentDistrib
      ((jointVariables cancelUnitW2 Prod.snd) ∘ Function.eval i)
      ((jointVariables cancelUnitW2 Prod.snd) ∘ Function.eval 0)
      cancelSampleLawW2 cancelSampleLawW2
    exact hID.comp hj
  · intro i
    have hMP : MeasurePreserving (Function.eval i) cancelSampleLawW2 cancelLawW2 := by
      simpa [cancelSampleLawW2] using
        (measurePreserving_eval_infinitePi (fun _ : ℕ => cancelLawW2) i)
    exact SAP.P029b.WH.W2.P.T27_L1.iv_preimage_of_preserving
      cancelSampleLawW2 (Function.eval i) hMP hIV
  · intro i
    have hMP : MeasurePreserving (Function.eval i) cancelSampleLawW2 cancelLawW2 := by
      simpa [cancelSampleLawW2] using
        (measurePreserving_eval_infinitePi (fun _ : ℕ => cancelLawW2) i)
    have hτ : Integrable (fun a : CancelAtomW2 => (cancelUnitW2 a).tau) cancelLawW2 := by
      rcases hIV with ⟨_, _, _, _, _, _, hY0, hY1, _, _, _, _, _⟩
      simpa [PotentialUnit.tau] using hY1.sub hY0
    have hτmap : AEStronglyMeasurable (fun a : CancelAtomW2 =>
        (cancelUnitW2 a).tau) (Measure.map (Function.eval i) cancelSampleLawW2) := by
      rw [hMP.map_eq]
      exact hτ.aestronglyMeasurable
    have hmapInt : (∫ a, (cancelUnitW2 a).tau ∂Measure.map (Function.eval i) cancelSampleLawW2) =
        ∫ ω, (cancelUnitW2 ((Function.eval i) ω)).tau ∂cancelSampleLawW2 := by
      exact integral_map (measurable_pi_apply i).aemeasurable hτmap
    rw [hMP.map_eq] at hmapInt
    change (∫ ω, (cancelUnitW2 ((Function.eval i) ω)).tau ∂cancelSampleLawW2) = 0
    rw [hmapInt.symm, hATE]
