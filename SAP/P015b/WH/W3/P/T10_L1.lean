import SAP.P015b.WH.W3.Leaves
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped MeasureTheory

theorem SAP.P015b.WH.W3.T10_L1_proof : SAP.P015b.WH.W3.T10_L1 := by
  intro Ω E B mΩ mE mB P hP T hT x hx f hf hi
  have hmX : MeasurableSpace.comap x mB ≤ mE := hx.comap_le
  have hcomp : @Measurable Ω B mΩ mB (fun ω => x (T ω)) := hx.comp hT
  have hmC : MeasurableSpace.comap (fun ω => x (T ω)) mB ≤ mΩ := hcomp.comap_le
  have hT' : @Measurable Ω E (MeasurableSpace.comap (fun ω => x (T ω)) mB)
      (MeasurableSpace.comap x mB) T := by
    rw [measurable_iff_comap_le]
    simp [MeasurableSpace.comap_comp, Function.comp_def]
  let k : E → ℝ := (P.map T)[f | MeasurableSpace.comap x mB]
  let g : Ω → ℝ := k ∘ T
  have hki : Integrable k (P.map T) := by
    dsimp [k]
    exact integrable_condExp (m := MeasurableSpace.comap x mB) (μ := P.map T) (f := f)
  have hgi : Integrable g P := by
    dsimp [g]
    exact hki.comp_measurable hT
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap (fun ω => x (T ω)) mB] g P := by
    have hk : StronglyMeasurable[MeasurableSpace.comap x mB] k := by
      dsimp [k]
      exact stronglyMeasurable_condExp (m := MeasurableSpace.comap x mB) (μ := P.map T) (f := f)
    exact (hk.comp_measurable hT').aestronglyMeasurable
  have hfi : Integrable (fun ω => f (T ω)) P := hi.comp_measurable hT
  have huniq : g =ᵐ[P] P[(fun ω => f (T ω)) |
      MeasurableSpace.comap (fun ω => x (T ω)) mB] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hmC hfi
    · intro s hs hsfin
      exact hgi.integrableOn
    · intro s hs hsfin
      obtain ⟨t, ht, rfl⟩ := (MeasurableSpace.measurableSet_comap.mp hs)
      have htX : MeasurableSet[MeasurableSpace.comap x mB] (x ⁻¹' t) :=
        MeasurableSpace.measurableSet_comap.mpr ⟨t, ht, rfl⟩
      have htMap : MeasurableSet (x ⁻¹' t) := hx ht
      have hkmeas : AEStronglyMeasurable k (P.map T) := hki.aestronglyMeasurable
      calc
        ∫ ω in (fun ω => x (T ω)) ⁻¹' t, g ω ∂P
            = ∫ y in x ⁻¹' t, k y ∂P.map T := by
                simpa [g, k, Function.comp_def, Set.preimage_preimage] using
                  (setIntegral_map (μ := P) (g := T) htMap hkmeas hT.aemeasurable).symm
        _ = ∫ y in x ⁻¹' t, f y ∂P.map T :=
              setIntegral_condExp hmX hi htX
        _ = ∫ ω in (fun ω => x (T ω)) ⁻¹' t, f (T ω) ∂P := by
              simpa [Function.comp_def, Set.preimage_preimage] using
                (setIntegral_map (μ := P) (g := T) htMap hf.aestronglyMeasurable
                  hT.aemeasurable)
    · exact hgm
  exact huniq.symm
