import SAP.P029b.WH.W1.Leaves
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

theorem SAP.P029b.WH.W1.T18_L3_proof : SAP.P029b.WH.W1.T18_L3 := by
  intro Ω X _ _ μ hμ U Z c m hiv hv hpos hwf
  classical
  let f : Ω → ℝ := fun ω => if (U ω).complier then (U ω).tau else 0
  let w : Ω → ℝ := fun ω => 1 / c (U ω).x
  let ρ : Measure X := Measure.map (fun ω => (U ω).x) μ
  have hcompSet : MeasurableSet {ω | (U ω).complier} := by
    exact (hiv.2.1 (measurableSet_singleton false)).inter
      (hiv.2.2.1 (measurableSet_singleton true))
  have htau : Integrable (fun ω => (U ω).tau) μ := by
    rcases hiv with ⟨_, _, _, _, _, _, hy0, hy1, _, _, _, _, _⟩
    exact hy1.sub hy0
  have hf : Integrable f μ := by
    dsimp [f]
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using!
      htau.indicator hcompSet
  have hG : covariateSigma U ≤ ‹MeasurableSpace Ω› := hiv.1.comap_le
  have hwG : StronglyMeasurable[covariateSigma U] w := by
    have hxG : Measurable[covariateSigma U] (fun ω => (U ω).x) :=
      Measurable.of_comap_le le_rfl
    dsimp [w]
    exact (measurable_const.div (hv.1.comp hxG)).stronglyMeasurable
  have hpull := condExp_mul_of_stronglyMeasurable_left hwG hwf hf
  have hprodInt : Integrable
      (fun ω => w ω * condExp (covariateSigma U) μ f ω) μ := by
    have hi : Integrable
        (fun ω => condExp (covariateSigma U) μ (fun ω => w ω * f ω) ω) μ :=
      integrable_condExp
    exact hi.congr hpull
  have hcancel : (fun ω => w ω * condExp (covariateSigma U) μ f ω) =ᵐ[μ]
      (fun ω => m (U ω).x) := by
    filter_upwards [hpos, hv.2.2.2] with ω hω hversion
    dsimp [w]
    change c (U ω).x * m (U ω).x =
      condExp (covariateSigma U) μ
        (fun ω => if (U ω).complier then (U ω).tau else 0) ω at hversion
    change 1 / c (U ω).x * condExp (covariateSigma U) μ
        (fun ω => if (U ω).complier then (U ω).tau else 0) ω = _
    rw [← hversion]
    field_simp [ne_of_gt hω]
  have hmX : Integrable (fun ω => m (U ω).x) μ := hprodInt.congr hcancel
  have hmρ : Integrable m ρ := by
    apply (integrable_map_measure hv.2.1.aestronglyMeasurable hiv.1.aemeasurable).2
    exact hmX
  have hposρ : ∀ᵐ x ∂ρ, 0 < c x := by
    apply (ae_map_iff hiv.1.aemeasurable (measurableSet_lt measurable_const hv.1)).2
    simpa using hpos
  have hcancelρ : (fun x => (c x * m x) / c x) =ᵐ[ρ] m := by
    filter_upwards [hposρ] with x hx
    field_simp [ne_of_gt hx]
  have hmap : (∫ x, m x ∂ρ) = ∫ ω, m (U ω).x ∂μ := by
    exact integral_map hiv.1.aemeasurable hv.2.1.aestronglyMeasurable
  have hmain : (∫ ω, w ω * f ω ∂μ) = ∫ x, (c x * m x) / c x ∂ρ := by
    calc
      (∫ ω, w ω * f ω ∂μ) =
          ∫ ω, w ω * condExp (covariateSigma U) μ f ω ∂μ := by
            calc
              _ = ∫ ω, condExp (covariateSigma U) μ
                    (fun ω => w ω * f ω) ω ∂μ :=
                (integral_condExp hG).symm
              _ = _ := integral_congr_ae hpull
      _ = ∫ ω, m (U ω).x ∂μ := integral_congr_ae hcancel
      _ = ∫ x, m x ∂ρ := hmap.symm
      _ = ∫ x, (c x * m x) / c x ∂ρ := (integral_congr_ae hcancelρ).symm
  refine ⟨hmρ, ?_, ?_⟩
  · simpa [f, w] using hmain
  · exact integral_congr_ae hcancelρ

end

