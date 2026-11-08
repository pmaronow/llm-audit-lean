import SAP.P001e.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

theorem SAP.P001e.WH.W2.T94_L1_proof : SAP.P001e.WH.W2.T94_L1 := by
  intro Ω E _ _ μ hμ Z hZ Y hY hi f hf
  rcases hf with ⟨hfmeas, hfnn, hfdens⟩
  let m : E → ℝ := fun z => ∫ y, y * f z y ∂volume
  have hIntegrand : StronglyMeasurable (fun p : E × ℝ => p.2 * f p.1 p.2) := by
    exact measurable_snd.stronglyMeasurable.mul hfmeas.stronglyMeasurable
  have hmStrong : StronglyMeasurable m := by
    have h := hIntegrand.integral_prod_right' (ν := volume)
    simpa [m] using h
  have hDensityMeas (z : E) : Measurable (fun y : ℝ => ENNReal.ofReal (f z y)) := by
    exact ENNReal.measurable_ofReal.comp
      (hfmeas.comp (measurable_const.prodMk measurable_id))
  have hFormula (z : E)
      (hd : condDistrib Y Z μ z = volume.withDensity (fun y => ENNReal.ofReal (f z y))) :
      (∫ y, y ∂condDistrib Y Z μ z) = ∫ y, y * f z y ∂volume := by
    rw [hd, integral_withDensity_eq_integral_toReal_smul (hDensityMeas z)
      (ae_of_all _ (fun y => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards with y
    rw [ENNReal.toReal_ofReal (hfnn z y), smul_eq_mul]
    ring
  have hce := condExp_ae_eq_integral_condDistrib' (Y := Y) hZ hi
  have hdensZ : ∀ᵐ ω ∂μ,
      condDistrib Y Z μ (Z ω) = volume.withDensity (fun y => ENNReal.ofReal (f (Z ω) y)) :=
    ae_of_ae_map hZ.aemeasurable hfdens
  have hmean : (μ[Y | MeasurableSpace.comap Z inferInstance]) =ᵐ[μ] (m ∘ Z) := by
    filter_upwards [hce, hdensZ] with ω hω hd
    change (μ[Y | MeasurableSpace.comap Z inferInstance]) ω = _ at hω
    change condDistrib Y Z μ (Z ω) = _ at hd
    calc
      (μ[Y | MeasurableSpace.comap Z inferInstance]) ω =
          ∫ y, y ∂condDistrib Y Z μ (Z ω) := hω
      _ = ∫ y, y * f (Z ω) y ∂volume := hFormula (Z ω) hd
      _ = m (Z ω) := rfl
  change Measurable m ∧ Integrable Y μ ∧ Integrable (m ∘ Z) μ ∧
    ∀ A : Set E, MeasurableSet A →
      (∫ ω in Z ⁻¹' A, Y ω ∂μ) = ∫ ω in Z ⁻¹' A, m (Z ω) ∂μ
  refine ⟨hmStrong.measurable, hi, ?_, ?_⟩
  · exact integrable_condExp.congr hmean
  · intro A hA
    have hZA : MeasurableSet (Z ⁻¹' A) := hZ hA
    calc
      (∫ ω in Z ⁻¹' A, Y ω ∂μ) =
          ∫ ω in Z ⁻¹' A, (μ[Y | MeasurableSpace.comap Z inferInstance]) ω ∂μ :=
        (setIntegral_condExp hZ.comap_le hi ⟨A, hA, rfl⟩).symm
      _ = ∫ ω in Z ⁻¹' A, m (Z ω) ∂μ :=
        setIntegral_congr_ae hZA (hmean.mono fun ω hω _ => hω)
