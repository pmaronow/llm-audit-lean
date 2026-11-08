import SAP.P001e.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.WH.W2.P.T94_L5

universe u v

noncomputable section

/-- A density version identifies its integrated mean with the moment of the
conditional distribution, almost everywhere under the conditioning law. -/
theorem density_moment_ae {Ω : Type u} {E : Type v}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → E) (Y : Ω → ℝ)
    (f : E → ℝ → ℝ)
    (hf : Measurable (fun w : E × ℝ => f w.1 w.2))
    (hnonneg : ∀ z y, 0 ≤ f z y)
    (hdens : ∀ᵐ z ∂μ.map Z,
      condDistrib Y Z μ z = volume.withDensity (fun y => ENNReal.ofReal (f z y))) :
    (fun z => ∫ y, y * f z y ∂volume) =ᵐ[μ.map Z]
      (fun z => ∫ y, y ∂condDistrib Y Z μ z) := by
  filter_upwards [hdens] with z hz
  have hfy : Measurable (fun y : ℝ => f z y) := by
    simpa [Function.comp_def] using hf.comp (measurable_prodMk_left (x := z))
  have hden : Measurable (fun y : ℝ => ENNReal.ofReal (f z y)) :=
    ENNReal.measurable_ofReal.comp hfy
  calc
    (∫ y, y * f z y ∂volume) =
        ∫ y, (ENNReal.ofReal (f z y)).toReal * y ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [ENNReal.toReal_ofReal (hnonneg z y)]
      ring
    _ = ∫ y, y ∂condDistrib Y Z μ z := by
      rw [hz]
      simpa only [smul_eq_mul] using
        ((integral_withDensity_eq_integral_toReal_smul
          (μ := volume) (f := fun y : ℝ => ENNReal.ofReal (f z y)) hden
          (Eventually.of_forall fun y => ENNReal.ofReal_lt_top) (fun y : ℝ => y)).symm)

/-- Joint measurability of a conditional density gives measurability of its
integrated first moment. -/
theorem measurable_density_moment {E : Type v} [MeasurableSpace E]
    (f : E → ℝ → ℝ) (hf : Measurable (fun w : E × ℝ => f w.1 w.2)) :
    Measurable (fun z => ∫ y, y * f z y ∂volume) := by
  have hprod : Measurable (fun w : E × ℝ => w.2 * f w.1 w.2) :=
    measurable_snd.mul hf
  have hsm : StronglyMeasurable (fun z => ∫ y, y * f z y ∂volume) := by
    simpa using hprod.stronglyMeasurable.integral_prod_right'
  exact hsm.measurable

end

end SAP.P001e.WH.W2.P.T94_L5

open SAP.P001e.WH.W2.P.T94_L5

/-- The requested version-independence leaf. -/
theorem SAP.P001e.WH.W2.T94_L5_proof : SAP.P001e.WH.W2.T94_L5 := by
  intro hL4 Ω Ω' _ _ μ ν _ _ K τ τ' X D Y0 Y1 p X' D' Y0' Y1' p'
    model model' g θ g' θ' correct correct' hlaw
  let Z : Ω → ℝ × (Fin K → ℝ) := fun ω => (D ω, X ω)
  let Z' : Ω' → ℝ × (Fin K → ℝ) := fun ω => (D' ω, X' ω)
  let O : Ω → ℝ := fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)
  let O' : Ω' → ℝ := fun ω => realizedOutcome (Y0' ω) (Y1' ω) (D' ω)
  have hZ : Measurable Z := model.hD.prodMk model.hX
  have hZ' : Measurable Z' := model'.hD.prodMk model'.hX
  have hO : Measurable O := by
    dsimp [O, realizedOutcome]
    exact (model.hY1.mul model.hD).add
      (model.hY0.mul (measurable_const.sub model.hD))
  have hO' : Measurable O' := by
    dsimp [O', realizedOutcome]
    exact (model'.hY1.mul model'.hD).add
      (model'.hY0.mul (measurable_const.sub model'.hD))
  have hjoint : Measurable (fun ω => (Z ω, O ω)) := hZ.prodMk hO
  have hjoint' : Measurable (fun ω => (Z' ω, O' ω)) := hZ'.prodMk hO'
  have hZlaw : μ.map Z = ν.map Z' := by
    calc
      μ.map Z = (μ.map (fun ω => (Z ω, O ω))).fst :=
        (Measure.fst_map_prodMk hZ hO).symm
      _ = (ν.map (fun ω => (Z' ω, O' ω))).fst := congrArg Measure.fst hlaw
      _ = ν.map Z' := Measure.fst_map_prodMk hZ' hO'
  have hXlaw : μ.map X = ν.map X' := by
    calc
      μ.map X = (μ.map Z).map Prod.snd := by
        rw [Measure.map_map measurable_snd hZ]
        rfl
      _ = (ν.map Z').map Prod.snd := congrArg
        (fun m : Measure (ℝ × (Fin K → ℝ)) => m.map Prod.snd) hZlaw
      _ = ν.map X' := by
        rw [Measure.map_map measurable_snd hZ']
        rfl
  have hkernel : condDistrib O Z μ =ᵐ[μ.map Z] condDistrib O' Z' ν := by
    apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hZ hO
    calc
      μ.map (fun ω => (Z ω, O ω)) = ν.map (fun ω => (Z' ω, O' ω)) := hlaw
      _ = (ν.map Z') ⊗ₘ condDistrib O' Z' ν :=
        (compProd_map_condDistrib hZ'.aemeasurable hO'.aemeasurable).symm
      _ = (μ.map Z) ⊗ₘ condDistrib O' Z' ν := by rw [← hZlaw]
  let f : (ℝ × (Fin K → ℝ)) → ℝ → ℝ := fun z y => g y z.1 z.2 θ
  let f' : (ℝ × (Fin K → ℝ)) → ℝ → ℝ := fun z y => g' y z.1 z.2 θ'
  have hf : Measurable (fun w : (ℝ × (Fin K → ℝ)) × ℝ => f w.1 w.2) := by
    simpa [f] using correct.1.1
  have hf' : Measurable (fun w : (ℝ × (Fin K → ℝ)) × ℝ => f' w.1 w.2) := by
    simpa [f'] using correct'.1.1
  have hnonneg : ∀ z y, 0 ≤ f z y := by
    intro z y
    exact correct.1.2.1 z y
  have hnonneg' : ∀ z y, 0 ≤ f' z y := by
    intro z y
    exact correct'.1.2.1 z y
  have hdens : ∀ᵐ z ∂μ.map Z,
      condDistrib O Z μ z = volume.withDensity (fun y => ENNReal.ofReal (f z y)) := by
    simpa [f] using correct.1.2.2
  have hdens' : ∀ᵐ z ∂ν.map Z',
      condDistrib O' Z' ν z = volume.withDensity (fun y => ENNReal.ofReal (f' z y)) := by
    simpa [f'] using correct'.1.2.2
  have hM : (fun z => ∫ y, y * f z y ∂volume) =ᵐ[μ.map Z]
      (fun z => ∫ y, y ∂condDistrib O Z μ z) :=
    density_moment_ae μ Z O f hf hnonneg hdens
  have hM' : (fun z => ∫ y, y * f' z y ∂volume) =ᵐ[ν.map Z']
      (fun z => ∫ y, y ∂condDistrib O' Z' ν z) :=
    density_moment_ae ν Z' O' f' hf' hnonneg' hdens'
  have hM'' : (fun z => ∫ y, y * f' z y ∂volume) =ᵐ[μ.map Z]
      (fun z => ∫ y, y ∂condDistrib O' Z' ν z) := by
    rw [hZlaw]
    exact hM'
  have hmeans : (fun z => ∫ y, y * f z y ∂volume) =ᵐ[μ.map Z]
      (fun z => ∫ y, y * f' z y ∂volume) := by
    filter_upwards [hM, hM'', hkernel] with z hz hz' hk
    calc
      (∫ y, y * f z y ∂volume) = ∫ y, y ∂condDistrib O Z μ z := hz
      _ = ∫ y, y ∂condDistrib O' Z' ν z := by rw [hk]
      _ = ∫ y, y * f' z y ∂volume := hz'.symm
  have hF : Measurable (fun z : ℝ × (Fin K → ℝ) => integratedModelMean g z.1 z.2 θ) := by
    simpa [integratedModelMean, f] using measurable_density_moment f hf
  have hG : Measurable (fun z : ℝ × (Fin K → ℝ) => integratedModelMean g' z.1 z.2 θ') := by
    simpa [integratedModelMean, f'] using measurable_density_moment f' hf'
  have hmeans' : (fun z : ℝ × (Fin K → ℝ) => integratedModelMean g z.1 z.2 θ) =ᵐ[μ.map Z]
      (fun z => integratedModelMean g' z.1 z.2 θ') := by
    simpa [integratedModelMean, f, f'] using hmeans
  have harms := hL4 μ X model.hX D model.hD model.binary p model.propensity model.overlap
    (fun z => integratedModelMean g z.1 z.2 θ)
    (fun z => integratedModelMean g' z.1 z.2 θ') hF hG hmeans'
  refine ⟨hXlaw, ?_⟩
  intro d hd
  simpa [Z] using harms d hd
