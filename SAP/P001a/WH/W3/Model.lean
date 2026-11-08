import SAP.P001a.WH.W3.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace SAP.P001a.WH.W3

theorem uniform_restrict : uniformLaw (0 : ℝ) 1 = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hdensity :
      (fun x : ℝ => ENNReal.ofReal
        (if x ∈ Set.Icc (0 : ℝ) 1 then (1 - 0)⁻¹ else 0)) =
      (Set.Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) := by
    funext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [hx]
  rw [uniformLaw, hdensity, withDensity_indicator_one measurableSet_Icc]

theorem uniform_probability : IsProbabilityMeasure (uniformLaw (0 : ℝ) 1) := by
  rw [uniform_restrict]
  constructor
  simp [Real.volume_Icc]

theorem model_facts {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : ℕ → Ω → ℝ)
    (hiid : IID μ (fun i ω => (X i ω, Y i ω)))
    (hlaw : μ.map (fun ω => (X 0 ω, Y 0 ω)) =
      (uniformLaw 0 1).prod (gaussianReal 0 1)) : SieveModelFactsW3 μ X Y := by
  classical
  letI : IsProbabilityMeasure (uniformLaw (0 : ℝ) 1) := uniform_probability
  have hZ := hiid.1 0
  have hXm : Measurable (X 0) := hZ.fst
  have hYm : Measurable (Y 0) := hZ.snd
  have hXlaw : μ.map (X 0) = uniformLaw 0 1 := by
    change μ.map (Prod.fst ∘ (fun ω => (X 0 ω, Y 0 ω))) = _
    rw [← Measure.map_map measurable_fst hZ, hlaw]
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
  have hYlaw : μ.map (Y 0) = gaussianReal 0 1 := by
    change μ.map (Prod.snd ∘ (fun ω => (X 0 ω, Y 0 ω))) = _
    rw [← Measure.map_map measurable_snd hZ, hlaw]
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
  have hind : IndepFun (X 0) (Y 0) μ := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hYm.aemeasurable).2
    rw [hXlaw, hYlaw]
    exact hlaw
  have hgauss : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) := by
    apply memLp_one_iff_integrable.mp
    simpa using (memLp_id_gaussianReal (μ := 0) (v := 1) (1 : ℝ≥0))
  have hY : Integrable (Y 0) μ := by
    have hid : Integrable (id : ℝ → ℝ) (μ.map (Y 0)) := hYlaw ▸ hgauss
    exact hid.comp_measurable hYm
  have hF : unitDensityW3 = (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp only [unitDensityW3, Set.indicator_apply]
  have hFm : Measurable unitDensityW3 := by
    rw [hF]
    exact measurable_const.indicator measurableSet_Icc
  have hFi : Integrable unitDensityW3 volume := by
    rw [hF]
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by norm_num [Real.volume_Icc]))
  have hpdf : HasPDF (μ.map (X 0)) unitDensityW3 := by
    refine ⟨hFm.aemeasurable, ?_, hFi, ?_⟩
    · intro x
      simp only [unitDensityW3]
      split_ifs <;> norm_num
    · rw [hXlaw]
      simp only [uniformLaw, unitDensityW3, sub_zero, inv_one]
  have hprodY : Integrable (Prod.snd : ℝ × ℝ → ℝ)
      ((uniformLaw 0 1).prod (gaussianReal 0 1)) := hgauss.comp_snd _
  have hcef : IsCEF μ (X 0) (Y 0) (fun _ : ℝ => 0) := by
    refine ⟨measurable_const, hY, integrable_const 0, ?_⟩
    intro A hA
    have hAfst : MeasurableSet (Prod.fst ⁻¹' A : Set (ℝ × ℝ)) := measurable_fst hA
    have htransport := setIntegral_map (μ := μ)
      (g := fun ω => (X 0 ω, Y 0 ω)) (f := Prod.snd)
      hAfst measurable_snd.aestronglyMeasurable hZ.aemeasurable
    rw [hlaw] at htransport
    change (∫ z in Prod.fst ⁻¹' A, z.2 ∂(uniformLaw 0 1).prod (gaussianReal 0 1)) =
      ∫ ω in X 0 ⁻¹' A, Y 0 ω ∂μ at htransport
    have hbox : (Prod.fst ⁻¹' A : Set (ℝ × ℝ)) = A ×ˢ Set.univ := by
      ext z
      simp
    have hzero : (∫ z in Prod.fst ⁻¹' A, z.2
        ∂(uniformLaw 0 1).prod (gaussianReal 0 1)) = 0 := by
      rw [hbox, setIntegral_prod (fun z : ℝ × ℝ => z.2) hprodY.integrableOn]
      simp only [setIntegral_univ, integral_id_gaussianReal, integral_zero]
    simpa only [integral_zero] using htransport.symm.trans hzero
  refine ⟨hXlaw, hYlaw, hind, hpdf, ?_, contDiff_const, hcef, ?_, ?_⟩
  · intro x
    simp only [unitDensityW3]
    split_ifs with h <;> simp [h]
  · intro k
    constructor
    · have h : Integrable (fun x : ℝ => x ^ k) (μ.map (X 0)) := by
        rw [hXlaw, uniform_restrict]
        exact (continuous_id.pow k).integrableOn_Icc
      exact h.comp_measurable hXm
    · have h : Integrable (fun y : ℝ => y ^ k) (μ.map (Y 0)) := by
        rw [hYlaw]
        by_cases hk : k = 0
        · simp [hk]
        · have hnorm := (memLp_id_gaussianReal (μ := 0) (v := 1)
            (k : ℝ≥0)).integrable_norm_pow hk
          apply hnorm.mono' (by fun_prop)
          exact Filter.Eventually.of_forall fun y => by simp [Real.norm_eq_abs, abs_pow]
      exact h.comp_measurable hYm
  · intro δ hδ hδ1
    have hsub : Set.Icc (0 : ℝ) δ ⊆ Set.Icc (0 : ℝ) 1 :=
      fun _ hx => ⟨hx.1, hx.2.trans hδ1⟩
    unfold prob
    change (μ (X 0 ⁻¹' Set.Icc 0 δ)).toReal = δ
    rw [← Measure.map_apply hXm measurableSet_Icc, hXlaw, uniform_restrict,
      Measure.restrict_apply measurableSet_Icc, Set.inter_eq_left.mpr hsub,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hδ.le]

end SAP.P001a.WH.W3
