import SAP.P006b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory

namespace SAP.P006b.WH.W1.P.T17_L4

lemma maximumDeviation_bound {X U : Type} [Nonempty U]
    (m : X × U → ℝ)
    (hmax : ∀ c : X × U, ∃ v, ∀ u, |m c-m (c.1,u)| ≤ |m c-m (c.1,v)|)
    (x : X) (u v : U) :
    |m (x,u)-m (x,v)| ≤ SAP.P006b.maximumDeviation m (x,u) := by
  obtain ⟨w, hw⟩ := hmax (x,u)
  have hbdd : BddAbove (Set.range (fun z : U => |m (x,u)-m (x,z)|)) := by
    refine ⟨|m (x,u)-m (x,w)|, ?_⟩
    rintro y ⟨z, rfl⟩
    exact hw z
  exact le_csSup hbdd (Set.mem_range_self v)

lemma maximumDeviation_nonneg {X U : Type} [Nonempty U]
    (m : X × U → ℝ)
    (hmax : ∀ c : X × U, ∃ v, ∀ u, |m c-m (c.1,u)| ≤ |m c-m (c.1,v)|)
    (x : X) (u : U) :
    0 ≤ SAP.P006b.maximumDeviation m (x,u) := by
  obtain ⟨v⟩ := ‹Nonempty U›
  exact (abs_nonneg _).trans (maximumDeviation_bound m hmax x u v)

lemma kernelMarginalBaseline_bound {X U : Type} [MeasurableSpace X]
    [MeasurableSpace U] [Nonempty U]
    (κ : Kernel X U) (hκ : IsMarkovKernel κ) (m : X × U → ℝ)
    (hm : Measurable m)
    (hmax : ∀ c : X × U, ∃ v, ∀ u, |m c-m (c.1,u)| ≤ |m c-m (c.1,v)|)
    (x : X) (u : U) :
    |SAP.P006b.kernelMarginalBaseline κ m x-m (x,u)| ≤
      SAP.P006b.maximumDeviation m (x,u) := by
  letI : IsMarkovKernel κ := hκ
  have hκx : IsProbabilityMeasure (κ x) := inferInstance
  let g : U → ℝ := fun v => m (x,v)-m (x,u)
  have hg_meas : Measurable g := by
    exact (hm.comp measurable_prodMk_left).sub measurable_const
  have hD : 0 ≤ SAP.P006b.maximumDeviation m (x,u) :=
    maximumDeviation_nonneg m hmax x u
  have hg_bound (v : U) : |g v| ≤ SAP.P006b.maximumDeviation m (x,u) := by
    dsimp [g]
    rw [abs_sub_comm]
    exact maximumDeviation_bound m hmax x u v
  have hg_integrable : Integrable g (κ x) := by
    apply (integrable_const (SAP.P006b.maximumDeviation m (x,u))).mono'
      hg_meas.aestronglyMeasurable
    filter_upwards with v
    simpa only [Real.norm_eq_abs] using hg_bound v
  have hconst : Integrable (fun _ : U => m (x,u)) (κ x) := integrable_const _
  have hm_section : Integrable (fun v : U => m (x,v)) (κ x) := by
    have heq : g + (fun _ : U => m (x,u)) = fun v => m (x,v) := by
      funext v
      dsimp [g]
      ring
    rw [← heq]
    exact hg_integrable.add hconst
  have hconst_integral : (∫ v : U, m (x,u) ∂κ x) = m (x,u) := by
    simp [hκx.measure_univ]
  have hmean : (∫ v : U, g v ∂κ x) = SAP.P006b.kernelMarginalBaseline κ m x-m (x,u) := by
    rw [integral_sub hm_section hconst]
    simp [g, SAP.P006b.kernelMarginalBaseline, hconst_integral]
  calc
    |SAP.P006b.kernelMarginalBaseline κ m x-m (x,u)| =
        |∫ v : U, g v ∂κ x| := by rw [← hmean]
    _ ≤ ∫ v : U, |g v| ∂κ x := abs_integral_le_integral_abs
    _ ≤ ∫ _v : U, SAP.P006b.maximumDeviation m (x,u) ∂κ x :=
      integral_mono hg_integrable.abs (integrable_const _) hg_bound
    _ = SAP.P006b.maximumDeviation m (x,u) := by
      simp [hκx.measure_univ]

end SAP.P006b.WH.W1.P.T17_L4

theorem SAP.P006b.WH.W1.T17_L4_proof : SAP.P006b.WH.W1.T17_L4 := by
  intro X U mX mU hU Q hQ κ hκ m hm hmi hmax hD
  letI : IsMarkovKernel κ := hκ
  have hjoint : IsProbabilityMeasure (Q.compProd κ) := inferInstance
  have hbase_meas : Measurable (SAP.P006b.kernelMarginalBaseline κ m) := by
    unfold SAP.P006b.kernelMarginalBaseline
    exact hm.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hdev_meas : Measurable (SAP.P006b.kernelMarginalDeviation κ m) := by
    unfold SAP.P006b.kernelMarginalDeviation
    exact ((hbase_meas.comp measurable_fst).sub hm).abs
  have hbound (c : X × U) :
      SAP.P006b.kernelMarginalDeviation κ m c ≤ SAP.P006b.maximumDeviation m c := by
    change |SAP.P006b.kernelMarginalBaseline κ m c.1-m (c.1,c.2)| ≤
      SAP.P006b.maximumDeviation m (c.1,c.2)
    exact SAP.P006b.WH.W1.P.T17_L4.kernelMarginalBaseline_bound
      κ hκ m hm hmax c.1 c.2
  have hdev_integrable : Integrable (SAP.P006b.kernelMarginalDeviation κ m) (Q.compProd κ) := by
    apply hD.mono' hdev_meas.aestronglyMeasurable
    filter_upwards with c
    have hc := hbound c
    simpa [SAP.P006b.kernelMarginalDeviation, Real.norm_eq_abs,
      abs_of_nonneg (SAP.P006b.WH.W1.P.T17_L4.maximumDeviation_nonneg m hmax c.1 c.2)]
      using hc
  refine ⟨hjoint, hdev_integrable, Filter.Eventually.of_forall hbound, ?_⟩
  exact integral_mono_ae hdev_integrable hD (Filter.Eventually.of_forall hbound)
