import SAP.P004a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2.P.T8_L4

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

private def studentMeasure (ν : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (studentDensity ν x))

private lemma studentDensity_pos (ν x : ℝ) (hν : 0 < ν) :
    0 < studentDensity ν x := by
  unfold studentDensity
  apply mul_pos
  · exact AronowAudit.P004.Wave1.t7_student_prefactor_pos ν hν
  · exact Real.rpow_pos_of_pos (by positivity) _

private lemma studentDensity_nonneg (ν x : ℝ) (hν : 0 < ν) :
    0 ≤ studentDensity ν x :=
  (studentDensity_pos ν x hν).le

private lemma studentMeasure_apply_Iic (ν x : ℝ) (hν : 0 < ν)
    (hInt : Integrable (studentDensity ν)) :
    studentMeasure ν (Iic x) = ENNReal.ofReal (∫ t in Iic x, studentDensity ν t) := by
  rw [studentMeasure, withDensity_apply _ measurableSet_Iic]
  symm
  exact ofReal_integral_eq_lintegral_ofReal hInt.integrableOn
    (ae_of_all _ fun t => studentDensity_nonneg ν t hν)

private lemma studentMeasure_isProbability (ν : ℝ) (hν : 0 < ν)
    (hInt : Integrable (studentDensity ν)) (hnorm : (∫ x, studentDensity ν x) = 1) :
    IsProbabilityMeasure (studentMeasure ν) := by
  rw [isProbabilityMeasure_iff]
  rw [studentMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (ae_of_all _ fun x => studentDensity_nonneg ν x hν)]
  rw [hnorm]
  norm_num

private lemma studentDensity_even (ν x : ℝ) :
    studentDensity ν (-x) = studentDensity ν x := by
  simp [studentDensity]

end
end SAP.P004a.WH.W2.P.T8_L4

open SAP.P004a.WH.W2.P.T8_L4
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem SAP.P004a.WH.W2.T8_L4_proof : SAP.P004a.WH.W2.T8_L4 := by
  intro ν hν hInt hnorm
  let μ : Measure ℝ := studentMeasure ν
  have hprob : IsProbabilityMeasure μ := by
    exact studentMeasure_isProbability ν hν hInt hnorm
  letI := hprob
  letI : NullSingletonClass μ := by
    dsimp [μ, studentMeasure]
    infer_instance
  have hcdf : studentCDF ν = ProbabilityTheory.cdf μ := by
    funext x
    rw [ProbabilityTheory.cdf_eq_real]
    rw [measureReal_def]
    have hmass : μ (Iic x) = ENNReal.ofReal (studentCDF ν x) := by
      change studentMeasure ν (Iic x) = _
      rw [studentMeasure_apply_Iic ν x hν hInt]
      rfl
    rw [hmass]
    have hnonneg : 0 ≤ studentCDF ν x := by
      unfold studentCDF
      exact integral_nonneg fun t => studentDensity_nonneg ν t hν
    rw [ENNReal.toReal_ofReal hnonneg]
  have hcont : Continuous (studentCDF ν) := by
    rw [hcdf]
    exact continuous_iff_continuousAt.mpr fun x =>
      AronowAudit.P053.NormalCompletion.cdf_continuousAt μ x
  have hstrict : StrictMono (studentCDF ν) := by
    intro a b hab
    have hsupport : Function.support (studentDensity ν) = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (studentDensity_pos ν x hν).ne'
    have hmass : 0 < (volume.restrict (Ioc a b)) (Function.support (studentDensity ν)) := by
      rw [hsupport, Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter]
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
    have hpositive : 0 < ∫ t in Ioc a b, studentDensity ν t :=
      (integral_pos_iff_support_of_nonneg
        (fun t => studentDensity_nonneg ν t hν)
        (hInt.mono_measure Measure.restrict_le_self)).2 hmass
    have hsplit : studentCDF ν b = studentCDF ν a +
        ∫ t in Ioc a b, studentDensity ν t := by
      unfold studentCDF
      rw [← Iic_union_Ioc_eq_Iic hab.le]
      have hdisj : Disjoint (Iic a) (Ioc a b) := by
        apply disjoint_left.mpr
        intro x hxa hxab
        change x ≤ a at hxa
        exact (not_lt_of_ge hxa) hxab.1
      exact setIntegral_union hdisj measurableSet_Ioc
        hInt.integrableOn hInt.integrableOn
    rw [hsplit]
    linarith
  have hzero : studentCDF ν 0 = 1 / 2 := by
    have hcover : Iic (0 : ℝ) ∪ Ioi 0 = Set.univ := by
      ext x
      simp only [mem_union, mem_Iic, mem_Ioi, mem_univ]
      constructor
      · intro _
        trivial
      · intro _
        exact le_or_gt x 0
    have hdisj : Disjoint (Iic (0 : ℝ)) (Ioi 0) := by
      apply disjoint_left.mpr
      intro x hxIic hxIoi
      change x ≤ 0 at hxIic
      change 0 < x at hxIoi
      linarith
    have hsplit : (∫ x, studentDensity ν x) =
        (∫ x in Iic (0 : ℝ), studentDensity ν x) +
          (∫ x in Ioi 0, studentDensity ν x) := by
      calc
        (∫ x, studentDensity ν x) =
            (∫ x in Iic (0 : ℝ) ∪ Ioi 0, studentDensity ν x) := by
              rw [hcover, setIntegral_univ]
        _ = _ := setIntegral_union hdisj measurableSet_Ioi
          hInt.integrableOn hInt.integrableOn
    have hsymm : (∫ x in Iic (0 : ℝ), studentDensity ν x) =
        (∫ x in Ioi 0, studentDensity ν x) := by
      calc
        (∫ x in Iic (0 : ℝ), studentDensity ν x) =
            (∫ x in Iic (0 : ℝ), studentDensity ν (-x)) := by
              apply setIntegral_congr_fun measurableSet_Iic
              intro x _
              exact (studentDensity_even ν x).symm
        _ = (∫ x in Ioi 0, studentDensity ν x) := by
          simpa using (integral_comp_neg_Iic (0 : ℝ) (studentDensity ν))
    have hhalf : (∫ x in Iic (0 : ℝ), studentDensity ν x) = 1 / 2 := by
      rw [hnorm] at hsplit
      rw [hsymm] at hsplit
      linarith
    simpa [studentCDF] using hhalf
  have htop : Tendsto (studentCDF ν) atTop (nhds 1) := by
    rw [hcdf]
    exact ProbabilityTheory.tendsto_cdf_atTop μ
  exact ⟨hcont, hstrict, hzero, htop⟩

