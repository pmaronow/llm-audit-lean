import SAP.P037a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P037a.WH.W2.P.T5_L5

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical Topology

private lemma measurable_positiveOrthantW2 (n : ℕ) :
    MeasurableSet (SAP.P037a.positiveOrthantW2 n) := by
  change MeasurableSet {e : Fin n → ℝ | ∀ i, 0 < e i}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt measurable_const (measurable_pi_apply i)

private lemma measurable_normalizationDomainW2 (m : ℕ) :
    MeasurableSet (SAP.P037a.normalizationDomainW2 m) := by
  change MeasurableSet
    ({z : Fin (m+1) → ℝ | SAP.P037a.headCoordinatesW2 m z ∈ SAP.P037a.openSimplex m} ∩
      {z | 0 < z (Fin.last m)})
  exact (SAP.P037a.WH.W2.measurable_openSimplexW2 m).preimage
      (SAP.P037a.WH.W2.measurable_headW2 m) |>.inter
    (measurableSet_lt measurable_const (measurable_pi_apply _))

private lemma measurable_inverseNormalizationW2 (m : ℕ) :
    Measurable (SAP.P037a.inverseNormalizationW2 m) := by
  apply Measurable.of_eval
  intro i
  change Measurable (fun z : Fin (m+1) → ℝ =>
    z (Fin.last m) * SAP.P037a.appendSimplex m (SAP.P037a.headCoordinatesW2 m z) i)
  exact (measurable_pi_apply (Fin.last m)).mul
    ((measurable_pi_apply i).comp
      ((SAP.P037a.WH.W2.measurable_appendW2 m).comp
        (SAP.P037a.WH.W2.measurable_headW2 m)))

private lemma measurable_expWeightW2 (m : ℕ) :
    Measurable (fun e : Fin (m+1) → ℝ =>
      ENNReal.ofReal (Real.exp (-∑ i, e i))) := by
  fun_prop

private lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (g : β → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    Measure.map f (μ.withDensity (fun x => g (f x))) =
      (Measure.map f μ).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs,
    withDensity_apply _ (hs.preimage hf),
    withDensity_apply g hs,
    setLIntegral_map hs hg hf]

private lemma sum_inverseNormalizationW2 (m : ℕ) (z : Fin (m+1) → ℝ) :
    ∑ i, SAP.P037a.inverseNormalizationW2 m z i = z (Fin.last m) := by
  simp only [SAP.P037a.inverseNormalizationW2, ← Finset.mul_sum,
    SAP.P037a.WH.W2.sum_appendW2, mul_one]

private lemma measurable_chartJacobianW2 (m : ℕ) :
    Measurable (fun z : Fin (m+1) → ℝ =>
      ENNReal.ofReal (z (Fin.last m) ^ m)) := by
  fun_prop

private lemma measurable_chartKernelW2 (m : ℕ) :
    Measurable (fun z : Fin (m+1) → ℝ => ENNReal.ofReal
      (z (Fin.last m)^m * Real.exp (-z (Fin.last m)))) := by
  fun_prop

private lemma chartKernel_eq_densityW2 (m : ℕ) (z : Fin (m+1) → ℝ)
    (hz : z ∈ SAP.P037a.normalizationDomainW2 m) :
    ENNReal.ofReal (z (Fin.last m)^m) *
        ENNReal.ofReal (Real.exp (-∑ i, SAP.P037a.inverseNormalizationW2 m z i)) =
      ENNReal.ofReal (z (Fin.last m)^m * Real.exp (-z (Fin.last m))) := by
  have ht := hz.2
  rw [sum_inverseNormalizationW2]
  rw [ENNReal.ofReal_mul (pow_nonneg ht.le m)]

end

end SAP.P037a.WH.W2.P.T5_L5

open MeasureTheory Set
open scoped BigOperators ENNReal Classical Topology

theorem SAP.P037a.WH.W2.T5_L5_proof : SAP.P037a.WH.W2.T5_L5 := by
  classical
  intro hJ hExp m
  let D := SAP.P037a.normalizationDomainW2 m
  let P := SAP.P037a.positiveOrthantW2 (m+1)
  let H := SAP.P037a.inverseNormalizationW2 m
  let F := SAP.P037a.forwardNormalizationW2 m
  let w : (Fin (m+1) → ℝ) → ENNReal := fun e =>
    ENNReal.ofReal (Real.exp (-∑ i, e i))
  let j : (Fin (m+1) → ℝ) → ENNReal := fun z =>
    ENNReal.ofReal (z (Fin.last m)^m)
  let ν : Measure (Fin (m+1) → ℝ) :=
    (volume.restrict D).withDensity j
  let ρ : Measure (Fin (m+1) → ℝ) :=
    ν.withDensity (fun z => w (H z))
  have hD : MeasurableSet D := by
    exact SAP.P037a.WH.W2.P.T5_L5.measurable_normalizationDomainW2 m
  have hP : MeasurableSet P := by
    exact SAP.P037a.WH.W2.P.T5_L5.measurable_positiveOrthantW2 (m+1)
  have hH : Measurable H := by
    exact SAP.P037a.WH.W2.P.T5_L5.measurable_inverseNormalizationW2 m
  have hF : Measurable F := by
    exact SAP.P037a.WH.W2.measurable_forwardW2 m
  have hw : Measurable w := by
    exact SAP.P037a.WH.W2.P.T5_L5.measurable_expWeightW2 m
  have hj : Measurable j := by
    exact SAP.P037a.WH.W2.P.T5_L5.measurable_chartJacobianW2 m
  have hgeom := SAP.P037a.WH.W2.geometry_proofW2 m
  have hinj : Set.InjOn H D := by
    intro z hz z' hz' hzz'
    calc
      z = F (H z) := (hgeom.2 z hz).2.symm
      _ = F (H z') := congrArg F hzz'
      _ = z' := (hgeom.2 z' hz').2
  have himage : H '' D = P := by
    apply Set.ext
    intro e
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hgeom.2 z hz).1
    · intro he
      refine ⟨F e, (hgeom.1 e he).1, ?_⟩
      exact (hgeom.1 e he).2
  have hderiv : ∀ z ∈ D,
      HasFDerivWithinAt H (fderiv ℝ H z) D z := by
    intro z hz
    exact (hJ m z hz).1.hasFDerivAt.hasFDerivWithinAt
  have hraw := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    (μ := volume) (s := D) (f := H) (f' := fun z => fderiv ℝ H z)
    hD.nullMeasurableSet hderiv hinj
  have hjac :
      (volume.restrict D).withDensity
          (fun z => ENNReal.ofReal |(fderiv ℝ H z).det|) = ν := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hD] with z hz
    change ENNReal.ofReal |(fderiv ℝ H z).det| = ENNReal.ofReal (z (Fin.last m)^m)
    rw [(hJ m z hz).2]
  have hmapν : Measure.map H ν = volume.restrict P := by
    rw [← hjac, hraw, himage]
  have htransport : Measure.map H ρ = (volume.restrict P).withDensity w := by
    dsimp [ρ]
    rw [SAP.P037a.WH.W2.P.T5_L5.map_withDensity_comp ν H w hH hw, hmapν]
  have hkernel :
      (volume.restrict D).withDensity (j * (fun z => w (H z))) =
        (volume.restrict D).withDensity
          (fun z => ENNReal.ofReal
            (z (Fin.last m)^m * Real.exp (-z (Fin.last m)))) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hD] with z hz
    exact SAP.P037a.WH.W2.P.T5_L5.chartKernel_eq_densityW2 m z hz
  have hρlaw : ρ = SAP.P037a.normalizationJointLawW2 m := by
    calc
      ρ = (volume.restrict D).withDensity (j * (fun z => w (H z))) := by
        dsimp [ρ, ν]
        exact (withDensity_mul (volume.restrict D) hj (hw.comp hH)).symm
      _ = (volume.restrict D).withDensity
          (fun z => ENNReal.ofReal
            (z (Fin.last m)^m * Real.exp (-z (Fin.last m)))) := hkernel
      _ = SAP.P037a.normalizationJointLawW2 m := by
          rw [SAP.P037a.normalizationJointLawW2]
          change (volume.restrict D).withDensity
              (fun z => ENNReal.ofReal
                (z (Fin.last m)^m * Real.exp (-z (Fin.last m)))) =
            volume.withDensity (D.indicator (fun z => ENNReal.ofReal
              (z (Fin.last m)^m * Real.exp (-z (Fin.last m)))))
          rw [withDensity_indicator hD]
  have hsource : Measure.map H ρ = SAP.P037a.exponentialInputW2 (m+1) := by
    rw [htransport, ← withDensity_indicator hP]
    change volume.withDensity (SAP.P037a.exponentialDensityW2 (m+1)) = _
    exact (hExp m).1.symm
  have hDρ : ∀ᵐ z ∂ρ, z ∈ D := by
    have hDν : ∀ᵐ z ∂ν, z ∈ D :=
      (withDensity_absolutelyContinuous (volume.restrict D) j).ae_le
        (ae_restrict_mem hD)
    have hDρ' : ∀ᵐ z ∂ρ, z ∈ D :=
      (withDensity_absolutelyContinuous ν (fun z => w (H z))).ae_le hDν
    exact hDρ'
  have hFH : (fun z => F (H z)) =ᵐ[ρ] id := by
    filter_upwards [hDρ] with z hz
    exact (hgeom.2 z hz).2
  have hcomp : Measure.map (fun z => F (H z)) ρ = ρ := by
    rw [Measure.map_congr hFH, Measure.map_id]
  calc
    Measure.map F (SAP.P037a.exponentialInputW2 (m+1)) =
        Measure.map F (Measure.map H ρ) := by rw [hsource]
    _ = Measure.map (fun z => F (H z)) ρ := by
      rw [Measure.map_map hF hH]
      rfl
    _ = SAP.P037a.normalizationJointLawW2 m := by rw [hcomp, hρlaw]
