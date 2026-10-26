import AronowAudit.P018.Wave1.WeightedConsistency.M1
import AronowAudit.P018.Wave1.WeightedConsistency.M0

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

/-- Scalar record coordinates are square integrable under the repeated sample law. -/
theorem record_memLp {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (d : Dyad N) (t : Fin (R.T N d)) (a : Fin k) :
    MemLp (fun ω => repeatedX R ω d t a) 2 (repeatedLaw R N) ∧
      MemLp (fun ω => repeatedY R ω d t) 2 (repeatedLaw R N) := by
  letI instUnitProbability : IsProbabilityMeasure R.μ := hR.1
  letI instSampleProbability : IsProbabilityMeasure (repeatedLaw R N) :=
    repeatedLaw_probability R hR N
  obtain ⟨B, hB, hb⟩ := hreg.2
  constructor
  · apply MemLp.of_bound (((measurable_pi_apply a).comp (hreg.1 N d t).1).aestronglyMeasurable) B
    filter_upwards [hb N d t] with ω hω
    exact (norm_le_pi_norm (repeatedX R ω d t) a).trans hω.1
  · exact MemLp.of_bound (hreg.1 N d t).2.aestronglyMeasurable B
      ((hb N d t).mono fun ω hω => hω.2)

theorem weighted_gram_mean {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (X : U → U → Vec k) (Y : U → U → ℝ) (hmom : RecordMoments R X Y)
    (v : (d : Dyad N) → Fin (R.T N d) → ℝ) :
    meanMat (repeatedLaw R N) (recordWeightedGram R v) =
      (∑ d : Dyad N, ∑ t, v d t) • popQ R.μ X := by
  ext a b
  have hi (d : Dyad N) (t : Fin (R.T N d)) :
      Integrable (fun ω => v d t * (repeatedX R ω d t a * repeatedX R ω d t b))
        (repeatedLaw R N) :=
    ((record_memLp R hR hreg d t a).1.integrable_mul
      (record_memLp R hR hreg d t b).1).const_mul _
  change (∫ ω, (recordWeightedGram R v ω) a b ∂repeatedLaw R N) = _
  simp only [recordWeightedGram, Matrix.sum_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, outer]
  rw [integral_finset_sum _ (fun d _ =>
    integrable_finset_sum _ (fun t _ => hi d t))]
  simp_rw [integral_finset_sum _ (fun t _ => hi _ t), integral_const_mul]
  have hm (d : Dyad N) (t : Fin (R.T N d)) :
      (∫ ω, repeatedX R ω d t a * repeatedX R ω d t b ∂repeatedLaw R N) =
        popQ R.μ X a b := congrFun (congrFun (hmom N d t).1 a) b
  simp_rw [hm, Finset.sum_mul]

theorem weighted_xy_mean {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hreg : RecordRegular R)
    (X : U → U → Vec k) (Y : U → U → ℝ) (hmom : RecordMoments R X Y)
    (v : (d : Dyad N) → Fin (R.T N d) → ℝ) :
    meanVec (repeatedLaw R N) (recordWeightedXY R v) =
      (∑ d : Dyad N, ∑ t, v d t) • popR R.μ X Y := by
  ext a
  have hi (d : Dyad N) (t : Fin (R.T N d)) :
      Integrable (fun ω => v d t * (repeatedY R ω d t * repeatedX R ω d t a))
        (repeatedLaw R N) :=
    ((record_memLp R hR hreg d t a).2.integrable_mul
      (record_memLp R hR hreg d t a).1).const_mul _
  change (∫ ω, (recordWeightedXY R v ω) a ∂repeatedLaw R N) = _
  simp only [recordWeightedXY, Finset.sum_apply, score, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [integral_finset_sum _ (fun d _ =>
    integrable_finset_sum _ (fun t _ => hi d t))]
  simp_rw [integral_finset_sum _ (fun t _ => hi _ t), integral_const_mul]
  have hm (d : Dyad N) (t : Fin (R.T N d)) :
      (∫ ω, repeatedY R ω d t * repeatedX R ω d t a ∂repeatedLaw R N) =
        popR R.μ X Y a := congrFun (hmom N d t).2 a
  simp_rw [hm, Finset.sum_mul]

theorem m3_proof : M3.{u} := by
  intro U _ k R X Y dir v C H hS hreg hmom
  letI instUnitProbability : IsProbabilityMeasure R.μ := hS.1.1
  obtain ⟨j, hj⟩ := (m1_proof R X Y dir v C H hS).2.2.2
  have hQjj : popQ R.μ X j j = 1 := by
    simp [popQ, meanMat, outer, hj]
  have hGram (N : ℕ) : recordWeightedH R (v N) = weightMass R v N • popQ R.μ X := by
    rw [recordWeightedH, weighted_gram_mean R hS.1 hreg X Y hmom, smul_smul]
    rfl
  have hMass : Tendsto (weightMass R v) atTop (𝓝 (H j j)) := by
    have hh := ((continuous_apply_apply j j).tendsto H).comp hS.2.2.2.2.2
    convert hh using 1
    funext N
    change weightMass R v N = recordWeightedH R (v N) j j
    rw [hGram, Matrix.smul_apply, hQjj, smul_eq_mul, mul_one]
  have hH : H = H j j • popQ R.μ X := by
    apply tendsto_nhds_unique hS.2.2.2.2.2
    have hh := hMass.smul_const (popQ R.μ X)
    simpa only [← hGram] using hh
  have hdet : (popQ R.μ X).det ≠ 0 := by
    intro hzero
    have hd := hS.2.2.2.2.1.det_pos
    rw [hH, Matrix.det_smul, hzero, mul_zero] at hd
    exact (lt_irrefl 0) hd
  refine ⟨hdet, ?_, H j j, hS.2.2.2.2.1.diag_pos (i := j), hH, hMass⟩
  intro N hN
  refine ⟨hGram N, ?_⟩
  have hdyad : Nonempty (Dyad N) := Fintype.card_pos_iff.mp (by
    rw [number_of_dyads]
    exact Nat.choose_pos hN)
  letI instDyadNonempty : Nonempty (Dyad N) := hdyad
  have hsum : 0 < ∑ d : Dyad N, ∑ t, v N d t := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro d hd
    have ht : Nonempty (Fin (R.T N d)) :=
      Fin.pos_iff_nonempty.mp (hS.1.2.1 N hN d)
    letI instRecordNonempty : Nonempty (Fin (R.T N d)) := ht
    exact Finset.sum_pos (fun t _ => (hS.2.2.2.1 N d t).1) Finset.univ_nonempty
  unfold recordWeightedBeta popBeta
  rw [weighted_gram_mean R hS.1 hreg X Y hmom,
    weighted_xy_mean R hS.1 hreg X Y hmom,
    matrix_inverse_scale_total _ _ hsum.ne']
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    inv_mul_cancel₀ hsum.ne', mul_inv_cancel₀ hsum.ne', one_smul]

end
end AronowAudit.P018.Wave1.WeightedConsistency
