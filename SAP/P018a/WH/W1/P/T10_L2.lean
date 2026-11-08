import SAP.P018a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P018a.WH.W1.P.T10_L2

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.P018 AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u
noncomputable section

theorem record_memLp_from_regular {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : AronowAudit.P018.RepeatedKernel U k) (hμ : IsProbabilityMeasure R.μ)
    (hreg : AronowAudit.P018.Wave1.WeightedConsistency.RecordRegular R)
    (d : AronowAudit.P018.Dyad N) (t : Fin (R.T N d)) (a : Fin k) :
    MemLp (fun ω => AronowAudit.P018.repeatedX R ω d t a) 2
      (AronowAudit.P018.repeatedLaw R N) ∧
      MemLp (fun ω => AronowAudit.P018.repeatedY R ω d t) 2
        (AronowAudit.P018.repeatedLaw R N) := by
  letI instUnitProbability : IsProbabilityMeasure R.μ := hμ
  letI instSampleProbability : IsProbabilityMeasure (AronowAudit.P018.repeatedLaw R N) := by
    unfold AronowAudit.P018.repeatedLaw
    infer_instance
  obtain ⟨B, hB, hb⟩ := hreg.2
  constructor
  · apply MemLp.of_bound (((measurable_pi_apply a).comp (hreg.1 N d t).1).aestronglyMeasurable) B
    filter_upwards [hb N d t] with ω hω
    exact (norm_le_pi_norm (AronowAudit.P018.repeatedX R ω d t) a).trans hω.1
  · exact MemLp.of_bound (hreg.1 N d t).2.aestronglyMeasurable B
      ((hb N d t).mono fun ω hω => hω.2)

theorem weighted_gram_mean_from_moments {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : AronowAudit.P018.RepeatedKernel U k) (hμ : IsProbabilityMeasure R.μ)
    (hreg : AronowAudit.P018.Wave1.WeightedConsistency.RecordRegular R)
    (X : U → U → Vec k) (Y : U → U → ℝ) (hmom : RecordMoments R X Y)
    (v : (d : AronowAudit.P018.Dyad N) → Fin (R.T N d) → ℝ) :
    AronowAudit.P018.meanMat (AronowAudit.P018.repeatedLaw R N)
        (AronowAudit.P018.recordWeightedGram R v) =
      (∑ d : AronowAudit.P018.Dyad N, ∑ t, v d t) • popQ R.μ X := by
  ext a b
  have hi (d : AronowAudit.P018.Dyad N) (t : Fin (R.T N d)) :
      Integrable (fun ω => v d t * (AronowAudit.P018.repeatedX R ω d t a *
        AronowAudit.P018.repeatedX R ω d t b)) (AronowAudit.P018.repeatedLaw R N) :=
    ((record_memLp_from_regular R hμ hreg d t a).1.integrable_mul
      (record_memLp_from_regular R hμ hreg d t b).1).const_mul _
  change (∫ ω, (AronowAudit.P018.recordWeightedGram R v ω) a b ∂
      AronowAudit.P018.repeatedLaw R N) = _
  simp only [AronowAudit.P018.recordWeightedGram, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, AronowAudit.P018.outer]
  rw [integral_finset_sum _ (fun d _ =>
    integrable_finset_sum _ (fun t _ => hi d t))]
  simp_rw [integral_finset_sum _ (fun t _ => hi _ t), integral_const_mul]
  have hm (d : AronowAudit.P018.Dyad N) (t : Fin (R.T N d)) :
      (∫ ω, AronowAudit.P018.repeatedX R ω d t a * AronowAudit.P018.repeatedX R ω d t b ∂
        AronowAudit.P018.repeatedLaw R N) =
        popQ R.μ X a b := congrFun (congrFun (hmom N d t).1 a) b
  simp_rw [hm, Finset.sum_mul]

theorem weighted_xy_mean_from_moments {U : Type u} [MeasurableSpace U] {k N : ℕ}
    (R : AronowAudit.P018.RepeatedKernel U k) (hμ : IsProbabilityMeasure R.μ)
    (hreg : AronowAudit.P018.Wave1.WeightedConsistency.RecordRegular R)
    (X : U → U → Vec k) (Y : U → U → ℝ) (hmom : RecordMoments R X Y)
    (v : (d : AronowAudit.P018.Dyad N) → Fin (R.T N d) → ℝ) :
    AronowAudit.P018.meanVec (AronowAudit.P018.repeatedLaw R N)
        (AronowAudit.P018.recordWeightedXY R v) =
      (∑ d : AronowAudit.P018.Dyad N, ∑ t, v d t) • popR R.μ X Y := by
  ext a
  have hi (d : AronowAudit.P018.Dyad N) (t : Fin (R.T N d)) :
      Integrable (fun ω => v d t * (AronowAudit.P018.repeatedY R ω d t *
        AronowAudit.P018.repeatedX R ω d t a)) (AronowAudit.P018.repeatedLaw R N) :=
    ((record_memLp_from_regular R hμ hreg d t a).2.integrable_mul
      (record_memLp_from_regular R hμ hreg d t a).1).const_mul _
  change (∫ ω, (AronowAudit.P018.recordWeightedXY R v ω) a ∂
      AronowAudit.P018.repeatedLaw R N) = _
  simp only [AronowAudit.P018.recordWeightedXY, Finset.sum_apply,
    AronowAudit.P018.score, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [integral_finset_sum _ (fun d _ =>
    integrable_finset_sum _ (fun t _ => hi d t))]
  simp_rw [integral_finset_sum _ (fun t _ => hi _ t), integral_const_mul]
  have hm (d : AronowAudit.P018.Dyad N) (t : Fin (R.T N d)) :
      (∫ ω, AronowAudit.P018.repeatedY R ω d t * AronowAudit.P018.repeatedX R ω d t a ∂
        AronowAudit.P018.repeatedLaw R N) =
        popR R.μ X Y a := congrFun (hmom N d t).2 a
  simp_rw [hm, Finset.sum_mul]

theorem weighted_block_mean_zero_of_normal_equation
    {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : AronowAudit.P018.RepeatedKernel U k) (hμ : IsProbabilityMeasure R.μ)
    (hreg : AronowAudit.P018.Wave1.WeightedConsistency.RecordRegular R)
    (X : U → U → Vec k) (Y : U → U → ℝ) (hmom : RecordMoments R X Y)
    (v : ∀ N : ℕ, (d : AronowAudit.P018.Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k)
    (hnormal : (popQ R.μ X).mulVec β = popR R.μ X Y) :
    ∀ N (d : AronowAudit.P018.Dyad N),
      AronowAudit.P018.meanVec (AronowAudit.P018.repeatedLaw R N)
        (fun ω => AronowAudit.P018.recordWeightedBlockScore R (v N) β ω d) = 0 := by
  intro N d
  let ν := AronowAudit.P018.repeatedLaw R N
  have hxy (t : Fin (R.T N d)) (a : Fin k) :
      Integrable (fun ω => AronowAudit.P018.repeatedY R ω d t *
        AronowAudit.P018.repeatedX R ω d t a) ν :=
    (record_memLp_from_regular R hμ hreg d t a).2.integrable_mul
      (record_memLp_from_regular R hμ hreg d t a).1
  have hxx (t : Fin (R.T N d)) (a b : Fin k) :
      Integrable (fun ω => (AronowAudit.P018.repeatedX R ω d t a *
        AronowAudit.P018.repeatedX R ω d t b) * β b) ν :=
    ((record_memLp_from_regular R hμ hreg d t a).1.integrable_mul
      (record_memLp_from_regular R hμ hreg d t b).1).mul_const _
  have hid (t : Fin (R.T N d)) (a : Fin k) (ω : Fin N → U) :
      (AronowAudit.P018.repeatedY R ω d t - AronowAudit.P018.dot
        (AronowAudit.P018.repeatedX R ω d t) β) * AronowAudit.P018.repeatedX R ω d t a =
        AronowAudit.P018.repeatedY R ω d t * AronowAudit.P018.repeatedX R ω d t a -
          ∑ b, (AronowAudit.P018.repeatedX R ω d t a *
            AronowAudit.P018.repeatedX R ω d t b) * β b := by
    simp only [AronowAudit.P018.dot, sub_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hmean (t : Fin (R.T N d)) (a : Fin k) :
      (∫ ω, (AronowAudit.P018.repeatedY R ω d t - AronowAudit.P018.dot
        (AronowAudit.P018.repeatedX R ω d t) β) *
        AronowAudit.P018.repeatedX R ω d t a ∂ν) = 0 := by
    simp_rw [hid]
    rw [integral_sub (hxy t a) (integrable_finset_sum _ (fun b _ => hxx t a b)),
      integral_finset_sum _ (fun b _ => hxx t a b)]
    simp_rw [integral_mul_const]
    have hmxy := congrFun (hmom N d t).2 a
    have hmxx (b : Fin k) := congrFun (congrFun (hmom N d t).1 a) b
    change (∫ ω, AronowAudit.P018.repeatedY R ω d t * AronowAudit.P018.repeatedX R ω d t a ∂ν) =
      popR R.μ X Y a at hmxy
    change ∀ b, (∫ ω, AronowAudit.P018.repeatedX R ω d t a *
      AronowAudit.P018.repeatedX R ω d t b ∂ν) =
      popQ R.μ X a b at hmxx
    rw [hmxy]
    simp_rw [hmxx]
    have he : (popQ R.μ X).mulVec β = popR R.μ X Y := hnormal
    exact sub_eq_zero.mpr (congrFun he a).symm
  ext a
  change (∫ ω, (AronowAudit.P018.recordWeightedBlockScore R (v N) β ω d) a ∂ν) = 0
  simp only [AronowAudit.P018.recordWeightedBlockScore, Finset.sum_apply,
    AronowAudit.P018.score, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [integral_finset_sum _ (fun t _ => ?_)]
  · simp_rw [integral_const_mul, hmean]
    simp
  · apply Integrable.const_mul
    simp_rw [hid]
    exact (hxy _ a).sub (integrable_finset_sum _ (fun b _ => hxx _ a b))

end
end SAP.P018a.WH.W1.P.T10_L2

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open AronowAudit.P018 AronowAudit.P018.Wave1.WeightedConsistency
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

theorem SAP.P018a.WH.W1.T10_L2_proof : SAP.P018a.WH.W1.T10_L2 := by
  intro U _ k R K dir v C H hSetting hRegular hMoments
  let R' : AronowAudit.P018.RepeatedKernel U k := Bridge.toRepeated R
  let v' : ∀ N : ℕ, (d : AronowAudit.P018.Dyad N) →
      Fin (R'.T N d) → ℝ := fun N d t => v N d t
  have hμeq : R'.μ = K.μ := hSetting.2.1.1
  have hμK : IsProbabilityMeasure K.μ := hSetting.1.1
  have hμR : IsProbabilityMeasure R'.μ := by
    rw [hμeq]
    exact hμK
  have hPos : H.PosDef := hSetting.2.2.2.1
  have hWeightedH_eq (N : ℕ) :
      AronowAudit.P018.recordWeightedH R' (v' N) = SAP.P018a.recordWeightedH R (v N) := by
    rfl
  have hlim : Tendsto (fun N : ℕ => AronowAudit.P018.recordWeightedH R' (v' N))
      atTop (𝓝 H) := by
    convert hSetting.2.2.2.2 using 1
    funext N
    exact hWeightedH_eq N
  obtain ⟨j, hj⟩ := hSetting.1.2.2.2.2
  let Q : Mat k := AronowAudit.P018.Wave1.WeightedConsistency.popQ R'.μ K.X
  let r : Vec k := AronowAudit.P018.Wave1.WeightedConsistency.popR R'.μ K.X K.Y
  have hQeq : Q = populationGram K := by
    ext a b
    simp [Q, AronowAudit.P018.Wave1.WeightedConsistency.popQ, populationGram, hμeq,
      AronowAudit.P018.meanMat, SAP.P018a.meanMat, AronowAudit.P018.outer,
      SAP.P018a.outer]
  have hreq : r = meanVec (K.μ.prod K.μ)
      (fun uv => score (K.X uv.1 uv.2) (K.Y uv.1 uv.2)) := by
    ext a
    simp [r, AronowAudit.P018.Wave1.WeightedConsistency.popR, hμeq,
      AronowAudit.P018.meanVec, SAP.P018a.meanVec, AronowAudit.P018.score,
      SAP.P018a.score]
  have hQjj : Q j j = 1 := by
    dsimp [Q, AronowAudit.P018.Wave1.WeightedConsistency.popQ,
      AronowAudit.P018.meanMat, AronowAudit.P018.outer]
    rw [hμeq]
    simp [hj]
  have hGram (N : ℕ) : AronowAudit.P018.recordWeightedH R' (v' N) =
      AronowAudit.P018.Wave1.WeightedConsistency.weightMass R' v' N • Q := by
    change (AronowAudit.P018.Dreal N)⁻¹ •
      AronowAudit.P018.meanMat (AronowAudit.P018.repeatedLaw R' N)
        (AronowAudit.P018.recordWeightedGram R' (v' N)) = _
    rw [SAP.P018a.WH.W1.P.T10_L2.weighted_gram_mean_from_moments
      R' hμR hRegular K.X K.Y hMoments (v' N)]
    simp [Q, AronowAudit.P018.Wave1.WeightedConsistency.weightMass, smul_smul]
  have hMass : Tendsto (AronowAudit.P018.Wave1.WeightedConsistency.weightMass R' v')
      atTop (𝓝 (H j j)) := by
    have hh := ((continuous_apply_apply j j).tendsto H).comp hlim
    convert hh using 1
    funext N
    change AronowAudit.P018.Wave1.WeightedConsistency.weightMass R' v' N =
      AronowAudit.P018.recordWeightedH R' (v' N) j j
    rw [hGram, Matrix.smul_apply, hQjj, smul_eq_mul, mul_one]
  have hHid : H = H j j • Q := by
    apply tendsto_nhds_unique hlim
    have hh := hMass.smul_const Q
    simpa only [← hGram] using hh
  have hQdet : Q.det ≠ 0 := by
    intro hz
    have hd := hPos.det_pos
    rw [hHid, Matrix.det_smul, hz, mul_zero] at hd
    exact (lt_irrefl 0) hd
  have hPopDet : (populationGram K).det ≠ 0 := by
    simpa [hQeq] using hQdet
  have hnormal : Q.mulVec (populationBeta K) = r := by
    rw [hQeq, hreq]
    unfold populationBeta
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hPopDet), Matrix.one_mulVec]
  have hnormalPop :
      (AronowAudit.P018.Wave1.WeightedConsistency.popQ R'.μ K.X).mulVec
        (populationBeta K) = AronowAudit.P018.Wave1.WeightedConsistency.popR R'.μ K.X K.Y := by
    simpa [Q, r] using hnormal
  have hQdetPop :
      (AronowAudit.P018.Wave1.WeightedConsistency.popQ R'.μ K.X).det ≠ 0 := by
    simpa [Q] using hQdet
  refine ⟨hPopDet, ?_, ?_⟩
  · exact SAP.P018a.WH.W1.P.T10_L2.weighted_block_mean_zero_of_normal_equation
      R' hμR hRegular K.X K.Y hMoments v' (populationBeta K) hnormal
  · have hpos : 0 < H j j := hPos.diag_pos (i := j)
    have hevent : ∀ᶠ N : ℕ in atTop,
        0 < AronowAudit.P018.Wave1.WeightedConsistency.weightMass R' v' N :=
      hMass.eventually (Ioi_mem_nhds hpos)
    obtain ⟨Nmass, hNmass⟩ := eventually_atTop.1 hevent
    refine ⟨max Nmass 2, ?_⟩
    intro N hN
    have hNmass' : Nmass ≤ N := (Nat.le_max_left _ _).trans hN
    have hNtwo : 2 ≤ N := (Nat.le_max_right _ _).trans hN
    have hmasspos : 0 < AronowAudit.P018.Wave1.WeightedConsistency.weightMass R' v' N :=
      hNmass N hNmass'
    have hDpos : 0 < AronowAudit.P018.Dreal N := by
      have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNtwo
      dsimp [AronowAudit.P018.Dreal]
      nlinarith
    have hinvD : 0 < (AronowAudit.P018.Dreal N)⁻¹ := inv_pos.mpr hDpos
    have htotalpos : 0 < ∑ d : AronowAudit.P018.Dyad N, ∑ t, v' N d t := by
      have hm : 0 < (AronowAudit.P018.Dreal N)⁻¹ *
          ∑ d : AronowAudit.P018.Dyad N, ∑ t, v' N d t := by
        exact hmasspos
      exact (mul_pos_iff_of_pos_left hinvD).mp hm
    have htotal : (∑ d : AronowAudit.P018.Dyad N, ∑ t, v' N d t) ≠ 0 :=
      ne_of_gt htotalpos
    have hbetaN : AronowAudit.P018.recordWeightedBeta R' (v' N) = populationBeta K := by
      unfold AronowAudit.P018.recordWeightedBeta
      rw [SAP.P018a.WH.W1.P.T10_L2.weighted_gram_mean_from_moments
          R' hμR hRegular K.X K.Y hMoments (v' N),
        SAP.P018a.WH.W1.P.T10_L2.weighted_xy_mean_from_moments
          R' hμR hRegular K.X K.Y hMoments (v' N)]
      rw [matrix_inverse_scale_total _ _ htotal]
      simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
        mul_inv_cancel₀ htotal, one_smul]
      rw [← hnormalPop, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQdetPop), Matrix.one_mulVec]
    exact hbetaN


