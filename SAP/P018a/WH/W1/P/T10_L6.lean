import SAP.P018a.WH.W1.Leaves
import AronowAudit.P018.Wave1.WeightedConsistency.M11

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000

noncomputable section
namespace SAP.P018a.WH.W1.P.T10_L6

open SAP.P018a.WH.W1
open AronowAudit.P018
open AronowAudit.P018.Wave1.WeightedConsistency
open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

theorem meanMat_scale_new {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (F : Ω → SAP.P018a.Mat k) (c : ℝ) :
    SAP.P018a.meanMat μ (fun ω => c • F ω) = c • SAP.P018a.meanMat μ F := by
  ext a b
  change (∫ ω, (c • F ω) a b ∂μ) = c * ∫ ω, (F ω) a b ∂μ
  have hfun : (fun ω => (c • F ω) a b) = (fun ω => c * (F ω a b)) := by
    funext ω
    simp
  rw [hfun, integral_const_mul]

theorem blockScore_uniform_bound
    {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : SAP.P018a.RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : SAP.P018a.Dyad N) → Fin (R.T N d) → ℝ)
    (β : SAP.P018a.Vec k) (C : ℝ)
    (hweights : ∀ N d t, 0 < v N d t ∧ v N d t ≤ C)
    (dir : ∀ N : ℕ, (d : SAP.P018a.Dyad N) → Fin (R.T N d) → Bool)
    (hdir : ∀ N d, Function.Injective (dir N d))
    (hreg : RecordRegular (SAP.P018a.Bridge.toRepeated R)) :
    ∃ Bq : ℝ, 0 ≤ Bq ∧ ∀ N d,
      ∀ᵐ ω ∂AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N,
        ‖AronowAudit.P018.recordWeightedBlockScore (SAP.P018a.Bridge.toRepeated R)
          (v N) β ω d‖ ≤ Bq := by
  classical
  obtain ⟨B, hB, hb⟩ := hreg.2
  let L := |C| * (B + (k : ℝ) * B * ‖β‖) * B
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨2 * L, by positivity, ?_⟩
  intro N d
  filter_upwards [ae_all_iff.mpr (fun t => hb N d t)] with ω hω
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  simp only [AronowAudit.P018.recordWeightedBlockScore, Finset.sum_apply,
    AronowAudit.P018.score, Pi.smul_apply, smul_eq_mul]
  change |∑ t, v N d t *
      (AronowAudit.P018.repeatedY (SAP.P018a.Bridge.toRepeated R) ω d t -
        AronowAudit.P018.dot
          (AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t) β) *
      AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t a| ≤ _
  calc
    _ ≤ ∑ t, |v N d t *
        (AronowAudit.P018.repeatedY (SAP.P018a.Bridge.toRepeated R) ω d t -
          AronowAudit.P018.dot
            (AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t) β) *
        AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin (R.T N d), L := by
      apply Finset.sum_le_sum
      intro t ht
      have hw : |v N d t| ≤ |C| := by
        rw [abs_of_pos (hweights N d t).1]
        exact (hweights N d t).2.trans (le_abs_self C)
      have he : |AronowAudit.P018.repeatedY (SAP.P018a.Bridge.toRepeated R) ω d t -
          AronowAudit.P018.dot
            (AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t) β| ≤
          B + (k : ℝ) * B * ‖β‖ :=
        (abs_sub _ _).trans (add_le_add (hω t).2
          (AronowAudit.P018.Wave1.WeightedConsistency.abs_dot_le_of_norm_le _ _ B (hω t).1))
      have hx : |AronowAudit.P018.repeatedX (SAP.P018a.Bridge.toRepeated R) ω d t a| ≤ B :=
        (norm_le_pi_norm _ a).trans (hω t).1
      simp only [abs_mul]
      dsimp [L]
      exact mul_le_mul (mul_le_mul hw he (abs_nonneg _) (abs_nonneg _)) hx
        (abs_nonneg _) (by positivity)
    _ = (R.T N d : ℝ) * L := by simp
    _ ≤ 2 * L := by
      apply mul_le_mul_of_nonneg_right _ hL
      have hc := Fintype.card_le_of_injective (dir N d) (hdir N d)
      exact_mod_cast (by simpa using hc : R.T N d ≤ 2)

theorem score_bound_of_directed
    {U : Type*} [MeasurableSpace U] {k : ℕ}
    (R : SAP.P018a.RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : SAP.P018a.Dyad N) → Fin (R.T N d) → ℝ)
    (β : SAP.P018a.Vec k) (C : ℝ)
    (hweights : ∀ N d t, 0 < v N d t ∧ v N d t ≤ C)
    (dir : ∀ N : ℕ, (d : SAP.P018a.Dyad N) → Fin (R.T N d) → Bool)
    (hdir : ∀ N d, Function.Injective (dir N d))
    (hreg : RecordRegular (SAP.P018a.Bridge.toRepeated R)) :
    ∃ Bq : ℝ, 0 ≤ Bq ∧ ∀ N d,
      ∀ᵐ ω ∂AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N,
        ‖AronowAudit.P018.recordWeightedBlockScore (SAP.P018a.Bridge.toRepeated R)
          (v N) β ω d‖ ≤ Bq := by
  exact blockScore_uniform_bound R v β C hweights dir hdir hreg

end SAP.P018a.WH.W1.P.T10_L6

open SAP.P018a.WH.W1
open SAP.P018a.WH.W1.P.T10_L6
open AronowAudit.P018
open AronowAudit.P018.Wave1.WeightedConsistency
open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

theorem SAP.P018a.WH.W1.T10_L6_proof : SAP.P018a.WH.W1.T10_L6 := by
  classical
  intro U hU k R K dir v C H hS hreg hcent
  rcases hS with ⟨hK, hrecords, hweights, hpos, hlim⟩
  have hdir : ∀ N d, Function.Injective (dir N d) := hrecords.2.1
  have hμ : R.μ = K.μ := hrecords.1
  have hβ : AronowAudit.P018.Wave1.WeightedConsistency.popBeta R.μ K.X K.Y =
      SAP.P018a.populationBeta K := by
    have hQ : AronowAudit.P018.Wave1.WeightedConsistency.popQ K.μ K.X =
        SAP.P018a.populationGram K := by
      ext a b
      rfl
    have hR : AronowAudit.P018.Wave1.WeightedConsistency.popR K.μ K.X K.Y =
        SAP.P018a.meanVec (K.μ.prod K.μ)
          (fun uv => SAP.P018a.score (K.X uv.1 uv.2) (K.Y uv.1 uv.2)) := by
      funext a
      rfl
    rw [hμ]
    simp [AronowAudit.P018.Wave1.WeightedConsistency.popBeta, hQ, hR,
      SAP.P018a.populationBeta]
  let β := AronowAudit.P018.Wave1.WeightedConsistency.popBeta R.μ K.X K.Y
  obtain ⟨Bq, hBq, hbound⟩ :=
    SAP.P018a.WH.W1.P.T10_L6.score_bound_of_directed R v β C hweights dir hdir hreg
  letI : IsProbabilityMeasure R.μ := by rw [hμ]; exact hK.1
  have hprob (N : ℕ) : IsProbabilityMeasure
      (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => R.μ))
    infer_instance
  letI : ∀ N : ℕ, IsProbabilityMeasure
      (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N) := hprob
  constructor
  · intro N hN
    let q : AronowAudit.P018.Dyad N → (Fin N → U) → AronowAudit.P018.Vec k :=
      fun d ω => AronowAudit.P018.recordWeightedBlockScore
        (SAP.P018a.Bridge.toRepeated R) (v N) β ω d
    have hLp (d : AronowAudit.P018.Dyad N) (a : Fin k) :
        MemLp (fun ω => q d ω a) 2
          (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N) := by
      apply MemLp.of_bound
        (AronowAudit.P018.Wave1.WeightedConsistency.blockScore_measurable
          (SAP.P018a.Bridge.toRepeated R) hreg (v N) β d a).aestronglyMeasurable Bq
      filter_upwards [hbound N d] with ω hω
      exact (norm_le_pi_norm _ a).trans hω
    have hzero (d : AronowAudit.P018.Dyad N) : meanVec
        (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N) (q d) = 0 := by
      let dS : SAP.P018a.Dyad N := d
      have he := SAP.P018a.Bridge.endpoints_agree dS
      have hs : q d = (fun ω => SAP.P018a.recordWeightedBlockScore R
          (v N) (SAP.P018a.populationBeta K) ω dS) := by
        funext ω
        ext a
        simp only [q, β, AronowAudit.P018.recordWeightedBlockScore,
          AronowAudit.P018.score, AronowAudit.P018.repeatedX,
          AronowAudit.P018.repeatedY, AronowAudit.P018.dot,
          SAP.P018a.recordWeightedBlockScore, SAP.P018a.score,
          SAP.P018a.repeatedX, SAP.P018a.repeatedY, SAP.P018a.dot,
          SAP.P018a.Bridge.toRepeated]
        rw [← he.1, ← he.2, hβ]
        rfl
      rw [hs]
      exact hcent N dS
    have hcov (d f : AronowAudit.P018.Dyad N)
        (hdf : ¬(AronowAudit.P018.members d ∩ AronowAudit.P018.members f).Nonempty) :
        AronowAudit.P018.covMat
          (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N) (q d) (q f) = 0 := by
      ext a b
      exact AronowAudit.P018.Wave1.WeightedConsistency.g2_proof R.μ
        (AronowAudit.P018.members d) (AronowAudit.P018.members f)
        (fun ω => q d ω a) (fun ω => q f ω b)
        (Finset.disjoint_iff_inter_eq_empty.mpr
          (Finset.not_nonempty_iff_eq_empty.mp hdf))
        (AronowAudit.P018.Wave1.WeightedConsistency.blockScore_measurable
          (SAP.P018a.Bridge.toRepeated R) hreg (v N) β d a)
        (AronowAudit.P018.Wave1.WeightedConsistency.blockScore_measurable
          (SAP.P018a.Bridge.toRepeated R) hreg (v N) β f b)
        (fun ω ω' h => congrFun
          (AronowAudit.P018.Wave1.WeightedConsistency.blockScore_support
            (SAP.P018a.Bridge.toRepeated R) (v N) β d ω ω' h) a)
        (fun ω ω' h => congrFun
          (AronowAudit.P018.Wave1.WeightedConsistency.blockScore_support
            (SAP.P018a.Bridge.toRepeated R) (v N) β f ω ω' h) b)
        (hLp d a) (hLp f b)
    have hv := AronowAudit.P018.variance_sparse_identity
      (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N)
      AronowAudit.P018.members q hLp hzero hcov
    rw [← hβ]
    unfold scaledMeatAt targetMeat
    rw [SAP.P018a.WH.W1.P.T10_L6.meanMat_scale_new]
    congr 1
    rw [hv]
    ext a b
    change (∫ ω, (AronowAudit.P018.meat AronowAudit.P018.members
      (fun d => q d ω)) a b
        ∂AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N) = _
    simp only [AronowAudit.P018.meat, Matrix.sum_apply, matrix_ite_apply,
      AronowAudit.P018.outer, Matrix.zero_apply, Pi.zero_apply]
    have hi (d f : AronowAudit.P018.Dyad N) : Integrable
        (fun ω => if (AronowAudit.P018.members d ∩ AronowAudit.P018.members f).Nonempty then
          q d ω a * q f ω b else 0)
        (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N) := by
      split_ifs
      · exact (hLp d a).integrable_mul (hLp f b)
      · exact integrable_const _
    rw [integral_finsetSum _ (fun d _ => integrable_finset_sum _ (fun f _ => hi d f))]
    simp_rw [integral_finsetSum _ (fun f _ => hi _ f)]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro f hf
    split_ifs <;> simp [SAP.P018a.meanMat, SAP.P018a.outer,
      AronowAudit.P018.meanMat, AronowAudit.P018.outer]
  · refine ⟨32 * Bq ^ 2, ?_⟩
    intro N
    rw [← hβ]
    by_cases hN : 2 ≤ N
    · have hLp (d : AronowAudit.P018.Dyad N) (a : Fin k) :
          MemLp (fun ω => AronowAudit.P018.recordWeightedBlockScore
            (SAP.P018a.Bridge.toRepeated R) (v N) β ω d a) 2
            (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N) := by
        apply MemLp.of_bound
          (AronowAudit.P018.Wave1.WeightedConsistency.blockScore_measurable
            (SAP.P018a.Bridge.toRepeated R) hreg (v N) β d a).aestronglyMeasurable Bq
        filter_upwards [hbound N d] with ω hω
        exact (norm_le_pi_norm _ a).trans hω
      have hboundA (d : AronowAudit.P018.Dyad N) (a : Fin k) :
          ∀ᵐ ω ∂AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N,
            |AronowAudit.P018.recordWeightedBlockScore
              (SAP.P018a.Bridge.toRepeated R) (v N) β ω d a| ≤ Bq := by
        filter_upwards [hbound N d] with ω hω
        exact (norm_le_pi_norm _ a).trans hω
      have hcov (d f : AronowAudit.P018.Dyad N) (a b : Fin k) :
          |covariance
            (fun ω => AronowAudit.P018.recordWeightedBlockScore
              (SAP.P018a.Bridge.toRepeated R) (v N) β ω d a)
            (fun ω => AronowAudit.P018.recordWeightedBlockScore
              (SAP.P018a.Bridge.toRepeated R) (v N) β ω f b)
            (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N)| ≤
          if AronowAudit.P018.overlap d f then 2 * Bq ^ 2 else 0 := by
        split_ifs with hov
        · exact AronowAudit.P018.Wave1.WeightedConsistency.abs_covariance_le_two_sq _
            (hLp d a) (hLp f b) (hboundA d a) (hboundA f b)
        · have hz := AronowAudit.P018.Wave1.WeightedConsistency.g2_proof R.μ
            (AronowAudit.P018.members d) (AronowAudit.P018.members f)
            (fun ω => AronowAudit.P018.recordWeightedBlockScore
              (SAP.P018a.Bridge.toRepeated R) (v N) β ω d a)
            (fun ω => AronowAudit.P018.recordWeightedBlockScore
              (SAP.P018a.Bridge.toRepeated R) (v N) β ω f b)
            (Finset.disjoint_iff_inter_eq_empty.mpr
              (Finset.not_nonempty_iff_eq_empty.mp hov))
            (AronowAudit.P018.Wave1.WeightedConsistency.blockScore_measurable
              (SAP.P018a.Bridge.toRepeated R) hreg (v N) β d a)
            (AronowAudit.P018.Wave1.WeightedConsistency.blockScore_measurable
              (SAP.P018a.Bridge.toRepeated R) hreg (v N) β f b)
            (fun ω ω' h => congrFun
              (AronowAudit.P018.Wave1.WeightedConsistency.blockScore_support
                (SAP.P018a.Bridge.toRepeated R) (v N) β d ω ω' h) a)
            (fun ω ω' h => congrFun
              (AronowAudit.P018.Wave1.WeightedConsistency.blockScore_support
                (SAP.P018a.Bridge.toRepeated R) (v N) β f ω ω' h) b)
            (hLp d a) (hLp f b)
          have hz' : covariance
              (fun ω => AronowAudit.P018.recordWeightedBlockScore
                (SAP.P018a.Bridge.toRepeated R) (v N) β ω d a)
              (fun ω => AronowAudit.P018.recordWeightedBlockScore
                (SAP.P018a.Bridge.toRepeated R) (v N) β ω f b)
              (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N) = 0 := by
            simpa [AronowAudit.P018.repeatedLaw, SAP.P018a.Bridge.toRepeated] using hz
          rw [hz']
          norm_num
      have hv (a b : Fin k) :
          |AronowAudit.P018.varMat
            (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N)
            (fun ω => ∑ d : AronowAudit.P018.Dyad N,
              AronowAudit.P018.recordWeightedBlockScore
                (SAP.P018a.Bridge.toRepeated R) (v N) β ω d) a b| ≤
          2 * Bq ^ 2 * (N : ℝ) ^ 3 := by
        change |covariance
          (fun ω => (∑ d : AronowAudit.P018.Dyad N,
            AronowAudit.P018.recordWeightedBlockScore
              (SAP.P018a.Bridge.toRepeated R) (v N) β ω d) a)
          (fun ω => (∑ d : AronowAudit.P018.Dyad N,
            AronowAudit.P018.recordWeightedBlockScore
              (SAP.P018a.Bridge.toRepeated R) (v N) β ω d) b) _| ≤ _
        simp only [Finset.sum_apply]
        rw [covariance_fun_sum_fun_sum (fun d => hLp d a) (fun f => hLp f b)]
        calc
          _ ≤ ∑ d, |∑ f, covariance
              (fun ω => AronowAudit.P018.recordWeightedBlockScore
                (SAP.P018a.Bridge.toRepeated R) (v N) β ω d a)
              (fun ω => AronowAudit.P018.recordWeightedBlockScore
                (SAP.P018a.Bridge.toRepeated R) (v N) β ω f b)
              (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ d, ∑ f, if AronowAudit.P018.overlap d f then 2 * Bq ^ 2 else 0 := by
            apply Finset.sum_le_sum
            intro d hd
            exact (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum (fun f _ => hcov d f a b))
          _ = 2 * Bq ^ 2 * ∑ d : AronowAudit.P018.Dyad N,
              ((univ.filter (fun f : AronowAudit.P018.Dyad N =>
                (AronowAudit.P018.members d ∩ AronowAudit.P018.members f).Nonempty)).card : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d hd
            rw [← Finset.sum_filter]
            simp only [sum_const, nsmul_eq_mul]
            have he : (univ : Finset (AronowAudit.P018.Dyad N)).filter
                (fun f => AronowAudit.P018.overlap d f) =
                (univ : Finset (AronowAudit.P018.Dyad N)).filter
                (fun f => (AronowAudit.P018.members d ∩ AronowAudit.P018.members f).Nonempty) := by
              apply Finset.filter_congr
              intro f hf
              rfl
            rw [he]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (AronowAudit.P018.Wave1.WeightedConsistency.g4_proof N).1 (by positivity)
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro a
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro b
      change |((N : ℝ) / (AronowAudit.P018.Dreal N) ^ 2) *
        AronowAudit.P018.varMat
          (AronowAudit.P018.repeatedLaw (SAP.P018a.Bridge.toRepeated R) N)
          (fun ω => ∑ d : AronowAudit.P018.Dyad N,
            AronowAudit.P018.recordWeightedBlockScore
              (SAP.P018a.Bridge.toRepeated R) (v N) β ω d) a b| ≤ _
      rw [abs_mul, abs_of_nonneg (show 0 ≤ (N : ℝ) / (AronowAudit.P018.Dreal N) ^ 2 by positivity)]
      calc
        _ ≤ ((N : ℝ) / (AronowAudit.P018.Dreal N) ^ 2) *
            (2 * Bq ^ 2 * (N : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left (hv a b) (by positivity)
        _ = 2 * Bq ^ 2 * (((N : ℝ) / (AronowAudit.P018.Dreal N) ^ 2) * (N : ℝ) ^ 3) := by ring
        _ ≤ 2 * Bq ^ 2 * 16 :=
          mul_le_mul_of_nonneg_left
            (AronowAudit.P018.Wave1.WeightedConsistency.normalized_dyad_count_le hN)
            (by positivity)
        _ = 32 * Bq ^ 2 := by ring
    · have hsmall : N = 0 ∨ N = 1 := by omega
      rcases hsmall with rfl | rfl <;>
        simp [targetMeat, AronowAudit.P018.Dreal] <;> positivity

end
