import SAP.P018a.Defs.WholeW3
import SAP.P018a.WH.W3.Helpers
import SAP.P018a.Bridge
import AronowAudit.P018.Wave1.Gap.GLP0181B1
import AronowAudit.P018.Wave1.Gap.GLP0181B3
import AronowAudit.P018.Wave1.Gap.GP0181B2
import AronowAudit.P018.Wave1.Gap.GP0181B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section
namespace SAP.P018a.WH.W3
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ENNReal

/-- Identify the expected conditional covariance of the total score with the
full double sum of residual conditional covariance terms. Prove coordinatewise:
use vc3_score_projection and condExp_finsetSum for E[S|X], expand the two finite
sums, use vc3_condterm_entry, and integrate the conditional expectation using
the tower property. All L2 and product integrability bounds follow from
vc3_score_lp and vc3_condscore_top. This does not discard disjoint terms. -/
def T2_L1 : Prop :=
  ∀ {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : Kernel U k), Standing K →
    (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) =
      meanMat (unitSampleLaw K N) (conditionalScoreVarianceW3 K)

/-- Bounded finite-record block scores are square-integrable, even for signed
fixed weights and an arbitrary fixed coefficient. Transport the pair-law bounds
through the distinct endpoint evaluation map; take finite sums of products of
L-infinity record coordinates and constants, then lower the exponent to 2.
The private record_memLp argument in GP0181B2 is a model, not a callable donor.
No uniform-in-N bound or positivity of weights is needed. -/
def T2_L2 : Prop :=
  ∀ {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k), RepeatedAtSize R N →
    ∀ (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (d : Dyad N) (a : Fin k),
      MemLp (fun ω => recordWeightedBlockScore R w β ω d a) 2 (repeatedLaw R N)

/-- Block scores on disjoint dyads are independent, for arbitrary fixed
coefficients and fixed signed record weights. Apply iIndepFun_pi, group the
coordinates by the two disjoint member finsets with indepFun_finset, and compose
with the measurable finite-record score functions. Different dyads may have
different counts and kernels. This is vector independence, not just zero covariance. -/
def T2_L3 : Prop :=
  ∀ {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (R : RepeatedKernel U k), RepeatedAtSize R N →
    ∀ (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (d f : Dyad N),
      ¬overlap d f →
      IndepFun (fun ω => recordWeightedBlockScore R w β ω d)
        (fun ω => recordWeightedBlockScore R w β ω f) (repeatedLaw R N)

/-- A bounded heterogeneous repeated-record witness to the necessity of the
block-mean correction. Use constant iid Unit characteristics, one intercept-only
record per dyad, response +1 on {0,1}, -1 on {2,3}, and 0 elsewhere. The Gram
is 6, the population coefficient is 0 and the two nonzero scores belong to
disjoint dyads. Finite sums and integrals of constants give zero total-score
variance and sparse raw and mean-product sums both equal to 2. Prove the
RepeatedAtSize certificate with bound 1, enumerate the six dyads, and use
integral_const / covariance_const_left. The record functions are allowed to
vary with the dyad by the corrected claim; there is no false single-record
common-kernel assertion in this leaf. -/
def T2_L4 : Prop :=
  ∃ R : RepeatedKernel Unit 1, RepeatedAtSize R 4 ∧ (repeatedH R 4).det ≠ 0 ∧
    let q := repeatedBlockScore R (repeatedBeta R 4)
    meanVec (repeatedLaw R 4) (fun ω => ∑ d : Dyad 4, q ω d) = 0 ∧
    varMat (repeatedLaw R 4) (fun ω => ∑ d : Dyad 4, q ω d) = 0 ∧
    sparseRawW3 (repeatedLaw R 4) q = !![(2 : ℝ)] ∧
    sparseMeansW3 (repeatedLaw R 4) q = !![(2 : ℝ)]

/-- Assembly of the corrected claim. Only the four displayed new steps remain
as hypotheses; all existing results and finite covariance algebra are proved. -/
theorem T2_assembly (h1 : T2_L1.{u}) (h2 : T2_L2.{u}) (h3 : T2_L3.{u})
    (h4 : T2_L4) : T2WholeStatement_W3.{u} := by
  have hbase : T2Statement.{u} := by
    intro U _ k K hK
    exact ⟨AronowAudit.P018.Wave1.variance_correction_proof (Bridge.toKernel K) hK,
      fun N hN => AronowAudit.P018.Wave1.conditional_moment_correction_proof
        (Bridge.toKernel K) hK hN⟩
  refine ⟨hbase, ?_, ?_, ?_, h4⟩
  · intro U _ k K hK
    refine ⟨?_, gamma_symmetricW3 K⟩
    intro N hN
    have hM := omittedVariance_eqW3 (N := N) K hK
    have hC := h1 K hK (N := N)
    have hdecomp : varMat (unitSampleLaw K N) (scoreSum K) =
        (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) + omittedVarianceW3 K :=
      (AronowAudit.P018.Wave1.vc3_conditional_decomposition (N := N) (Bridge.toKernel K) hK).1
    have hraw : correctedSigma K N = diagonalNeighborsW3 (N := N) (scoreMomentW3 K) := by
      rw [diagonalNeighbors_eqW3]
      have hexp : correctedSigma K N = ∑ d : Dyad N, ∑ f : Dyad N,
          if overlap d f then meanMat (unitSampleLaw K N) (fun ω =>
            outer (score (design K ω d) (epsilon K ω d))
              (score (design K ω f) (epsilon K ω f))) else 0 :=
        AronowAudit.P018.Wave1.vc3_corrected_expand (Bridge.toKernel K) hK
      rw [hexp]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro f hf
      split_ifs
      · ext a b
        apply integral_congr_ae
        filter_upwards with ω
        simp only [outer, score, Pi.smul_apply,
          smul_eq_mul, Matrix.smul_apply]
        ring
      · rfl
    have hconditional : correctedSigma K N =
        diagonalNeighborsW3 (N := N) (conditionalSecondMomentW3 K) := by
      rw [diagonalNeighbors_eqW3]
      exact (AronowAudit.P018.Wave1.conditional_moment_correction_proof
        (Bridge.toKernel K) hK hN).1
    refine ⟨conditionalScoreSum_eqW3 K hK, hM, hC, ?_, hraw, hconditional,
      ?_, ?_, finiteTarget_eqW3 K hK N hN, ?_⟩
    · rw [← hC, ← hM]
      exact hdecomp
    · intro d
      exact AronowAudit.P018.Wave1.vc3_same_moment (Bridge.toKernel K) hK d
    · intro d f hne hov
      exact AronowAudit.P018.Wave1.vc3_overlap_moment (Bridge.toKernel K) hK d f hne hov
    · change ((N : ℝ)/(Dreal N)^2) • sandwich (populationGram K)⁻¹ (correctedSigma K N) = _
      unfold trueTarget
      have hv : varMat (unitSampleLaw K N) (scoreSum K) = correctedSigma K N :=
        AronowAudit.P018.Wave1.vc3_sparse_variance (Bridge.toKernel K) hK
      rw [hv]
  · have hK : Standing nonlinearKernel := AronowAudit.P018.nonlinear_model_assumptions
    obtain ⟨_, _, _, _, _, _, _, _, hfinite, _⟩ :=
      AronowAudit.P018.Wave1.nonlinear_counterexample_proof
    have hnonlinear := hfinite 3 (by decide)
    have hnv : varMat (unitSampleLaw nonlinearKernel 3) (scoreSum nonlinearKernel) ≠ 0 :=
      hnonlinear.2.2.2
    have hzero : (∑ d : Dyad 3, ∑ f : Dyad 3, conditionalTerm nonlinearKernel d f) = 0 := by
      have hterm (d f : Dyad 3) : conditionalTerm nonlinearKernel d f = 0 := by
        ext a b
        change (∫ ω, conditionalResidualCov nonlinearKernel d f ω *
          (design nonlinearKernel ω d a * design nonlinearKernel ω f b) ∂unitSampleLaw nonlinearKernel 3) = 0
        have hcov : conditionalResidualCov nonlinearKernel d f =ᵐ[unitSampleLaw nonlinearKernel 3] 0 :=
          hnonlinear.1 d f
        calc
          _ = ∫ _ : Fin 3 → ℝ, (0 : ℝ) ∂unitSampleLaw nonlinearKernel 3 := by
            apply integral_congr_ae
            filter_upwards [hcov] with ω hω
            rw [hω]
            simp
          _ = 0 := integral_zero _ _
      simp only [hterm, Finset.sum_const_zero]
    refine ⟨nonlinearKernel, 3, hK, by decide, ?_, ?_⟩
    · exact AronowAudit.P018.Wave1.vc3_dyad_mean (Bridge.toKernel nonlinearKernel) hK
    · have hd : varMat (unitSampleLaw nonlinearKernel 3) (scoreSum nonlinearKernel) =
          (∑ d : Dyad 3, ∑ f : Dyad 3, conditionalTerm nonlinearKernel d f) +
            omittedVarianceW3 (N := 3) nonlinearKernel :=
        (AronowAudit.P018.Wave1.vc3_conditional_decomposition (N := 3)
          (Bridge.toKernel nonlinearKernel) hK).1
      rw [hzero, zero_add] at hd
      exact fun hz => hnv (hd.trans hz)
  · intro U _ k N R hk hN hR
    let : IsProbabilityMeasure R.μ := hR.1
    let : IsProbabilityMeasure (repeatedLaw R N) := by
      unfold repeatedLaw
      infer_instance
    constructor
    · intro hH
      have hd := AronowAudit.P018.Wave1.repeated_target_correction_proof
        (Bridge.toRepeated R) hR hN hH
      have hq (d : Dyad N) (a : Fin k) : MemLp
          (fun ω => repeatedBlockScore R (repeatedBeta R N) ω d a) 2 (repeatedLaw R N) := by
        simpa only [recordWeightedBlockScore, one_mul, repeatedBlockScore] using
          h2 R hR (fun _ _ => 1) (repeatedBeta R N) d a
      have hi (d f : Dyad N) (ho : ¬overlap d f) :
          IndepFun (fun ω => repeatedBlockScore R (repeatedBeta R N) ω d)
            (fun ω => repeatedBlockScore R (repeatedBeta R N) ω f) (repeatedLaw R N) := by
        simpa only [recordWeightedBlockScore, one_mul, repeatedBlockScore] using
          h3 R hR (fun _ _ => 1) (repeatedBeta R N) d f ho
      have hm : meanVec (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
          repeatedBlockScore R (repeatedBeta R N) ω d) = 0 := hd.1
      have hb := blockCovarianceW3 (repeatedLaw R N)
        (repeatedBlockScore R (repeatedBeta R N)) hq hi hm
      refine ⟨repeatedL_posW3 R hR hN, hq, hi, hb, hd.2.1, ?_, hd.2.2.1⟩
      change ((N : ℝ)/(repeatedL R N)^2) • sandwich (repeatedH R N)⁻¹
        (varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
          repeatedBlockScore R (repeatedBeta R N) ω d)) = _
      rw [hb.2.2.1]
    · intro w hH
      have hd := AronowAudit.P018.Wave1.weighted_target_correction_proof
        (Bridge.toRepeated R) hR hN w hH
      have hm : meanVec (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
          recordWeightedBlockScore R w (recordWeightedBeta R w) ω d) = 0 := hd.1
      have hb := blockCovarianceW3 (repeatedLaw R N)
        (recordWeightedBlockScore R w (recordWeightedBeta R w))
        (h2 R hR w (recordWeightedBeta R w)) (h3 R hR w (recordWeightedBeta R w)) hm
      refine ⟨h2 R hR w (recordWeightedBeta R w), h3 R hR w (recordWeightedBeta R w),
        hb, hd.2.1, ?_, hd.2.2.1⟩
      change ((N : ℝ)/(Dreal N)^2) • sandwich (recordWeightedH R w)⁻¹
        (varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
          recordWeightedBlockScore R w (recordWeightedBeta R w) ω d)) = _
      rw [hb.2.2.1]

end SAP.P018a.WH.W3
