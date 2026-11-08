import SAP.P018a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W3.P.T2_L1

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ENNReal

theorem conditionalScoreVariance_mean_eq_diff
    {U : Type*} [MeasurableSpace U] {k N : ℕ}
    (K : SAP.P018a.Kernel U k) (hK : SAP.P018a.Standing K) :
    meanMat (unitSampleLaw K N) (conditionalScoreVarianceW3 K) =
      varMat (unitSampleLaw K N) (scoreSum K) -
        varMat (unitSampleLaw K N) (conditionalScoreSumW3 K) := by
  let P := unitSampleLaw K N
  letI : IsProbabilityMeasure K.μ := hK.1
  letI : IsProbabilityMeasure P := by
    dsimp [P, unitSampleLaw]
    infer_instance
  have hX (a : Fin k) : MemLp (fun ω => scoreSum K ω a) 2 P := by
    unfold scoreSum
    simp only [Finset.sum_apply]
    exact memLp_finsetSum univ (fun d _ =>
      AronowAudit.P018.Wave1.vc3_score_lp (SAP.P018a.Bridge.toKernel K) hK d a 2)
  have hA (a : Fin k) :
      MemLp (fun ω => conditionalScoreSumW3 K ω a) 2 P := by
    change MemLp (P[fun ω => scoreSum K ω a | designSigma K]) 2 P
    exact (hX a).condExp (by norm_num)
  have hmSap : designSigma K ≤ (inferInstance : MeasurableSpace (Fin N → U)) := by
    have hdesign : Measurable (design (N := N) K) := by
      apply measurable_pi_lambda
      intro d
      have hp : Measurable (fun ω : Fin N → U =>
          (ω (firstUnit d), ω (secondUnit d))) :=
        (measurable_pi_apply _).prodMk (measurable_pi_apply _)
      simpa only [Function.comp_def, design] using hK.2.1.comp hp
    exact hdesign.comap_le
  have hmDonor := AronowAudit.P018.Wave1.vc3_design_le (N := N)
    (SAP.P018a.Bridge.toKernel K) hK
  haveI : IsFiniteMeasure (P.trim hmSap) :=
    MeasureTheory.isFiniteMeasure_trim hmSap
  haveI : SigmaFinite (P.trim hmSap) := inferInstance
  ext a b
  change (∫ ω, P[(fun z => (scoreSum K z a - conditionalScoreSumW3 K z a) *
      (scoreSum K z b - conditionalScoreSumW3 K z b)) | designSigma K] ω ∂P) =
    ProbabilityTheory.covariance (fun ω => scoreSum K ω a)
      (fun ω => scoreSum K ω b) P -
    ProbabilityTheory.covariance (fun ω => conditionalScoreSumW3 K ω a)
      (fun ω => conditionalScoreSumW3 K ω b) P
  rw [integral_condExp (μ := P) (f := fun z =>
    (scoreSum K z a - conditionalScoreSumW3 K z a) *
      (scoreSum K z b - conditionalScoreSumW3 K z b)) hmSap]
  have htc := by
    letI : IsFiniteMeasure (P.trim hmDonor) :=
      MeasureTheory.isFiniteMeasure_trim hmDonor
    letI : SigmaFinite (P.trim hmDonor) := inferInstance
    exact AronowAudit.P018.Wave1.vc3_total_covariance P
      (AronowAudit.P018.designSigma (SAP.P018a.Bridge.toKernel K)) hmDonor
      (hX a) (hX b) (hA a) (hA b)
      Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl
  linarith

end SAP.P018a.WH.W3.P.T2_L1

theorem SAP.P018a.WH.W3.T2_L1_proof : SAP.P018a.WH.W3.T2_L1 := by
  intro U _ k N K hK
  let P := unitSampleLaw K N
  have hdecomp : varMat P (scoreSum K) =
      (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) +
        varMat P (conditionalScoreSumW3 K) := by
    have hd := (AronowAudit.P018.Wave1.vc3_conditional_decomposition (N := N)
      (SAP.P018a.Bridge.toKernel K) hK).1
    have hcs := conditionalScoreSum_eqW3 (N := N) K hK
    have hmean : varMat P (fun ω => ∑ d : Dyad N,
        score (design K ω d) (conditionalResidualMean K d ω)) =
          varMat P (conditionalScoreSumW3 K) := by
      change covMat P (residualMeanScoreSumW3 K) (residualMeanScoreSumW3 K) = _
      exact covMat_congrW3 P hcs.symm hcs.symm
    change varMat P (scoreSum K) =
      (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) +
        varMat P (fun ω => ∑ d : Dyad N,
          score (design K ω d) (conditionalResidualMean K d ω)) at hd
    rw [hmean] at hd
    exact hd
  have hvar := SAP.P018a.WH.W3.P.T2_L1.conditionalScoreVariance_mean_eq_diff
    (N := N) K hK
  calc
    (∑ d : Dyad N, ∑ f : Dyad N, conditionalTerm K d f) =
        varMat P (scoreSum K) - varMat P (conditionalScoreSumW3 K) := by
      rw [hdecomp]
      ext a b
      simp only [Matrix.add_apply, Matrix.sub_apply]
      ring
    _ = meanMat P (conditionalScoreVarianceW3 K) := hvar.symm
