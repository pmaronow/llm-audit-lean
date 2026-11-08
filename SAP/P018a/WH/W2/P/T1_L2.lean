import SAP.P018a.WH.W2.Leaves
import AronowAudit.P018.Wave1.Gap.GP0181B1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace SAP.P018a.WH.W2.P.T1_L2

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

open SAP.P018a
open AronowAudit.P018
open AronowAudit.P018.Wave1

lemma single_repeated_sigma (N : ℕ) :
    wholeRepeatedDesignSigma (N := N) (singleRecord nonlinearKernel) =
      designSigma nonlinearKernel := by
  let F : (Fin N → ℝ) → ((d : Dyad N) → Fin 1 → Vec 2) :=
    fun ω d t => repeatedX (singleRecord nonlinearKernel) ω d t
  let G : (Fin N → ℝ) → (Dyad N → Vec 2) := design nonlinearKernel
  have hGF : G = (fun x : (d : Dyad N) → Fin 1 → Vec 2 => fun d => x d 0) ∘ F := by
    funext ω
    funext d
    simp [F, G, singleRecord, design, repeatedX]
  have hFG : F = (fun x : Dyad N → Vec 2 => fun d t => x d) ∘ G := by
    funext ω
    funext d
    funext t
    fin_cases t
    simp [F, G, singleRecord, design, repeatedX]
  change MeasurableSpace.comap F inferInstance = MeasurableSpace.comap G inferInstance
  apply le_antisymm
  · exact MeasurableSpace.comap_le_comap_of_eq_comp
      (fun x d t => x d) (by fun_prop) hFG
  · exact MeasurableSpace.comap_le_comap_of_eq_comp
      (fun x d => x d 0) (by fun_prop) hGF

lemma repeated_residual_eq_epsilon (N : ℕ) (hN : 2 ≤ N)
    (ω : Fin N → ℝ) (d : Dyad N) (t : Fin 1) :
    wholeRepeatedResidual (singleRecord nonlinearKernel) ω d t =
      epsilon nonlinearKernel ω d := by
  change nonlinearKernel.Y (ω (firstUnit d)) (ω (secondUnit d)) -
    dot (nonlinearKernel.X (ω (firstUnit d)) (ω (secondUnit d)))
      (repeatedBeta (singleRecord nonlinearKernel) N) = epsilon nonlinearKernel ω d
  have hβsrc := AronowAudit.P018.Wave1.corrected_single_beta
    (Bridge.toKernel nonlinearKernel) AronowAudit.P018.nonlinear_model_assumptions hN
  have hβ : repeatedBeta (singleRecord nonlinearKernel) N = populationBeta nonlinearKernel := by
    exact hβsrc
  rw [hβ]
  rfl

lemma weighted_residual_eq_epsilon (N : ℕ) (hN : 2 ≤ N)
    (ω : Fin N → ℝ) (d : Dyad N) :
    response nonlinearKernel ω d - dot (design nonlinearKernel ω d)
      (weightedPopulationBeta nonlinearKernel (fun _ : Dyad N => 1)) =
      epsilon nonlinearKernel ω d := by
  have hβsrc := AronowAudit.P018.Wave1.corrected_one_beta
    (Bridge.toKernel nonlinearKernel) AronowAudit.P018.nonlinear_model_assumptions hN
  have hβ : weightedPopulationBeta nonlinearKernel (fun _ : Dyad N => 1) =
      populationBeta nonlinearKernel := by
    exact hβsrc
  rw [hβ]
  rfl

end SAP.P018a.WH.W2.P.T1_L2

namespace SAP.P018a.WH.W2

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
open SAP.P018a
open AronowAudit.P018

theorem T1_L2_proof : SAP.P018a.WH.W2.T1_L2 := by
  change T1PrintedZeros
  intro N hN
  have hSrcZeros := AronowAudit.P018.Wave1.nonlinear_counterexample_proof
    |>.2.2.2.2.2.2.2.2.1
  have hSrcCov : ∀ d f : Dyad N,
      AronowAudit.P018.conditionalResidualCov AronowAudit.P018.nonlinearKernel d f =ᵐ[
        AronowAudit.P018.unitSampleLaw AronowAudit.P018.nonlinearKernel N] 0 :=
    (hSrcZeros N hN).1
  have hBridgeCov (d f : Dyad N) :
      AronowAudit.P018.conditionalResidualCov (Bridge.toKernel nonlinearKernel) d f =ᵐ[
        AronowAudit.P018.unitSampleLaw (Bridge.toKernel nonlinearKernel) N] 0 := by
    simpa [Bridge.toKernel, SAP.P018a.nonlinearKernel, AronowAudit.P018.nonlinearKernel,
      SAP.P018a.uniformUnitLaw, AronowAudit.P018.uniformUnitLaw] using
      hSrcCov d f
  have hCov (d f : Dyad N) :
      conditionalResidualCov nonlinearKernel d f =ᵐ[unitSampleLaw nonlinearKernel N] 0 := by
    rw [(Bridge.conditional_quantities_agree nonlinearKernel).2,
      (Bridge.kernel_sample_agrees nonlinearKernel (fun _ => 0)).1]
    exact hBridgeCov d f
  have hTerm (d f : Dyad N) : conditionalTerm nonlinearKernel d f = 0 := by
    ext a b
    unfold conditionalTerm meanMat
    apply integral_eq_zero_of_ae
    filter_upwards [hCov d f] with ω hω
    simp [hω]
  have hAll : ∀ᵐ ω ∂unitSampleLaw nonlinearKernel N,
      ∀ d f : Dyad N, conditionalResidualCov nonlinearKernel d f ω = 0 := by
    classical
    filter_upwards [ae_all_iff.2 (fun d => ae_all_iff.2 (fun f => hCov d f))]
      with ω hω
    exact hω
  have hRepFactor (d f : Dyad N) (t u : Fin 1) (ω : Fin N → ℝ) :
      MeasureTheory.condExp
        (wholeRepeatedDesignSigma (N := N) (singleRecord nonlinearKernel))
        (unitSampleLaw nonlinearKernel N)
        (fun v =>
          (wholeRepeatedResidual (singleRecord nonlinearKernel) v d t -
            MeasureTheory.condExp
              (wholeRepeatedDesignSigma (N := N) (singleRecord nonlinearKernel))
              (unitSampleLaw nonlinearKernel N)
              (fun v => wholeRepeatedResidual (singleRecord nonlinearKernel) v d t) v) *
          (wholeRepeatedResidual (singleRecord nonlinearKernel) v f u -
            MeasureTheory.condExp
              (wholeRepeatedDesignSigma (N := N) (singleRecord nonlinearKernel))
              (unitSampleLaw nonlinearKernel N)
              (fun v => wholeRepeatedResidual (singleRecord nonlinearKernel) v f u) v)) ω =
        conditionalResidualCov nonlinearKernel d f ω := by
    rw [SAP.P018a.WH.W2.P.T1_L2.single_repeated_sigma N]
    simp_rw [SAP.P018a.WH.W2.P.T1_L2.repeated_residual_eq_epsilon N (by omega)]
    simp [conditionalResidualCov, conditionalResidualMean]
  have hWFactor (d f : Dyad N) (ω : Fin N → ℝ) :
      MeasureTheory.condExp (designSigma nonlinearKernel)
        (unitSampleLaw nonlinearKernel N)
        (fun v =>
          (response nonlinearKernel v d - dot (design nonlinearKernel v d)
              (weightedPopulationBeta nonlinearKernel (fun _ : Dyad N => 1)) -
            MeasureTheory.condExp (designSigma nonlinearKernel)
              (unitSampleLaw nonlinearKernel N)
              (fun v => response nonlinearKernel v d - dot (design nonlinearKernel v d)
                (weightedPopulationBeta nonlinearKernel (fun _ : Dyad N => 1))) v) *
          (response nonlinearKernel v f - dot (design nonlinearKernel v f)
              (weightedPopulationBeta nonlinearKernel (fun _ : Dyad N => 1)) -
            MeasureTheory.condExp (designSigma nonlinearKernel)
              (unitSampleLaw nonlinearKernel N)
              (fun v => response nonlinearKernel v f - dot (design nonlinearKernel v f)
                (weightedPopulationBeta nonlinearKernel (fun _ : Dyad N => 1))) v)) ω =
        conditionalResidualCov nonlinearKernel d f ω := by
    simp_rw [SAP.P018a.WH.W2.P.T1_L2.weighted_residual_eq_epsilon N (by omega)]
    simp [conditionalResidualCov, conditionalResidualMean]
  let repIntegrand : (Fin N → ℝ) → Mat 2 := fun ω =>
    ∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then ∑ t : Fin 1, ∑ u : Fin 1,
      (MeasureTheory.condExp
        (wholeRepeatedDesignSigma (N := N) (singleRecord nonlinearKernel))
        (unitSampleLaw nonlinearKernel N)
        (fun v =>
          (wholeRepeatedResidual (singleRecord nonlinearKernel) v d t -
            MeasureTheory.condExp
              (wholeRepeatedDesignSigma (N := N) (singleRecord nonlinearKernel))
              (unitSampleLaw nonlinearKernel N)
              (fun v => wholeRepeatedResidual (singleRecord nonlinearKernel) v d t) v) *
          (wholeRepeatedResidual (singleRecord nonlinearKernel) v f u -
            MeasureTheory.condExp
              (wholeRepeatedDesignSigma (N := N) (singleRecord nonlinearKernel))
              (unitSampleLaw nonlinearKernel N)
              (fun v => wholeRepeatedResidual (singleRecord nonlinearKernel) v f u) v)) ω) •
        outer (repeatedX (singleRecord nonlinearKernel) ω d t)
          (repeatedX (singleRecord nonlinearKernel) ω f u) else 0
  have hRepInner : ∀ᵐ ω ∂unitSampleLaw nonlinearKernel N, repIntegrand ω = 0 := by
    filter_upwards [hAll] with ω hω
    ext a b
    simp [repIntegrand, hRepFactor, hω]
  let weightedIntegrand : (Fin N → ℝ) → Mat 2 := fun ω =>
    ∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then
      (1 * 1 * MeasureTheory.condExp (designSigma nonlinearKernel)
        (unitSampleLaw nonlinearKernel N)
        (fun v =>
          (response nonlinearKernel v d - dot (design nonlinearKernel v d)
              (weightedPopulationBeta nonlinearKernel (fun _ : Dyad N => 1)) -
            MeasureTheory.condExp (designSigma nonlinearKernel)
              (unitSampleLaw nonlinearKernel N)
              (fun v => response nonlinearKernel v d - dot (design nonlinearKernel v d)
                (weightedPopulationBeta nonlinearKernel (fun _ : Dyad N => 1))) v) *
          (response nonlinearKernel v f - dot (design nonlinearKernel v f)
              (weightedPopulationBeta nonlinearKernel (fun _ : Dyad N => 1)) -
            MeasureTheory.condExp (designSigma nonlinearKernel)
              (unitSampleLaw nonlinearKernel N)
              (fun v => response nonlinearKernel v f - dot (design nonlinearKernel v f)
                (weightedPopulationBeta nonlinearKernel (fun _ : Dyad N => 1))) v)) ω) •
        outer (design nonlinearKernel ω d) (design nonlinearKernel ω f) else 0
  have hWInner : ∀ᵐ ω ∂unitSampleLaw nonlinearKernel N, weightedIntegrand ω = 0 := by
    filter_upwards [hAll] with ω hω
    ext a b
    simp [weightedIntegrand, hWFactor, hω]
  have hRepMeat : wholePrintedRepeatedMeat (singleRecord nonlinearKernel) N = 0 := by
    unfold wholePrintedRepeatedMeat
    rw [show repeatedLaw (singleRecord nonlinearKernel) N = unitSampleLaw nonlinearKernel N from rfl]
    change meanMat (unitSampleLaw nonlinearKernel N) repIntegrand = 0
    ext a b
    apply integral_eq_zero_of_ae
    filter_upwards [hRepInner] with ω hω
    exact congrFun (congrFun hω a) b
  have hWeightedMeat :
      wholePrintedWeightedMeat nonlinearKernel (fun _ : Dyad N => 1) = 0 := by
    unfold wholePrintedWeightedMeat
    change meanMat (unitSampleLaw nonlinearKernel N) weightedIntegrand = 0
    ext a b
    apply integral_eq_zero_of_ae
    filter_upwards [hWInner] with ω hω
    exact congrFun (congrFun hω a) b
  refine ⟨?_, ?_, hRepMeat, hWeightedMeat⟩
  · intro d
    exact hCov d d
  · simp [hTerm]

end SAP.P018a.WH.W2

end
