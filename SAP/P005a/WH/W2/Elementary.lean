import SAP.P005a.Defs.WholeW2
import SAP.P005a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2
noncomputable section
open Finset Filter SAP.P005a.Bridge
open scoped BigOperators Matrix Topology
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

/-- Full finite sign counterexample: every added clause is elementary exact arithmetic. -/
theorem T5_complete : T5WholeStatement := by
  have hb : T5Statement := T5_correspondence.mp AronowAudit.P005.interacted_sign_counterexample
  have hi : Function.Injective signX := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [signX] <;> norm_num at *
  have hv : ∀ S ∈ design 6 2, 0 < firstVariance signPopulation S ∧
      0 < firstVariance signPopulation (control S) := by
    intro S hS
    change S ∈ AronowAudit.P005.design 6 2 at hS
    rw [AronowAudit.P005.design_six_two] at hS
    simp only [AronowAudit.P005.assignmentsSixTwo, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [firstVariance, sampleCov, mean, signPopulation, signX,
      control, show (univ : Finset (Fin 6)) = {0,1,2,3,4,5} from by decide,
      Finset.sdiff_eq_filter, Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty]
  have he : ∀ f : Finset (Fin 6) → ℝ,
      expectation 2 f = AronowAudit.P005.expectation 2 f := fun _ => rfl
  refine ⟨hb, ?_, ?_, ?_, by norm_num, ?_, hi, hv, ?_⟩
  all_goals norm_num [ he, signPopulation, signX, leverage, dot, xMean, armNu3, centered,
    popMean, mean, NTTT, NCCC, pT, leverageCov, popCov, sampleCov,
    AronowAudit.P005.expectation_six_two, control,
    show (univ : Finset (Fin 6)) = {0,1,2,3,4,5} from by decide,
    Finset.sdiff_eq_filter, Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty, Fin.sum_univ_succ]

  all_goals intro i; ring

/-- Full finite weight counterexample, with scalar scaling identities kept explicit. -/
theorem T10_complete : T10WholeStatement := by
  have hb : T10Statement := T10_correspondence.mp AronowAudit.P005.interacted_weight_counterexample
  have hs : weightScale^2 = (3/20 : ℝ) := Real.sq_sqrt (by norm_num)
  have hi : Function.Injective weightA := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [weightA] <;> norm_num at *
  have hv : ∀ S ∈ design 6 2,
      0 < firstVariance weightPopulation S ∧ 0 < firstVariance weightPopulation (control S) := by
    exact AronowAudit.P005.interacted_inverse_counterexample.2.2.1
  have hvar : ∀ S : Finset (Fin 6), firstVariance weightPopulation S =
      (3/20 : ℝ)*sampleCov S weightA weightA := by
    intro S
    change AronowAudit.P005.sampleCov S (fun i => weightScale*weightA i)
      (fun i => weightScale*weightA i) = _
    rw [AronowAudit.P005.sampleCov_scale_both, hs]
    rfl
  have hvs : ∀ S ∈ design 6 2,
      0 < firstVariance weightPopulation S ∧ 0 < firstVariance weightPopulation (control S) ∧
      firstVariance weightPopulation S = (3/20 : ℝ)*sampleCov S weightA weightA ∧
      firstVariance weightPopulation (control S) = (3/20 : ℝ)*sampleCov (control S) weightA weightA := by
    intro S hS
    exact ⟨(hv S hS).1, (hv S hS).2, hvar S, hvar (control S)⟩
  have hl : ∀ i, leverage weightPopulation i = (3/20 : ℝ)*weightA i^2 := by
    intro i
    have h := congrFun (AronowAudit.P005.scalar_leverage weightA weightY (fun _ => 0) weightScale) i
    change leverage weightPopulation i = weightScale^2*weightA i^2 at h
    simpa only [hs] using h
  have hd : ∀ S : Finset (Fin 6),
      dot (xMean weightPopulation S) (armN weightPopulation S weightY) =
        (3/20 : ℝ)*mean S weightA*(mean S (fun i => weightA i*weightY i) -
          mean S weightA*mean S weightY) := by
    intro S
    exact (AronowAudit.P005.scalar_dot_armN weightA weightY (fun _ => 0) weightY weightScale S).trans
      (by rw [hs]; rfl)
  have hc : ∀ S : Finset (Fin 6), sampleCov S (leverage weightPopulation) weightY =
      (3/20 : ℝ)*(mean S (fun i => weightA i^2*weightY i) -
        mean S (fun i => weightA i^2)*mean S weightY) := by
    intro S
    simp_rw [show leverage weightPopulation = (fun i => (3/20 : ℝ)*weightA i^2) from funext hl]
    exact AronowAudit.P005.sampleCov_scale_left S (fun i => weightA i^2) weightY (3/20)
  have ha : ∀ S : Finset (Fin 6),
      weightExpression (1/8) S - weightExpression (1/2) S =
        -(3/8 : ℝ)*sampleCov S (leverage weightPopulation) weightY ∧
      dot (xMean weightPopulation S) (armN weightPopulation S weightY) =
        (3/20 : ℝ)*mean S weightA*(mean S (fun i => weightA i*weightY i) -
          mean S weightA*mean S weightY) ∧
      sampleCov S (leverage weightPopulation) weightY =
        (3/20 : ℝ)*(mean S (fun i => weightA i^2*weightY i) -
          mean S (fun i => weightA i^2)*mean S weightY) := by
    intro S
    exact ⟨by unfold weightExpression; ring, hd S, hc S⟩
  have hE1 : expectation 2 (weightExpression (1/8)) = (4913/1200 : ℝ) := hb.2.2.2.2.2.1
  have hE2 : expectation 2 (weightExpression (1/2)) = (20/3 : ℝ) := hb.2.2.2.2.2.2.1
  have he : ∀ f : Finset (Fin 6) → ℝ,
      expectation 2 f = AronowAudit.P005.expectation 2 f := fun _ => rfl
  refine ⟨hb, by decide, hi, hvs, hl, ?_, ?_, ?_, by norm_num, by norm_num, ha, ?_, ?_⟩
  all_goals norm_num [hl, hE1, hE2, hc, he,
    leverageCov, popCov, sampleCov, popMean, mean, weightA, weightY,
    AronowAudit.P005.expectation_six_two,
    show (univ : Finset (Fin 6)) = {0,1,2,3,4,5} from by decide]

end
end SAP.P005a.WH.W2
