import SAP.P009a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009a.WH.W3.P.T7_L1

open SAP.P009a.WH.W3
open scoped BigOperators Classical

noncomputable section

private def Eseq (t : ℕ) : FiniteExperiment (t + 1) :=
  nonshrinkingSequence.experiment t

private theorem fairMarginal (t : ℕ) (i : Fin (t + 1)) (b : Bool) :
    armProbability (Eseq t) i b = 1 / 2 := by
  change AronowAudit.P009.marginal
    (SAP.P009a.Bridge.toProjectExperiment (Eseq t)) i b = 1 / 2
  exact AronowAudit.P009.SparseCompletion.fair_marginal (t + 1)
    (fun i z => (Eseq t).outcome i z) i b

private theorem contribution_zero (t : ℕ) (z : TreatmentVector (t + 1)) :
    (if z 0 = true then (Eseq t).outcome 0 z else 0) / (1 / 2) -
      (if z 0 = false then (Eseq t).outcome 0 z else 0) / (1 / 2) =
        2 * treatmentValue (z 0) := by
  cases hz : z 0 <;>
    simp [Eseq, nonshrinkingSequence, nonshrinkingPopulation, fairPopulation,
      treatmentValue, hz] <;> norm_num

private theorem contribution_succ (t : ℕ) (i : Fin t) (z : TreatmentVector (t + 1)) :
    (if z i.succ = true then (Eseq t).outcome i.succ z else 0) / (1 / 2) -
      (if z i.succ = false then (Eseq t).outcome i.succ z else 0) / (1 / 2) = 1 := by
  cases hz : z i.succ <;>
    simp [Eseq, nonshrinkingSequence, nonshrinkingPopulation, fairPopulation,
      treatmentValue, hz] <;> norm_num

private theorem ht_formula (t : ℕ) (z : TreatmentVector (t + 1)) :
    htEstimate (Eseq t) z =
      (((t : ℝ) + 2 * treatmentValue (z 0)) / (t + 1 : ℕ)) := by
  have hMarg : ∀ i : Fin (t + 1), ∀ b : Bool,
      armProbability (Eseq t) i b = 1 / 2 := fun i b => fairMarginal t i b
  unfold htEstimate estimatedArmMean
  simp_rw [hMarg]
  have hsum :
      (∑ i : Fin (t + 1),
          ((if z i = true then (Eseq t).outcome i z else 0) / (1 / 2) -
            (if z i = false then (Eseq t).outcome i z else 0) / (1 / 2))) =
        (t : ℝ) + 2 * treatmentValue (z 0) := by
    simp only [Fin.sum_univ_succ]
    rw [contribution_zero]
    simp_rw [contribution_succ]
    simp <;> ring
  rw [← sub_div, ← Finset.sum_sub_distrib, hsum]

private theorem ate_at_one (t : ℕ) (z : TreatmentVector (t + 1)) :
    assignmentATE (Eseq t) z = 1 := by
  have heff : ∀ i : Fin (t + 1), individualEffect (Eseq t) i z = 1 := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp [individualEffect, potentialResponse, Eseq, nonshrinkingSequence,
        nonshrinkingPopulation, fairPopulation, treatmentValue]
    · have hval : i.val ≠ 0 := by
        intro hv
        exact hi (Fin.ext hv)
      simp [individualEffect, potentialResponse, Eseq, nonshrinkingSequence,
        nonshrinkingPopulation, fairPopulation, treatmentValue, hi]
  unfold assignmentATE
  rw [Finset.sum_congr rfl (fun i _ => heff i)]
  have hn : (t + 1 : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  field_simp [hn] <;> ring

private theorem expectedATE_one (t : ℕ) : expectedATE (Eseq t) = 1 := by
  change AronowAudit.P009.mean
    (SAP.P009a.Bridge.toProjectDistribution (Eseq t).design)
    (fun z => assignmentATE (Eseq t) z) = 1
  simp_rw [ate_at_one]
  exact AronowAudit.P009.mean_const _ 1

private theorem ht_mean_one (t : ℕ) : expectation (Eseq t).design (htEstimate (Eseq t)) = 1 := by
  have hmean : expectation (Eseq t).design (htEstimate (Eseq t)) =
      1 := by
    change AronowAudit.P009.mean
      (SAP.P009a.Bridge.toProjectDistribution (Eseq t).design)
      (htEstimate (Eseq t)) = _
    change AronowAudit.P009.mean (AronowAudit.P009.fairLaw (t + 1))
      (fun z => htEstimate (Eseq t) z) = _
    simp_rw [ht_formula]
    change AronowAudit.P009.mean (AronowAudit.P009.fairLaw (t + 1))
      (fun z => ((t : ℝ) + 2 * treatmentValue (z 0)) / (t + 1 : ℕ)) = _
    rw [AronowAudit.P009.fair_first_coordinate t
      (fun b => ((t : ℝ) + 2 * treatmentValue b) / (t + 1 : ℕ))]
    norm_num [treatmentValue]
    have hn : (t + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hn] <;> ring
  exact hmean

private theorem ht_variance (t : ℕ) :
    variance (Eseq t).design (htEstimate (Eseq t)) = 1 / (t + 1 : ℝ)^2 := by
  unfold variance covariance
  rw [ht_mean_one]
  change AronowAudit.P009.mean (AronowAudit.P009.fairLaw (t + 1))
    (fun z => (htEstimate (Eseq t) z - 1) * (htEstimate (Eseq t) z - 1)) = _
  simp_rw [ht_formula]
  rw [AronowAudit.P009.fair_first_coordinate t
    (fun b => (((t : ℝ) + 2 * treatmentValue b) / (t + 1 : ℕ) - 1) *
      (((t : ℝ) + 2 * treatmentValue b) / (t + 1 : ℕ) - 1))]
  have hn : (t + 1 : ℝ) ≠ 0 := by positivity
  norm_num [treatmentValue]
  field_simp [hn] <;> ring

private theorem proof : SAP.P009a.WH.W3.T7_L1 := by
  intro t
  dsimp [nonshrinkingSequence, sparseSequence, sampleSize]
  have he : expectedATE (nonshrinkingPopulation (t + 1)) = 1 := by
    simpa [Eseq, nonshrinkingSequence] using expectedATE_one t
  have hm : expectation (nonshrinkingPopulation (t + 1)).design
      (htEstimate (nonshrinkingPopulation (t + 1))) = 1 := by
    simpa [Eseq, nonshrinkingSequence] using ht_mean_one t
  have hv : variance (nonshrinkingPopulation (t + 1)).design
      (htEstimate (nonshrinkingPopulation (t + 1))) = 1 / (t + 1 : ℝ)^2 := by
    simpa [Eseq, nonshrinkingSequence, Nat.cast_add] using ht_variance t
  refine ⟨he, hm, ?_, ?_⟩
  · change variance (nonshrinkingPopulation (t + 1)).design
      (htEstimate (nonshrinkingPopulation (t + 1))) =
        1 / (((t + 1 : ℕ) : ℝ)) ^ 2
    simpa [Nat.cast_add] using hv
  intro z
  have hf : htEstimate (nonshrinkingPopulation (t + 1)) z =
      ((t : ℝ) + 2 * treatmentValue (z 0)) / (t + 1 : ℝ) := by
    simpa [Eseq, nonshrinkingSequence, Nat.cast_add] using ht_formula t z
  constructor
  · rw [hf]
    push_cast
    ring
  · unfold standardizedHT
    rw [he, hv, hf]
    have hnpos : (0 : ℝ) < t + 1 := by positivity
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
      Real.sqrt_sq hnpos.le]
    have htR : ((t : ℝ) + 1) ≠ 0 := ne_of_gt hnpos
    cases hz : z 0 <;> simp [treatmentValue, hz] <;> field_simp [htR] <;> ring

end

end SAP.P009a.WH.W3.P.T7_L1

theorem SAP.P009a.WH.W3.T7_L1_proof : SAP.P009a.WH.W3.T7_L1 := by
  exact SAP.P009a.WH.W3.P.T7_L1.proof
