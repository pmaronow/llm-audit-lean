import SAP.P009a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SAP.P009a.WH.W1.P.T1_L3

open Bridge
open scoped BigOperators Classical

lemma ht_formula (t : ℕ) (z : TreatmentVector (t + 1)) :
    htEstimate (sparsePopulation (t + 1)) z =
      2 * treatmentValue (z 0) / (t + 1 : ℕ) := by
  rw [Bridge.estimator_correspondence]
  change AronowAudit.P009.ht (AronowAudit.P009.sparseExperiment (t + 1)) z = _
  simpa [treatmentValue, AronowAudit.P009.bit] using
    (AronowAudit.P009.sparse_estimators_finite t z).1

lemma expected_formula (t : ℕ) :
    expectedATE (sparsePopulation (t + 1)) = 1 / (t + 1 : ℕ) := by
  change AronowAudit.P009.eate (AronowAudit.P009.sparseStudy.experiment t) = _
  rw [AronowAudit.P009.SparseCompletion.sparse_eate]
  simp [AronowAudit.P009.size, AronowAudit.P009.sparseStudy]

lemma true_variance_formula (t : ℕ) :
    variance (sparsePopulation (t + 1)).design
      (htEstimate (sparsePopulation (t + 1))) = 1 / (t + 1 : ℕ) ^ 2 := by
  change AronowAudit.P009.var
    (AronowAudit.P009.sparseExperiment (t + 1)).design
    (AronowAudit.P009.ht (AronowAudit.P009.sparseExperiment (t + 1))) = _
  simpa [AronowAudit.P009.sparseStudy, AronowAudit.P009.size] using
    (AronowAudit.P009.sparse_moments_finite t).2.1

lemma whole_variance_formula (t : ℕ) (a : Fin 4) (z : TreatmentVector (t + 1)) :
    wholeVarianceEstimate (sparsePopulation (t + 1)) a z =
      4 * treatmentValue (z 0) / (t + 1 : ℕ) ^ 2 := by
  have hber : bernoulliVarianceEstimate (sparsePopulation (t + 1)) z =
      4 * treatmentValue (z 0) / (t + 1 : ℕ) ^ 2 := by
    change AronowAudit.P009.vBER
      (AronowAudit.P009.sparseExperiment (t + 1)) z = _
    simpa [treatmentValue, AronowAudit.P009.bit] using
      (AronowAudit.P009.sparse_estimators_finite t z).2
  have hinfl := AronowAudit.P009.Wave1.sparseCoverage_inflations t z
  have havg : averageVarianceEstimate (sparsePopulation (t + 1)) z =
      bernoulliVarianceEstimate (sparsePopulation (t + 1)) z := by
    change AronowAudit.P009.vAVG
      (AronowAudit.P009.sparseExperiment (t + 1)) z = _
    exact hinfl.1
  have hmax : maximumVarianceEstimate (sparsePopulation (t + 1)) z =
      bernoulliVarianceEstimate (sparsePopulation (t + 1)) z := by
    change AronowAudit.P009.vMAX
      (AronowAudit.P009.sparseExperiment (t + 1)) z = _
    exact hinfl.2.1
  have hsr : spectralVarianceEstimate (sparsePopulation (t + 1)) z =
      bernoulliVarianceEstimate (sparsePopulation (t + 1)) z := by
    change AronowAudit.P009.vSR
      (AronowAudit.P009.sparseExperiment (t + 1)) z = _
    exact hinfl.2.2
  fin_cases a <;>
    simp [wholeVarianceEstimate, hber, havg, hmax, hsr]

lemma first_true_probability (t : ℕ) :
    probability (sparseSequence.experiment t).design
      (fun z => z ⟨0, sparseSequence.positive t⟩ = true) = 1 / 2 := by
  classical
  rw [Bridge.probability_correspondence]
  change AronowAudit.P009.prob
    (AronowAudit.P009.sparseExperiment (t + 1)).design
      (fun z => z (⟨0, by omega⟩ : Fin (t + 1)) = true) = 1 / 2
  unfold AronowAudit.P009.prob AronowAudit.P009.sparseExperiment AronowAudit.P009.fairExperiment
  dsimp only
  let i : Fin (t + 1) := ⟨0, by omega⟩
  let f : Bool → ℝ := fun b =>
    @ite ℝ (b = true) (Classical.propDecidable (b = true)) 1 0
  have hi : i = (0 : Fin (t + 1)) := Fin.ext rfl
  rw [AronowAudit.P009.SparseCompletion.fair_coordinate (t + 1) i f]
  norm_num [f, i]

lemma first_false_probability (t : ℕ) :
    probability (sparseSequence.experiment t).design
      (fun z => z ⟨0, sparseSequence.positive t⟩ = false) = 1 / 2 := by
  classical
  rw [Bridge.probability_correspondence]
  change AronowAudit.P009.prob
    (AronowAudit.P009.sparseExperiment (t + 1)).design
      (fun z => z (⟨0, by omega⟩ : Fin (t + 1)) = false) = 1 / 2
  unfold AronowAudit.P009.prob AronowAudit.P009.sparseExperiment AronowAudit.P009.fairExperiment
  dsimp only
  let i : Fin (t + 1) := ⟨0, by omega⟩
  let f : Bool → ℝ := fun b =>
    @ite ℝ (b = false) (Classical.propDecidable (b = false)) 1 0
  have hi : i = (0 : Fin (t + 1)) := Fin.ext rfl
  rw [AronowAudit.P009.SparseCompletion.fair_coordinate (t + 1) i f]
  norm_num [f, i]

lemma interval_cases (t : ℕ) (α : ℝ) (a : Fin 4) (z : TreatmentVector (t + 1))
    (hα : 0 < α) (hα1 : α < 1) :
    (z 0 = false →
      htEstimate (sparsePopulation (t + 1)) z = 0 ∧
      wholeVarianceEstimate (sparsePopulation (t + 1)) a z = 0 ∧
      htEstimate (sparsePopulation (t + 1)) z -
        Real.sqrt (wholeVarianceEstimate (sparsePopulation (t + 1)) a z / α) = 0 ∧
      htEstimate (sparsePopulation (t + 1)) z +
        Real.sqrt (wholeVarianceEstimate (sparsePopulation (t + 1)) a z / α) = 0 ∧
      ¬ IntervalCovers (htEstimate (sparsePopulation (t + 1)) z)
        (expectedATE (sparsePopulation (t + 1)))
        (wholeVarianceEstimate (sparsePopulation (t + 1)) a z) α) ∧
    (z 0 = true →
      (htEstimate (sparsePopulation (t + 1)) z -
        expectedATE (sparsePopulation (t + 1))) ^ 2 = 1 / (t + 1 : ℕ) ^ 2 ∧
      (htEstimate (sparsePopulation (t + 1)) z -
        expectedATE (sparsePopulation (t + 1))) ^ 2 ≤
          wholeVarianceEstimate (sparsePopulation (t + 1)) a z / α ∧
      IntervalCovers (htEstimate (sparsePopulation (t + 1)) z)
        (expectedATE (sparsePopulation (t + 1)))
        (wholeVarianceEstimate (sparsePopulation (t + 1)) a z) α) := by
  have hn : (0 : ℝ) < (t + 1 : ℕ) := by positivity
  have hT := ht_formula t z
  have hθ := expected_formula t
  have hV := whole_variance_formula t a z
  constructor
  · intro hz
    have hT0 : htEstimate (sparsePopulation (t + 1)) z = 0 := by
      rw [hT, hz]
      simp [treatmentValue]
    have hV0 : wholeVarianceEstimate (sparsePopulation (t + 1)) a z = 0 := by
      rw [hV, hz]
      simp [treatmentValue]
    refine ⟨hT0, hV0, ?_, ?_, ?_⟩
    · rw [hT0, hV0]
      simp
    · rw [hT0, hV0]
      simp
    · intro hc
      have hpos : 0 < |(0 : ℝ) - 1 / (t + 1 : ℕ)| := by
        apply abs_pos.mpr
        have hne : (1 : ℝ) / (t + 1 : ℕ) ≠ 0 := one_div_ne_zero (ne_of_gt hn)
        exact sub_ne_zero.mpr (Ne.symm hne)
      change |htEstimate (sparsePopulation (t + 1)) z -
        expectedATE (sparsePopulation (t + 1))| ≤
          Real.sqrt (wholeVarianceEstimate (sparsePopulation (t + 1)) a z / α) at hc
      rw [hT0, hθ, hV0] at hc
      simp only [zero_div, Real.sqrt_zero] at hc
      exact (not_le_of_gt hpos) hc
  · intro hz
    have hT1 : htEstimate (sparsePopulation (t + 1)) z =
        2 / (t + 1 : ℕ) := by
      rw [hT, hz]
      simp [treatmentValue]
    have hV1 : wholeVarianceEstimate (sparsePopulation (t + 1)) a z =
        4 / (t + 1 : ℕ) ^ 2 := by
      rw [hV, hz]
      simp [treatmentValue]
    have hsq : (2 / ((t + 1 : ℕ) : ℝ) - 1 / ((t + 1 : ℕ) : ℝ)) ^ 2 =
        1 / ((t + 1 : ℕ) : ℝ) ^ 2 := by
      have hn0 : ((t + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hn
      field_simp [hn0]
      ring
    have hbound : (1 / ((t + 1 : ℕ) : ℝ) ^ 2) ≤
        (4 / ((t + 1 : ℕ) : ℝ) ^ 2) / α := by
      have hsmall : (1 : ℝ) ≤ 4 / α := (le_div_iff₀ hα).2 (by linarith)
      have hdiv := div_le_div_of_nonneg_right hsmall
        (sq_nonneg (((t + 1 : ℕ) : ℝ)))
      calc
        (1 / ((t + 1 : ℕ) : ℝ) ^ 2) ≤ (4 / α) / ((t + 1 : ℕ) : ℝ) ^ 2 := hdiv
        _ = (4 / ((t + 1 : ℕ) : ℝ) ^ 2) / α := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hT1, hθ]
      simpa using hsq
    · rw [hT1, hθ, hV1]
      exact (le_of_eq hsq).trans hbound
    · unfold IntervalCovers
      rw [hT1, hθ, hV1]
      apply Real.abs_le_sqrt
      exact (le_of_eq hsq).trans hbound

lemma relative_event_iff_false (t : ℕ) (η : ℝ) (a : Fin 4)
    (z : TreatmentVector (t + 1)) (hη : 0 < η) (hη1 : η < 1) :
    wholeVarianceEstimate (sparsePopulation (t + 1)) a z <
      (1 - η) * variance (sparsePopulation (t + 1)).design
        (htEstimate (sparsePopulation (t + 1))) ↔ z 0 = false := by
  have hn : (0 : ℝ) < (t + 1 : ℕ) := by positivity
  rw [whole_variance_formula, true_variance_formula]
  cases hz : z 0
  · simp [treatmentValue]
    exact mul_pos (by linarith) (by positivity)
  · simp [treatmentValue]
    have hsmall : 1 - η < 1 := by linarith
    have hden : 0 < (1 / (t + 1 : ℕ) ^ 2 : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hsmall.le hden.le
    have hbase : (1 / ((t + 1 : ℕ) : ℝ) ^ 2) <
        4 / ((t + 1 : ℕ) : ℝ) ^ 2 := by
      have hsquare : 0 < ((t + 1 : ℕ) : ℝ) ^ 2 := sq_pos_of_pos hn
      have h := div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 4) hsquare
      simpa using h
    have hright : (1 - η) * (1 / ((t + 1 : ℕ) : ℝ) ^ 2) <
        4 / ((t + 1 : ℕ) : ℝ) ^ 2 := by
      exact lt_of_le_of_lt (by simpa using hmul) hbase
    simpa [div_eq_mul_inv] using hright.le

end SAP.P009a.WH.W1.P.T1_L3

theorem SAP.P009a.WH.W1.T1_L3_proof : SAP.P009a.WH.W1.T1_L3 := by
  classical
  intro t
  dsimp only [SAP.P009a.WH.W1.T1_L3, W1SparseIntervals]
  constructor
  · intro α hα hα1 a
    refine ⟨?_, ?_⟩
    · intro z
      simpa only [sparseSequence, sampleSize] using
        SAP.P009a.WH.W1.P.T1_L3.interval_cases t α a z hα hα1
    · let i : Fin (sparseSequence.N t) := ⟨0, sparseSequence.positive t⟩
      have hi : i = (⟨0, by omega⟩ : Fin (t + 1)) := rfl
      have hi0 : (⟨0, by omega⟩ : Fin (t + 1)) = 0 := Fin.ext rfl
      have hiff : ∀ z : TreatmentVector (sparseSequence.N t),
          IntervalCovers (htEstimate (sparseSequence.experiment t) z)
            (expectedATE (sparseSequence.experiment t))
            (wholeVarianceEstimate (sparseSequence.experiment t) a z) α ↔ z i = true := by
        intro z
        have hc := SAP.P009a.WH.W1.P.T1_L3.interval_cases t α a z hα hα1
        have hc' :
            (z i = false →
              htEstimate (sparseSequence.experiment t) z = 0 ∧
              wholeVarianceEstimate (sparseSequence.experiment t) a z = 0 ∧
              htEstimate (sparseSequence.experiment t) z -
                Real.sqrt (wholeVarianceEstimate (sparseSequence.experiment t) a z / α) = 0 ∧
              htEstimate (sparseSequence.experiment t) z +
                Real.sqrt (wholeVarianceEstimate (sparseSequence.experiment t) a z / α) = 0 ∧
              ¬ IntervalCovers (htEstimate (sparseSequence.experiment t) z)
                (expectedATE (sparseSequence.experiment t))
                (wholeVarianceEstimate (sparseSequence.experiment t) a z) α) ∧
            (z i = true →
              (htEstimate (sparseSequence.experiment t) z -
                expectedATE (sparseSequence.experiment t)) ^ 2 =
                  1 / sampleSize sparseSequence t ^ 2 ∧
              (htEstimate (sparseSequence.experiment t) z -
                expectedATE (sparseSequence.experiment t)) ^ 2 ≤
                  wholeVarianceEstimate (sparseSequence.experiment t) a z / α ∧
              IntervalCovers (htEstimate (sparseSequence.experiment t) z)
                (expectedATE (sparseSequence.experiment t))
                (wholeVarianceEstimate (sparseSequence.experiment t) a z) α) := by
          simpa [sparseSequence, sampleSize, i, hi] using hc
        constructor
        · intro hcov
          cases hz : z i with
          | false => exact False.elim ((hc'.1 hz).2.2.2.2 hcov)
          | true => rfl
        · intro hz
          exact (hc'.2 hz).2.2
      have hp := SAP.P009a.WH.W1.P.T1_L3.first_true_probability t
      unfold probability at hp ⊢
      convert hp using 1
      congr 1
      funext z
      dsimp only
      simp [hiff z, i, hi]
  · intro η hη hη1 a
    let i : Fin (sparseSequence.N t) := ⟨0, sparseSequence.positive t⟩
    have hi : i = (⟨0, by omega⟩ : Fin (t + 1)) := rfl
    have hi0 : (⟨0, by omega⟩ : Fin (t + 1)) = 0 := Fin.ext rfl
    have hiff : ∀ z : TreatmentVector (sparseSequence.N t),
        (wholeVarianceEstimate (sparseSequence.experiment t) a z <
          (1 - η) * variance (sparseSequence.experiment t).design
            (htEstimate (sparseSequence.experiment t))) ↔ z i = false := by
      intro z
      have hc := SAP.P009a.WH.W1.P.T1_L3.relative_event_iff_false t η a z hη hη1
      simpa [sparseSequence, i, hi, hi0] using hc
    have hp := SAP.P009a.WH.W1.P.T1_L3.first_false_probability t
    unfold probability at hp ⊢
    convert hp using 1
    congr 1
    funext z
    dsimp only
    simp [hiff z, i, hi]
