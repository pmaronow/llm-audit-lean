import AronowAudit.P013.Wave1.CorrectedCoverageBlueprint

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.CorrectedCoverage

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-! The auxiliary witness has independent own assignments and both outcomes equal to one.
The existing block-design moment lemmas are independent of its block outcome table. -/

private def onesPopulation (N : ℕ) : Population (blockDesign N) N 2 where
  exposure z i := z i
  outcome _ _ := 1

private theorem ones_pi (N : ℕ) (i : Fin N) (d : Fin 2) :
    pi (onesPopulation N) i d = 1 / 2 := by
  change pi (blockPopulation N) i d = 1 / 2
  exact block_pi N i d

private theorem ones_joint (N : ℕ) (i j : Fin N) (hij : i ≠ j) (d e : Fin 2) :
    jointPi (onesPopulation N) i j d e = 1 / 4 := by
  change jointPi (blockPopulation N) i j d e = 1 / 4
  exact block_joint N i j hij d e

private theorem ones_pairTerm (N : ℕ) (i j : Fin N) (hij : i ≠ j)
    (d e : Fin 2) (z : Fin N → Fin 2) : pairTerm (onesPopulation N) i j d e z = 0 := by
  unfold pairTerm
  rw [ones_joint N i j hij, ones_pi, ones_pi]
  norm_num

private theorem ones_indicator_sum (N : ℕ) (z : Fin N → Fin 2) :
    (∑ i, indicator (onesPopulation N).exposure i 1 z) +
      (∑ i, indicator (onesPopulation N).exposure i 0 z) = (N : ℝ) := by
  rw [← Finset.sum_add_distrib]
  have hunit (i : Fin N) : indicator (onesPopulation N).exposure i 1 z +
      indicator (onesPopulation N).exposure i 0 z = 1 := by
    change (if z i = 1 then (1 : ℝ) else 0) + (if z i = 0 then 1 else 0) = 1
    generalize z i = t
    fin_cases t <;> norm_num
  simp only [hunit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

private theorem ones_correction (N : ℕ) (d : Fin 2) (z : Fin N → Fin 2) :
    correctionA2 (onesPopulation N) d z = 0 := by
  unfold correctionA2
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  rw [ones_joint N i j hij]
  norm_num

private theorem ones_varianceHT (N : ℕ) (d : Fin 2) (z : Fin N → Fin 2) :
    varianceHT (onesPopulation N) d z =
      2 * ∑ i, indicator (onesPopulation N).exposure i d z := by
  have hpairs : (∑ i : Fin N, ∑ j ∈ (univ : Finset (Fin N)).erase i,
      pairTerm (onesPopulation N) i j d d z) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j hj
    exact ones_pairTerm N i j (Finset.ne_of_mem_erase hj).symm d d z
  unfold varianceHT
  rw [hpairs, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ones_pi]
  change indicator (onesPopulation N).exposure i d z * (1 - (1 / 2 : ℝ)) *
      (1 / (1 / 2 : ℝ)) ^ 2 = 2 * indicator (onesPopulation N).exposure i d z
  ring

private theorem ones_covarianceA (N : ℕ) (z : Fin N → Fin 2) :
    covarianceA (onesPopulation N) 1 0 z = -(N : ℝ) := by
  have hpositive : (∑ i : Fin N, ∑ j ∈ (univ : Finset (Fin N)).erase i,
      if 0 < jointPi (onesPopulation N) i j 1 0 then
        pairTerm (onesPopulation N) i j 1 0 z else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j hj
    rw [ones_pairTerm N i j (Finset.ne_of_mem_erase hj).symm]
    split_ifs <;> rfl
  have hzero (i : Fin N) :
      (∑ j : Fin N, if jointPi (onesPopulation N) i j 1 0 = 0 then
        indicator (onesPopulation N).exposure i 1 z * (onesPopulation N).outcome i 1 ^ 2 /
            (2 * pi (onesPopulation N) i 1) +
          indicator (onesPopulation N).exposure j 0 z * (onesPopulation N).outcome j 0 ^ 2 /
            (2 * pi (onesPopulation N) j 0) else 0) =
        indicator (onesPopulation N).exposure i 1 z +
          indicator (onesPopulation N).exposure i 0 z := by
    calc
      _ = (if jointPi (onesPopulation N) i i 1 0 = 0 then
          indicator (onesPopulation N).exposure i 1 z * (onesPopulation N).outcome i 1 ^ 2 /
              (2 * pi (onesPopulation N) i 1) +
            indicator (onesPopulation N).exposure i 0 z * (onesPopulation N).outcome i 0 ^ 2 /
              (2 * pi (onesPopulation N) i 0) else 0) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [ones_joint N i j hji.symm]
          norm_num
        · simp
      _ = _ := by
        rw [jointPi_cross_self (onesPopulation N) i 1 0 (by decide), if_pos rfl,
          ones_pi, ones_pi]
        change indicator (onesPopulation N).exposure i 1 z * 1 ^ 2 / (2 * (1 / 2 : ℝ)) +
            indicator (onesPopulation N).exposure i 0 z * 1 ^ 2 / (2 * (1 / 2 : ℝ)) = _
        ring
  unfold covarianceA
  rw [hpositive]
  simp_rw [hzero]
  rw [Finset.sum_add_distrib, ones_indicator_sum]
  ring

private theorem ones_variance_estimate (N : ℕ) (hN : 0 < N) (z : Fin N → Fin 2) :
    effectVariance (onesPopulation N) 1 0 z = 4 / (N : ℝ) := by
  have hsum := ones_indicator_sum N z
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold effectVariance
  rw [ones_varianceHT, ones_correction, ones_varianceHT, ones_correction, ones_covarianceA]
  have hnum :
      2 * (∑ i, indicator (onesPopulation N).exposure i 1 z) + 0 +
        2 * (∑ i, indicator (onesPopulation N).exposure i 0 z) + 0 - 2 * -(N : ℝ) =
          4 * (N : ℝ) := by linarith
  rw [hnum]
  field_simp [hN0] <;> ring

private theorem ones_effect (N : ℕ) (z : Fin N → Fin 2) :
    htEffect (onesPopulation N) 1 0 z =
      (∑ i, rademacher (z i)) * (2 / (N : ℝ)) := by
  have hunit (i : Fin N) :
      indicator (onesPopulation N).exposure i 1 z *
          ((onesPopulation N).outcome i 1 / pi (onesPopulation N) i 1) -
        indicator (onesPopulation N).exposure i 0 z *
          ((onesPopulation N).outcome i 0 / pi (onesPopulation N) i 0) =
          2 * rademacher (z i) := by
    rw [ones_pi, ones_pi]
    change (if z i = 1 then (1 : ℝ) else 0) * (1 / (1 / 2 : ℝ)) -
      (if z i = 0 then 1 else 0) * (1 / (1 / 2 : ℝ)) = 2 * rademacher (z i)
    generalize z i = t
    fin_cases t <;> norm_num [rademacher]
  unfold htEffect htTotal
  rw [← Finset.sum_sub_distrib]
  simp_rw [hunit]
  rw [← Finset.mul_sum]
  ring

private theorem ones_true_variance (N : ℕ) (hN : 0 < N) :
    variance (blockDesign N) (htEffect (onesPopulation N) 1 0) = 4 / (N : ℝ) := by
  have hfun : htEffect (onesPopulation N) 1 0 =
      fun z => (∑ i, rademacher (z i)) * (2 / (N : ℝ)) := by
    funext z
    exact ones_effect N z
  rw [hfun, variance, covariance_mul_const]
  change variance (replicateDesign sharedDesign N) (fun z => ∑ i, rademacher (z i)) *
    (2 / (N : ℝ)) * (2 / (N : ℝ)) = 4 / (N : ℝ)
  rw [rademacher_sum_variance]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hN0] <;> ring

/-! Relabel only the support; retain own exposures and constant potential outcomes. -/

private def fairSupport (n : ℕ) : ℕ := Fintype.card (Fin (n + 1) → Fin 2)

private def fairEquiv (n : ℕ) : (Fin (n + 1) → Fin 2) ≃ Fin (fairSupport n) :=
  Fintype.equivFin _

private def fairDesign (n : ℕ) : Design (Fin (fairSupport n)) :=
  relabelDesign (blockDesign (n + 1)) (fairEquiv n)

private def fairPopulation (n : ℕ) : Population (fairDesign n) (n + 1) 2 :=
  relabelPopulation (onesPopulation (n + 1)) (fairEquiv n)

private theorem fair_pi (n : ℕ) (i : Fin (n + 1)) (d : Fin 2) :
    pi (fairPopulation n) i d = 1 / 2 := by
  change pi (relabelPopulation (onesPopulation (n + 1)) (fairEquiv n)) i d = 1 / 2
  rw [pi_relabel]
  exact ones_pi (n + 1) i d

private def fairSequence : ExperimentSequence where
  experiment n := {
    supportSize := fairSupport n
    exposureSize := 2
    design := fairDesign n
    population := fairPopulation n }
  treated _ := (1 : Fin 2)
  control _ := (0 : Fin 2)
  distinct _ := by show (1 : Fin 2) ≠ 0; decide
  positiveTreated n i := by
    show 0 < pi (fairPopulation n) i 1 ∧ pi (fairPopulation n) i 1 < 1
    rw [fair_pi]
    norm_num
  positiveControl n i := by
    show 0 < pi (fairPopulation n) i 0 ∧ pi (fairPopulation n) i 0 < 1
    rw [fair_pi]
    norm_num

private theorem fair_effect (n : ℕ) (z : Fin (fairSupport n)) :
    htEffect (fairPopulation n) 1 0 z =
      htEffect (onesPopulation (n + 1)) 1 0 ((fairEquiv n).symm z) := by
  change htEffect (relabelPopulation (onesPopulation (n + 1)) (fairEquiv n)) 1 0 z =
    htEffect (onesPopulation (n + 1)) 1 0 ((fairEquiv n).symm z)
  unfold htEffect htTotal
  simp only [pi_relabel]
  rfl

private theorem fair_true_variance (n : ℕ) :
    seqTrueVariance fairSequence n = 4 / ((n : ℝ) + 1) := by
  change variance (relabelDesign (blockDesign (n + 1)) (fairEquiv n))
    (htEffect (fairPopulation n) 1 0) = 4 / ((n : ℝ) + 1)
  have hvar : ∀ X : Fin (fairSupport n) → ℝ,
      variance (relabelDesign (blockDesign (n + 1)) (fairEquiv n)) X =
        variance (blockDesign (n + 1)) (fun z => X (fairEquiv n z)) := by
    intro X
    simp only [variance, covariance, expectation_relabel]
  rw [hvar]
  have hfun : (fun z => htEffect (fairPopulation n) 1 0 (fairEquiv n z)) =
      htEffect (onesPopulation (n + 1)) 1 0 := by
    funext z
    rw [fair_effect, Equiv.symm_apply_apply]
  rw [hfun]
  simpa only [Nat.cast_add, Nat.cast_one] using ones_true_variance (n + 1) (by omega)

private theorem fair_variance_estimate (n : ℕ) (z : Fin (fairSupport n)) :
    seqVarianceEstimate fairSequence n z = 4 / ((n : ℝ) + 1) := by
  have hrel : effectVariance (fairPopulation n) 1 0 z =
      effectVariance (onesPopulation (n + 1)) 1 0 ((fairEquiv n).symm z) := by
    change effectVariance (relabelPopulation (onesPopulation (n + 1)) (fairEquiv n)) 1 0 z =
      effectVariance (onesPopulation (n + 1)) 1 0 ((fairEquiv n).symm z)
    unfold effectVariance varianceHT correctionA2 covarianceA pairTerm
    simp only [pi_relabel, jointPi_relabel]
    rfl
  change effectVariance (fairPopulation n) 1 0 z = _
  rw [hrel]
  simpa only [Nat.cast_add, Nat.cast_one] using
    ones_variance_estimate (n + 1) (by omega) ((fairEquiv n).symm z)

private theorem fair_dependency (n : ℕ) :
    GenuineDependency (fairDesign n) (fairPopulation n).exposure
      (fun i j => decide (i = j)) := by
  intro A B hdis hno a b
  change probability (relabelDesign (blockDesign (n + 1)) (fairEquiv n))
      (fun z => (∀ i ∈ A, (fairPopulation n).exposure z i = a i) ∧
        (∀ j ∈ B, (fairPopulation n).exposure z j = b j)) =
    probability (relabelDesign (blockDesign (n + 1)) (fairEquiv n))
        (fun z => ∀ i ∈ A, (fairPopulation n).exposure z i = a i) *
      probability (relabelDesign (blockDesign (n + 1)) (fairEquiv n))
        (fun z => ∀ j ∈ B, (fairPopulation n).exposure z j = b j)
  simp only [probability_relabel, fairPopulation, relabelPopulation, onesPopulation,
    Equiv.symm_apply_apply]
  exact (coordinate_population_genuine_dependency sharedDesign (n + 1)
    (fun i : Fin (n + 1) => i) (fun _ x => x)) A B hdis hno a b

/-- The corrected premises have a nonzero-variance, bounded genuine-degree instance. -/
theorem n10_proof : N10 := by
  classical
  refine ⟨fairSequence, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ => ⟨Fin.val, Fin.val_injective⟩, 1, 0, fun _ _ => 1,
      by decide, fun _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl⟩
  · intro n d i
    change Fin 2 at d
    change 0 < pi (fairPopulation n) i d ∧ pi (fairPopulation n) i d < 1
    rw [fair_pi n i d]
    norm_num
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    intro n i
    change |(1 : ℝ)| ≤ 1 ∧ |(1 : ℝ)| ≤ 1 ∧
      |1 / pi (fairPopulation n) i 1| ≤ 2 ∧ |1 / pi (fairPopulation n) i 0| ≤ 2
    rw [fair_pi, fair_pi]
    norm_num
  · refine ⟨1, fun _ i j => decide (i = j), ?_⟩
    intro n
    refine ⟨?_, fair_dependency n, ?_⟩
    · intro i j
      simp only [eq_comm]
    · intro i
      simp [eq_comm]
  · refine ⟨4, by norm_num, ?_⟩
    have heq : (fun n : ℕ => ((n : ℝ) + 1) * seqTrueVariance fairSequence n) =
        fun _ => (4 : ℝ) := by
      funext n
      rw [fair_true_variance]
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hn]
    rw [heq]
    exact tendsto_const_nhds
  · intro δ hδ
    have heq : (fun n : ℕ => probability (seqLaw fairSequence n)
        (fun z => ((n : ℝ) + 1) * seqVarianceEstimate fairSequence n z <
          ((n : ℝ) + 1) * seqTrueVariance fairSequence n - δ)) = fun _ => (0 : ℝ) := by
      funext n
      have hfalse : ∀ z, ¬ (((n : ℝ) + 1) * seqVarianceEstimate fairSequence n z <
          ((n : ℝ) + 1) * seqTrueVariance fairSequence n - δ) := by
        intro z
        rw [fair_variance_estimate n z, fair_true_variance n]
        linarith
      simp only [probability, hfalse, if_false, Finset.sum_const_zero]
    rw [heq]
    exact tendsto_const_nhds
  · intro n z
    exact ⟨fair_true_variance n, fair_variance_estimate n z⟩

end

end AronowAudit.P013.Wave1.CorrectedCoverage
