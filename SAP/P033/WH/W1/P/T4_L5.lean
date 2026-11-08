import SAP.P033.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P033.WH.W1.P.T4_L5

open SAP.P033.WH.W1

lemma physicalDistance_active (n : ℕ) (hn : 3 ≤ n)
    (j : Fin n) :
    wholePhysicalDistance n (wholeActiveIndex n j) =
      wholeBandwidth n * shrinkingDistance n j := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold wholePhysicalDistance wholeBandwidth shrinkingDistance wholeActiveIndex
  simp only [Fin.val_castLE]
  field_simp

lemma physicalMoment_eq (n : ℕ) (hn : 3 ≤ n)
    (hg : wholePhysicalGeometry n) (k : ℕ) :
    wholePhysicalMoment n k = wholeBandwidth n ^ k * shrinkingMoment n k := by
  rw [wholePhysicalMoment, hg.2.2.2.2.2.1]
  simp_rw [physicalDistance_active n hn]
  simp only [shrinkingMoment]
  calc
    (∑ j : Fin n, shrinkingKernel n j *
        (wholeBandwidth n * shrinkingDistance n j) ^ k) =
        ∑ j : Fin n, wholeBandwidth n ^ k *
          (shrinkingKernel n j * shrinkingDistance n j ^ k) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_pow]
      ring
    _ = wholeBandwidth n ^ k *
        ∑ j : Fin n, shrinkingKernel n j * shrinkingDistance n j ^ k := by
      rw [Finset.mul_sum]

lemma physicalDeterminant_eq (n : ℕ) (hn : 3 ≤ n)
    (hg : wholePhysicalGeometry n) :
    wholePhysicalMoment n 0 * wholePhysicalMoment n 2 -
      wholePhysicalMoment n 1 ^ 2 =
      wholeBandwidth n ^ 2 *
        (shrinkingMoment n 0 * shrinkingMoment n 2 - shrinkingMoment n 1 ^ 2) := by
  rw [physicalMoment_eq n hn hg 0, physicalMoment_eq n hn hg 1,
    physicalMoment_eq n hn hg 2]
  ring

lemma physicalIntercept_active (n : ℕ) (hn : 3 ≤ n)
    (hg : wholePhysicalGeometry n) (j : Fin n) :
    wholePhysicalIntercept n (wholeActiveIndex n j) = shrinkingIntercept n j := by
  have h1 := physicalMoment_eq n hn hg 1
  have h2 := physicalMoment_eq n hn hg 2
  have hd := physicalDeterminant_eq n hn hg
  have hh : wholeBandwidth n ≠ 0 := ne_of_gt hg.1
  have hdelta :
      shrinkingMoment n 0 * shrinkingMoment n 2 - shrinkingMoment n 1 ^ 2 ≠ 0 :=
    ne_of_gt (AronowAudit.P033.shrinking_wls_certificate n hn).2.2.2.2.1
  unfold wholePhysicalIntercept shrinkingIntercept
  rw [hd, h1, h2, physicalDistance_active n hn j,
    hg.2.2.2.2.1 j]
  field_simp [hh, hdelta]

end SAP.P033.WH.W1.P.T4_L5

theorem SAP.P033.WH.W1.T4_L5_proof : SAP.P033.WH.W1.T4_L5 := by
  intro n hn hg
  have hweights : ∀ j : Fin (n * (n + 1)),
      wholePhysicalIntercept n j = wholePaddedWeight n (shrinkingIntercept n) j := by
    intro j
    by_cases hj : j.val < n
    · let i : Fin n := ⟨j.val, hj⟩
      have hji : j = wholeActiveIndex n i := by
        apply Fin.ext
        simp [wholeActiveIndex, i]
      rw [hji, SAP.P033.WH.W1.P.T4_L5.physicalIntercept_active n hn hg i]
      change shrinkingIntercept n i =
        wholePaddedWeight n (shrinkingIntercept n) (wholeActiveIndex n i)
      simp [wholePaddedWeight, wholeActiveIndex]
    · have hnot : ¬ 0 < wholePhysicalKernel n j := by
        intro hp
        exact hj ((hg.2.2.1 j).mp hp)
      have hk : wholePhysicalKernel n j = 0 := by
        unfold wholePhysicalKernel
        apply le_antisymm
        · exact le_of_not_gt hnot
        · exact le_max_left _ _
      simp [wholePhysicalIntercept, wholePaddedWeight, hj, hk]
  have hbias : wholePhysicalBiasMoment n =
      wholeBandwidth n ^ 2 *
        (∑ j : Fin n, shrinkingIntercept n j * shrinkingDistance n j ^ 2) := by
    calc
      wholePhysicalBiasMoment n =
          ∑ j : Fin (n * (n + 1)),
            wholePaddedWeight n (shrinkingIntercept n) j *
              wholePhysicalDistance n j ^ 2 := by
        unfold wholePhysicalBiasMoment
        apply Finset.sum_congr rfl
        intro j hj
        rw [hweights j]
      _ = ∑ j : Fin n, shrinkingIntercept n j *
          wholePhysicalDistance n (wholeActiveIndex n j) ^ 2 :=
        hg.2.2.2.2.2.2 (shrinkingIntercept n)
          (fun j => wholePhysicalDistance n j ^ 2)
      _ = wholeBandwidth n ^ 2 *
          (∑ j : Fin n, shrinkingIntercept n j * shrinkingDistance n j ^ 2) := by
        calc
          _ = ∑ j : Fin n, wholeBandwidth n ^ 2 *
              (shrinkingIntercept n j * shrinkingDistance n j ^ 2) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [SAP.P033.WH.W1.P.T4_L5.physicalDistance_active n hn j]
            rw [mul_pow]
            ring
          _ = wholeBandwidth n ^ 2 *
              (∑ j : Fin n, shrinkingIntercept n j * shrinkingDistance n j ^ 2) := by
            rw [Finset.mul_sum]
  exact ⟨hweights, hbias⟩
