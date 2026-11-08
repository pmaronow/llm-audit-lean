import SAP.P024.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P024.WH.W1.P.T5_L1

open scoped BigOperators
open SAP.P024

theorem fewDozen_means :
    clusterMean0 fewDozenPopulation = (fun _ => 0) ∧
      clusterMean1 fewDozenPopulation = (fun j => if j = 0 then 1 else 0) := by
  constructor
  · funext j
    change (∑ _ : Fin (if j = 0 then 46 else 1), (0 : ℝ)) / _ = 0
    simp
  · funext j
    change (∑ _ : Fin (if j = 0 then 46 else 1),
      (if j = 0 then (1 : ℝ) else 0)) / ((if j = 0 then 46 else 1 : ℕ) : ℝ) = _
    by_cases hj : j = 0 <;> norm_num [hj]

end SAP.P024.WH.W1.P.T5_L1

open scoped BigOperators
open SAP.P024

theorem SAP.P024.WH.W1.T5_L1_proof : SAP.P024.WH.W1.T5_L1 := by
  classical
  intro empty s
  have hs0 : s.val ≠ ∅ := by
    intro h
    have hc := s.property
    rw [h] at hc
    simp at hc
  have hs1 : s.val ≠ Finset.univ := by
    intro h
    have hc := s.property
    rw [h] at hc
    simp at hc
  rcases SAP.P024.WH.W1.P.T5_L1.fewDozen_means with ⟨hm0, hm1⟩
  have he : SAP.P024.populationEstimator SAP.P024.fewDozenPopulation empty s.val =
      SAP.P024.clusterDIM (fun j => SAP.P024.fewDozenPopulation.size j)
        (SAP.P024.clusterMean0 SAP.P024.fewDozenPopulation)
        (SAP.P024.clusterMean1 SAP.P024.fewDozenPopulation)
        (SAP.P024.subsetExposure s.val) := by
    unfold SAP.P024.populationEstimator
    simp [hs0, hs1]
  rw [he]
  change AronowAudit.P024.clusterDIM
      (fun j => SAP.P024.fewDozenPopulation.size j)
      (SAP.P024.clusterMean0 SAP.P024.fewDozenPopulation)
      (SAP.P024.clusterMean1 SAP.P024.fewDozenPopulation)
      (AronowAudit.P024.subsetExposure s.val) = _
  rw [AronowAudit.P024.cluster_dim_subset]
  rw [hm0, hm1]
  have hterm1 : ∀ j : Fin 24,
      (SAP.P024.fewDozenPopulation.size j : ℝ) * (if j = 0 then (1 : ℝ) else 0) =
        if j = 0 then 46 else 0 := by
    intro j
    by_cases hj : j = 0 <;> simp [SAP.P024.fewDozenPopulation, hj]
  have htermD : ∀ j : Fin 24,
      (SAP.P024.fewDozenPopulation.size j : ℝ) = if j = 0 then 46 else 1 := by
    intro j
    by_cases hj : j = 0 <;> simp [SAP.P024.fewDozenPopulation, hj]
  have hnum : (∑ j ∈ s.val,
      (SAP.P024.fewDozenPopulation.size j : ℝ) * (if j = 0 then (1 : ℝ) else 0)) =
      if (0 : Fin 24) ∈ s.val then 46 else 0 := by
    simp_rw [hterm1]
    rw [AronowAudit.P024.sum_two_values]
    norm_num
  have hden : (∑ j ∈ s.val, (SAP.P024.fewDozenPopulation.size j : ℝ)) =
      12 + if (0 : Fin 24) ∈ s.val then 45 else 0 := by
    simp_rw [htermD]
    rw [AronowAudit.P024.sum_two_values]
    norm_num [s.property]
  rw [hnum, hden]
  simp only [mul_zero, Finset.sum_const_zero, zero_div, sub_zero]
  by_cases hz : (0 : Fin 24) ∈ s.val
  · simp [hz]
    norm_num
  · simp [hz]

