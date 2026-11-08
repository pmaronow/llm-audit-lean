import SAP.P014.Bridge.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014.Bridge
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

theorem defective_valid : IsDistribution assignmentDistribution5 :=
  fromAudit_valid (AronowAudit.P014.sixLaw.map
    (fun ω => AronowAudit.P014.threshold (AronowAudit.P014.defectiveX ω)))

/-- The three distinct vectors, already enumerated in the source proof of T5. -/
theorem defective_support : assignmentDistribution5.atoms =
    {![true,false,false,true], ![false,true,false,true], ![false,false,true,true]} := by
  change (AronowAudit.P014.sixLaw.map
    (fun ω => AronowAudit.P014.threshold (AronowAudit.P014.defectiveX ω))).support = _
  ext z
  norm_num [AronowAudit.P014.FiniteLaw.map, AronowAudit.P014.sixLaw,
    AronowAudit.P014.defectiveX, AronowAudit.P014.threshold, Fin.exists_fin_succ,
    funext_iff, Fin.forall_fin_succ]

theorem defective_masses :
    assignmentDistribution5.weight ![true,false,false,true] = 1/6 ∧
    assignmentDistribution5.weight ![false,true,false,true] = 1/6 ∧
    assignmentDistribution5.weight ![false,false,true,true] = 2/3 := by
  norm_num [assignmentDistribution5, pushforward, probability, uniformSix, scores5,
    thresholdAssignment, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]

theorem defective_positive : PositiveArms assignmentDistribution5 localThree := by
  intro i hi a
  simp only [localThree, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> cases a <;>
    norm_num [armProbability, armAssignments, defective_support, defective_masses,
      Finset.filter_insert, Finset.filter_singleton, funext_iff, Fin.forall_fin_succ]

theorem defective_scores_card : (pushforward uniformSix scores5).atoms.card = 6 := by
  have hinj : Function.Injective AronowAudit.P014.defectiveX := by
    intro a b h
    have he := congrArg (fun x : Fin 4 → ℝ => (x 0, x 1, x 3)) h
    fin_cases a <;> fin_cases b <;> norm_num [AronowAudit.P014.defectiveX] at he <;> rfl
  change (AronowAudit.P014.sixLaw.map AronowAudit.P014.defectiveX).support.card = 6
  simpa only [AronowAudit.P014.sixLaw, Finset.card_univ, Fintype.card_fin] using
    AronowAudit.P014.map_support_card_of_injective AronowAudit.P014.sixLaw _ hinj

theorem defective_other_permutations :
    probability uniformSix (fun ω => localCoordinates scores5 ω = ![1,-1,-2]) = 1/6 ∧
    probability uniformSix (fun ω => localCoordinates scores5 ω = ![-1,1,-2]) = 1/6 ∧
    probability uniformSix (fun ω => localCoordinates scores5 ω = ![-2,-1,1]) = 0 ∧
    probability uniformSix (fun ω => localCoordinates scores5 ω = ![-2,1,-1]) = 0 ∧
    probability uniformSix (fun ω => localCoordinates scores5 ω = ![1,-2,-1]) = 0 := by
  norm_num [probability, uniformSix, localCoordinates, scores5,
    Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]

theorem defective_pointwise : ∀ z ∈ assignmentDistribution5.atoms,
    armSize localThree z true = 1 ∧
    differenceOfMeans localThree outcomes5 z = binaryValue (z 0) := by
  intro z hz
  rw [defective_support] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl <;>
    norm_num [armSize, localThree, differenceOfMeans, observedArmTotal, outcomes5, binaryValue,
      Finset.filter_insert, Finset.filter_singleton]

theorem defective_means : ∀ i ∈ localThree, ∀ a,
    supportAverage assignmentDistribution5 outcomes5 i a =
      (if i = 0 then binaryValue a else 0) ∧
    conditionalAverage assignmentDistribution5 outcomes5 i a =
      (if i = 0 then binaryValue a else 0) := by
  intro i hi a
  apply AronowAudit.P014.constant_arm_means
    (toAudit assignmentDistribution5 defective_valid) outcomes5 i a _
    (defective_positive i hi a).ne'
  intro z hz
  have ha : z i = a := (Finset.mem_filter.mp hz).2
  simp only [localThree, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> simp_all [outcomes5]

theorem T5_proof : T5Statement := by
  obtain ⟨hl,hp,hne,hp1,hp2,hp3,hE,hT⟩ := AronowAudit.P014.t5_counterexample
  have hE' : expectation assignmentDistribution5 (differenceOfMeans localThree outcomes5) = 1/6 := hE
  have hT' : windowContrast localThree (supportAverage assignmentDistribution5 outcomes5) = 1/3 := hT
  refine ⟨six_valid,defective_valid,hl,defective_scores_card,
    defective_other_permutations.1,defective_other_permutations.2.1,hp,
    defective_other_permutations.2.2.1,defective_other_permutations.2.2.2.1,
    defective_other_permutations.2.2.2.2,hne,hp1,hp2,hp3,defective_positive,
    defective_support,defective_masses.1,defective_masses.2.1,defective_masses.2.2,
    defective_pointwise,defective_means,?_,hE,hT,?_⟩
  · intro i hi z z' hz
    simp only [localThree, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> simp_all [outcomes5]
  · rw [hE', hT']; norm_num

end
end SAP.P014.Bridge
