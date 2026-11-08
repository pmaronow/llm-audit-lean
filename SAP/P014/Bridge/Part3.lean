import SAP.P014.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P014.Bridge
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

theorem six_valid : IsDistribution uniformSix :=
  fromAudit_valid AronowAudit.P014.sixLaw

theorem witness_valid : IsDistribution assignmentDistribution :=
  fromAudit_valid AronowAudit.P014.witnessLaw

theorem witness_masses : AssignmentMasses :=
  ⟨AronowAudit.P014.witness_support, AronowAudit.P014.witness_masses⟩

theorem witness_counts : CommonWitnessCounts := AronowAudit.P014.witness_counts_propensities

theorem witness_positive : PositiveArms assignmentDistribution localThree := by
  apply interior_arms _ witness_valid
  intro i hi
  have h := witness_counts.2 i hi
  rw [h]
  norm_num

theorem scores1_card : (pushforward uniformSix scores1).atoms.card = 6 := by
  have hinj : Function.Injective AronowAudit.P014.witnessX := by
    intro a b hab
    exact AronowAudit.P014.witness_local_arrangements.1
      (congrArg (fun x : Fin 4 → ℝ => fun i : Fin 3 => x (Fin.castSucc i)) hab)
  change (AronowAudit.P014.sixLaw.map AronowAudit.P014.witnessX).support.card = 6
  simpa only [AronowAudit.P014.sixLaw, Finset.card_univ, Fintype.card_fin] using
    AronowAudit.P014.map_support_card_of_injective AronowAudit.P014.sixLaw _ hinj

/-- Arithmetic at the three zero-valued arms, using the exported four atoms
and their masses, rather than imposing any condition on potential outcomes. -/
theorem t1_zero_arms :
    conditionalAverage assignmentDistribution outcomes1 0 true = 0 ∧
    conditionalAverage assignmentDistribution outcomes1 1 true = 0 ∧
    conditionalAverage assignmentDistribution outcomes1 2 false = 0 := by
  change AronowAudit.P014.weightedMean AronowAudit.P014.witnessLaw
    AronowAudit.P014.spilloverAll 0 true = 0 ∧
    AronowAudit.P014.weightedMean AronowAudit.P014.witnessLaw
      AronowAudit.P014.spilloverAll 1 true = 0 ∧
    AronowAudit.P014.weightedMean AronowAudit.P014.witnessLaw
      AronowAudit.P014.spilloverAll 2 false = 0
  norm_num [AronowAudit.P014.weightedMean, AronowAudit.P014.weightedNumerator,
    AronowAudit.P014.armMass, AronowAudit.P014.armSupport,
    AronowAudit.P014.witness_support, AronowAudit.P014.witness_masses,
    AronowAudit.P014.spilloverAll, AronowAudit.P014.bit,
    Finset.filter_insert, Finset.filter_singleton, funext_iff, Fin.forall_fin_succ]

theorem T1_proof : T1Statement := by
  obtain ⟨a1,a2,a3,a4,a5,a6,w1,w2,w3,hpoint,hE,hT,hW⟩ := AronowAudit.P014.t1_arithmetic
  have hE' : expectation assignmentDistribution (differenceOfMeans localThree outcomes1) = 0 := hE
  have hT' : windowContrast localThree (supportAverage assignmentDistribution outcomes1) = -1/18 := hT
  refine ⟨six_valid, witness_valid, AronowAudit.P014.witness_printed_local,
    by norm_num [localThree], scores1_card, AronowAudit.P014.witness_threshold.1,
    AronowAudit.P014.all_local_permutations_equiprobable.1, witness_masses, witness_counts,
    witness_positive, a1,a2,a3,a4,a5,a6, t1_zero_arms.1,w1,t1_zero_arms.2.1,w2,w3,
    t1_zero_arms.2.2,hpoint,hE,hT,hW,?_,?_⟩
  · rw [hE', hT']; norm_num
  · rw [hE', hT']; norm_num

theorem T4_proof : T4Statement := by
  obtain ⟨hl, _, _, hE, hT, hne⟩ := AronowAudit.P014.t1_counterexample
  rw [AronowAudit.P014.witness_threshold.1] at hE hT hne
  exact ⟨six_valid, witness_valid, hl, AronowAudit.P014.witness_threshold.1,
    AronowAudit.P014.all_local_permutations_equiprobable.1, witness_counts,
    witness_positive, hE, hT, hne⟩

theorem scores9_card : (pushforward uniformSix scores9).atoms.card = 6 := by
  have hinj : Function.Injective AronowAudit.P014.comparisonX := by
    intro a b h
    have he := congrArg (fun x : Fin 4 → ℝ => (x 0, x 1)) h
    fin_cases a <;> fin_cases b <;> norm_num [AronowAudit.P014.comparisonX] at he <;> rfl
  change (AronowAudit.P014.sixLaw.map AronowAudit.P014.comparisonX).support.card = 6
  simpa only [AronowAudit.P014.sixLaw, Finset.card_univ, Fintype.card_fin] using
    AronowAudit.P014.map_support_card_of_injective AronowAudit.P014.sixLaw _ hinj

theorem t9_zero_arms :
    supportAverage assignmentDistribution outcomes9 0 true = 0 ∧
    conditionalAverage assignmentDistribution outcomes9 0 true = 0 ∧
    (∀ i ∈ localThree, i ≠ 0 → ∀ a,
      supportAverage assignmentDistribution outcomes9 i a = 0 ∧
      conditionalAverage assignmentDistribution outcomes9 i a = 0) := by
  have hz (i : Fin 4) (a : Bool) (h : i = 0 → a = true) :
      supportAverage assignmentDistribution outcomes9 i a = 0 ∧
      conditionalAverage assignmentDistribution outcomes9 i a = 0 := by
    change AronowAudit.P014.printedMean AronowAudit.P014.witnessLaw
      AronowAudit.P014.spilloverOne i a = 0 ∧
      AronowAudit.P014.weightedMean AronowAudit.P014.witnessLaw
        AronowAudit.P014.spilloverOne i a = 0
    fin_cases i <;> cases a <;>
      norm_num [AronowAudit.P014.printedMean, AronowAudit.P014.weightedMean,
        AronowAudit.P014.weightedNumerator, AronowAudit.P014.armMass, AronowAudit.P014.armSupport,
        AronowAudit.P014.witness_support, AronowAudit.P014.witness_masses,
        AronowAudit.P014.spilloverOne, AronowAudit.P014.bit, Finset.filter_insert,
        Finset.filter_singleton, funext_iff, Fin.forall_fin_succ] at *
  exact ⟨(hz 0 true (by simp)).1, (hz 0 true (by simp)).2,
    fun i _ hi a => hz i a (fun he => (hi he).elim)⟩

theorem t9_pointwise : ∀ z ∈ assignmentDistribution.atoms,
    differenceOfMeans localThree outcomes9 z =
      if z = ![false,false,true,true] then -1/2 else 0 := by
  intro z hz
  change z ∈ AronowAudit.P014.witnessLaw.support at hz
  rw [AronowAudit.P014.witness_support] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    norm_num [differenceOfMeans, observedArmTotal, armSize, localThree, outcomes9,
      binaryValue, Finset.filter_insert, Finset.filter_singleton, funext_iff, Fin.forall_fin_succ]

theorem T9_proof : T9Statement := by
  obtain ⟨hl,hA,hM,hTA,hTM,_,_,hE⟩ := AronowAudit.P014.t9_counterexample
  obtain ⟨hD,hn1,hn2,hbias⟩ := AronowAudit.P014.t9_hudgens_halloran_comparison
  rw [AronowAudit.P014.witness_threshold.2] at hE hbias
  exact ⟨six_valid,witness_valid,hl,scores9_card,AronowAudit.P014.witness_threshold.2,
    AronowAudit.P014.all_local_permutations_equiprobable.2,witness_masses,witness_counts,
    witness_positive,hA,hM,(fun i hi a => AronowAudit.P014.hhMean_eq_weighted
      AronowAudit.P014.witnessLaw AronowAudit.P014.spilloverOne i a
      (witness_positive i hi a)),t9_zero_arms.1,t9_zero_arms.2.1,t9_zero_arms.2.2,
    hTA,hTM,hD,hn1,hn2,t9_pointwise,hE,hbias⟩

end
end SAP.P014.Bridge
