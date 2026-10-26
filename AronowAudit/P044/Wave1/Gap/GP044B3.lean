import AronowAudit.P044.P044_NetworkSpillovers
import AronowAudit.P045.P045_ExposureVariance

/-! Exposure-variance calculations using an explicit equivalence of the
P044 and P045 exposure types. The full-count table is transported from
the P045 counterpart through this equivalence. -/

namespace AronowAudit.P044.Wave1
open Finset
open scoped BigOperators
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The exposure names agree under this explicit bijection. -/
def clique_joint_moments_exposureEquiv : Exposure ≃
    AronowAudit.P045.ExposureVariance.Exposure where
  toFun
    | .d11 => .d11
    | .d10 => .d10
    | .d01 => .d01
    | .d00 => .d00
  invFun
    | .d11 => .d11
    | .d10 => .d10
    | .d01 => .d01
    | .d00 => .d00
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

theorem clique_joint_moments_exposure_iff (r : Fin 66) (i : Fin 12) (a : Exposure) :
    AronowAudit.P045.ExposureVariance.cliqueF r i = clique_joint_moments_exposureEquiv a ↔
      cliqueF r i = a := by
  have h : clique_joint_moments_exposureEquiv (cliqueF r i) =
      AronowAudit.P045.ExposureVariance.cliqueF r i := by
    unfold cliqueF AronowAudit.P045.ExposureVariance.cliqueF
    simp only [show AronowAudit.P045.ExposureVariance.cliquePairs = cliquePairs from rfl]
    split_ifs <;> rfl
  rw [← h]
  exact clique_joint_moments_exposureEquiv.injective.eq_iff

theorem clique_joint_moments_full_counts :
    (∀ i a, exposureCount cliqueF i a = cliqueFullCount a) ∧
    (∀ i j a b, (a = Exposure.d01 ∨ a = .d00) → (b = Exposure.d01 ∨ b = .d00) →
      jointCount cliqueF i j a b = cliqueFullJoint i j a b) := by
  constructor
  · intro i a
    have hc : exposureCount cliqueF i a =
        AronowAudit.P045.ExposureVariance.exposureCount
          AronowAudit.P045.ExposureVariance.cliqueF i (clique_joint_moments_exposureEquiv a) := by
      unfold exposureCount AronowAudit.P045.ExposureVariance.exposureCount
      congr 1
      apply Finset.filter_congr
      intro r _
      exact (clique_joint_moments_exposure_iff r i a).symm
    rw [hc, AronowAudit.P045.ExposureVariance.clique_full_counts.1]
    cases a <;> rfl
  · intro i j a b ha hb
    have ha' : clique_joint_moments_exposureEquiv a = .d01 ∨
        clique_joint_moments_exposureEquiv a = .d00 := by
      rcases ha with rfl | rfl <;> decide
    have hb' : clique_joint_moments_exposureEquiv b = .d01 ∨
        clique_joint_moments_exposureEquiv b = .d00 := by
      rcases hb with rfl | rfl <;> decide
    have hc : jointCount cliqueF i j a b =
        AronowAudit.P045.ExposureVariance.jointCount
          AronowAudit.P045.ExposureVariance.cliqueF i j
            (clique_joint_moments_exposureEquiv a) (clique_joint_moments_exposureEquiv b) := by
      unfold jointCount AronowAudit.P045.ExposureVariance.jointCount
      congr 1
      apply Finset.filter_congr
      intro r _
      exact and_congr (clique_joint_moments_exposure_iff r i a).symm
        (clique_joint_moments_exposure_iff r j b).symm
    rw [hc, AronowAudit.P045.ExposureVariance.clique_full_counts.2 i j _ _ ha' hb']
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl

theorem clique_observation_joint_certificate (t : Fin 66) (included : Bool) (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    joint (cliqueObservationMass t included) cliqueF i j a b = cliqueObservationJoint t included i j a b := by
  cases included
  · calc
      joint (cliqueObservationMass t false) cliqueF i j a b = (jointCount cliqueF i j a b : ℚ) / 66 := by
        rw [clique_observation_independent_mass]
        simpa using
          (exhaustive_probabilities (K := ℚ) (by decide : 0 < 66) cliqueF i j a b).2
      _ = cliqueObservationJoint t false i j a b := by
        rw [clique_joint_moments_full_counts.2 i j a b ha hb]
        rfl
  · have he : joint (cliqueObservationMass t true) cliqueF i j a b =
        joint (fun _ : Fin 65 => (1/65 : ℚ)) (retainedF t) i j a b := by
      unfold joint cliqueObservationMass retainedF
      rw [Fin.sum_univ_succAbove _ t]
      simp [Fin.succAbove_ne]
    calc
      joint (cliqueObservationMass t true) cliqueF i j a b =
          (jointCount (retainedF t) i j a b : ℚ) / 65 := by
        rw [he]
        simpa using (exhaustive_probabilities (K := ℚ) (by decide : 0 < 65) (retainedF t) i j a b).2
      _ = cliqueObservationJoint t true i j a b := by
        change ((Finset.univ.filter (fun r : Fin 65 =>
          cliqueF (t.succAbove r) i = a ∧ cliqueF (t.succAbove r) j = b)).card : ℚ) / 65 = _
        rw [count_delete_atom t (fun r : Fin 66 => cliqueF r i = a ∧ cliqueF r j = b)]
        rw [show (Finset.univ.filter (fun r => cliqueF r i = a ∧ cliqueF r j = b)).card =
          cliqueFullJoint i j a b from clique_joint_moments_full_counts.2 i j a b ha hb]
        rfl

theorem clique_observation_marginal_certificate (t : Fin 66) (included : Bool) (i : Fin 12) (a : Exposure) :
    marginal (cliqueObservationMass t included) cliqueF i a = cliqueObservationMarginal t included i a := by
  cases included
  · calc
      marginal (cliqueObservationMass t false) cliqueF i a = (exposureCount cliqueF i a : ℚ) / 66 := by
        rw [clique_observation_independent_mass]
        simpa using
          (exhaustive_probabilities (K := ℚ) (by decide : 0 < 66) cliqueF i i a a).1
      _ = cliqueObservationMarginal t false i a := by
        rw [clique_joint_moments_full_counts.1 i a]
        rfl
  · have he : marginal (cliqueObservationMass t true) cliqueF i a =
        marginal (fun _ : Fin 65 => (1/65 : ℚ)) (retainedF t) i a := by
      unfold marginal cliqueObservationMass retainedF
      rw [Fin.sum_univ_succAbove _ t]
      simp [Fin.succAbove_ne]
    calc
      marginal (cliqueObservationMass t true) cliqueF i a =
          (exposureCount (retainedF t) i a : ℚ) / 65 := by
        rw [he]
        simpa using (exhaustive_probabilities (K := ℚ) (by decide : 0 < 65) (retainedF t) i i a a).1
      _ = cliqueObservationMarginal t true i a := by
        change ((Finset.univ.filter (fun r : Fin 65 => cliqueF (t.succAbove r) i = a)).card : ℚ) / 65 = _
        rw [count_delete_atom t (fun r : Fin 66 => cliqueF r i = a)]
        rw [show (Finset.univ.filter (fun r => cliqueF r i = a)).card = cliqueFullCount a
          from clique_joint_moments_full_counts.1 i a]
        rfl

theorem clique_joint_moments_conditional_moments (t : Fin 66) (included : Bool) :
    expect (cliqueObservationMass t included) (cliqueT t) = cliqueConditionalMean t included ∧
    expect (cliqueObservationMass t included) (fun z => cliqueT t z ^ 2) = cliqueConditionalSecond t included ∧
    expect (cliqueObservationMass t included) (cliqueV t) = cliqueConditionalV t included := by
  have hkk := fun i j => clique_observation_joint_certificate t included i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
  have hll := fun i j => clique_observation_joint_certificate t included i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
  have hkl := fun i j => clique_observation_joint_certificate t included i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  have hlk := fun i j => clique_observation_joint_certificate t included i j .d00 .d01 (Or.inr rfl) (Or.inl rfl)
  refine ⟨?_, ?_, ?_⟩
  · unfold cliqueT htContrast
    rw [expect_sub, htMean_expectation, htMean_expectation]
    simp only [cliqueY, one_mul]
    simp_rw [clique_observation_marginal_certificate]
    unfold cliqueConditionalMean
    ring
  · unfold cliqueT
    rw [htContrast_second_moment]
    simp_rw [hkk, hll, hkl, hlk]
    simp [cliqueY, cliqueConditionalSecond, div_eq_mul_inv, mul_inv_rev] <;> norm_num
  · unfold cliqueV
    rw [varianceEstimate_expectation]
    unfold expectedVariance cliqueConditionalV expectedVariance expectedTotalVariance expectedTotalCovariance
    simp_rw [hkk, hll, hkl, clique_observation_marginal_certificate]

theorem clique_relabeling_verified_certificate :
    ∀ t : Fin 66,
      (∀ i j, cliqueAdj (cliqueRelabeling t i) (cliqueRelabeling t j) = cliqueAdj i j) ∧
      (∀ i, cliqueAssignments t (cliqueRelabeling t i) =
        cliqueAssignments (if (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4 then 0 else 3) i) ∧
      (∀ i, cliqueF t (cliqueRelabeling t i) =
        cliqueF (if (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4 then 0 else 3) i) := by
  intro t
  fin_cases t <;> decide +kernel

theorem clique_reduced_arithmetic_pair_sum_relabel (e : Equiv.Perm (Fin 12)) (F : Fin 12 → Fin 12 → ℚ) :
    (∑ i, ∑ j, F i j) = ∑ i, ∑ j, F (e i) (e j) := by
  calc
    (∑ i, ∑ j, F i j) = ∑ i, ∑ j, F (e i) j := (Equiv.sum_comp e _).symm
    _ = ∑ i, ∑ j, F (e i) (e j) :=
      Finset.sum_congr rfl (fun i _ => (Equiv.sum_comp e (fun j => F (e i) j)).symm)

theorem clique_reduced_arithmetic_conditional_relabel (t : Fin 66) (included : Bool) :
    let r : Fin 66 := if (cliquePairs t).1.val/4=(cliquePairs t).2.val/4 then 0 else 3
    cliqueConditionalMean t included=cliqueConditionalMean r included ∧
    cliqueConditionalSecond t included=cliqueConditionalSecond r included ∧
    cliqueConditionalV t included=cliqueConditionalV r included := by
  let r : Fin 66 := if (cliquePairs t).1.val/4=(cliquePairs t).2.val/4 then 0 else 3
  classical
  dsimp only
  let e := cliqueRelabeling t
  have hr := clique_relabeling_verified_certificate t
  have hF : ∀ i, cliqueF t (e i)=cliqueF r i := hr.2.2
  have heq : ∀ i j, e i=e j ↔ i=j := fun i j => e.injective.eq_iff
  have hsame : ∀ i j, (e i).val/4=(e j).val/4 ↔ i.val/4=j.val/4 := by
    intro i j
    by_cases hij : i=j
    · subst j
      simp
    · have hne : e i ≠ e j := e.injective.ne hij
      have hg0 : decide (e i ≠ e j ∧ (e i).val/4=(e j).val/4) =
          decide (i ≠ j ∧ i.val/4=j.val/4) := hr.1 i j
      have hg : decide ((e i).val/4=(e j).val/4) = decide (i.val/4=j.val/4) := by
        simpa [hij, hne] using hg0
      exact decide_eq_decide.mp hg
  have hc : ∀ i j a b, (a=Exposure.d01 ∨ a=.d00) → (b=Exposure.d01 ∨ b=.d00) →
      cliqueFullJoint (e i) (e j) a b=cliqueFullJoint i j a b := by
    intro i j a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals simp only [cliqueFullJoint, heq, hsame]
  have hw : ∀ i a, cliqueWeights t (e i) a=cliqueWeights r i a := by
    intro i a
    simp only [cliqueWeights, hF]
  have hm : ∀ i a, cliqueObservationMarginal t included (e i) a=
      cliqueObservationMarginal r included i a := by
    intro i a
    simp only [cliqueObservationMarginal, hF]
  have hJ : ∀ i j a b, (a=Exposure.d01 ∨ a=.d00) → (b=Exposure.d01 ∨ b=.d00) →
      cliqueObservationJoint t included (e i) (e j) a b=
        cliqueObservationJoint r included i j a b := by
    intro i j a b ha hb
    simp only [cliqueObservationJoint, hc i j a b ha hb, hF]
  have hq : ∀ i j a b, (a=Exposure.d01 ∨ a=.d00) → (b=Exposure.d01 ∨ b=.d00) →
      cliqueJoints t (e i) (e j) a b=cliqueJoints r i j a b := by
    intro i j a b ha hb
    simp only [cliqueJoints, hc i j a b ha hb, hF, heq]
  have hkk := fun i j => hJ i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
  have hll := fun i j => hJ i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
  have hkl := fun i j => hJ i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  have hlk := fun i j => hJ i j .d00 .d01 (Or.inr rfl) (Or.inl rfl)
  refine ⟨?_, ?_, ?_⟩
  · have hsum : ∀ a, (∑ i, cliqueObservationMarginal t included i a/cliqueWeights t i a) =
        ∑ i, cliqueObservationMarginal r included i a/cliqueWeights r i a := by
      intro a
      calc
        _ = ∑ i, cliqueObservationMarginal t included (e i) a/cliqueWeights t (e i) a :=
          (Equiv.sum_comp e _).symm
        _ = _ := by simp only [hm,hw]
    unfold cliqueConditionalMean
    rw [hsum,hsum]
  · unfold cliqueConditionalSecond
    rw [clique_reduced_arithmetic_pair_sum_relabel e]
    simp only [hkk,hll,hkl,hlk,hw]
    rfl
  · have hwithin : ∀ a, (a=Exposure.d01 ∨ a=.d00) →
        expectedTotalVariance (cliqueObservationMarginal t included)
          (cliqueObservationJoint t included) cliqueY (cliqueWeights t) (cliqueJoints t) a =
        expectedTotalVariance (cliqueObservationMarginal r included)
          (cliqueObservationJoint r included) cliqueY (cliqueWeights r) (cliqueJoints r) a := by
      intro a ha
      unfold expectedTotalVariance
      rw [clique_reduced_arithmetic_pair_sum_relabel e]
      simp only [hJ _ _ a a ha ha, hq _ _ a a ha ha, hm,hw,cliqueY, ne_eq,heq]
    have hcross : expectedTotalCovariance (cliqueObservationMarginal t included)
          (cliqueObservationJoint t included) cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00 =
        expectedTotalCovariance (cliqueObservationMarginal r included)
          (cliqueObservationJoint r included) cliqueY (cliqueWeights r) (cliqueJoints r) .d01 .d00 := by
      unfold expectedTotalCovariance
      rw [clique_reduced_arithmetic_pair_sum_relabel e]
      simp only [hkl, hq _ _ .d01 .d00 (Or.inl rfl) (Or.inr rfl),hm,hw,cliqueY]
    unfold cliqueConditionalV expectedVariance
    rw [hwithin .d01 (Or.inl rfl), hwithin .d00 (Or.inr rfl), hcross]

theorem clique_reduced_arithmetic_two_class_expect (F : Fin 66 → ℚ) (a b : ℚ)
    (hF : ∀ t, F t=if (cliquePairs t).1.val/4=(cliquePairs t).2.val/4 then a else b) :
    expect (fun _ : Fin 66 => (1/66 : ℚ)) F=(18*a+48*b)/66 := by
  simp only [expect]
  simp_rw [hF, mul_ite]
  rw [Finset.sum_ite]
  have hsame : (Finset.univ.filter (fun t : Fin 66 =>
      (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4)).card = 18 := by
    decide +kernel
  have hdiff : (Finset.univ.filter (fun t : Fin 66 =>
      ¬ (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4)).card = 48 := by
    decide +kernel
  simp only [Finset.sum_const, nsmul_eq_mul, hsame, hdiff]
  norm_num
  ring

theorem clique_reduced_arithmetic_two_representative_arithmetic :
    let M := fun included => (18*cliqueConditionalMean 0 included+48*cliqueConditionalMean 3 included)/66
    let S := fun included => (18*cliqueConditionalSecond 0 included+48*cliqueConditionalSecond 3 included)/66
    let V := fun included => (18*cliqueConditionalV 0 included+48*cliqueConditionalV 3 included)/66
    M false = -67/53592 ∧ S false-M false^2 = 113448938731/232640299584 ∧
    V false = 1040129476423/2326402995840 ∧
    M true = -67/52780 ∧ S true-M true^2 = 11375808887/23342482800 ∧
    V true = 4673362763/10414338480 ∧
    (∀ included, V included < S included-M included^2 ∧ V included < 6050/11907) := by
  decide +kernel

theorem clique_reduced_arithmetic_certificate :
    let U := fun _ : Fin 66 => (1/66 : ℚ)
    let M := fun included => expect U (fun t => cliqueConditionalMean t included)
    let S := fun included => expect U (fun t => cliqueConditionalSecond t included)
    let V := fun included => expect U (fun t => cliqueConditionalV t included)
    M false = -67/53592 ∧ S false - M false ^ 2 = 113448938731/232640299584 ∧
    V false = 1040129476423/2326402995840 ∧
    M true = -67/52780 ∧ S true - M true ^ 2 = 11375808887/23342482800 ∧
    V true = 4673362763/10414338480 ∧
    (∀ included, V included < S included - M included ^ 2 ∧ V included < 6050/11907) := by
  dsimp only
  have hM : ∀ included, expect (fun _ : Fin 66 => (1/66 : ℚ))
      (fun t => cliqueConditionalMean t included) =
      (18*cliqueConditionalMean 0 included+48*cliqueConditionalMean 3 included)/66 := by
    intro included
    apply clique_reduced_arithmetic_two_class_expect
    intro t
    have h := (clique_reduced_arithmetic_conditional_relabel t included).1
    split_ifs with hs <;> simpa only [hs,ite_true,ite_false] using h
  have hS : ∀ included, expect (fun _ : Fin 66 => (1/66 : ℚ))
      (fun t => cliqueConditionalSecond t included) =
      (18*cliqueConditionalSecond 0 included+48*cliqueConditionalSecond 3 included)/66 := by
    intro included
    apply clique_reduced_arithmetic_two_class_expect
    intro t
    have h := (clique_reduced_arithmetic_conditional_relabel t included).2.1
    split_ifs with hs <;> simpa only [hs,ite_true,ite_false] using h
  have hV : ∀ included, expect (fun _ : Fin 66 => (1/66 : ℚ))
      (fun t => cliqueConditionalV t included) =
      (18*cliqueConditionalV 0 included+48*cliqueConditionalV 3 included)/66 := by
    intro included
    apply clique_reduced_arithmetic_two_class_expect
    intro t
    have h := (clique_reduced_arithmetic_conditional_relabel t included).2.2
    split_ifs with hs <;> simpa only [hs,ite_true,ite_false] using h
  simp_rw [hM,hS,hV]
  exact clique_reduced_arithmetic_two_representative_arithmetic

theorem clique_joint_moments_proof :
    expect (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = -67/53592 ∧
    designVariance (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = 113448938731/232640299584 ∧
    expect (cliqueJointMass false) (fun x => cliqueV x.1 x.2) = 1040129476423/2326402995840 ∧
    expect (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = -67/52780 ∧
    designVariance (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = 11375808887/23342482800 ∧
    expect (cliqueJointMass true) (fun x => cliqueV x.1 x.2) = 4673362763/10414338480 ∧
    (∀ included,
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) <
        designVariance (cliqueJointMass included) (fun x => cliqueT x.1 x.2) ∧
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) < 6050/11907) := by
  have hM (included : Bool) : expect (cliqueJointMass included) (fun x => cliqueT x.1 x.2) =
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (fun t => cliqueConditionalMean t included) := by
    rw [clique_joint_expectation included cliqueT]
    congr 1
    funext t
    exact (clique_joint_moments_conditional_moments t included).1
  have hS (included : Bool) : expect (cliqueJointMass included) (fun x => cliqueT x.1 x.2 ^ 2) =
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (fun t => cliqueConditionalSecond t included) := by
    rw [clique_joint_expectation included (fun t z => cliqueT t z ^ 2)]
    congr 1
    funext t
    exact (clique_joint_moments_conditional_moments t included).2.1
  have hV (included : Bool) : expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) =
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (fun t => cliqueConditionalV t included) := by
    rw [clique_joint_expectation included cliqueV]
    congr 1
    funext t
    exact (clique_joint_moments_conditional_moments t included).2.2
  unfold designVariance
  simp_rw [hM, hS, hV]
  exact clique_reduced_arithmetic_certificate

theorem clique_observation_joint_proof (t : Fin 66) (included : Bool) (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    joint (cliqueObservationMass t included) cliqueF i j a b = cliqueObservationJoint t included i j a b := by
  exact clique_observation_joint_certificate t included i j a b ha hb

theorem clique_observation_marginal_proof (t : Fin 66) (included : Bool) (i : Fin 12) (a : Exposure) :
    marginal (cliqueObservationMass t included) cliqueF i a = cliqueObservationMarginal t included i a := by
  exact clique_observation_marginal_certificate t included i a

theorem clique_pairs_complete_proof :
    (∀ r, (cliquePairs r).1 < (cliquePairs r).2) ∧
    (∀ i j : Fin 12, i < j → ∃ r : Fin 66, cliquePairs r = (i,j)) := by
  constructor
  · intro r
    fin_cases r <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel

theorem clique_reduced_arithmetic_proof :
    let U := fun _ : Fin 66 => (1/66 : ℚ)
    let M := fun included => expect U (fun t => cliqueConditionalMean t included)
    let S := fun included => expect U (fun t => cliqueConditionalSecond t included)
    let V := fun included => expect U (fun t => cliqueConditionalV t included)
    M false = -67/53592 ∧ S false - M false ^ 2 = 113448938731/232640299584 ∧
    V false = 1040129476423/2326402995840 ∧
    M true = -67/52780 ∧ S true - M true ^ 2 = 11375808887/23342482800 ∧
    V true = 4673362763/10414338480 ∧
    (∀ included, V included < S included - M included ^ 2 ∧ V included < 6050/11907) := by
  exact clique_reduced_arithmetic_certificate

theorem clique_relabeling_verified_proof :
    ∀ t : Fin 66,
      (∀ i j, cliqueAdj (cliqueRelabeling t i) (cliqueRelabeling t j) = cliqueAdj i j) ∧
      (∀ i, cliqueAssignments t (cliqueRelabeling t i) =
        cliqueAssignments (if (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4 then 0 else 3) i) ∧
      (∀ i, cliqueF t (cliqueRelabeling t i) =
        cliqueF (if (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4 then 0 else 3) i) := by
  exact clique_relabeling_verified_certificate

end
end AronowAudit.P044.Wave1
