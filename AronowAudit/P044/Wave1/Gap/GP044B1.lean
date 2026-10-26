import AronowAudit.P044.P044_NetworkSpillovers

/-! Finite exposure-variance calculations using the P044 definitions.
Finite certificates and finite-sum algebra are adapted from this repository's P045
exposure-variance model. -/
namespace AronowAudit.P044.Wave1
open Finset
open scoped BigOperators
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem cfx_full_counts :
    (∀ i a, exposureCount cliqueF i a = cliqueFullCount a) ∧
    (∀ i j a b, (a = Exposure.d01 ∨ a = .d00) → (b = Exposure.d01 ∨ b = .d00) →
      jointCount cliqueF i j a b = cliqueFullJoint i j a b) := by
  constructor
  · intro i a
    fin_cases i <;> cases a <;> decide +kernel
  · intro i j a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals (fin_cases i <;> fin_cases j <;> decide +kernel)

theorem cfx_observation_marginal (t : Fin 66) (included : Bool) (i : Fin 12) (a : Exposure) :
    marginal (cliqueObservationMass t included) cliqueF i a = cliqueObservationMarginal t included i a := by
  cases included
  · calc
      marginal (cliqueObservationMass t false) cliqueF i a = (exposureCount cliqueF i a : ℚ) / 66 := by
        rw [clique_observation_independent_mass]
        simpa using
          (exhaustive_probabilities (K := ℚ) (by decide : 0 < 66) cliqueF i i a a).1
      _ = cliqueObservationMarginal t false i a := by
        rw [cfx_full_counts.1 i a]
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
          from cfx_full_counts.1 i a]
        rfl

theorem cfx_observation_joint (t : Fin 66) (included : Bool) (i j : Fin 12) (a b : Exposure)
    (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
    joint (cliqueObservationMass t included) cliqueF i j a b = cliqueObservationJoint t included i j a b := by
  cases included
  · calc
      joint (cliqueObservationMass t false) cliqueF i j a b = (jointCount cliqueF i j a b : ℚ) / 66 := by
        rw [clique_observation_independent_mass]
        simpa using
          (exhaustive_probabilities (K := ℚ) (by decide : 0 < 66) cliqueF i j a b).2
      _ = cliqueObservationJoint t false i j a b := by
        rw [cfx_full_counts.2 i j a b ha hb]
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
          cliqueFullJoint i j a b from cfx_full_counts.2 i j a b ha hb]
        rfl

theorem cfx_conditional_moments (t : Fin 66) (included : Bool) :
    expect (cliqueObservationMass t included) (cliqueT t) = cliqueConditionalMean t included ∧
    expect (cliqueObservationMass t included) (fun z => cliqueT t z ^ 2) = cliqueConditionalSecond t included ∧
    expect (cliqueObservationMass t included) (cliqueV t) = cliqueConditionalV t included := by
  have hkk := fun i j => cfx_observation_joint t included i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
  have hll := fun i j => cfx_observation_joint t included i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
  have hkl := fun i j => cfx_observation_joint t included i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  have hlk := fun i j => cfx_observation_joint t included i j .d00 .d01 (Or.inr rfl) (Or.inl rfl)
  refine ⟨?_, ?_, ?_⟩
  · unfold cliqueT htContrast
    rw [expect_sub, htMean_expectation, htMean_expectation]
    simp only [cliqueY, one_mul]
    simp_rw [cfx_observation_marginal]
    unfold cliqueConditionalMean
    ring
  · unfold cliqueT
    rw [htContrast_second_moment]
    simp_rw [hkk, hll, hkl, hlk]
    simp [cliqueY, cliqueConditionalSecond, div_eq_mul_inv, mul_inv_rev] <;> norm_num
  · unfold cliqueV
    rw [varianceEstimate_expectation]
    unfold expectedVariance cliqueConditionalV expectedVariance expectedTotalVariance expectedTotalCovariance
    simp_rw [hkk, hll, hkl, cfx_observation_marginal]

theorem cfx_relabeling_verified :
    ∀ t : Fin 66,
      (∀ i j, cliqueAdj (cliqueRelabeling t i) (cliqueRelabeling t j) = cliqueAdj i j) ∧
      (∀ i, cliqueAssignments t (cliqueRelabeling t i) =
        cliqueAssignments (if (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4 then 0 else 3) i) ∧
      (∀ i, cliqueF t (cliqueRelabeling t i) =
        cliqueF (if (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4 then 0 else 3) i) := by
  intro t
  fin_cases t <;> decide +kernel

theorem cfx_pair_sum_relabel (e : Equiv.Perm (Fin 12)) (F : Fin 12 → Fin 12 → ℚ) :
    (∑ i, ∑ j, F i j) = ∑ i, ∑ j, F (e i) (e j) := by
  calc
    (∑ i, ∑ j, F i j) = ∑ i, ∑ j, F (e i) j := (Equiv.sum_comp e _).symm
    _ = ∑ i, ∑ j, F (e i) (e j) :=
      Finset.sum_congr rfl (fun i _ => (Equiv.sum_comp e (fun j => F (e i) j)).symm)

theorem cfx_conditional_relabel (t : Fin 66) (included : Bool) :
    let r : Fin 66 := if (cliquePairs t).1.val/4=(cliquePairs t).2.val/4 then 0 else 3
    cliqueConditionalMean t included=cliqueConditionalMean r included ∧
    cliqueConditionalSecond t included=cliqueConditionalSecond r included ∧
    cliqueConditionalV t included=cliqueConditionalV r included := by
  let r : Fin 66 := if (cliquePairs t).1.val/4=(cliquePairs t).2.val/4 then 0 else 3
  classical
  dsimp only
  let e := cliqueRelabeling t
  have hr := cfx_relabeling_verified t
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
    rw [cfx_pair_sum_relabel e]
    simp only [hkk,hll,hkl,hlk,hw]
    rfl
  · have hwithin : ∀ a, (a=Exposure.d01 ∨ a=.d00) →
        expectedTotalVariance (cliqueObservationMarginal t included)
          (cliqueObservationJoint t included) cliqueY (cliqueWeights t) (cliqueJoints t) a =
        expectedTotalVariance (cliqueObservationMarginal r included)
          (cliqueObservationJoint r included) cliqueY (cliqueWeights r) (cliqueJoints r) a := by
      intro a ha
      unfold expectedTotalVariance
      rw [cfx_pair_sum_relabel e]
      simp only [hJ _ _ a a ha ha, hq _ _ a a ha ha, hm,hw,cliqueY, ne_eq,heq]
    have hcross : expectedTotalCovariance (cliqueObservationMarginal t included)
          (cliqueObservationJoint t included) cliqueY (cliqueWeights t) (cliqueJoints t) .d01 .d00 =
        expectedTotalCovariance (cliqueObservationMarginal r included)
          (cliqueObservationJoint r included) cliqueY (cliqueWeights r) (cliqueJoints r) .d01 .d00 := by
      unfold expectedTotalCovariance
      rw [cfx_pair_sum_relabel e]
      simp only [hkl, hq _ _ .d01 .d00 (Or.inl rfl) (Or.inr rfl),hm,hw,cliqueY]
    unfold cliqueConditionalV expectedVariance
    rw [hwithin .d01 (Or.inl rfl), hwithin .d00 (Or.inr rfl), hcross]

theorem cfx_fixed_reduced_arithmetic :
    cliqueConditionalSecond 0 false - (cliqueConditionalMean 0 false)^2 = 2810528137/5767941312 ∧
    cliqueConditionalV 0 false = 267260522663/634473544320 ∧
    cliqueConditionalV 0 false < cliqueConditionalSecond 0 false - (cliqueConditionalMean 0 false)^2 ∧
    cliqueConditionalSecond 3 false - (cliqueConditionalMean 3 false)^2 = 937589375/1922647104 ∧
    cliqueConditionalV 3 false = 4830430961/10574559072 ∧
    cliqueConditionalV 3 false < cliqueConditionalSecond 3 false - (cliqueConditionalMean 3 false)^2 ∧
    cliqueConditionalV 0 false - (cliqueConditionalSecond 0 false - (cliqueConditionalMean 0 false)^2) =
      -1551761941/23499020160 ∧
    cliqueConditionalV 3 false - (cliqueConditionalSecond 3 false - (cliqueConditionalMean 3 false)^2) =
      -72513467/2349902016 := by
  decide +kernel

theorem cfx_all_fixed_reduced_arithmetic :
    ∀ t : Fin 66,
      let same := (cliquePairs t).1.val/4=(cliquePairs t).2.val/4
      cliqueConditionalSecond t false-(cliqueConditionalMean t false)^2 =
        (if same then 2810528137/5767941312 else 937589375/1922647104) ∧
      cliqueConditionalV t false =
        (if same then 267260522663/634473544320 else 4830430961/10574559072) ∧
      cliqueConditionalV t false-
        (cliqueConditionalSecond t false-(cliqueConditionalMean t false)^2) =
        (if same then -1551761941/23499020160 else -72513467/2349902016) ∧
      cliqueConditionalV t false <
        cliqueConditionalSecond t false-(cliqueConditionalMean t false)^2 := by
  intro t
  have h := cfx_conditional_relabel t false
  dsimp only at h
  by_cases hs : (cliquePairs t).1.val/4=(cliquePairs t).2.val/4
  · simp only [hs,ite_true] at h ⊢
    rw [h.1,h.2.1,h.2.2]
    exact ⟨cfx_fixed_reduced_arithmetic.1, cfx_fixed_reduced_arithmetic.2.1,
      cfx_fixed_reduced_arithmetic.2.2.2.2.2.2.1, cfx_fixed_reduced_arithmetic.2.2.1⟩
  · simp only [hs,ite_false] at h ⊢
    rw [h.1,h.2.1,h.2.2]
    exact ⟨cfx_fixed_reduced_arithmetic.2.2.2.1, cfx_fixed_reduced_arithmetic.2.2.2.2.1,
      cfx_fixed_reduced_arithmetic.2.2.2.2.2.2.2, cfx_fixed_reduced_arithmetic.2.2.2.2.2.1⟩

theorem clique_all_fixed_table_counterexamples_proof :
    ∀ t : Fin 66,
      let same := (cliquePairs t).1.val / 4 = (cliquePairs t).2.val / 4
      designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT t) =
        (if same then 2810528137/5767941312 else 937589375/1922647104) ∧
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV t) =
        (if same then 267260522663/634473544320 else 4830430961/10574559072) ∧
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV t) -
        designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT t) =
        (if same then -1551761941/23499020160 else -72513467/2349902016) ∧
      expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV t) <
        designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT t) := by
  intro t
  have h := cfx_conditional_moments t false
  simp only [clique_observation_independent_mass] at h
  unfold designVariance
  rw [h.1,h.2.1,h.2.2]
  exact cfx_all_fixed_reduced_arithmetic t


theorem ccs_pairs_complete :
    (∀ r, (cliquePairs r).1 < (cliquePairs r).2) ∧
    (∀ i j : Fin 12, i < j → ∃ r : Fin 66, cliquePairs r = (i,j)) := by
  constructor
  · intro r
    fin_cases r <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel

theorem clique_complete_support_proof (z : Assignment 12) :
    (Finset.univ.filter (fun i => z i)).card = 2 ↔ ∃ r, cliqueAssignments r = z := by
  constructor
  · intro hz
    obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp hz
    have hvec (r : Fin 66) (hr : cliquePairs r = (i,j) ∨ cliquePairs r = (j,i)) : cliqueAssignments r = z := by
      have hm (t : Fin 12) : z t = true ↔ t = i ∨ t = j := by
        calc
          z t = true ↔ t ∈ Finset.univ.filter (fun k => z k) := by simp
          _ ↔ t ∈ ({i,j} : Finset (Fin 12)) := by rw [hs]
          _ ↔ t = i ∨ t = j := by simp
      funext t
      unfold cliqueAssignments
      rcases hr with hr | hr <;> rw [hr]
      · cases ht : z t
        · have hn : ¬(t = i ∨ t = j) := by simpa [ht] using hm t
          simp [hn]
        · have hp := (hm t).mp ht
          simp [hp]
      · cases ht : z t
        · have hn : ¬(t = i ∨ t = j) := by simpa [ht] using hm t
          simp [hn, or_comm]
        · have hp := (hm t).mp ht
          simp [hp, or_comm]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · obtain ⟨r, hr⟩ := ccs_pairs_complete.2 i j hlt
      exact ⟨r, hvec r (Or.inl hr)⟩
    · obtain ⟨r, hr⟩ := ccs_pairs_complete.2 j i hgt
      exact ⟨r, hvec r (Or.inr hr)⟩
  · rintro ⟨r, rfl⟩
    fin_cases r <;> decide +kernel


theorem clique_conditional_moments_proof (t : Fin 66) (included : Bool) :
    expect (cliqueObservationMass t included) (cliqueT t) = cliqueConditionalMean t included ∧
    expect (cliqueObservationMass t included) (fun z => cliqueT t z ^ 2) = cliqueConditionalSecond t included ∧
    expect (cliqueObservationMass t included) (cliqueV t) = cliqueConditionalV t included := by
  exact cfx_conditional_moments t included

theorem cem_exact_reduced_arithmetic :
    let m := cliqueObservationMarginal 0 false
    let J := cliqueObservationJoint 0 false
    let M := ((∑ i, m i .d01 / m i .d01) - (∑ i, m i .d00 / m i .d00)) / 12
    let S := (∑ i, ∑ j,
      (J i j .d01 .d01 / (m i .d01 * m j .d01) +
       J i j .d00 .d00 / (m i .d00 * m j .d00) -
       J i j .d01 .d00 / (m i .d01 * m j .d00) -
       J i j .d00 .d01 / (m i .d00 * m j .d01))) / 144
    M = 0 ∧ S - M^2 = 6050/11907 ∧ expectedVariance m J cliqueY m J .d01 .d00 = 6050/11907 := by
  decide +kernel

theorem clique_exact_moments_proof :
    let p := fun _ : Fin 66 => (1/66 : ℚ)
    let m := marginal p cliqueF
    let J := joint p cliqueF
    let T := htContrast cliqueF cliqueY m .d01 .d00
    expect p T = 0 ∧ designVariance p T = 6050/11907 ∧
      expect p (varianceEstimate cliqueF cliqueY m J .d01 .d00) = 6050/11907 := by
  let p := fun _ : Fin 66 => (1/66 : ℚ)
  let m := cliqueObservationMarginal 0 false
  let J := cliqueObservationJoint 0 false
  let M := ((∑ i, m i .d01 / m i .d01) - (∑ i, m i .d00 / m i .d00)) / 12
  let S := (∑ i, ∑ j,
    (J i j .d01 .d01 / (m i .d01 * m j .d01) +
     J i j .d00 .d00 / (m i .d00 * m j .d00) -
     J i j .d01 .d00 / (m i .d01 * m j .d00) -
     J i j .d00 .d01 / (m i .d00 * m j .d01))) / 144
  have hm : marginal p cliqueF = m := by
    funext i a
    simpa only [p, m, clique_observation_independent_mass] using cfx_observation_marginal 0 false i a
  have hkk (i j) : joint p cliqueF i j .d01 .d01 = J i j .d01 .d01 := by
    simpa only [p, J, clique_observation_independent_mass] using
      cfx_observation_joint 0 false i j .d01 .d01 (Or.inl rfl) (Or.inl rfl)
  have hll (i j) : joint p cliqueF i j .d00 .d00 = J i j .d00 .d00 := by
    simpa only [p, J, clique_observation_independent_mass] using
      cfx_observation_joint 0 false i j .d00 .d00 (Or.inr rfl) (Or.inr rfl)
  have hkl (i j) : joint p cliqueF i j .d01 .d00 = J i j .d01 .d00 := by
    simpa only [p, J, clique_observation_independent_mass] using
      cfx_observation_joint 0 false i j .d01 .d00 (Or.inl rfl) (Or.inr rfl)
  have hlk (i j) : joint p cliqueF i j .d00 .d01 = J i j .d00 .d01 := by
    simpa only [p, J, clique_observation_independent_mass] using
      cfx_observation_joint 0 false i j .d00 .d01 (Or.inr rfl) (Or.inl rfl)
  have hmean : expect p (htContrast cliqueF cliqueY (marginal p cliqueF) .d01 .d00) = M := by
    unfold htContrast
    rw [expect_sub, htMean_expectation, htMean_expectation, hm]
    simp only [cliqueY, one_mul]
    unfold M
    ring
  have hsecond : expect p (fun r => htContrast cliqueF cliqueY (marginal p cliqueF) .d01 .d00 r ^ 2) = S := by
    rw [htContrast_second_moment, hm]
    simp_rw [hkk, hll, hkl, hlk]
    simp [cliqueY, S, div_eq_mul_inv, mul_inv_rev] <;> norm_num
  have hv : expect p (varianceEstimate cliqueF cliqueY (marginal p cliqueF) (joint p cliqueF) .d01 .d00) =
      expectedVariance m J cliqueY m J .d01 .d00 := by
    rw [varianceEstimate_expectation, hm]
    unfold expectedVariance expectedTotalVariance expectedTotalCovariance
    simp_rw [hkk, hll, hkl]
  have hnum : M = 0 ∧ S - M^2 = 6050/11907 ∧ expectedVariance m J cliqueY m J .d01 .d00 = 6050/11907 :=
    cem_exact_reduced_arithmetic
  refine ⟨hmean.trans hnum.1, ?_, hv.trans hnum.2.2⟩
  unfold designVariance
  rw [hsecond, hmean]
  exact hnum.2.1


theorem clique_exact_profile_estimates_proof :
    let m := cliqueObservationMarginal 0 false
    ∀ r, htContrast cliqueF cliqueY m .d01 .d00 r =
      if (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 then -220/189 else 55/126 := by
  decide +kernel


theorem clique_exact_reduced_arithmetic_proof :
    let m := cliqueObservationMarginal 0 false
    let J := cliqueObservationJoint 0 false
    let M := ((∑ i, m i .d01 / m i .d01) - (∑ i, m i .d00 / m i .d00)) / 12
    let S := (∑ i, ∑ j,
      (J i j .d01 .d01 / (m i .d01 * m j .d01) +
       J i j .d00 .d00 / (m i .d00 * m j .d00) -
       J i j .d01 .d00 / (m i .d01 * m j .d00) -
       J i j .d00 .d01 / (m i .d00 * m j .d01))) / 144
    M = 0 ∧ S - M^2 = 6050/11907 ∧ expectedVariance m J cliqueY m J .d01 .d00 = 6050/11907 := by
  exact cem_exact_reduced_arithmetic

end
end AronowAudit.P044.Wave1
