import AronowAudit.P044.P044_NetworkSpillovers
import AronowAudit.P045.P045_ExposureVariance

namespace AronowAudit.P044.Wave1

open Finset
open scoped BigOperators

noncomputable section

-- The assignment enumeration is definitionally the same in P045.
private theorem clique_retained_injective_assignment : Function.Injective cliqueAssignments := by
  exact AronowAudit.P045.ExposureVariance.clique_assignment_injective

theorem clique_retained_injective_proof (t : Fin 66) :
    Function.Injective (retainedAssignments t) ∧
      ∀ r, retainedAssignments t r ≠ cliqueAssignments t := by
  constructor
  · exact clique_retained_injective_assignment.comp Fin.succAbove_right_injective
  · intro r he
    exact Fin.succAbove_ne t r (clique_retained_injective_assignment he)

-- Transport the full counts across the exposure labels.
private def clique_retained_weights_to45 : Exposure → AronowAudit.P045.ExposureVariance.Exposure
  | .d11 => .d11 | .d10 => .d10 | .d01 => .d01 | .d00 => .d00

private theorem clique_retained_weights_to45_injective :
    Function.Injective clique_retained_weights_to45 := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

private theorem clique_retained_weights_mapF (r : Fin 66) (i : Fin 12) :
    clique_retained_weights_to45 (cliqueF r i) = AronowAudit.P045.ExposureVariance.cliqueF r i := by
  unfold cliqueF AronowAudit.P045.ExposureVariance.cliqueF
  change clique_retained_weights_to45
    (if i = (cliquePairs r).1 ∨ i = (cliquePairs r).2 then
      (if (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 then .d11 else .d10)
    else (if i.val / 4 = (cliquePairs r).1.val / 4 ∨
      i.val / 4 = (cliquePairs r).2.val / 4 then .d01 else .d00)) =
    (if i = (cliquePairs r).1 ∨ i = (cliquePairs r).2 then
      (if (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 then
        AronowAudit.P045.ExposureVariance.Exposure.d11 else .d10)
    else (if i.val / 4 = (cliquePairs r).1.val / 4 ∨
      i.val / 4 = (cliquePairs r).2.val / 4 then .d01 else .d00))
  split_ifs <;> rfl

private theorem clique_retained_weights_event (r : Fin 66) (i : Fin 12) (a : Exposure) :
    AronowAudit.P045.ExposureVariance.cliqueF r i = clique_retained_weights_to45 a ↔ cliqueF r i = a := by
  rw [← clique_retained_weights_mapF]
  exact clique_retained_weights_to45_injective.eq_iff

private theorem clique_retained_weights_count (i : Fin 12) (a : Exposure) :
    AronowAudit.P045.ExposureVariance.exposureCount AronowAudit.P045.ExposureVariance.cliqueF i (clique_retained_weights_to45 a) =
      exposureCount cliqueF i a := by
  simp only [AronowAudit.P045.ExposureVariance.exposureCount, exposureCount, clique_retained_weights_event]

private theorem clique_retained_weights_jointCount (i j : Fin 12) (a b : Exposure) :
    AronowAudit.P045.ExposureVariance.jointCount AronowAudit.P045.ExposureVariance.cliqueF i j
      (clique_retained_weights_to45 a) (clique_retained_weights_to45 b) =
      jointCount cliqueF i j a b := by
  simp only [AronowAudit.P045.ExposureVariance.jointCount, jointCount, clique_retained_weights_event]

private theorem clique_retained_weights_fullCount (a : Exposure) :
    AronowAudit.P045.ExposureVariance.cliqueFullCount (clique_retained_weights_to45 a) = cliqueFullCount a := by
  cases a <;> rfl

private theorem clique_retained_weights_fullJoint (i j : Fin 12) (a b : Exposure) :
    AronowAudit.P045.ExposureVariance.cliqueFullJoint i j (clique_retained_weights_to45 a)
      (clique_retained_weights_to45 b) = cliqueFullJoint i j a b := by
  cases a <;> cases b
  · exact congrArg (fun c : ℕ => if i = j then 3 else c)
      (clique_retained_weights_jointCount i j .d11 .d11)
  · exact congrArg (fun c : ℕ => if i = j then 0 else c)
      (clique_retained_weights_jointCount i j .d11 .d10)
  · exact congrArg (fun c : ℕ => if i = j then 0 else c)
      (clique_retained_weights_jointCount i j .d11 .d01)
  · exact congrArg (fun c : ℕ => if i = j then 0 else c)
      (clique_retained_weights_jointCount i j .d11 .d00)
  · exact congrArg (fun c : ℕ => if i = j then 0 else c)
      (clique_retained_weights_jointCount i j .d10 .d11)
  · exact congrArg (fun c : ℕ => if i = j then 8 else c)
      (clique_retained_weights_jointCount i j .d10 .d10)
  · exact congrArg (fun c : ℕ => if i = j then 0 else c)
      (clique_retained_weights_jointCount i j .d10 .d01)
  · exact congrArg (fun c : ℕ => if i = j then 0 else c)
      (clique_retained_weights_jointCount i j .d10 .d00)
  · exact congrArg (fun c : ℕ => if i = j then 0 else c)
      (clique_retained_weights_jointCount i j .d01 .d11)
  · exact congrArg (fun c : ℕ => if i = j then 0 else c)
      (clique_retained_weights_jointCount i j .d01 .d10)
  · rfl
  · rfl
  · exact congrArg (fun c : ℕ => if i = j then 0 else c)
      (clique_retained_weights_jointCount i j .d00 .d11)
  · exact congrArg (fun c : ℕ => if i = j then 0 else c)
      (clique_retained_weights_jointCount i j .d00 .d10)
  · rfl
  · rfl

private theorem clique_retained_weights_full_counts :
    (∀ i a, exposureCount cliqueF i a = cliqueFullCount a) ∧
    (∀ i j a b, (a = Exposure.d01 ∨ a = .d00) → (b = Exposure.d01 ∨ b = .d00) →
      jointCount cliqueF i j a b = cliqueFullJoint i j a b) := by
  constructor
  · intro i a
    rw [← clique_retained_weights_count, ← clique_retained_weights_fullCount]
    exact AronowAudit.P045.ExposureVariance.clique_full_counts.1 i (clique_retained_weights_to45 a)
  · intro i j a b ha hb
    rw [← clique_retained_weights_jointCount, ← clique_retained_weights_fullJoint]
    apply AronowAudit.P045.ExposureVariance.clique_full_counts.2
    · rcases ha with rfl | rfl <;> simp [clique_retained_weights_to45]
    · rcases hb with rfl | rfl <;> simp [clique_retained_weights_to45]

theorem clique_retained_weights_proof :
    (∀ t i a, cliqueWeights t i a = (smoothedWeight (retainedF t) i a : ℚ)) ∧
    (∀ t i j a b, (a = Exposure.d01 ∨ a = .d00) → (b = Exposure.d01 ∨ b = .d00) →
      cliqueJoints t i j a b = (smoothedJoint (retainedF t) i j a b : ℚ)) := by
  have hc (t : Fin 66) (i : Fin 12) (a : Exposure) :
      exposureCount (retainedF t) i a = cliqueFullCount a - if cliqueF t i = a then 1 else 0 := by
    change (Finset.univ.filter (fun r : Fin 65 => cliqueF (t.succAbove r) i = a)).card = _
    rw [count_delete_atom t (fun r : Fin 66 => cliqueF r i = a)]
    rw [← clique_retained_weights_full_counts.1 i a]
    rfl
  have hj (t : Fin 66) (i j : Fin 12) (a b : Exposure)
      (ha : a = .d01 ∨ a = .d00) (hb : b = .d01 ∨ b = .d00) :
      jointCount (retainedF t) i j a b = cliqueFullJoint i j a b -
        if cliqueF t i = a ∧ cliqueF t j = b then 1 else 0 := by
    change (Finset.univ.filter (fun r : Fin 65 =>
      cliqueF (t.succAbove r) i = a ∧ cliqueF (t.succAbove r) j = b)).card = _
    rw [count_delete_atom t (fun r : Fin 66 => cliqueF r i = a ∧ cliqueF r j = b)]
    rw [← clique_retained_weights_full_counts.2 i j a b ha hb]
    rfl
  constructor
  · intro t i a
    unfold cliqueWeights smoothedWeight
    rw [hc]
    push_cast
    norm_num
  · intro t i j a b ha hb
    unfold cliqueJoints smoothedJoint
    rw [hj t i j a b ha hb]
    by_cases he : a = b <;> by_cases hij : i = j <;> simp [he, hij, Nat.cast_add] <;> norm_num


-- Transport the graph and profile identities.
theorem clique_structure_proof :
    Function.Injective cliqueAssignments ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueAssignments r i)).card = 2) ∧
    (∀ i j, cliqueAdj i j = cliqueAdj j i) ∧
    (∀ i, cliqueAdj i i = false ∧ ∃ j, cliqueAdj i j = true) ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueF r i = .d01)).card =
        if (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 then 2 else 6) ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueF r i = .d00)).card =
        if (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4 then 8 else 4) ∧
    (Finset.univ.filter (fun r => (cliquePairs r).1.val / 4 = (cliquePairs r).2.val / 4)).card = 18 ∧
    (Finset.univ.filter (fun r => (cliquePairs r).1.val / 4 ≠ (cliquePairs r).2.val / 4)).card = 48 := by
  have h := AronowAudit.P045.ExposureVariance.clique_structure
  have hp : AronowAudit.P045.ExposureVariance.cliquePairs = cliquePairs := rfl
  have hk (r : Fin 66) (i : Fin 12) :
      AronowAudit.P045.ExposureVariance.cliqueF r i = .d01 ↔ cliqueF r i = .d01 :=
    clique_retained_weights_event r i .d01
  have hl (r : Fin 66) (i : Fin 12) :
      AronowAudit.P045.ExposureVariance.cliqueF r i = .d00 ↔ cliqueF r i = .d00 :=
    clique_retained_weights_event r i .d00
  refine ⟨clique_retained_injective_assignment, h.2.1, h.2.2.1, h.2.2.2.1,
    ?_, ?_, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
  · intro r
    simpa only [hk, hp] using h.2.2.2.2.1 r
  · intro r
    simpa only [hl, hp] using h.2.2.2.2.2.1 r

-- Scalar transport preserves every event, coefficient and estimator.
private theorem clique_variance_counterexample_weights (t : Fin 66) (i : Fin 12)
    (a : Exposure) :
    AronowAudit.P045.ExposureVariance.cliqueWeights t i (clique_retained_weights_to45 a) = cliqueWeights t i a := by
  simp only [AronowAudit.P045.ExposureVariance.cliqueWeights, cliqueWeights, clique_retained_weights_fullCount,
    clique_retained_weights_event]

private theorem clique_variance_counterexample_joints (t : Fin 66) (i j : Fin 12)
    (a b : Exposure) :
    AronowAudit.P045.ExposureVariance.cliqueJoints t i j (clique_retained_weights_to45 a)
      (clique_retained_weights_to45 b) = cliqueJoints t i j a b := by
  simp only [AronowAudit.P045.ExposureVariance.cliqueJoints, cliqueJoints, clique_retained_weights_fullJoint,
    clique_retained_weights_event, clique_retained_weights_to45_injective.eq_iff]

private theorem clique_variance_counterexample_marginal (p : Fin 66 → ℚ)
    (i : Fin 12) (a : Exposure) :
    AronowAudit.P045.ExposureVariance.marginal p AronowAudit.P045.ExposureVariance.cliqueF i (clique_retained_weights_to45 a) =
      marginal p cliqueF i a := by
  simp only [AronowAudit.P045.ExposureVariance.marginal, marginal, clique_retained_weights_event]

private theorem clique_variance_counterexample_joint (p : Fin 66 → ℚ)
    (i j : Fin 12) (a b : Exposure) :
    AronowAudit.P045.ExposureVariance.joint p AronowAudit.P045.ExposureVariance.cliqueF i j (clique_retained_weights_to45 a)
      (clique_retained_weights_to45 b) = joint p cliqueF i j a b := by
  simp only [AronowAudit.P045.ExposureVariance.joint, joint, clique_retained_weights_event]

private theorem clique_variance_counterexample_contrast
    (w : Fin 12 → Exposure → ℚ) (W : Fin 12 → AronowAudit.P045.ExposureVariance.Exposure → ℚ)
    (hw : ∀ i a, W i (clique_retained_weights_to45 a) = w i a)
    (a b : Exposure) (z : Fin 66) :
    AronowAudit.P045.ExposureVariance.htContrast AronowAudit.P045.ExposureVariance.cliqueF AronowAudit.P045.ExposureVariance.cliqueY W
      (clique_retained_weights_to45 a) (clique_retained_weights_to45 b) z =
      htContrast cliqueF cliqueY w a b z := by
  simp only [AronowAudit.P045.ExposureVariance.htContrast, htContrast, AronowAudit.P045.ExposureVariance.htMean, htMean, AronowAudit.P045.ExposureVariance.htTerm, htTerm,
    AronowAudit.P045.ExposureVariance.cliqueY, cliqueY, clique_retained_weights_event, hw]

private theorem clique_variance_counterexample_variance
    (w : Fin 12 → Exposure → ℚ) (W : Fin 12 → AronowAudit.P045.ExposureVariance.Exposure → ℚ)
    (q : Fin 12 → Fin 12 → Exposure → Exposure → ℚ)
    (Q : Fin 12 → Fin 12 → AronowAudit.P045.ExposureVariance.Exposure → AronowAudit.P045.ExposureVariance.Exposure → ℚ)
    (hw : ∀ i a, W i (clique_retained_weights_to45 a) = w i a)
    (hq : ∀ i j a b, Q i j (clique_retained_weights_to45 a)
      (clique_retained_weights_to45 b) = q i j a b)
    (a b : Exposure) (z : Fin 66) :
    AronowAudit.P045.ExposureVariance.varianceEstimate AronowAudit.P045.ExposureVariance.cliqueF AronowAudit.P045.ExposureVariance.cliqueY W Q
      (clique_retained_weights_to45 a) (clique_retained_weights_to45 b) z =
      varianceEstimate cliqueF cliqueY w q a b z := by
  simp only [AronowAudit.P045.ExposureVariance.varianceEstimate, varianceEstimate,
    AronowAudit.P045.ExposureVariance.totalVarianceEstimate, totalVarianceEstimate,
    AronowAudit.P045.ExposureVariance.totalCovarianceEstimate, totalCovarianceEstimate,
    AronowAudit.P045.ExposureVariance.cliqueY, cliqueY, clique_retained_weights_event, hw, hq]

private theorem clique_variance_counterexample_T (t z : Fin 66) :
    AronowAudit.P045.ExposureVariance.cliqueT t z = cliqueT t z := by
  exact clique_variance_counterexample_contrast _ _
    (clique_variance_counterexample_weights t) .d01 .d00 z

private theorem clique_variance_counterexample_V (t z : Fin 66) :
    AronowAudit.P045.ExposureVariance.cliqueV t z = cliqueV t z := by
  exact clique_variance_counterexample_variance _ _ _ _
    (clique_variance_counterexample_weights t) (clique_variance_counterexample_joints t)
    .d01 .d00 z

private theorem clique_variance_counterexample_exactT (z : Fin 66) :
    AronowAudit.P045.ExposureVariance.htContrast AronowAudit.P045.ExposureVariance.cliqueF AronowAudit.P045.ExposureVariance.cliqueY
      (AronowAudit.P045.ExposureVariance.marginal (fun _ : Fin 66 => (1/66 : ℚ)) AronowAudit.P045.ExposureVariance.cliqueF) .d01 .d00 z =
    htContrast cliqueF cliqueY
      (marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF) .d01 .d00 z := by
  exact clique_variance_counterexample_contrast _ _
    (clique_variance_counterexample_marginal _) .d01 .d00 z

private theorem clique_variance_counterexample_exactV (z : Fin 66) :
    AronowAudit.P045.ExposureVariance.varianceEstimate AronowAudit.P045.ExposureVariance.cliqueF AronowAudit.P045.ExposureVariance.cliqueY
      (AronowAudit.P045.ExposureVariance.marginal (fun _ : Fin 66 => (1/66 : ℚ)) AronowAudit.P045.ExposureVariance.cliqueF)
      (AronowAudit.P045.ExposureVariance.joint (fun _ : Fin 66 => (1/66 : ℚ)) AronowAudit.P045.ExposureVariance.cliqueF) .d01 .d00 z =
    varianceEstimate cliqueF cliqueY
      (marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF)
      (joint (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF) .d01 .d00 z := by
  exact clique_variance_counterexample_variance _ _ _ _
    (clique_variance_counterexample_marginal _) (clique_variance_counterexample_joint _)
    .d01 .d00 z
private theorem clique_variance_counterexample_expect {Ω : Type*} [Fintype Ω]
    (p u : Ω → ℚ) :
    AronowAudit.P045.ExposureVariance.expect p u = expect p u := by
  rfl

private theorem clique_variance_counterexample_designVariance {Ω : Type*} [Fintype Ω]
    (p u : Ω → ℚ) :
    AronowAudit.P045.ExposureVariance.designVariance p u = designVariance p u := by
  rfl

private theorem clique_variance_counterexample_T_function :
    AronowAudit.P045.ExposureVariance.cliqueT = cliqueT := by
  funext t z
  exact clique_variance_counterexample_T t z

private theorem clique_variance_counterexample_V_function :
    AronowAudit.P045.ExposureVariance.cliqueV = cliqueV := by
  funext t z
  exact clique_variance_counterexample_V t z

private theorem clique_variance_counterexample_mass :
    AronowAudit.P045.ExposureVariance.cliqueJointMass = cliqueJointMass := by
  rfl

/-- T1(iii)–(v): exact rational computation on all 4356 independent or 4290
included (omitted,realized) pairs. Inputs are the omission formulas, whose
bridge to the enumerated assignment bank is `clique_retained_weights_proof`. -/
private theorem clique_variance_counterexample_joint_moments : (expect (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = -67/53592 ∧
    designVariance (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = 113448938731/232640299584 ∧
    expect (cliqueJointMass false) (fun x => cliqueV x.1 x.2) = 1040129476423/2326402995840 ∧
    expect (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = -67/52780 ∧
    designVariance (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = 11375808887/23342482800 ∧
    expect (cliqueJointMass true) (fun x => cliqueV x.1 x.2) = 4673362763/10414338480 ∧
    (∀ included,
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) <
        designVariance (cliqueJointMass included) (fun x => cliqueT x.1 x.2) ∧
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) < 6050/11907)) := by
  simpa only [clique_variance_counterexample_expect,
    clique_variance_counterexample_designVariance, clique_variance_counterexample_mass,
    clique_variance_counterexample_T_function, clique_variance_counterexample_V_function]
    using AronowAudit.P045.ExposureVariance.clique_joint_moments


/-- T1(vi): the two representative fixed banks, omitting (0,1) or (0,4),
have precisely the stated variances and expected variance estimates, and
both strictly underestimate the design variance. These are exact finite
counterexamples conditional on a table, using the same `varianceEstimate` functional. -/
private theorem clique_variance_counterexample_fixed_moments : (designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 0) = 2810528137/5767941312 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 0) = 267260522663/634473544320 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 0) <
      designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 0) ∧
    designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 3) = 937589375/1922647104 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 3) = 4830430961/10574559072 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 3) <
      designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 3)) := by
  simpa only [clique_variance_counterexample_expect,
    clique_variance_counterexample_designVariance,
    clique_variance_counterexample_T_function, clique_variance_counterexample_V_function]
    using AronowAudit.P045.ExposureVariance.clique_fixed_table_counterexamples


/-- T1(ii): the exact design probabilities give zero HT mean, design
variance 6050/11907, and expected variance estimate equal to that variance.
This bridges the kernel arithmetic to actual finite randomization moments. -/
private theorem clique_variance_counterexample_exact_moments : (let p := fun _ : Fin 66 => (1/66 : ℚ)
    let m := marginal p cliqueF
    let J := joint p cliqueF
    let T := htContrast cliqueF cliqueY m .d01 .d00
    expect p T = 0 ∧ designVariance p T = 6050/11907 ∧
      expect p (varianceEstimate cliqueF cliqueY m J .d01 .d00) = 6050/11907) := by
  simpa only [AronowAudit.P045.ExposureVariance.designVariance, designVariance, AronowAudit.P045.ExposureVariance.expect, expect,
    clique_variance_counterexample_exactT, clique_variance_counterexample_exactV]
    using AronowAudit.P045.ExposureVariance.clique_exact_moments

private theorem clique_variance_counterexample_marginals (i : Fin 12) :
    marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i .d01 = 9/22 ∧
    marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i .d00 = 14/33 := by
  have hk := AronowAudit.P045.ExposureVariance.clique_observation_marginal 0 false i .d01
  have hl := AronowAudit.P045.ExposureVariance.clique_observation_marginal 0 false i .d00
  rw [AronowAudit.P045.ExposureVariance.clique_observation_independent_mass] at hk hl
  norm_num [AronowAudit.P045.ExposureVariance.cliqueObservationMarginal, AronowAudit.P045.ExposureVariance.cliqueFullCount] at hk hl
  exact ⟨(clique_variance_counterexample_marginal _ i .d01).symm.trans hk,
    (clique_variance_counterexample_marginal _ i .d00).symm.trans hl⟩

private theorem clique_variance_counterexample_positive_weights (t : Fin 66) (i : Fin 12) :
    0 < (smoothedWeight (retainedF t) i .d01 : ℚ) ∧ 0 < (smoothedWeight (retainedF t) i .d00 : ℚ) := by
  rw [← clique_retained_weights_proof.1 t i .d01, ← clique_retained_weights_proof.1 t i .d00]
  unfold cliqueWeights cliqueFullCount
  split_ifs <;> norm_num

theorem clique_variance_counterexample_proof :
    cliqueF = (fun r => exposure cliqueAdj (cliqueAssignments r)) ∧
    (∀ z : Assignment 12, (Finset.univ.filter (fun i => z i)).card = 2 ↔ ∃ r, cliqueAssignments r = z) ∧
    (∀ i j, cliqueAdj i j = cliqueAdj j i) ∧
    Function.Injective cliqueAssignments ∧
    (∀ r, (Finset.univ.filter (fun i => cliqueAssignments r i)).card = 2) ∧
    (∀ i, cliqueAdj i i = false ∧ ∃ j, cliqueAdj i j = true) ∧
    (∀ i, marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i .d01 = 9/22 ∧
      marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF i .d00 = 14/33) ∧
    (∀ t, Function.Injective (retainedAssignments t) ∧
      (∀ r, retainedAssignments t r ≠ cliqueAssignments t)) ∧
    (∀ t i, 0 < (smoothedWeight (retainedF t) i .d01 : ℚ) ∧
      0 < (smoothedWeight (retainedF t) i .d00 : ℚ)) ∧
    tau cliqueY .d01 .d00 = 0 ∧
    (let w := marginal (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF
     let q := joint (fun _ : Fin 66 => (1/66 : ℚ)) cliqueF
     let T := htContrast cliqueF cliqueY w .d01 .d00
     expect (fun _ : Fin 66 => (1/66 : ℚ)) T = 0 ∧
     designVariance (fun _ : Fin 66 => (1/66 : ℚ)) T = 6050/11907 ∧
     expect (fun _ : Fin 66 => (1/66 : ℚ))
       (varianceEstimate cliqueF cliqueY w q .d01 .d00) = 6050/11907) ∧
    expect (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = -67/53592 ∧
    designVariance (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = 113448938731/232640299584 ∧
    expect (cliqueJointMass false) (fun x => cliqueV x.1 x.2) = 1040129476423/2326402995840 ∧
    expect (cliqueJointMass false) (fun x => cliqueV x.1 x.2) -
      designVariance (cliqueJointMass false) (fun x => cliqueT x.1 x.2) = -953130413/23499020160 ∧
    expect (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = -67/52780 ∧
    designVariance (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = 11375808887/23342482800 ∧
    expect (cliqueJointMass true) (fun x => cliqueV x.1 x.2) = 4673362763/10414338480 ∧
    expect (cliqueJointMass true) (fun x => cliqueV x.1 x.2) -
      designVariance (cliqueJointMass true) (fun x => cliqueT x.1 x.2) = -20161943/522324075 ∧
    (∀ included,
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) <
        designVariance (cliqueJointMass included) (fun x => cliqueT x.1 x.2) ∧
      expect (cliqueJointMass included) (fun x => cliqueV x.1 x.2) < 6050/11907) ∧
    designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 0) = 2810528137/5767941312 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 0) = 267260522663/634473544320 ∧
    designVariance (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueT 3) = 937589375/1922647104 ∧
    expect (fun _ : Fin 66 => (1/66 : ℚ)) (cliqueV 3) = 4830430961/10574559072 := by
  have hs := clique_structure_proof
  have hj := clique_variance_counterexample_joint_moments
  have hf := clique_variance_counterexample_fixed_moments
  have hexact := clique_variance_counterexample_exact_moments
  have hprob := clique_variance_counterexample_marginals
  have hpos := clique_variance_counterexample_positive_weights
  refine ⟨cliqueF_is_exposure, AronowAudit.P045.ExposureVariance.clique_complete_support, hs.2.2.1, hs.1, hs.2.1, hs.2.2.2.1, hprob, clique_retained_injective_proof, hpos, ?_,
    hexact, hj.1, hj.2.1, hj.2.2.1, ?_,
    hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1, ?_, hj.2.2.2.2.2.2,
    hf.1, hf.2.1, hf.2.2.2.1, hf.2.2.2.2.1⟩
  · simp [tau, cliqueY]
  · rw [hj.2.2.1, hj.2.1]
    norm_num
  · rw [hj.2.2.2.2.2.1, hj.2.2.2.2.1]
    norm_num


end
end AronowAudit.P044.Wave1
