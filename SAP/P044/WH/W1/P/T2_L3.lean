import SAP.P044.WH.W1.Leaves
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P044.WH.W1.P.T2_L3
open Finset
open scoped BigOperators
private theorem exposureCount_perm {R N : ℕ} (f : Fin R → Fin N → Exposure) (e : Equiv.Perm (Fin R)) (i : Fin N) (a : Exposure) : exposureCount (fun r => f (e r)) i a = exposureCount f i a := by
  simp only [exposureCount, Finset.card_filter]
  exact Finset.sum_equiv e (by simp) (by intro r hr; rfl)
private theorem jointCount_perm {R N : ℕ} (f : Fin R → Fin N → Exposure)
    (e : Equiv.Perm (Fin R)) (i j : Fin N) (a b : Exposure) :
    jointCount (fun r => f (e r)) i j a b = jointCount f i j a b := by
  simp only [jointCount, Finset.card_filter]
  exact Finset.sum_equiv e (by simp) (by intro r hr; rfl)
private theorem assignment_distinguished {n : ℕ} (s : Fin (w1MatchingR n))
    {i : Fin (w1MatchingN n)} (hi : i.val < 2) :
    w1MatchingAssignments n s i = w1MatchingAssignments n s ⟨0, by
      simp [w1MatchingN]
    ⟩ := by
  have hd : i.val / 2 = 0 := by omega
  unfold w1MatchingAssignments
  change decide (if i.val / 2 = 0 then _ else _) =
    decide (if (0 : ℕ) / 2 = 0 then _ else _)
  rw [hd]
  norm_num
private theorem dist_exposure_eq {n : ℕ} (hg : W1MatchingGeometry n)
    (s : Fin (w1MatchingR n)) {i j : Fin (w1MatchingN n)}
    (hi : i.val < 2) (hj : j.val < 2) :
    w1MatchingF n s i = w1MatchingF n s j := by
  rw [hg.2.2.2.1 s i, hg.2.2.2.1 s j,
    assignment_distinguished s hi, assignment_distinguished s hj]
private theorem exposure_d11_iff {n : ℕ} (hg : W1MatchingGeometry n)
    (s : Fin (w1MatchingR n)) (i : Fin (w1MatchingN n)) :
    w1MatchingF n s i = .d11 ↔ w1MatchingAssignments n s i = true := by
  rw [hg.2.2.2.1 s i]
  cases w1MatchingAssignments n s i <;> simp
private theorem exposure_d00_iff {n : ℕ} (hg : W1MatchingGeometry n)
    (s : Fin (w1MatchingR n)) (i : Fin (w1MatchingN n)) :
    w1MatchingF n s i = .d00 ↔ w1MatchingAssignments n s i = false := by
  rw [hg.2.2.2.1 s i]
  cases w1MatchingAssignments n s i <;> simp
private theorem count_distinguished {n : ℕ} (hm : W1MatchingMarginals n)
    {i : Fin (w1MatchingN n)} (hi : i.val < 2) (a : Exposure)
    (ha : a = .d11 ∨ a = .d00) :
    exposureCount (w1MatchingF n) i a = n + 2 := by
  have hp := (AronowAudit.P044.exhaustive_probabilities
    (K := ℚ) (by unfold w1MatchingR; omega)
    (w1MatchingF n) i i a a).1
  have hv : marginal w1Uniform (w1MatchingF n) i a = (1 / 2 : ℚ) := by
    rw [hm.1 i a]
    rcases ha with rfl | rfl <;> simp [hi]
  have hp0 : marginal (fun _ : Fin (w1MatchingR n) =>
      (1 / (w1MatchingR n : ℚ))) (w1MatchingF n) i a =
      (exposureCount (w1MatchingF n) i a : ℚ) / (w1MatchingR n : ℚ) := by
    simpa only [SAP.P044.Bridge.marginal_eq, SAP.P044.Bridge.exposureCount_eq] using hp
  have hmass : w1Uniform = (fun _ : Fin (w1MatchingR n) =>
      (1 / (w1MatchingR n : ℚ))) := by
    funext s
    simp [w1Uniform]
  have hp' : marginal w1Uniform (w1MatchingF n) i a =
      (exposureCount (w1MatchingF n) i a : ℚ) / (w1MatchingR n : ℚ) := by
    rw [hmass]
    exact hp0
  rw [hp'] at hv
  have hR : (w1MatchingR n : ℚ) = 2 * ((n : ℚ) + 2) := by
    simp [w1MatchingR]
  rw [hR] at hv
  have hc : (exposureCount (w1MatchingF n) i a : ℚ) = (n : ℚ) + 2 := by
    have hn : (0 : ℚ) < (n : ℚ) + 2 := by positivity
    field_simp at hv
    nlinarith
  exact_mod_cast hc
private def matchingRowEquiv (n : ℕ) :
    Fin 2 × Fin (n + 2) ≃ Fin (w1MatchingR n) := by
  unfold SAP.P044.w1MatchingR
  exact finProdFinEquiv
private theorem assignment_pair_distinguished {n : ℕ} (x : Fin 2)
    (t : Fin (n + 2)) {i : Fin (w1MatchingN n)} (hi : i.val < 2) :
    w1MatchingAssignments n (matchingRowEquiv n (x, t)) i = decide (x = 1) := by
  change w1MatchingAssignments n (finProdFinEquiv (x, t)) i = decide (x = 1)
  have hd : i.val / 2 = 0 := by omega
  unfold w1MatchingAssignments
  rw [Equiv.symm_apply_apply]
  simp only [hd, if_true, Prod.fst]
private theorem assignment_pair_ordinary {n : ℕ} (x : Fin 2)
    (t : Fin (n + 2)) {j : Fin (w1MatchingN n)} (hj : 2 ≤ j.val) :
    w1MatchingAssignments n (matchingRowEquiv n (x, t)) j =
      decide (j.val / 2 = t.val + 1) := by
  change w1MatchingAssignments n (finProdFinEquiv (x, t)) j =
    decide (j.val / 2 = t.val + 1)
  have hd : j.val / 2 ≠ 0 := by omega
  unfold w1MatchingAssignments
  rw [Equiv.symm_apply_apply]
  simp only [if_neg hd, Prod.snd]
private theorem ordinary_fiber_count {n : ℕ} (j : Fin (w1MatchingN n))
    (hj : 2 ≤ j.val) :
    (∑ t : Fin (n + 2), if j.val / 2 = t.val + 1 then (1 : ℕ) else 0) = 1 := by
  let k : Fin (n + 2) := ⟨j.val / 2 - 1, by
    have hjlt := j.isLt
    unfold w1MatchingN at hjlt
    omega
  ⟩
  have hfiber (t : Fin (n + 2)) :
      (j.val / 2 = t.val + 1) ↔ t = k := by
    constructor
    · intro h
      apply Fin.ext
      dsimp [k]
      omega
    · intro h
      have hv := congrArg Fin.val h
      dsimp [k] at hv
      omega
  simp_rw [hfiber]
  simp
private theorem ordinary_complement_count {n : ℕ} (j : Fin (w1MatchingN n))
    (hj : 2 ≤ j.val) :
    (∑ t : Fin (n + 2), if j.val / 2 ≠ t.val + 1 then (1 : ℕ) else 0) = n + 1 := by
  have hyes := ordinary_fiber_count j hj
  have hsplit :
      (∑ t : Fin (n + 2), if j.val / 2 = t.val + 1 then (1 : ℕ) else 0) +
      (∑ t : Fin (n + 2), if j.val / 2 ≠ t.val + 1 then (1 : ℕ) else 0) = n + 2 := by
    rw [← Finset.sum_add_distrib]
    have hp (t : Fin (n + 2)) :
        (if j.val / 2 = t.val + 1 then (1 : ℕ) else 0) +
        (if j.val / 2 ≠ t.val + 1 then (1 : ℕ) else 0) = 1 := by
      by_cases h : j.val / 2 = t.val + 1 <;> simp [h]
    simp_rw [hp]
    simp
  omega
private theorem ordinary_fiber_card {n : ℕ} (j : Fin (w1MatchingN n))
    (hj : 2 ≤ j.val) :
    (Finset.univ.filter (fun t : Fin (n + 2) => j.val / 2 = t.val + 1)).card = 1 := by
  calc
    _ = ∑ t : Fin (n + 2), if j.val / 2 = t.val + 1 then (1 : ℕ) else 0 := by
      simp only [Finset.card_filter]
    _ = 1 := ordinary_fiber_count j hj
private theorem ordinary_complement_card {n : ℕ} (j : Fin (w1MatchingN n))
    (hj : 2 ≤ j.val) :
    (Finset.univ.filter (fun t : Fin (n + 2) => j.val / 2 ≠ t.val + 1)).card = n + 1 := by
  calc
    _ = ∑ t : Fin (n + 2), if j.val / 2 ≠ t.val + 1 then (1 : ℕ) else 0 := by
      simp only [Finset.card_filter]
    _ = n + 1 := ordinary_complement_count j hj
private theorem mixed_assignment_count {n : ℕ}
    {i j : Fin (w1MatchingN n)} (hi : i.val < 2) (hj : 2 ≤ j.val)
    (u v : Bool) :
    (Finset.univ.filter (fun s : Fin (w1MatchingR n) =>
      w1MatchingAssignments n s i = u ∧ w1MatchingAssignments n s j = v)).card =
        if v then 1 else n + 1 := by
  let pred : Fin (w1MatchingR n) → Prop := fun s =>
    w1MatchingAssignments n s i = u ∧ w1MatchingAssignments n s j = v
  let coord : Fin 2 × Fin (n + 2) ≃ Fin (w1MatchingR n) := matchingRowEquiv n
  have hcard : (Finset.univ.filter pred).card =
      ∑ s : Fin (w1MatchingR n), if pred s then (1 : ℕ) else 0 := by
    simp only [Finset.card_filter]
  rw [hcard]
  have hsum :
      (∑ s : Fin (w1MatchingR n), if pred s then (1 : ℕ) else 0) =
      ∑ p : Fin 2 × Fin (n + 2), if pred (coord p) then (1 : ℕ) else 0 := by
    exact (Equiv.sum_comp coord (fun s => if pred s then (1 : ℕ) else 0)).symm
  rw [hsum]
  simp_rw [coord, pred]
  rw [Fintype.sum_prod_type]
  simp_rw [assignment_pair_distinguished (n := n) _ _ (i := i) hi,
    assignment_pair_ordinary (n := n) _ _ (j := j) hj]
  cases u <;> cases v <;>
    simp [Fin.sum_univ_two, ordinary_fiber_card, ordinary_complement_card, hj]
private theorem mixed_joint_count {n : ℕ} (hg : W1MatchingGeometry n)
    {i j : Fin (w1MatchingN n)} (hi : i.val < 2) (hj : 2 ≤ j.val)
    (a b : Exposure) (ha : a = .d11 ∨ a = .d00)
    (hb : b = .d11 ∨ b = .d00) :
    jointCount (w1MatchingF n) i j a b = if b = .d11 then 1 else n + 1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · subst a
    subst b
    simpa [jointCount, exposure_d11_iff hg] using
      (mixed_assignment_count hi hj true true)
  · subst a
    subst b
    simpa [jointCount, exposure_d11_iff hg, exposure_d00_iff hg] using
      (mixed_assignment_count hi hj true false)
  · subst a
    subst b
    simpa [jointCount, exposure_d00_iff hg, exposure_d11_iff hg] using
      (mixed_assignment_count hi hj false true)
  · subst a
    subst b
    simpa [jointCount, exposure_d00_iff hg] using
      (mixed_assignment_count hi hj false false)
private theorem jointCount_dist_same {n : ℕ} (hg : W1MatchingGeometry n)
    {i j : Fin (w1MatchingN n)} (hi : i.val < 2) (hj : j.val < 2)
    (a : Exposure) :
    jointCount (w1MatchingF n) i j a a = exposureCount (w1MatchingF n) i a := by
  unfold jointCount exposureCount
  congr 1
  ext s
  simp [dist_exposure_eq hg s hi hj]
private theorem jointCount_dist_diff {n : ℕ} (hg : W1MatchingGeometry n)
    {i j : Fin (w1MatchingN n)} (hi : i.val < 2) (hj : j.val < 2)
    {a b : Exposure} (hab : a ≠ b) :
    jointCount (w1MatchingF n) i j a b = 0 := by
  have hno (s : Fin (w1MatchingR n)) :
      ¬ (w1MatchingF n s i = a ∧ w1MatchingF n s j = b) := by
    rintro ⟨ha, hb⟩
    apply hab
    calc
      a = w1MatchingF n s i := ha.symm
      _ = w1MatchingF n s j := dist_exposure_eq hg s hi hj
      _ = b := hb
  unfold jointCount
  have hempty : (Finset.univ.filter
      (fun s : Fin (w1MatchingR n) =>
        w1MatchingF n s i = a ∧ w1MatchingF n s j = b)) = ∅ := by
    ext s
    simp [hno s]
  rw [hempty]
  simp
private theorem jointCount_distinguished {n : ℕ} (hg : W1MatchingGeometry n)
    (hm : W1MatchingMarginals n) {i j : Fin (w1MatchingN n)}
    (hi : i.val < 2) (hj : j.val < 2) (a b : Exposure)
    (ha : a = .d11 ∨ a = .d00) :
    jointCount (w1MatchingF n) i j a b = if a = b then n + 2 else 0 := by
  by_cases hab : a = b
  · subst b
    rw [jointCount_dist_same hg hi hj a]
    simp [count_distinguished hm hi a ha]
  · rw [jointCount_dist_diff hg hi hj hab]
    simp [hab]
private theorem jointCount_swap {R N : ℕ}
    (f : Fin R → Fin N → Exposure) (i j : Fin N) (a b : Exposure) :
    jointCount f i j a b = jointCount f j i b a := by
  unfold jointCount
  congr 1
  ext r
  simp [and_comm]
end SAP.P044.WH.W1.P.T2_L3
open SAP.P044.WH.W1.P.T2_L3
theorem SAP.P044.WH.W1.T2_L3_proof : SAP.P044.WH.W1.T2_L3 := by
  intro n hg hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e i a
    unfold w1MatchingW w1MatchingBankF smoothedWeight
    positivity
  · intro e i j a b
    unfold w1MatchingQ w1MatchingBankF smoothedJoint
    by_cases hab : a = b
    · simp only [if_pos hab]
      positivity
    · simp only [if_neg hab]
      positivity
  · intro e i a
    unfold w1MatchingQ w1MatchingW w1MatchingBankF smoothedJoint smoothedWeight
    simp [jointCount, exposureCount]
  · intro e i a hi ha
    have hc := count_distinguished hm hi a ha
    unfold w1MatchingW w1MatchingBankF smoothedWeight
    rw [exposureCount_perm, hc]
    unfold w1MatchingWeight w1MatchingR
    push_cast
    ring
  · intro e i j a b hi hj ha hb
    have hc := jointCount_distinguished hg hm hi hj a b ha
    unfold w1MatchingQ w1MatchingBankF smoothedJoint
    rw [jointCount_perm, hc]
    by_cases hab : a = b
    · by_cases hij : i = j
      · simp [hab, hij, w1MatchingWeight, w1MatchingR]
        push_cast
        ring
      · simp [hab, hij, w1MatchingJoint, w1MatchingR]
        push_cast
        ring
    · simp [hab]
  · intro e i j a b hmix ha hb
    have hbase : 0 < jointCount (w1MatchingF n) i j a b := by
      rcases hmix with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rw [mixed_joint_count hg hi hj a b ha hb]
        rcases hb with rfl | rfl <;> simp <;> omega
      · rw [jointCount_swap]
        rw [mixed_joint_count hg hj hi b a hb ha]
        rcases ha with rfl | rfl <;> simp <;> omega
    have hcount : 0 < jointCount (w1MatchingBankF n e) i j a b := by
      unfold w1MatchingBankF
      rw [jointCount_perm]
      exact hbase
    have hnumNat := hcount
    change 0 < jointCount (fun s => w1MatchingF n (e s)) i j a b at hnumNat
    have hnum : (0 : ℚ) <
        (jointCount (fun s => w1MatchingF n (e s)) i j a b : ℚ) := by
      exact_mod_cast hnumNat
    unfold w1MatchingQ smoothedJoint
    by_cases hab : a = b
    · simp only [if_pos hab]
      positivity
    · simp only [if_neg hab]
      have hR : (0 : ℚ) < (w1MatchingR n : ℚ) := by
        unfold SAP.P044.w1MatchingR
        positivity
      exact div_pos hnum hR
