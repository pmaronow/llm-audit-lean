import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectGeometry
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectLimits

/-! Finite pinned moment identities with the resampling law eliminated.

All donor counts refer to the same original configuration.  In particular the
two-replica expression squares a conditional mean in that shared configuration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectMoments (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

def markedSuccessorEmbedding (n : ℕ) : Fin n ↪ Fin (n+1) :=
  ⟨Fin.succ,Fin.succ_injective n⟩

/-- The strictly closer donor labels, in the actual resampling population. -/
def markedForbiddenLabels {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit) (x : ℝ) :
    Finset (Fin (n+1)) :=
  (Finset.univ.filter (fun i => z i ∈ markedCloserDonors p x)).map
    (markedSuccessorEmbedding n)

theorem marked_forbidden_count {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit) (x : ℝ) :
    (markedForbiddenLabels p z x).card = markedWindowCount (markedCloserDonors p x) z := by
  simp only [markedForbiddenLabels,Finset.card_map,markedWindowCount]

theorem marked_forbidden_central {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit) (x : ℝ) :
    (0 : Fin (n+1)) ∉ markedForbiddenLabels p z x := by
  simp [markedForbiddenLabels,markedSuccessorEmbedding]

theorem marked_forbidden_recipient {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit)
    (x : ℝ) (i : Fin n) (hi : (z i).2.1 = false) :
    i.succ ∉ markedForbiddenLabels p z x := by
  intro h
  obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp h
  have hji' : j = i := Fin.succ_injective n hji
  subst j
  have hr := (Finset.mem_filter.mp hj).2.1
  simp only [hi,Bool.false_eq_true] at hr

theorem marked_forbidden_count_le {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit) (x : ℝ) :
    (markedForbiddenLabels p z x).card ≤ n := by
  rw [marked_forbidden_count]
  exact marked_window_count_le _ _ _

theorem marked_forbidden_union_count_le {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit)
    (x y : ℝ) :
    (markedForbiddenLabels p z x ∪ markedForbiddenLabels p z y).card ≤ n := by
  have hsub : markedForbiddenLabels p z x ∪ markedForbiddenLabels p z y ⊆
      Finset.univ.map (markedSuccessorEmbedding n) := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    all_goals
      obtain ⟨j,_,hji⟩ := Finset.mem_map.mp h
      exact Finset.mem_map.mpr ⟨j,Finset.mem_univ _,hji⟩
  simpa only [Finset.card_map,Finset.card_univ,Fintype.card_fin] using
    Finset.card_le_card hsub

theorem marked_forbidden_avoidance {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit)
    (x : ℝ) (a : Fin (n+1) → Fin (n+1)) :
    markedNoRetained (markedCloserDonors p x) z a ↔
      markedAvoids (markedForbiddenLabels p z x) a := by
  constructor
  · intro h t ht
    obtain ⟨i,hi,hit⟩ := Finset.mem_map.mp ht
    exact h i (Finset.mem_filter.mp hi).2 t hit.symm
  · intro h i hi t ht
    apply h t
    exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,ht.symm⟩

theorem marked_avoids_union {N : ℕ} (D E : Finset (Fin N)) (a : Fin N → Fin N) :
    markedAvoids (D ∪ E) a ↔ markedAvoids D a ∧ markedAvoids E a := by
  simp only [markedAvoids,Finset.mem_union,not_or]
  aesop

/-- A recipient term including the separate central-retention gate. -/
def markedRetainedRecipient {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit)
    (a : Fin (n+1) → Fin (n+1)) (i : Fin n) : ℝ :=
  if 0 < reuseOccupancy a 0 then markedRecipientTerm p z a i else 0

theorem marked_pinned_U_sum (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (a : Fin (n+1) → Fin (n+1))
    (hp : ∀ i l v : Fin (n+1), l ≠ v →
      |(pin n p z l).1-(pin n p z i).1| ≠
        |(pin n p z v).1-(pin n p z i).1|) :
    U (pin n p z) a 0 = reuseOccupancy a 0 + ∑ i, markedRetainedRecipient p z a i := by
  rw [marked_pinned_U_direct n p z a hp]
  by_cases hc : 0 < reuseOccupancy a 0 <;> simp [markedRetainedRecipient,hc]

/-- Exact conditional recipient expectation, retaining the central mark. -/
theorem marked_retained_recipient_mean (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (i : Fin n) :
    mean (UniformResampling (n+1)) (fun a => markedRetainedRecipient p z a i) =
      if (z i).2.1 = false then markedRetainedDrawPower (n+1)
        ((markedForbiddenLabels p z (z i).1).card) 1 else 0 := by
  by_cases hi : (z i).2.1 = false
  · rw [if_pos hi]
    let D := markedForbiddenLabels p z (z i).1
    have hd : D.card ≤ n := marked_forbidden_count_le p z _
    have heq (a : Fin (n+1) → Fin (n+1)) :
        markedRetainedRecipient p z a i =
          if markedAvoids D a ∧ 0 < reuseOccupancy a 0 then reuseOccupancy a i.succ else 0 := by
      simp only [markedRetainedRecipient,markedRecipientTerm,hi,true_and,
        marked_forbidden_avoidance]
      by_cases hc : 0 < reuseOccupancy a 0 <;>
        by_cases ha : markedAvoids D a <;> simp [D,hc,ha]
    simp only [heq]
    rw [marked_central_recipient_avoidance (Nat.succ_pos n) D 0 i.succ
      (marked_forbidden_central p z _) (marked_forbidden_recipient p z _ i hi)
      (Fin.succ_ne_zero i)]
    simp only [markedRetainedDrawPower,
      marked_draw_power_of_le (Nat.succ_pos n) (by omega : D.card ≤ n+1),
      marked_draw_power_of_le (Nat.succ_pos n) (by omega : D.card+1 ≤ n+1),
      Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,D]
  · simp [markedRetainedRecipient,markedRecipientTerm,hi,mean]

theorem marked_central_occupancy_mean (n : ℕ) :
    mean (UniformResampling (n+1)) (fun a => reuseOccupancy a 0) = 1 := by
  simpa only [markedAvoids,Finset.notMem_empty,implies_true,not_false_eq_true,forall_true_iff,ite_true,
    Finset.card_empty,Nat.cast_zero,zero_div,sub_zero,one_pow] using
    marked_occupancy_avoidance (Nat.succ_pos n) ∅ (0 : Fin (n+1)) (by simp)

/-- Eliminate the complete resampling average from the pinned first moment. -/
theorem marked_pinned_U_mean_direct (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (hp : ∀ i l v : Fin (n+1), l ≠ v →
      |(pin n p z l).1-(pin n p z i).1| ≠
        |(pin n p z v).1-(pin n p z i).1|) :
    mean (UniformResampling (n+1)) (fun a => U (pin n p z) a 0) =
      1 + ∑ i, if (z i).2.1 = false then markedRetainedDrawPower (n+1)
        ((markedForbiddenLabels p z (z i).1).card) 1 else 0 := by
  simp only [marked_pinned_U_sum n p z _ hp,mean]
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  change mean (UniformResampling (n+1)) (fun a => reuseOccupancy a 0) +
    (∑ i, mean (UniformResampling (n+1)) (fun a => markedRetainedRecipient p z a i)) = _
  rw [marked_central_occupancy_mean]
  simp only [marked_retained_recipient_mean]

/-- Exact two-replica moment given the shared original configuration. -/
theorem marked_pinned_U_cross_direct (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (hp : ∀ i l v : Fin (n+1), l ≠ v →
      |(pin n p z l).1-(pin n p z i).1| ≠
        |(pin n p z v).1-(pin n p z i).1|) :
    mean (UniformResampling (n+1)) (fun a =>
      mean (UniformResampling (n+1)) (fun b => U (pin n p z) a 0 * U (pin n p z) b 0)) =
      (1 + ∑ i, if (z i).2.1 = false then markedRetainedDrawPower (n+1)
        ((markedForbiddenLabels p z (z i).1).card) 1 else 0)^2 := by
  have he : mean (UniformResampling (n+1)) (fun a =>
      mean (UniformResampling (n+1)) (fun b => U (pin n p z) a 0 * U (pin n p z) b 0)) =
      (mean (UniformResampling (n+1)) (fun a => U (pin n p z) a 0))^2 := by
    simp only [mean,integral_const_mul,integral_mul_const,pow_two]
  rw [he,marked_pinned_U_mean_direct n p z hp]

/-- The central second moment is exact for every positive sample size. -/
theorem marked_central_occupancy_square_mean (n : ℕ) :
    mean (UniformResampling (n+1)) (fun a => (reuseOccupancy a 0)^2) =
      1+markedPairCoefficient (n+1) := by
  simpa only [markedAvoids,Finset.notMem_empty,implies_true,not_false_eq_true,forall_true_iff,ite_true,
    Finset.card_empty,Nat.cast_zero,zero_div,sub_zero,one_pow,mul_one,pow_two,
    markedPairCoefficient] using
    marked_occupancy_product_avoidance (Nat.succ_pos n) ∅
      (0 : Fin (n+1)) 0 (by simp) (by simp)

/-- The central mark cancels its own retention gate in the cross term. -/
theorem marked_central_recipient_cross_mean (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (i : Fin n) :
    mean (UniformResampling (n+1)) (fun a =>
      reuseOccupancy a 0*markedRetainedRecipient p z a i) =
      if (z i).2.1 = false then markedPairCoefficient (n+1)*markedDrawPower (n+1)
        ((markedForbiddenLabels p z (z i).1).card) 2 else 0 := by
  by_cases hi : (z i).2.1 = false
  · rw [if_pos hi]
    let D := markedForbiddenLabels p z (z i).1
    have heq (a : Fin (n+1) → Fin (n+1)) :
        reuseOccupancy a 0*markedRetainedRecipient p z a i =
          if markedAvoids D a then reuseOccupancy a 0*reuseOccupancy a i.succ else 0 := by
      by_cases hc : 0 < reuseOccupancy a 0
      · simp only [markedRetainedRecipient,markedRecipientTerm,hi,true_and,
          if_pos hc,marked_forbidden_avoidance]
        by_cases ha : markedAvoids D a <;> simp [D,ha]
      · have hc0 : reuseOccupancy a 0 = 0 :=
          le_antisymm (le_of_not_gt hc) (reuse_occupancy_nonneg a 0)
        simp [hc0]
    simp only [heq]
    rw [marked_occupancy_product_avoidance (Nat.succ_pos n) D 0 i.succ
      (marked_forbidden_central p z _) (marked_forbidden_recipient p z _ i hi)]
    simp only [Ne.symm (Fin.succ_ne_zero i),ite_false,zero_add,markedPairCoefficient,
      marked_draw_power_of_le (Nat.succ_pos n)
        ((marked_forbidden_count_le p z _).trans (Nat.le_succ n)),D]
  · simp [markedRetainedRecipient,markedRecipientTerm,hi,mean]

/-- Exact pair contribution.  The union of forbidden donor sets preserves
shared original locations, and the diagonal keeps the second recipient mark. -/
theorem marked_recipient_pair_mean (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (i j : Fin n) :
    mean (UniformResampling (n+1)) (fun a =>
      markedRetainedRecipient p z a i*markedRetainedRecipient p z a j) =
      if (z i).2.1 = false ∧ (z j).2.1 = false then
        (if i = j then markedRetainedDrawPower (n+1)
          ((markedForbiddenLabels p z (z i).1 ∪ markedForbiddenLabels p z (z j).1).card) 1
          else 0) +
        markedPairCoefficient (n+1)*markedRetainedDrawPower (n+1)
          ((markedForbiddenLabels p z (z i).1 ∪ markedForbiddenLabels p z (z j).1).card) 2
      else 0 := by
  by_cases hi : (z i).2.1 = false
  · by_cases hj : (z j).2.1 = false
    · rw [if_pos ⟨hi,hj⟩]
      let D := markedForbiddenLabels p z (z i).1 ∪ markedForbiddenLabels p z (z j).1
      have hc : (0 : Fin (n+1)) ∉ D := by
        simp only [D,Finset.mem_union,not_or]
        exact ⟨marked_forbidden_central p z _,marked_forbidden_central p z _⟩
      have hiD : i.succ ∉ D := by
        simp only [D,Finset.mem_union,not_or]
        exact ⟨marked_forbidden_recipient p z _ i hi,marked_forbidden_recipient p z _ i hi⟩
      have hjD : j.succ ∉ D := by
        simp only [D,Finset.mem_union,not_or]
        exact ⟨marked_forbidden_recipient p z _ j hj,marked_forbidden_recipient p z _ j hj⟩
      have hd : D.card ≤ n := marked_forbidden_union_count_le p z _ _
      have heq (a : Fin (n+1) → Fin (n+1)) :
          markedRetainedRecipient p z a i*markedRetainedRecipient p z a j =
            if markedAvoids D a ∧ 0 < reuseOccupancy a 0 then
              reuseOccupancy a i.succ*reuseOccupancy a j.succ else 0 := by
        simp only [markedRetainedRecipient,markedRecipientTerm,hi,hj,true_and,
          marked_forbidden_avoidance,D,marked_avoids_union]
        by_cases hc : 0 < reuseOccupancy a 0 <;>
          by_cases ha : markedAvoids (markedForbiddenLabels p z (z i).1) a <;>
          by_cases hb : markedAvoids (markedForbiddenLabels p z (z j).1) a <;>
          simp [hc,ha,hb]
      simp only [heq]
      rw [marked_central_recipient_product_avoidance (Nat.succ_pos n) D 0 i.succ j.succ
        hc hiD hjD (Fin.succ_ne_zero i) (Fin.succ_ne_zero j)]
      simp only [Fin.succ_inj,markedRetainedDrawPower,markedPairCoefficient,
        marked_draw_power_of_le (Nat.succ_pos n) (by omega : D.card ≤ n+1),
        marked_draw_power_of_le (Nat.succ_pos n) (by omega : D.card+1 ≤ n+1),
        Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,D]
    · simp [markedRetainedRecipient,markedRecipientTerm,hj,mean]
  · simp [markedRetainedRecipient,markedRecipientTerm,hi,mean]

/-- Eliminate the entire resampling law from the pinned bootstrap second
moment.  All sums are literal original-recipient sums in the same configuration. -/
theorem marked_pinned_U_square_direct (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (hp : ∀ i l v : Fin (n+1), l ≠ v →
      |(pin n p z l).1-(pin n p z i).1| ≠
        |(pin n p z v).1-(pin n p z i).1|) :
    mean (UniformResampling (n+1)) (fun a => (U (pin n p z) a 0)^2) =
      1+markedPairCoefficient (n+1) +
      2*(∑ i, if (z i).2.1 = false then markedPairCoefficient (n+1)*markedDrawPower (n+1)
        ((markedForbiddenLabels p z (z i).1).card) 2 else 0) +
      ∑ i, ∑ j, if (z i).2.1 = false ∧ (z j).2.1 = false then
        (if i = j then markedRetainedDrawPower (n+1)
          ((markedForbiddenLabels p z (z i).1 ∪ markedForbiddenLabels p z (z j).1).card) 1
          else 0) +
        markedPairCoefficient (n+1)*markedRetainedDrawPower (n+1)
          ((markedForbiddenLabels p z (z i).1 ∪ markedForbiddenLabels p z (z j).1).card) 2
      else 0 := by
  have heq (a : Fin (n+1) → Fin (n+1)) : (U (pin n p z) a 0)^2 =
      (reuseOccupancy a 0)^2 +
      2*(∑ i, reuseOccupancy a 0*markedRetainedRecipient p z a i) +
      ∑ i, ∑ j, markedRetainedRecipient p z a i*markedRetainedRecipient p z a j := by
    rw [marked_pinned_U_sum n p z a hp]
    rw [← Finset.sum_mul_sum,← Finset.mul_sum]
    ring
  simp only [heq,mean]
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite,integral_const_mul,
    integral_finsetSum _ (fun _ _ => Integrable.of_finite),
    integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  change mean (UniformResampling (n+1)) (fun a => (reuseOccupancy a 0)^2) +
    2*(∑ i, mean (UniformResampling (n+1))
      (fun a => reuseOccupancy a 0*markedRetainedRecipient p z a i)) +
    (∑ i, ∑ j, mean (UniformResampling (n+1))
      (fun a => markedRetainedRecipient p z a i*markedRetainedRecipient p z a j)) = _
  simp only [marked_central_occupancy_square_mean,marked_central_recipient_cross_mean,
    marked_recipient_pair_mean]

end AronowAudit.P001.TailA
