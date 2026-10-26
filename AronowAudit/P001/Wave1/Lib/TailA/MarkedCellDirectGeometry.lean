import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellFiniteAvoidance

/-! Exact assignment-to-avoidance reduction for pinned weights.

The forbidden interval is determined by a recipient position.  Thus first and
second moments can be expanded using one or two fixed original recipients,
without ordering the random labels in a finite-window representation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectGeometry (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Original donors strictly closer to a query than the pin is. -/
def markedCloserDonors (p x : ℝ) : Set MatchUnit :=
  {u | u.2.1 = true ∧ |u.1-x| < |p-x|}

theorem marked_closer_donors_measurable (p x : ℝ) :
    MeasurableSet (markedCloserDonors p x) := by
  have hm : Measurable (fun u : MatchUnit => |u.1-x|) :=
    continuous_abs.measurable.comp (measurable_fst.sub_const x)
  exact (measurableSet_eq_fun measurable_snd.fst measurable_const).inter
    (measurableSet_lt hm measurable_const)

theorem marked_closer_right {p x q : ℝ} (hpx : p ≤ x) :
    |q-x| < |p-x| ↔ p < q ∧ q < 2*x-p := by
  rw [abs_of_nonpos (sub_nonpos.mpr hpx),abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem marked_closer_left {p x q : ℝ} (hxp : x ≤ p) :
    |q-x| < |p-x| ↔ 2*x-p < q ∧ q < p := by
  rw [abs_of_nonneg (sub_nonneg.mpr hxp),abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

/-- The cell comparison predicate is exactly the absence of any strictly
closer retained original donor; the central label has its own retention mark. -/
theorem marked_pinned_cell_avoidance (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (a : Fin (n+1) → Fin (n+1)) (i : Fin n) :
    markedCellContains (fun l => (pin n p z l).1) (fun l => (pin n p z l).2.1)
      a 0 i.succ ↔
      0 < reuseOccupancy a 0 ∧ markedNoRetained (markedCloserDonors p (z i).1) z a := by
  have hcentral : reuseRetained (fun l => (pin n p z l).2.1) a 0 ↔
      0 < reuseOccupancy a 0 := by
    simp only [reuseRetained,pin,Fin.cases_zero,and_self, true_and]
    exact (marked_occupancy_positive_iff a 0).symm
  constructor
  · intro h
    refine ⟨hcentral.mp h.1,?_⟩
    intro l hl t ht
    have hret : reuseRetained (fun v => (pin n p z v).2.1) a l.succ :=
      ⟨by simpa only [pin,Fin.cases_succ] using hl.1,t,ht⟩
    have hmin := h.2 l.succ hret
    exact (not_lt_of_ge hmin) hl.2
  · rintro ⟨hc,havoid⟩
    refine ⟨hcentral.mpr hc,?_⟩
    intro l
    refine Fin.cases ?_ (fun j => ?_) l
    · intro _
      exact le_rfl
    · intro hl
      apply le_of_not_gt
      intro hj
      obtain ⟨hr,t,ht⟩ := hl
      exact havoid j ⟨hr,hj⟩ t ht

/-- Recipient multiplicity times the actual strictly-closer-donor void event.
The central retention is deliberately kept separate. -/
def markedRecipientTerm {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit)
    (a : Fin (n+1) → Fin (n+1)) (i : Fin n) : ℝ :=
  if (z i).2.1 = false ∧ markedNoRetained (markedCloserDonors p (z i).1) z a
    then reuseOccupancy a i.succ else 0

/-- Exact pinned bootstrap weight as its central multiplicity plus a marked
recipient sum.  Distinct original distances suffice; duplicate copies may tie. -/
theorem marked_pinned_U_direct (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (a : Fin (n+1) → Fin (n+1))
    (hp : ∀ i l v : Fin (n+1), l ≠ v →
      |(pin n p z l).1-(pin n p z i).1| ≠
        |(pin n p z v).1-(pin n p z i).1|) :
    U (pin n p z) a 0 = reuseOccupancy a 0 +
      if 0 < reuseOccupancy a 0 then ∑ i, markedRecipientTerm p z a i else 0 := by
  rw [U,marked_aggregated_weight _ _ _ _ hp,Fin.sum_univ_succ]
  simp only [show (pin n p z 0).2.1 = true from rfl,ite_true,mul_one]
  congr 1
  by_cases hc : 0 < reuseOccupancy a 0
  · rw [if_pos hc]
    apply Finset.sum_congr rfl
    intro i _
    simp only [marked_pinned_cell_avoidance n p z a i]
    cases hr : (z i).2.1 <;> simp [markedRecipientTerm,pin,hr,hc]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro i _
    simp only [marked_pinned_cell_avoidance n p z a i]
    cases hr : (z i).2.1 <;> simp [pin,hr,hc]

/-- The original pinned weight is one plus its recipient-assignment count. -/
theorem marked_pinned_W_direct (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (hp : ∀ i l v : Fin (n+1), l ≠ v →
      |(pin n p z l).1-(pin n p z i).1| ≠
        |(pin n p z v).1-(pin n p z i).1|) :
    W (pin n p z) 0 = 1 + ∑ i, markedRecipientTerm p z id i := by
  have h := marked_pinned_U_direct n p z id hp
  have hid (j : Fin (n+1)) : reuseOccupancy (id : Fin (n+1) → Fin (n+1)) j = 1 := by
    have hf : (Finset.univ.filter (fun i : Fin (n+1) => id i = j)) = {j} := by
      ext i
      simp
    simp only [reuseOccupancy,hf,Finset.card_singleton,Nat.cast_one]
  simpa only [U,reuse_identity,W,hid,zero_lt_one,ite_true] using h

/-- Splitting a square into diagonal and distinct-recipient terms. -/
theorem marked_sum_square_split {I : Type*} [Fintype I] (f : I → ℝ) :
    (∑ i, f i)^2 = (∑ i, (f i)^2) +
      ∑ i, ∑ j, if i = j then 0 else f i*f j := by
  rw [pow_two,Finset.sum_mul_sum]
  have hsplit (i j : I) : f i*f j =
      (if i = j then (f i)^2 else 0) + (if i = j then 0 else f i*f j) := by
    by_cases hij : i = j <;> simp [hij,pow_two]
  calc
    (∑ i, ∑ j, f i*f j) = ∑ i, ∑ j,
        ((if i = j then (f i)^2 else 0) + (if i = j then 0 else f i*f j)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => hsplit i j)
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end AronowAudit.P001.TailA
