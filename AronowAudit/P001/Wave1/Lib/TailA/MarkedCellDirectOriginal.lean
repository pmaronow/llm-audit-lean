import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectMoments
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellBoundaries

/-! Direct finite moment identities in the actual pinned original-sample law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectOriginal (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- The original pinned experiment avoids every comparison boundary. -/
theorem marked_pinned_actual_distances_unique (n : ℕ) (p : ℝ) :
    ∀ᵐ z ∂MatchProduct n, ∀ i l v : Fin (n+1), l ≠ v →
      |(pin n p z l).1-(pin n p z i).1| ≠
        |(pin n p z v).1-(pin n p z i).1| := by
  have hmap : ∀ᵐ s ∂(MatchProduct n).map (fun z : Fin n → MatchUnit => fun i => (z i).1),
      ∀ i l v : Fin (n+1), l ≠ v →
        |markedPinnedScores p s l-markedPinnedScores p s i| ≠
          |markedPinnedScores p s v-markedPinnedScores p s i| := by
    rw [(matching_score_product_marginal n).map_eq]
    exact marked_pinned_distances_unique MatchingScoreLaw n p
  have hpull := ae_of_ae_map (matching_score_product_marginal n).measurable.aemeasurable hmap
  filter_upwards [hpull] with z hz
  have hscore (i : Fin (n+1)) : (pin n p z i).1 =
      markedPinnedScores p (fun j => (z j).1) i := by
    refine Fin.cases rfl (fun _ => rfl) i
  simpa only [hscore] using hz

def markedOriginalRecipient {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit) (i : Fin n) : ℝ :=
  if (z i).2.1 = false ∧ (markedForbiddenLabels p z (z i).1).card = 0 then 1 else 0

def markedOriginalRecipientPair {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit)
    (i j : Fin n) : ℝ :=
  if (z i).2.1 = false ∧ (z j).2.1 = false ∧
      (markedForbiddenLabels p z (z i).1 ∪ markedForbiddenLabels p z (z j).1).card = 0
    then 1 else 0

theorem marked_identity_avoidance {N : ℕ} (D : Finset (Fin N)) :
    markedAvoids D id ↔ D.card = 0 := by
  rw [Finset.card_eq_zero]
  simp only [markedAvoids,id_eq]
  constructor
  · intro h
    ext t
    simp [h t]
  · rintro rfl
    simp

theorem marked_original_recipient_term (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (i : Fin n) : markedRecipientTerm p z id i = markedOriginalRecipient p z i := by
  have hid : reuseOccupancy (id : Fin (n+1) → Fin (n+1)) i.succ = 1 := by
    have hf : (Finset.univ.filter (fun j : Fin (n+1) => id j = i.succ)) = {i.succ} := by
      ext j
      simp
    simp only [reuseOccupancy,hf,Finset.card_singleton,Nat.cast_one]
  simp only [markedRecipientTerm,markedOriginalRecipient,hid,
    marked_forbidden_avoidance,marked_identity_avoidance]

theorem marked_original_recipient_pair (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (i j : Fin n) :
    markedOriginalRecipient p z i*markedOriginalRecipient p z j =
      markedOriginalRecipientPair p z i j := by
  have hc : (markedForbiddenLabels p z (z i).1 ∪ markedForbiddenLabels p z (z j).1).card = 0 ↔
      (markedForbiddenLabels p z (z i).1).card = 0 ∧
        (markedForbiddenLabels p z (z j).1).card = 0 := by
    simp only [Finset.card_eq_zero,Finset.union_eq_empty]
  simp only [markedOriginalRecipient,markedOriginalRecipientPair,hc]
  split_ifs <;> simp_all

/-- Exact original square as a one-recipient term and a distinct-recipient
term.  The coefficient three includes the diagonal of the recipient square. -/
theorem marked_pinned_W_square_direct (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit)
    (hp : ∀ i l v : Fin (n+1), l ≠ v →
      |(pin n p z l).1-(pin n p z i).1| ≠
        |(pin n p z v).1-(pin n p z i).1|) :
    (W (pin n p z) 0)^2 = 1+3*(∑ i, markedOriginalRecipient p z i) +
      ∑ i, ∑ j, if i = j then 0 else markedOriginalRecipientPair p z i j := by
  have hW : W (pin n p z) 0 = 1+∑ i, markedOriginalRecipient p z i := by
    simp only [marked_pinned_W_direct n p z hp,marked_original_recipient_term]
  have hid (i : Fin n) : (markedOriginalRecipient p z i)^2 = markedOriginalRecipient p z i := by
    unfold markedOriginalRecipient
    split_ifs <;> norm_num
  have hs := marked_sum_square_split (fun i => markedOriginalRecipient p z i)
  simp only [hid,marked_original_recipient_pair] at hs
  rw [hW]
  nlinarith [hs]

/-- The exact first-moment formula appearing inside the conditional replica
square; it is an explicit finite sum of donor-count kernels. -/
def markedDirectFirst {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit) : ℝ :=
  1+∑ i, if (z i).2.1 = false then markedRetainedDrawPower (n+1)
    ((markedForbiddenLabels p z (z i).1).card) 1 else 0

/-- The exact conditional bootstrap square, with same-recipient and
separate-recipient contributions both included. -/
def markedDirectSecond {n : ℕ} (p : ℝ) (z : Fin n → MatchUnit) : ℝ :=
  1+markedPairCoefficient (n+1) +
    2*(∑ i, if (z i).2.1 = false then markedPairCoefficient (n+1)*markedDrawPower (n+1)
      ((markedForbiddenLabels p z (z i).1).card) 2 else 0) +
    ∑ i, ∑ j, if (z i).2.1 = false ∧ (z j).2.1 = false then
      (if i = j then markedRetainedDrawPower (n+1)
        ((markedForbiddenLabels p z (z i).1 ∪ markedForbiddenLabels p z (z j).1).card) 1
        else 0) +
      markedPairCoefficient (n+1)*markedRetainedDrawPower (n+1)
        ((markedForbiddenLabels p z (z i).1 ∪ markedForbiddenLabels p z (z j).1).card) 2
    else 0

/-- Elimination of resampling in the actual pinned second-moment integrand.
There is no no-ties hypothesis: its null-set proof is included. -/
theorem marked_pinned_U_second_integral_direct (n : ℕ) (p : ℝ) :
    mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
      (fun a => (U (pin n p z) a 0)^2)) =
        mean (MatchProduct n) (markedDirectSecond p) := by
  apply integral_congr_ae
  filter_upwards [marked_pinned_actual_distances_unique n p] with z hz
  exact marked_pinned_U_square_direct n p z hz

/-- The actual two-replica integrand is the square of an explicit conditional
mean under the shared original configuration. -/
theorem marked_pinned_U_cross_integral_direct (n : ℕ) (p : ℝ) :
    mean (MatchProduct n) (fun z => mean (UniformResampling (n+1)) (fun a =>
      mean (UniformResampling (n+1)) (fun b => U (pin n p z) a 0*U (pin n p z) b 0))) =
        mean (MatchProduct n) (fun z => (markedDirectFirst p z)^2) := by
  apply integral_congr_ae
  filter_upwards [marked_pinned_actual_distances_unique n p] with z hz
  exact marked_pinned_U_cross_direct n p z hz

/-- The original integrand also reduces exactly to donor-count avoidance,
with all actual finite recipient labels retained in the sums. -/
theorem marked_pinned_W_second_integral_direct (n : ℕ) (p : ℝ) :
    mean (MatchProduct n) (fun z => (W (pin n p z) 0)^2) =
      mean (MatchProduct n) (fun z => 1+3*(∑ i, markedOriginalRecipient p z i) +
        ∑ i, ∑ j, if i = j then 0 else markedOriginalRecipientPair p z i j) := by
  apply integral_congr_ae
  filter_upwards [marked_pinned_actual_distances_unique n p] with z hz
  exact marked_pinned_W_square_direct n p z hz

end AronowAudit.P001.TailA
