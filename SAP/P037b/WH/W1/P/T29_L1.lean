import SAP.P037b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037b.WH.W1.P.T29_L1

open scoped BigOperators
attribute [local instance] Classical.propDecidable

open AronowAudit.P037
open AronowAudit.P037.Wave1

private abbrev peerFive : Finset (Fin 10) := {0, 1, 2, 3, 4}
private abbrev avoidingFive : Finset (Fin 10) := {5, 6, 7, 8, 9}

lemma block_referent_count :
    (Finset.univ.filter (fun b : SAP.P037b.RareBlockW1 => (0 : Fin 10) ∈ b.val)).card = 126 := by
  let blocks : Finset (Finset (Fin 10)) :=
    (Finset.univ : Finset (Fin 10)).powersetCard 5
  have hpow : (blocks.filter (fun s => (0 : Fin 10) ∈ s)).card = 126 := by
    have he : blocks.filter (fun s => (0 : Fin 10) ∈ s) =
        blocks.filter (fun s => ({0} : Finset (Fin 10)) ⊆ s) := by
      ext s
      simp [blocks]
    rw [he]
    dsimp [blocks]
    rw [Finset.card_filter_powersetCard_subset {0} Finset.univ 5 (by simp) (by simp)]
    norm_num [Nat.choose]
  have hs := rare_probability_block_sum
    (fun s : Finset (Fin 10) => if (0 : Fin 10) ∈ s then (1 : ℝ) else 0)
  have hcast :
      ((Finset.univ.filter
        (fun b : SAP.P037b.RareBlockW1 => (0 : Fin 10) ∈ b.val)).card : ℝ) =
      ((blocks.filter (fun s => (0 : Fin 10) ∈ s)).card : ℝ) := by
    simpa only [Finset.sum_boole, blocks] using hs
  have hreal :
      ((Finset.univ.filter
        (fun b : SAP.P037b.RareBlockW1 => (0 : Fin 10) ∈ b.val)).card : ℝ) = 126 := by
    rw [hcast, hpow]
    norm_num
  exact_mod_cast hreal

lemma avoid_block_eq (b : SAP.P037b.RareBlockW1)
    (h : Disjoint b.val peerFive) : b.val = avoidingFive := by
  have hsubset : b.val ⊆ avoidingFive := by
    have hcover : peerFive ∪ avoidingFive = Finset.univ := by
      ext x
      fin_cases x <;> norm_num [peerFive, avoidingFive]
    intro x hx
    have hxnot : x ∉ peerFive := by
      intro hxpeer
      exact (Finset.disjoint_left.mp h) hx hxpeer
    have hxU : x ∈ (Finset.univ : Finset (Fin 10)) := Finset.mem_univ x
    rw [← hcover] at hxU
    rcases Finset.mem_union.mp hxU with hxpeer | hxavoid
    · exact (False.elim (hxnot hxpeer))
    · exact hxavoid
  apply Finset.eq_of_subset_of_card_le hsubset
  simpa [avoidingFive] using b.property.ge

lemma avoid_iff_singleton (s : SAP.P037b.RarePairW1) :
    SAP.P037b.rareAvoidsPairW1 s ↔ s = SAP.P037b.rareAvoidingPairW1 := by
  constructor
  · intro hs
    rcases s with ⟨a, b⟩
    change Disjoint a.val peerFive ∧ Disjoint b.val peerFive at hs
    apply Prod.ext
    · apply Subtype.ext
      exact avoid_block_eq a hs.1
    · apply Subtype.ext
      exact avoid_block_eq b hs.2
  · intro hs
    subst s
    constructor <;> norm_num [SAP.P037b.rareAvoidsPairW1,
      SAP.P037b.rareAvoidingPairW1, peerFive, avoidingFive,
      Finset.disjoint_left]

lemma block_point_mass (b : SAP.P037b.RareBlockW1) :
    designMean rare_probability_block_law
      (fun x => if x = b then (1 : ℝ) else 0) = 1 / 252 := by
  unfold designMean rare_probability_block_law
  simp

lemma pair_uniform_marginal (s : SAP.P037b.RarePairW1) :
    (∑ z : SAP.P037b.RareSeedAssignments,
      SAP.P037b.rareAssignmentMass z *
        (if (z.2 0, z.2 1) = s then (1 : ℝ) else 0)) = 1 / 63504 := by
  rcases s with ⟨a, b⟩
  change designMean rare_design_law
    (fun z => if (z.2 0, z.2 1) = (a, b) then (1 : ℝ) else 0) = _
  rw [rare_design_split]
  have hsplit :
      (fun w : Fin 4 → RareProbabilityDesignBlock =>
        if (w 0, w 1) = (a, b) then (1 : ℝ) else 0) =
      (fun w => (if w 0 = a then (1 : ℝ) else 0) *
        (if w 1 = b then (1 : ℝ) else 0)) := by
    funext w
    by_cases h0 : w 0 = a <;> by_cases h1 : w 1 = b <;> simp [h0, h1]
  rw [hsplit]
  change (designMean rare_probability_blocks_law
      (fun w => (if w 0 = a then (1 : ℝ) else 0) *
        (if w 1 = b then (1 : ℝ) else 0)) +
    designMean rare_probability_blocks_law
      (fun w => (if w 0 = a then (1 : ℝ) else 0) *
        (if w 1 = b then (1 : ℝ) else 0))) / 2 = _
  rw [rare_probability_blocks_law,
    product_design_coordinate_pair (fun _ : Fin 4 => rare_probability_block_law)
      0 1 (by decide)
      (fun x => if x = a then (1 : ℝ) else 0)
      (fun x => if x = b then (1 : ℝ) else 0),
    block_point_mass, block_point_mass]
  norm_num

lemma pair_containing_referent_count :
    (Finset.univ.filter
      (fun s : SAP.P037b.RarePairW1 => (0 : Fin 10) ∈ s.1.val)).card = 31752 := by
  let U : Finset SAP.P037b.RareBlockW1 := Finset.univ
  have hu : U.card = 252 := by
    simpa [U] using rare_probability_block_card
  have hprod : (Finset.univ : Finset SAP.P037b.RarePairW1) = U ×ˢ U := by
    ext s
    simp [U]
  rw [hprod,
    Finset.filter_product_left (s := U) (t := U)
      (p := fun b : SAP.P037b.RareBlockW1 => (0 : Fin 10) ∈ b.val),
    Finset.card_product]
  rw [block_referent_count, hu]

lemma pair_avoiding_count :
    (Finset.univ.filter SAP.P037b.rareAvoidsPairW1).card = 1 := by
  have hf : Finset.univ.filter SAP.P037b.rareAvoidsPairW1 =
      {SAP.P037b.rareAvoidingPairW1} := by
    ext s
    simp [avoid_iff_singleton]
  rw [hf]
  simp

lemma pair_total_count : (Finset.univ : Finset SAP.P037b.RarePairW1).card = 63504 := by
  have h : Fintype.card SAP.P037b.RarePairW1 = 63504 := by
    rw [Fintype.card_prod, rare_probability_block_card]
  simpa using h

lemma pair_nonreferent_nonavoiding_count :
    (Finset.univ.filter (fun s : SAP.P037b.RarePairW1 =>
      (0 : Fin 10) ∉ s.1.val ∧ ¬SAP.P037b.rareAvoidsPairW1 s)).card = 31751 := by
  let N : Finset SAP.P037b.RarePairW1 :=
    Finset.univ.filter (fun s => (0 : Fin 10) ∉ s.1.val)
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset SAP.P037b.RarePairW1))
    (fun s => (0 : Fin 10) ∈ s.1.val)
  have hn : N.card = 31752 := by
    rw [pair_containing_referent_count, pair_total_count] at hpart
    have hnot : (Finset.univ.filter (fun s : SAP.P037b.RarePairW1 =>
        ¬(0 : Fin 10) ∈ s.1.val)).card = N.card := by
      simp [N]
    rw [← hnot] at hpart
    omega
  have havoids : (N.filter SAP.P037b.rareAvoidsPairW1).card = 1 := by
    have hf : N.filter SAP.P037b.rareAvoidsPairW1 =
        {SAP.P037b.rareAvoidingPairW1} := by
      ext s
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hs
        exact (avoid_iff_singleton s).mp hs.2
      · intro hs
        subst s
        exact ⟨by norm_num [SAP.P037b.rareAvoidingPairW1],
          (avoid_iff_singleton _).mpr rfl⟩
    rw [hf]
    simp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := N) (fun s : SAP.P037b.RarePairW1 =>
      SAP.P037b.rareAvoidsPairW1 s)
  have htarget :
      (Finset.univ.filter (fun s : SAP.P037b.RarePairW1 =>
        (0 : Fin 10) ∉ s.1.val ∧ ¬SAP.P037b.rareAvoidsPairW1 s)).card =
        (N.filter fun s => ¬SAP.P037b.rareAvoidsPairW1 s).card := by
    simp [N, Finset.filter_filter]
  rw [havoids, hn] at hsplit
  rw [htarget]
  omega

end SAP.P037b.WH.W1.P.T29_L1

namespace SAP.P037b.WH.W1

theorem T29_L1_proof : T29_L1 := by
  refine ⟨?_, SAP.P037b.WH.W1.P.T29_L1.pair_avoiding_count, ?_,
    SAP.P037b.WH.W1.P.T29_L1.pair_containing_referent_count,
    SAP.P037b.WH.W1.P.T29_L1.pair_nonreferent_nonavoiding_count⟩
  · exact SAP.P037b.WH.W1.P.T29_L1.pair_uniform_marginal
  · exact SAP.P037b.WH.W1.P.T29_L1.avoid_iff_singleton

end SAP.P037b.WH.W1
