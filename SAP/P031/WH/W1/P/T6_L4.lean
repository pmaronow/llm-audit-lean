import SAP.P031.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000

open Finset

namespace SAP.P031.WH.W1.P.T6_L4

lemma sign_partition_card (N : ℕ) (q : Fin N → ℝ)
    (hnp : (univ.filter (fun i => q i < 0)).card =
      (univ.filter (fun i => 0 < q i)).card) :
    (univ.filter (fun i => q i < 0)).card +
      (univ.filter (fun i => q i = 0)).card +
      (univ.filter (fun i => 0 < q i)).card = N := by
  classical
  let negSet : Finset (Fin N) := univ.filter (fun i => q i < 0)
  let zeroSet : Finset (Fin N) := univ.filter (fun i => q i = 0)
  let posSet : Finset (Fin N) := univ.filter (fun i => 0 < q i)
  have hpartition : (negSet ∪ zeroSet) ∪ posSet = univ := by
    ext i
    simp only [Finset.mem_union, negSet, zeroSet, posSet, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      rcases lt_trichotomy (q i) 0 with hn | hz | hp
      · exact Or.inl (Or.inl hn)
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hp
  have hnegzero : Disjoint negSet zeroSet := by
    refine Finset.disjoint_left.mpr ?_
    intro i hi hz
    simp only [negSet, zeroSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hz
    linarith
  have hnegzeroPos : Disjoint (negSet ∪ zeroSet) posSet := by
    refine Finset.disjoint_left.mpr ?_
    intro i hi hp
    simp only [Finset.mem_union, negSet, zeroSet, posSet, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi hp
    rcases hi with hn | hz <;> linarith
  have hposneg : posSet.card = negSet.card := by
    simpa [negSet, posSet] using hnp.symm
  calc
    negSet.card + zeroSet.card + posSet.card =
        (negSet ∪ zeroSet).card + posSet.card := by
          rw [Finset.card_union_of_disjoint hnegzero]
    _ = ((negSet ∪ zeroSet) ∪ posSet).card :=
          (Finset.card_union_of_disjoint hnegzeroPos).symm
    _ = (univ : Finset (Fin N)).card := congrArg Finset.card hpartition
    _ = N := by simp

end SAP.P031.WH.W1.P.T6_L4

theorem SAP.P031.WH.W1.T6_L4_proof : SAP.P031.WH.W1.T6_L4 := by
  classical
  intro N q hN hnp
  let negSet : Finset (Fin N) := univ.filter (fun i => q i < 0)
  let zeroSet : Finset (Fin N) := univ.filter (fun i => q i = 0)
  let posSet : Finset (Fin N) := univ.filter (fun i => 0 < q i)
  let badPairs : Finset (Fin N × Fin N) :=
    univ.filter (fun ij => q ij.1 * q ij.2 ≤ 0)
  let goodPairs : Finset (Fin N × Fin N) :=
    univ.filter (fun ij => 0 < q ij.1 * q ij.2)
  have hposneg : posSet.card = negSet.card := by
    simpa [negSet, posSet] using hnp.symm
  have hgood_eq : goodPairs = negSet ×ˢ negSet ∪ posSet ×ˢ posSet := by
    ext ⟨i, j⟩
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_product, negSet, posSet, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simpa [or_comm] using (mul_pos_iff (a := q i) (b := q j))
  have hgood_disjoint : Disjoint (negSet ×ˢ negSet) (posSet ×ˢ posSet) := by
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨i, j⟩ hij hji
    have hleft := Finset.mem_product.mp hij
    have hright := Finset.mem_product.mp hji
    have hn : q i < 0 := by simpa [negSet] using hleft.1
    have hp : 0 < q i := by simpa [posSet] using hright.1
    linarith
  have hgood_card : goodPairs.card = 2 * negSet.card ^ 2 := by
    calc
      goodPairs.card = (negSet ×ˢ negSet).card + (posSet ×ˢ posSet).card := by
        rw [hgood_eq, Finset.card_union_of_disjoint hgood_disjoint]
      _ = 2 * negSet.card ^ 2 := by
        rw [Finset.card_product, Finset.card_product, hposneg]
        ring
  have htotal : badPairs.card + goodPairs.card = N * N := by
    simpa [badPairs, goodPairs, not_le, Finset.card_product] using
      (Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (Fin N × Fin N)))
        (p := fun ij => q ij.1 * q ij.2 ≤ 0))
  have hsize : negSet.card + zeroSet.card + posSet.card = N := by
    simpa [negSet, zeroSet, posSet] using
      SAP.P031.WH.W1.P.T6_L4.sign_partition_card N q hnp
  have hsizeR : (negSet.card : ℝ) + (zeroSet.card : ℝ) +
      (posSet.card : ℝ) = (N : ℝ) := by
    exact_mod_cast hsize
  have hposnegR : (posSet.card : ℝ) = (negSet.card : ℝ) := by
    exact_mod_cast hposneg
  rw [hposnegR] at hsizeR
  have hdecomp : (N : ℝ) = 2 * (negSet.card : ℝ) + (zeroSet.card : ℝ) := by
    linarith [hsizeR]
  have htotalR : (badPairs.card : ℝ) + (goodPairs.card : ℝ) =
      (N : ℝ) * (N : ℝ) := by
    exact_mod_cast htotal
  have hgoodR : (goodPairs.card : ℝ) = 2 * (negSet.card : ℝ) ^ 2 := by
    exact_mod_cast hgood_card
  have hbadR : (badPairs.card : ℝ) =
      (N : ℝ) * (N : ℝ) - 2 * (negSet.card : ℝ) ^ 2 := by
    linarith [htotalR, hgoodR]
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold SAP.P031.WH.W1.nonpositiveProductFraction SAP.P031.WH.W1.zeroFraction
  have hformula : (badPairs.card : ℝ) / (N : ℝ) ^ 2 =
      1 / 2 + (zeroSet.card : ℝ) / (N : ℝ) -
        ((zeroSet.card : ℝ) / (N : ℝ)) ^ 2 / 2 := by
    rw [hbadR]
    have hNne : (N : ℝ) ≠ 0 := hNreal.ne'
    field_simp [hNne]
    rw [hdecomp]
    ring
  simpa [badPairs, zeroSet] using hformula
