import SAP.P003a.WH.W3.Leaves
import AronowAudit.P003.P003_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W3.P.T16_L4

open scoped BigOperators
open SAP.P003a
open SAP.P003a.WH.W3
attribute [local instance 0] Classical.propDecidable

private def remSet {n : ℕ} (i j : Fin n) : Finset (Fin n) :=
  (Finset.univ.erase i).erase j

private theorem rem_not_labels {n : ℕ} {i j a : Fin n} (ha : a ∈ remSet i j) :
    a ≠ i ∧ a ≠ j := by
  have hp : a ≠ j ∧ a ≠ i := by simpa [remSet] using ha
  exact ⟨hp.2, hp.1⟩

private theorem rem_sum_equiv {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n))
    (i j : Fin n) (e : Fin (n-2) ≃ WholeRemaining n i j) :
    (∑ k ∈ remSet i j, wholeSignedTerm w z k) =
      ∑ k : Fin (n-2), wholeSignedTerm (wholeRestrictedTable w e)
        (wholeRestrictedAssignment z e) k := by
  classical
  apply Finset.sum_bij (fun a ha => e.symm ⟨a, rem_not_labels ha⟩)
  · intro a ha
    simp
  · intro a₁ ha₁ a₂ ha₂ heq
    have hv := congrArg Subtype.val (congrArg e heq)
    simpa using hv
  · intro k hk
    refine ⟨(e k).val, ?_, ?_⟩
    · have hp := (e k).property
      simp [remSet, Finset.mem_erase, hp.1, hp.2, hk]
    · have hq : (⟨(e k).val, (e k).property⟩ : WholeRemaining n i j) = e k := by
        apply Subtype.ext
        rfl
      rw [hq]
      exact e.symm_apply_apply k
  · intro a ha
    have hv : (e (e.symm ⟨a, rem_not_labels ha⟩)).val = a :=
      congrArg Subtype.val (e.apply_symm_apply ⟨a, rem_not_labels ha⟩)
    simp [wholeSignedTerm, wholeRestrictedTable, wholeRestrictedAssignment,
      Finset.mem_filter, hv]

private theorem pair_terms {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n))
    (i j : Fin n) (hij : i ∈ z ↔ j ∉ z) :
    wholeSignedTerm w z i + wholeSignedTerm w z j =
      (pairContribution (w i) (w j) (decide (i ∈ z)) : ℝ) := by
  by_cases hi : i ∈ z
  · have hj : j ∉ z := fun h => (hij.mp hi) h
    simp [wholeSignedTerm, pairContribution, hi, hj, bit] <;> ring
  · have hj : j ∈ z := by
      by_contra hn
      exact hi (hij.mpr hn)
    simp [wholeSignedTerm, pairContribution, hi, hj, bit] <;> ring

private theorem rem_assignment_card {n m : ℕ} (z : Assignment n m) (i j : Fin n)
    (hij : i ∈ z.val ↔ j ∉ z.val)
    (e : Fin (n-2) ≃ WholeRemaining n i j) :
    (wholeRestrictedAssignment z.val e).card = m-1 := by
  classical
  let t := wholeRestrictedAssignment z.val e
  have hcard : t.card = ((z.val.erase i).erase j).card := by
    symm
    apply Finset.card_bij (s := (z.val.erase i).erase j) (t := t)
      (fun a ha => by
        simp only [Finset.mem_erase, Finset.mem_univ, true_and] at ha
        exact e.symm ⟨a, ⟨ha.2.1, ha.1⟩⟩)
    · intro a ha
      simp only [Finset.mem_erase, Finset.mem_univ, true_and] at ha
      simp [t, wholeRestrictedAssignment, Finset.mem_filter]
      have hv : (e (e.symm ⟨a, ⟨ha.2.1, ha.1⟩⟩)).val = a :=
        congrArg Subtype.val (e.apply_symm_apply ⟨a, ⟨ha.2.1, ha.1⟩⟩)
      simpa [hv] using ha.2.2
    · intro a₁ ha₁ a₂ ha₂ heq
      apply_fun (fun q : Fin (n-2) => (e q).val) at heq
      simpa only [Equiv.apply_symm_apply] using heq
    · intro k hk
      refine ⟨(e k).val, ?_, ?_⟩
      · have hmem : (e k).val ∈ z.val := by
          simpa [t, wholeRestrictedAssignment, Finset.mem_filter] using hk
        simp only [Finset.mem_erase, Finset.mem_univ, true_and]
        exact ⟨(e k).property.2, (e k).property.1, hmem⟩
      · have hq : (⟨(e k).val, (e k).property⟩ : WholeRemaining n i j) = e k := by
          apply Subtype.ext
          rfl
        rw [hq]
        exact e.symm_apply_apply k
  rw [hcard]
  by_cases hi : i ∈ z.val
  · have hj : j ∉ z.val := hij.mp hi
    have hj' : j ∉ z.val.erase i := by
      simp only [Finset.mem_erase]
      intro h
      exact hj h.2
    rw [Finset.erase_eq_of_notMem hj']
    rw [Finset.card_erase_of_mem hi, z.property]
  · have hj : j ∈ z.val := by
      by_contra hn
      exact hi (hij.mpr hn)
    rw [Finset.erase_eq_of_notMem hi]
    rw [Finset.card_erase_of_mem hj, z.property]

private theorem split_sum {n : ℕ} (f : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    (∑ k, f k) = f i + f j + ∑ k ∈ remSet i j, f k := by
  classical
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ.erase i) := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
  have h1 : (∑ k ∈ (Finset.univ.erase i), f k) + f i = ∑ k, f k :=
    Finset.sum_erase_add _ _ hi
  have h2 : (∑ k ∈ ((Finset.univ.erase i).erase j), f k) + f j =
      ∑ k ∈ (Finset.univ.erase i), f k := Finset.sum_erase_add _ _ hj
  calc
    (∑ k, f k) = ((∑ k ∈ remSet i j, f k) + f j) + f i := by
      rw [← h1, ← h2]
      rfl
    _ = f i + f j + ∑ k ∈ remSet i j, f k := by ring

private theorem remSet_empty_two {n : ℕ} (hn : n = 2) (i j : Fin n) (hij : i ≠ j) :
    remSet i j = ∅ := by
  subst n
  ext k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [remSet]

end SAP.P003a.WH.W3.P.T16_L4

theorem SAP.P003a.WH.W3.T16_L4_proof : SAP.P003a.WH.W3.T16_L4 := by
  classical
  intro n m hm hn w z i j hij
  have hpartner : i ≠ j.val := j.property.symm
  have hcard : z.val.card = m := z.property
  refine ⟨?_, ?_, ?_⟩
  · have hbase : tableEstimator w z.val =
        (∑ k, wholeSignedTerm w z.val k)/(m : ℝ) := by
      simpa only [SAP.P003a.Bridge.to_tableEstimator, wholeSignedTerm,
        SAP.P003a.Bridge.bit_eq] using
        AronowAudit.P003.corrected_signed_sum w z.val m hm hn hcard
    rw [hbase]
    rw [SAP.P003a.WH.W3.P.T16_L4.split_sum
      (fun k => wholeSignedTerm w z.val k) i j.val hpartner]
    rw [SAP.P003a.WH.W3.P.T16_L4.pair_terms w z.val i j.val hij]
    unfold wholeResidualContribution SAP.P003a.WH.W3.P.T16_L4.remSet
    push_cast
    ring
  · intro hmone
    have hn2 : n = 2 := by omega
    have hzeroSet := SAP.P003a.WH.W3.P.T16_L4.remSet_empty_two hn2 i j.val hpartner
    change (∑ k ∈ SAP.P003a.WH.W3.P.T16_L4.remSet i j.val,
      wholeSignedTerm w z.val k)/(m : ℝ) = 0
    rw [hzeroSet]
    simp [hmone]
  · intro e
    have hremcard := SAP.P003a.WH.W3.P.T16_L4.rem_assignment_card z i j.val hij e
    have hsum := SAP.P003a.WH.W3.P.T16_L4.rem_sum_equiv w z.val i j.val e
    refine ⟨hremcard, ?_, ?_⟩
    · unfold wholeResidualContribution
      change (∑ k ∈ SAP.P003a.WH.W3.P.T16_L4.remSet i j.val,
        wholeSignedTerm w z.val k)/(m : ℝ) = _
      rw [hsum]
    · intro hmgt
      have hm' : 0 < m-1 := by omega
      have hn' : n-2 = 2*(m-1) := by omega
      have hest : tableEstimator (wholeRestrictedTable w e)
          (wholeRestrictedAssignment z.val e) =
          (∑ k, wholeSignedTerm (wholeRestrictedTable w e)
            (wholeRestrictedAssignment z.val e) k)/((m-1 : ℕ) : ℝ) := by
        simpa only [SAP.P003a.Bridge.to_tableEstimator, wholeSignedTerm,
          SAP.P003a.Bridge.bit_eq] using
          AronowAudit.P003.corrected_signed_sum
            (wholeRestrictedTable w e) (wholeRestrictedAssignment z.val e) (m-1)
            hm' hn' hremcard
      rw [show wholeResidualContribution w z.val m i j.val =
        (∑ k : Fin (n-2), wholeSignedTerm (wholeRestrictedTable w e)
          (wholeRestrictedAssignment z.val e) k)/(m : ℝ) by
          unfold wholeResidualContribution
          change (∑ k ∈ SAP.P003a.WH.W3.P.T16_L4.remSet i j.val,
            wholeSignedTerm w z.val k)/(m : ℝ) = _
          rw [hsum]]
      rw [hest]
      have hmc : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
      have hmc' : ((m-1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm')
      field_simp
