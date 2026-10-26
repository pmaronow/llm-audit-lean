import AronowAudit.P004.Wave1.PairedWitnessBlueprint

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

/-- Exchange the two members of an even-sized block. No mate is needed when N is odd. -/
def pairMate {N : ℕ} (hE : Even N) (i : Fin N) : Fin N :=
  ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by
    obtain ⟨r, hr⟩ := hE
    have hi := i.isLt
    split_ifs <;> omega⟩

theorem pairMate_ne {N : ℕ} (hE : Even N) (i : Fin N) : pairMate hE i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [pairMate] at hv
  split_ifs at hv <;> omega

theorem pairMate_div {N : ℕ} (hE : Even N) (i : Fin N) :
    (pairMate hE i).val / 2 = i.val / 2 := by
  dsimp only [pairMate]
  split_ifs <;> omega

theorem pairMate_characterization {N : ℕ} (hE : Even N) (i j : Fin N) :
    (j ≠ i ∧ j.val / 2 = i.val / 2) ↔ j = pairMate hE i := by
  constructor
  · rintro ⟨hji, hdiv⟩
    have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    apply Fin.ext
    dsimp only [pairMate]
    split_ifs <;> omega
  · intro h
    subst j
    exact ⟨pairMate_ne hE i, pairMate_div hE i⟩

/-- The syntactic mate sum contains exactly one term at an even population size. -/
theorem pairedTable_even {N : ℕ} (hE : Even N) (i : Fin N) (z : Assignment N) :
    pairedTable N i z = bit (z i) - bit (z (pairMate hE i)) := by
  unfold pairedTable
  rw [if_pos hE]
  congr 1
  rw [Finset.sum_eq_single (pairMate hE i)]
  · rw [if_pos ⟨pairMate_ne hE i, pairMate_div hE i⟩]
  · intro j _ hj
    have hnot : ¬ (j ≠ i ∧ j.val / 2 = i.val / 2) := by
      intro h
      exact hj ((pairMate_characterization hE i j).mp h)
    rw [if_neg hnot]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- Two natural indices in the same block of length two differ by at most one. -/
theorem pair_block_close {N : ℕ} (i j : Fin N) (h : i.val / 2 = j.val / 2) :
    |(i : ℝ) - (j : ℝ)| ≤ 1 := by
  have hi : i.val ≤ j.val + 1 := by omega
  have hj : j.val ≤ i.val + 1 := by omega
  have hir : (i : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hi
  have hjr : (j : ℝ) ≤ (i : ℝ) + 1 := by exact_mod_cast hj
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem pw4_proof : PW4 := by
  intro N i z
  by_cases hE : Even N
  · rw [pairedTable_even hE]
    cases hi : z i <;> cases hm : z (pairMate hE i) <;>
      norm_num [bit, hi, hm]
  · simp [pairedTable, hE]

end
end AronowAudit.P004.Wave1.PairedWitness
