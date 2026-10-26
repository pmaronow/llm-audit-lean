import AronowAudit.P004.Wave1.PairedWitness.PW5

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

/-- Direct computation of the line distance, independently of N1. -/
theorem pairedPop_separation {N : ℕ} (i j : Fin N) :
    nodeSeparation (pairedPop N) i j = 10 * |(i : ℝ) - (j : ℝ)| := by
  have hsep : nodeSeparation (pairedPop N) i j =
      dist (planePoint (10 * (i : ℝ)) 0) (planePoint (10 * (j : ℝ)) 0) := by
    simp [nodeSeparation, pairedPop, linePopulation]
  rw [hsep, EuclideanSpace.dist_eq]
  have hsum :
      (∑ k : Fin 2,
        dist (planePoint (10 * (i : ℝ)) 0 k) (planePoint (10 * (j : ℝ)) 0 k) ^ 2) =
        (10 * ((i : ℝ) - (j : ℝ))) ^ 2 := by
    simp [planePoint, Fin.sum_univ_succ, Real.dist_eq, sq_abs]
    <;> ring
  rw [hsum, Real.sqrt_sq_eq_abs, abs_mul]
  norm_num

/-- This also accounts for the compulsory diagonal in `interferes`. -/
theorem paired_interferes_block {N : ℕ} (i l : Fin N)
    (h : interferes (pairedTable N) i l) : l.val / 2 = i.val / 2 := by
  rcases h with hil | ⟨z, z', hz, hne⟩
  · subst l
    rfl
  · by_contra hblock
    apply hne
    apply pairedTable_congr_block
    intro k hk
    apply hz k
    intro hkl
    subst k
    exact hblock hk

theorem pw6_proof : PW6 := by
  intro N i j hfar hshared
  obtain ⟨l, hil, hjl⟩ := hshared
  have hli := paired_interferes_block i l hil
  have hlj := paired_interferes_block j l hjl
  have hij : i.val / 2 = j.val / 2 := hli.symm.trans hlj
  have hclose := pair_block_close i j hij
  rw [pairedPop_separation] at hfar
  linarith

end
end AronowAudit.P004.Wave1.PairedWitness
