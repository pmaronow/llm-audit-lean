import AronowAudit.P004.Wave1.LinePopulation.N2

namespace AronowAudit.P004.Wave1.LinePopulation

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

theorem n7_proof : N7 := by
  intro N R ρ d hρ hd hR
  classical
  let D : Fin N → Fin N → ℝ := fun i j => 10 * |(i : ℝ) - (j : ℝ)|
  have hsym (i j : Fin N) : D i j = D j i := by
    dsimp only [D]
    rw [abs_sub_comm]
  have htri (i j k : Fin N) : D i k ≤ D i j + D j k := by
    dsimp only [D]
    have h := abs_sub_le (i : ℝ) (j : ℝ) (k : ℝ)
    linarith
  -- A source farther than d + ρ cannot change any term of this average.
  have havg (i l : Fin N) (z : Assignment N) (b : Bool)
      (hfar : d + ρ < D i l) :
      circleAverage (linePopulation R) d i (Function.update z l b) =
        circleAverage (linePopulation R) d i z := by
    rw [n2_proof R d hd i (Function.update z l b), n2_proof R d hd i z]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hij : D i j ≤ d := by
      have hmem := (Finset.mem_filter.mp hj).2
      simpa only [n1_proof R] using hmem
    apply hR j l z b
    change ρ < D j l
    have htriangle := htri i j l
    linarith
  -- This also treats the compulsory i = l branch of `interferes`.
  have hsource (i l : Fin N)
      (hil : interferes (circleAverage (linePopulation R) d) i l) :
      D i l ≤ d + ρ := by
    rcases hil with hdiag | ⟨z, z', hz, hne⟩
    · subst l
      simp only [D, sub_self, abs_zero, mul_zero]
      linarith
    · by_contra hn
      have hfar : d + ρ < D i l := lt_of_not_ge hn
      have hu : Function.update z l (z' l) = z' := by
        funext k
        by_cases hkl : k = l
        · subst k
          simp
        · rw [Function.update_of_ne hkl]
          exact hz k hkl
      have heq := havg i l z (z' l) hfar
      rw [hu] at heq
      exact hne heq.symm
  intro i j hfar hshared
  obtain ⟨l, hil, hjl⟩ := hshared
  have hi := hsource i l hil
  have hj := hsource j l hjl
  rw [n1_proof R i j] at hfar
  change 2 * d + 2 * ρ < D i j at hfar
  have htriangle := htri i l j
  rw [hsym l j] at htriangle
  linarith

end
end AronowAudit.P004.Wave1.LinePopulation
