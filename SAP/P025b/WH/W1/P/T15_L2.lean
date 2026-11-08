import SAP.P025b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem SAP.P025b.WH.W1.T15_L2_proof : SAP.P025b.WH.W1.T15_L2 := by
  intro m hsum
  constructor
  · rintro ⟨T, hT, hcompat⟩
    have hsum' : m 0 + m 1 = 3 := by
      simpa [Fin.sum_univ_two] using hsum
    have h0 := hcompat 0
    have h1 := hcompat 1
    norm_num at h0 h1
    have hcases : (m 0 = 1 ∧ m 1 = 2) ∨ (m 0 = 2 ∧ m 1 = 1) := by
      omega
    rcases hcases with hgood | hbad
    · ext j
      fin_cases j <;> simp [hgood]
    · have hTlo : (3 : ℝ) ≤ T := by
        rcases hbad with ⟨hm0, hm1⟩
        rw [hm0] at h0
        rw [hm1] at h1
        norm_num at h0 h1
        nlinarith [h0.1]
      have hThi : T ≤ (9 : ℝ) / 8 := by
        rcases hbad with ⟨hm0, hm1⟩
        rw [hm0] at h0
        rw [hm1] at h1
        norm_num at h0 h1
        nlinarith [h1.2]
      norm_num at hTlo hThi
      linarith
  · intro hm
    subst m
    refine ⟨2, by norm_num, ?_⟩
    intro j
    fin_cases j <;> norm_num [SAP.P025b.absoluteCompatible]

