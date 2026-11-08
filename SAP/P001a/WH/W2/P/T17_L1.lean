import SAP.P001a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators Classical

namespace SAP.P001a.WH.W2.P.T17_L1

end SAP.P001a.WH.W2.P.T17_L1

theorem SAP.P001a.WH.W2.T17_L1_proof : SAP.P001a.WH.W2.T17_L1 := by
  constructor
  · intro x z d
    by_cases hx : x ∈ ({-1, 0, 1} : Set ℝ)
    · have hx' : x = -1 ∨ x = 0 ∨ x = 1 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
      rcases hx' with rfl | rfl | rfl
      · by_cases hz₁ : z = -1 <;> by_cases hz₂ : z = 1 <;>
          by_cases hd₁ : d = 1 <;> by_cases hd₀ : d = 0 <;>
          norm_num [fprob, placeboLaw, placeboX, placeboZ, placeboD,
            W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ,
            hz₁, hz₂, hd₁, hd₀, eq_comm]
      · by_cases hz₁ : z = -1 <;> by_cases hz₂ : z = 1 <;>
          by_cases hd₁ : d = 1 <;> by_cases hd₀ : d = 0 <;>
          norm_num [fprob, placeboLaw, placeboX, placeboZ, placeboD,
            W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ,
            hz₁, hz₂, hd₁, hd₀, eq_comm]
      · by_cases hz₁ : z = -1 <;> by_cases hz₂ : z = 1 <;>
          by_cases hd₁ : d = 1 <;> by_cases hd₀ : d = 0 <;>
          norm_num [fprob, placeboLaw, placeboX, placeboZ, placeboD,
            W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ,
            hz₁, hz₂, hd₁, hd₀, eq_comm]
    · have hx1 : x ≠ -1 := by intro h; apply hx; simp [h]
      have hx0 : x ≠ 0 := by intro h; apply hx; simp [h]
      have hx2 : x ≠ 1 := by intro h; apply hx; simp [h]
      norm_num [fprob, placeboLaw, placeboX, placeboZ, placeboD,
        W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ,
        hx1, hx0, hx2, eq_comm]
  · intro x hx w d
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · subst x
      have hden : fprob placeboLaw (fun i => placeboX i = (-1:ℝ)) = 1/3 := by
        norm_num [fprob, placeboLaw, placeboX, Fin.sum_univ_succ]
      have hnum : fprob placeboLaw (fun i => placeboX i = (-1:ℝ) ∧ placeboW i = w ∧ placeboD i = d) =
          (1/3:ℝ) * (if w = (-1:ℝ)^2 - 1/2 ∨ w = (-1:ℝ)^2 + 1/2 then
            (1/2:ℝ) * W2BernoulliMass (W2PlaceboPropensity (-1)) d else 0) := by
        by_cases hw₁ : w = (1:ℝ)/2
        · subst w
          by_cases hd₁ : d = 1
          · subst d
            norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
          · by_cases hd₀ : d = 0
            · subst d
              norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
            · norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hd₁, hd₀]
        · by_cases hw₂ : w = (3:ℝ)/2
          · subst w
            by_cases hd₁ : d = 1
            · subst d
              norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
            · by_cases hd₀ : d = 0
              · subst d
                norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
              · norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hd₁, hd₀]
          ·
            by_cases hd₁ : d = 1
            · subst d
              norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hw₁, hw₂]
            · by_cases hd₀ : d = 0
              · subst d
                norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hw₁, hw₂]
              · norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hw₁, hw₂, hd₁, hd₀]

      rw [hnum, hden]
      split_ifs <;> field_simp <;> ring
    · subst x
      have hden : fprob placeboLaw (fun i => placeboX i = (0:ℝ)) = 1/3 := by
        norm_num [fprob, placeboLaw, placeboX, Fin.sum_univ_succ]
      have hnum : fprob placeboLaw (fun i => placeboX i = (0:ℝ) ∧ placeboW i = w ∧ placeboD i = d) =
          (1/3:ℝ) * (if w = (0:ℝ)^2 - 1/2 ∨ w = (0:ℝ)^2 + 1/2 then
            (1/2:ℝ) * W2BernoulliMass (W2PlaceboPropensity (0:ℝ)) d else 0) := by
        by_cases hw₁ : w = -(1:ℝ)/2
        · subst w
          by_cases hd₁ : d = 1
          · subst d
            norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
          · by_cases hd₀ : d = 0
            · subst d
              norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
            · norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hd₁, hd₀]
        · by_cases hw₂ : w = (1:ℝ)/2
          · subst w
            by_cases hd₁ : d = 1
            · subst d
              norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
            · by_cases hd₀ : d = 0
              · subst d
                norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
              · norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hd₁, hd₀]
          ·
            by_cases hd₁ : d = 1
            · subst d
              norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hw₁, hw₂]
            · by_cases hd₀ : d = 0
              · subst d
                norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hw₁, hw₂]
              · norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hw₁, hw₂, hd₁, hd₀]

      rw [hnum, hden]
      split_ifs <;> field_simp <;> ring
    · subst x
      have hden : fprob placeboLaw (fun i => placeboX i = (1:ℝ)) = 1/3 := by
        norm_num [fprob, placeboLaw, placeboX, Fin.sum_univ_succ]
      have hnum : fprob placeboLaw (fun i => placeboX i = (1:ℝ) ∧ placeboW i = w ∧ placeboD i = d) =
          (1/3:ℝ) * (if w = (1:ℝ)^2 - 1/2 ∨ w = (1:ℝ)^2 + 1/2 then
            (1/2:ℝ) * W2BernoulliMass (W2PlaceboPropensity (1:ℝ)) d else 0) := by
        by_cases hw₁ : w = (1:ℝ)/2
        · subst w
          by_cases hd₁ : d = 1
          · subst d
            norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
          · by_cases hd₀ : d = 0
            · subst d
              norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
            · norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hd₁, hd₀]
        · by_cases hw₂ : w = (3:ℝ)/2
          · subst w
            by_cases hd₁ : d = 1
            · subst d
              norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
            · by_cases hd₀ : d = 0
              · subst d
                norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm]
              · norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hd₁, hd₀]
          ·
            by_cases hd₁ : d = 1
            · subst d
              norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hw₁, hw₂]
            · by_cases hd₀ : d = 0
              · subst d
                norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hw₁, hw₂]
              · norm_num [fprob, placeboLaw, placeboX, placeboW, placeboZ, placeboD, W2BernoulliMass, W2PlaceboPropensity, Fin.sum_univ_succ, eq_comm, hw₁, hw₂, hd₁, hd₀]

      rw [hnum, hden]
      split_ifs <;> field_simp <;> ring
