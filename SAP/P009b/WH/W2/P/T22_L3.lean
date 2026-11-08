import SAP.P009b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter

namespace SAP.P009b.WH.W2.P.T22_L3

end SAP.P009b.WH.W2.P.T22_L3

theorem SAP.P009b.WH.W2.T22_L3_proof : SAP.P009b.WH.W2.T22_L3 := by
  intro ell hell
  obtain ⟨M, hM⟩ := exists_nat_ge (max (1 : ℝ) (max ell ell⁻¹))
  have hMone : (1 : ℝ) ≤ (M : ℝ) := le_trans (le_max_left _ _) hM
  have hOuter : max ell ell⁻¹ ≤ max (1 : ℝ) (max ell ell⁻¹) := le_max_right _ _
  have hMell : ell ≤ (M : ℝ) :=
    le_trans (le_max_left _ _) (le_trans hOuter hM)
  have hMinv : ell⁻¹ ≤ (M : ℝ) :=
    le_trans (le_max_right _ _) (le_trans hOuter hM)
  have hMpos : 0 < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hMone)
  have hellM : 1 ≤ ell * (M : ℝ) := by
    calc
      1 = ell * ell⁻¹ := by field_simp
      _ ≤ ell * (M : ℝ) := mul_le_mul_of_nonneg_left hMinv hell.le
  let N : ℕ → ℕ := fun t => (t + M) ^ 2
  let a : ℕ → ℝ := fun t => ell * ((t + M : ℕ) : ℝ)
  refine ⟨N, a, ?_, ?_, ?_, ?_⟩
  · intro t
    dsimp [N]
    positivity
  · apply tendsto_atTop_mono (f := fun t : ℕ => t) (g := N) ?_ tendsto_id
    intro t
    dsimp [N]
    exact (Nat.le_add_right t M).trans (by simpa [pow_two] using Nat.le_mul_self (t + M))
  · intro t
    constructor
    · have hlow : 1 ≤ a t := by
        dsimp [a]
        calc
          1 ≤ ell * (M : ℝ) := hellM
          _ ≤ ell * ((t + M : ℕ) : ℝ) := by
            apply mul_le_mul_of_nonneg_left
            · exact_mod_cast (Nat.le_add_left M t)
            · exact hell.le
      exact Nat.floor_pos.mpr hlow
    · have hup : a t ≤ (N t : ℝ) := by
        dsimp [a, N]
        calc
          ell * ((t + M : ℕ) : ℝ) ≤ (M : ℝ) * ((t + M : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hMell (by positivity)
          _ ≤ ((t + M : ℕ) : ℝ) ^ 2 := by
            calc
              (M : ℝ) * ((t + M : ℕ) : ℝ) ≤
                  ((t + M : ℕ) : ℝ) * ((t + M : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_right
                  (by exact_mod_cast (Nat.le_add_left M t)) (by positivity)
              _ = ((t + M : ℕ) : ℝ) ^ 2 := by rw [pow_two]
          _ = (((t + M) ^ 2 : ℕ) : ℝ) := by simp
      exact Nat.floor_le_of_le hup
  · have hratio : ∀ t, a t / Real.sqrt (N t : ℝ) = ell := by
      intro t
      dsimp [a, N]
      rw [Nat.cast_pow, Real.sqrt_sq (by positivity : 0 ≤ ((t + M : ℕ) : ℝ))]
      field_simp
    have hfun : (fun t => a t / Real.sqrt (N t : ℝ)) = fun _ => ell := by
      funext t
      exact hratio t
    rw [hfun]
    exact tendsto_const_nhds

