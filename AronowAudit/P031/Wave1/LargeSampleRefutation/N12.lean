import AronowAudit.P031.Wave1.LargeSampleRefutationBlueprint
import AronowAudit.P031.Wave1.LargeSampleRefutation.N1

/-!
Assemble the exact pair standardization, the with-replacement comparison, and
the coin CDF limit. All probabilistic inputs are precisely the premises of N12.
-/

namespace AronowAudit.P031.Wave1.LargeSampleRefutation
noncomputable section
open scoped BigOperators Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem n12_proof : N12 := by
  intro hV hPair hCount hCoin hCylinder hTransfer hStd hContinuous
  refine ⟨Eventually.of_forall (fun n => ?_), ?_⟩
  · have hN16 : (16 : ℝ) ≤ (hcN n : ℝ) := by exact_mod_cast hcN_ge n
    have hN0 : 0 < (hcN n : ℝ) := by linarith
    have hN1 : 0 < (hcN n : ℝ) - 1 := by linarith
    rw [(hV n).1]
    apply div_pos
    · linarith
    · positivity
  · intro x
    let F : ℕ → ℝ := fun n => eventProbability (hypercubePopulation n) (fun s =>
      (pointEstimate (hypercubePopulation n) s - populationEffect (hypercubePopulation n)) /
        Real.sqrt (trueVariance (hypercubePopulation n)) ≤ x)
    let G : ℕ → ℝ → ℝ := fun m y =>
      ((Finset.univ.filter (fun v : Fin m → Fin 2 =>
        (Real.sqrt m)⁻¹ * ∑ j, sgn2 (v j) ≤ y)).card : ℝ) / 2 ^ m
    let c : ℕ → ℝ := fun n => Real.sqrt (((hcN n : ℝ) - 2) / ((hcN n : ℝ) - 1))
    let E : ℕ → ℝ → Prop := fun n z => z / Real.sqrt 2 ≤ c n * x
    have hN : Tendsto hcN atTop atTop := n1_proof
    have hPhi : Tendsto (fun n => 2 * hcK n) atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_) tendsto_id
      dsimp [hcK]
      nlinarith
    have hInvN : Tendsto (fun n => 1 / (hcN n : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp hN
    have hInvNm1 : Tendsto (fun n => 1 / ((hcN n : ℝ) - 1)) atTop (nhds 0) := by
      have hNm1 : Tendsto (fun n => hcN n - 1) atTop atTop :=
        (tendsto_sub_atTop_nat 1).comp hN
      have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hNm1
      refine h.congr (fun n => ?_)
      dsimp only [Function.comp_def]
      rw [Nat.cast_sub (by have := hcN_ge n; omega : 1 ≤ hcN n), Nat.cast_one]
    have hRatio : Tendsto (fun n => ((hcN n : ℝ) - 2) / ((hcN n : ℝ) - 1))
        atTop (nhds 1) := by
      have h : Tendsto (fun n => 1 - 1 / ((hcN n : ℝ) - 1))
          atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hInvNm1
      simp only [sub_zero] at h
      refine h.congr (fun n => ?_)
      have hN16 : (16 : ℝ) ≤ (hcN n : ℝ) := by exact_mod_cast hcN_ge n
      have hN1 : (hcN n : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hN1] <;> ring
    have hC : Tendsto c atTop (nhds 1) := by
      simpa only [Real.sqrt_one] using hRatio.sqrt
    have hMono : ∀ m, Monotone (G m) := by
      intro m a b hab
      dsimp [G]
      apply div_le_div_of_nonneg_right ?_ (by positivity)
      have hsub : (Finset.univ.filter (fun v : Fin m → Fin 2 =>
          (Real.sqrt m)⁻¹ * ∑ j, sgn2 (v j) ≤ a)) ⊆
          Finset.univ.filter (fun v : Fin m → Fin 2 =>
            (Real.sqrt m)⁻¹ * ∑ j, sgn2 (v j) ≤ b) := by
        intro v hv
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hv).2).trans hab⟩
      exact_mod_cast Finset.card_le_card hsub
    have hG : ∀ y, Tendsto (fun m => G m y) atTop (nhds (normalCDF y)) := by
      intro y
      exact (hCoin y).congr (fun m => hCylinder m y)
    have hSqrt (n : ℕ) : Real.sqrt ((2 * hcK n : ℕ) : ℝ) =
        2 * ((n : ℝ) + 1) * Real.sqrt 2 := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
      norm_num [hcK, mul_pow, Real.sq_sqrt] <;> ring
    have hNorm (n : ℕ) (z : ℝ) :
        (z / (2 * ((n : ℝ) + 1))) / Real.sqrt 2 =
          (Real.sqrt ((2 * hcK n : ℕ) : ℝ))⁻¹ * z := by
      rw [hSqrt n]
      field_simp [show (n : ℝ) + 1 ≠ 0 by positivity,
        show Real.sqrt 2 ≠ 0 by positivity] <;> ring
    have hDen (n : ℕ) : (hcN n : ℝ) ^ 2 = (2 : ℝ) ^ (2 * hcK n) := by
      calc
        (hcN n : ℝ) ^ 2 = ((2 : ℝ) ^ hcK n) ^ 2 := by simp [hcN]
        _ = (2 : ℝ) ^ (hcK n * 2) := (pow_mul _ _ _).symm
        _ = (2 : ℝ) ^ (2 * hcK n) := by rw [Nat.mul_comm (hcK n) 2]
    have hThreshold (n : ℕ) (z : ℝ) :
        z / Real.sqrt 2 * Real.sqrt (((hcN n : ℝ) - 1) / ((hcN n : ℝ) - 2)) ≤ x ↔
          E n z := by
      have hN16 : (16 : ℝ) ≤ (hcN n : ℝ) := by exact_mod_cast hcN_ge n
      have hN1 : 0 < (hcN n : ℝ) - 1 := by linarith
      have hN2 : 0 < (hcN n : ℝ) - 2 := by linarith
      have ha : 0 < Real.sqrt (((hcN n : ℝ) - 1) / ((hcN n : ℝ) - 2)) :=
        Real.sqrt_pos.mpr (div_pos hN1 hN2)
      have hInv : (Real.sqrt (((hcN n : ℝ) - 1) / ((hcN n : ℝ) - 2)))⁻¹ = c n := by
        rw [← Real.sqrt_inv]
        dsimp [c]
        rw [inv_div]
      have hx : x / Real.sqrt (((hcN n : ℝ) - 1) / ((hcN n : ℝ) - 2)) = c n * x := by
        rw [div_eq_mul_inv, hInv]
        ring
      change (_ ≤ x) ↔ z / Real.sqrt 2 ≤ c n * x
      rw [← le_div_iff₀ ha, hx]
    have hEvent (n : ℕ) (s : Finset (Fin (hypercubePopulation n).N))
        (hs : s ∈ (Finset.univ).powersetCard (hypercubePopulation n).M) :
        ((pointEstimate (hypercubePopulation n) s - populationEffect (hypercubePopulation n)) /
          Real.sqrt (trueVariance (hypercubePopulation n)) ≤ x) ↔
          ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ E n (hcQ n i + hcQ n j) := by
      change Finset (Fin (hcN n)) at s
      rw [hStd n s hs]
      change ((∑ i ∈ s, hcQ n i) / Real.sqrt 2 *
        Real.sqrt (((hcN n : ℝ) - 1) / ((hcN n : ℝ) - 2)) ≤ x) ↔
        ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ E n (hcQ n i + hcQ n j)
      have hcard : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
      obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
      have hsum : (∑ a ∈ ({i, j} : Finset (Fin (hcN n))), hcQ n a) =
          hcQ n i + hcQ n j := by simp [hij, hij.symm]
      rw [hsum, hThreshold n (hcQ n i + hcQ n j)]
      constructor
      · intro h
        exact ⟨i, by simp, j, by simp, hij, h⟩
      · rintro ⟨a, ha, b, hb, hab, h⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact (hab rfl).elim
        · exact h
        · simpa only [add_comm] using h
        · exact (hab rfl).elim
    have hProb (n : ℕ) : F n = eventProbability (hypercubePopulation n)
        (fun s => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ E n (hcQ n i + hcQ n j)) := by
      dsimp [F]
      unfold eventProbability
      apply expectation_congr
      intro s hs
      simp only [hEvent n s hs]
      congr
    have hFrequency (n : ℕ) :
        ((Finset.univ.filter (fun ij : Fin (hcN n) × Fin (hcN n) =>
          E n (hcQ n ij.1 + hcQ n ij.2))).card : ℝ) / (hcN n : ℝ) ^ 2 =
            G (2 * hcK n) (c n * x) := by
      have hsets :
          (Finset.univ.filter (fun v : Fin (2 * hcK n) → Fin 2 =>
            E n ((∑ j, sgn2 (v j)) / (2 * ((n : ℝ) + 1))))) =
          Finset.univ.filter (fun v : Fin (2 * hcK n) → Fin 2 =>
            (Real.sqrt ((2 * hcK n : ℕ) : ℝ))⁻¹ * ∑ j, sgn2 (v j) ≤ c n * x) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change ((∑ j, sgn2 (v j)) / (2 * ((n : ℝ) + 1))) / Real.sqrt 2 ≤ c n * x ↔ _
        rw [hNorm n (∑ j, sgn2 (v j))]
      rw [hCount n (E n), hsets, hDen n] <;> rfl
    apply hTransfer F G normalCDF (fun n => 2 * hcK n) c
      (fun n => 1 / (hcN n : ℝ)) x hMono (hContinuous x) hG hPhi hC hInvN
    intro n
    rw [hProb n, ← hFrequency n]
    exact hPair (hypercubePopulation n)
      (fun i j => E n (hcQ n i + hcQ n j)) rfl
      (fun i j h => by simpa only [add_comm] using h)

end
end AronowAudit.P031.Wave1.LargeSampleRefutation
