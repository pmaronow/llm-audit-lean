import SAP.P022.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1.P.T6_L4

open SAP.P022 SAP.P022.WH.W1
open scoped BigOperators

lemma coefficient_pos (θ ρ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (i : Fin 8) :
    0 < termRateCoefficient θ ρ i := by
  have hτρ : 0 < θ * ρ := mul_pos hθ hρ
  have h1τρ : 0 < 1 - θ * ρ := by
    have hlt : θ * ρ < θ := by nlinarith [mul_lt_mul_of_pos_left hρ1 hθ]
    linarith
  have h1mρ : 0 < 1 - ρ := by linarith
  have hθmρ : 0 < θ * (1 - ρ) := mul_pos hθ h1mρ
  have hθmρlt : θ * (1 - ρ) < θ := by
    have := mul_lt_mul_of_pos_left (show 1 - ρ < 1 by linarith) hθ
    nlinarith
  have h1θmρ : 0 < 1 - θ * (1 - ρ) := by linarith
  fin_cases i <;> simp [termRateCoefficient] <;> positivity

lemma root_pos (θ ρ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (i : Fin 8) :
    0 < coefficientRoots θ ρ i := by
  unfold coefficientRoots
  exact Real.rpow_pos_of_pos (coefficient_pos θ ρ hθ hθ1 hρ hρ1 i) _

lemma root_cube (θ ρ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (i : Fin 8) :
    (coefficientRoots θ ρ i) ^ 3 = termRateCoefficient θ ρ i := by
  have hc := coefficient_pos θ ρ hθ hθ1 hρ hρ1 i
  unfold coefficientRoots
  rw [← Real.rpow_mul_natCast hc.le (1 / 3 : ℝ) 3]
  norm_num

lemma rootSum_pos (θ ρ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) : 0 < rootSum θ ρ := by
  unfold rootSum
  apply Finset.sum_pos
  · intro i hi
    exact root_pos θ ρ hθ hθ1 hρ hρ1 i
  · exact ⟨0, by simp⟩

lemma optimal_sum (θ ρ s : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hs : 0 < s) :
    (∑ i, optimalAllocation θ ρ s i) = s := by
  unfold optimalAllocation
  have hR : rootSum θ ρ ≠ 0 := (rootSum_pos θ ρ hθ hθ1 hρ hρ1).ne'
  calc
    (∑ i, s * coefficientRoots θ ρ i / rootSum θ ρ) =
        (s / rootSum θ ρ) * (∑ i, coefficientRoots θ ρ i) := by
          simp_rw [div_eq_mul_inv]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = s := by
      field_simp [rootSum, hR]
      rfl

lemma optimal_cost (θ ρ s : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hs : 0 < s) :
    coefficientSum θ ρ (optimalAllocation θ ρ s) = (rootSum θ ρ) ^ 3 / s ^ 2 := by
  have hRpos := rootSum_pos θ ρ hθ hθ1 hρ hρ1
  have hR : rootSum θ ρ ≠ 0 := hRpos.ne'
  have hsi (i : Fin 8) := root_pos θ ρ hθ hθ1 hρ hρ1 i
  unfold coefficientSum
  calc
    (∑ i, termRateCoefficient θ ρ i / (optimalAllocation θ ρ s i) ^ 2) =
        ∑ i, coefficientRoots θ ρ i * ((rootSum θ ρ) ^ 2 / s ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [optimalAllocation, ← root_cube θ ρ hθ hθ1 hρ hρ1]
      have hri := hsi i
      field_simp [hR, hs.ne', hri.ne']
    _ = (rootSum θ ρ) ^ 3 / s ^ 2 := by
      rw [← Finset.sum_mul]
      unfold rootSum
      ring

lemma holder_minimum (r ν : Fin 8 → ℝ) (hr : ∀ i, 0 < r i)
    (hν : ∀ i, 0 < ν i) :
    (∑ i, r i) ^ 3 ≤ (∑ i, (r i) ^ 3 / (ν i) ^ 2) * (∑ i, ν i) ^ 2 := by
  let f : Fin 8 → ℝ := fun i => r i / (ν i ^ (2 / 3 : ℝ))
  let g : Fin 8 → ℝ := fun i => ν i ^ (2 / 3 : ℝ)
  have hgpos (i : Fin 8) : 0 < g i := by
    dsimp [g]
    exact Real.rpow_pos_of_pos (hν i) _
  have hfg (i : Fin 8) : f i * g i = r i := by
    dsimp [f, g]
    exact div_mul_cancel₀ _ (hgpos i).ne'
  have hfpos (i : Fin 8) : 0 < f i := by
    dsimp [f]
    exact div_pos (hr i) (Real.rpow_pos_of_pos (hν i) _)
  have hpowf (i : Fin 8) : (f i) ^ 3 = (r i) ^ 3 / (ν i) ^ 2 := by
    dsimp [f]
    rw [div_pow]
    have hh : (ν i ^ (2 / 3 : ℝ)) ^ 3 = (ν i) ^ 2 := by
      rw [← Real.rpow_mul_natCast (hν i).le (2 / 3 : ℝ) 3]
      norm_num
    rw [hh]
  have hpowg (i : Fin 8) : (g i) ^ (3 / 2 : ℝ) = ν i := by
    dsimp [g]
    rw [← Real.rpow_mul (hν i).le]
    norm_num [Real.rpow_one]
  have hpq : (3 : ℝ).HolderConjugate (3 / 2 : ℝ) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) (f := f) (g := g) hpq
    (fun i hi => (hfpos i).le) (fun i hi => (hgpos i).le)
  have hsum : (∑ i, r i) ≤
      ((∑ i, (r i) ^ 3 / (ν i) ^ 2) ^ (1 / 3 : ℝ)) *
        ((∑ i, ν i) ^ (2 / 3 : ℝ)) := by
    simpa [hfg, hpowf, hpowg] using hh
  have hcpos : 0 < ∑ i, (r i) ^ 3 / (ν i) ^ 2 := by
    apply Finset.sum_pos
    · intro i hi
      exact div_pos (pow_pos (hr i) _) (pow_pos (hν i) _)
    · exact ⟨0, by simp⟩
  have hνsum : 0 < ∑ i, ν i := by
    apply Finset.sum_pos
    · intro i hi
      exact hν i
    · exact ⟨0, by simp⟩
  let X := (∑ i, (r i) ^ 3 / (ν i) ^ 2) ^ (1 / 3 : ℝ) *
    (∑ i, ν i) ^ (2 / 3 : ℝ)
  have hXpos : 0 < X := by dsimp [X]; positivity
  have hcube : (∑ i, r i) ^ 3 ≤ X ^ 3 := by
    have hsum' : ∑ i, r i ≤ X := by simpa [X] using hsum
    have hrSum : 0 ≤ ∑ i, r i := Finset.sum_nonneg fun i hi => (hr i).le
    have hfactor : 0 ≤ X ^ 2 + X * (∑ i, r i) + (∑ i, r i) ^ 2 := by
      positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hsum') hfactor]
  have hXcube : X ^ 3 =
      (∑ i, (r i) ^ 3 / (ν i) ^ 2) * (∑ i, ν i) ^ 2 := by
    dsimp [X]
    rw [mul_pow]
    rw [← Real.rpow_mul_natCast hcpos.le (1 / 3 : ℝ) 3]
    rw [← Real.rpow_mul_natCast hνsum.le (2 / 3 : ℝ) 3]
    norm_num
  rw [hXcube] at hcube
  exact hcube

end SAP.P022.WH.W1.P.T6_L4

open SAP.P022.WH.W1.P.T6_L4

theorem SAP.P022.WH.W1.T6_L4_proof : SAP.P022.WH.W1.T6_L4 := by
  intro θ ρ hθ hθ1 hρ hρ1 s hs
  have hcoeff : ∀ i, 0 < termRateCoefficient θ ρ i :=
    fun i => coefficient_pos θ ρ hθ hθ1 hρ hρ1 i
  have hroot : ∀ i, 0 < coefficientRoots θ ρ i :=
    fun i => root_pos θ ρ hθ hθ1 hρ hρ1 i
  refine ⟨hcoeff, ?_, ?_, ?_, ?_⟩
  · intro i
    unfold optimalAllocation
    exact div_pos (mul_pos hs (hroot i)) (rootSum_pos θ ρ hθ hθ1 hρ hρ1)
  · exact optimal_sum θ ρ s hθ hθ1 hρ hρ1 hs
  · exact optimal_cost θ ρ s hθ hθ1 hρ hρ1 hs
  · intro ν hν hνsum
    have h := holder_minimum (coefficientRoots θ ρ) ν hroot hν
    rw [hνsum] at h
    have hsquare : 0 < s ^ 2 := pow_pos hs _
    have hcost : (∑ i, coefficientRoots θ ρ i ^ 3 / ν i ^ 2) =
        coefficientSum θ ρ ν := by
      unfold coefficientSum
      apply Finset.sum_congr rfl
      intro i hi
      rw [root_cube θ ρ hθ hθ1 hρ hρ1]
    have hfinal : (rootSum θ ρ) ^ 3 / s ^ 2 ≤ coefficientSum θ ρ ν := by
      apply (div_le_iff₀ hsquare).2
      unfold rootSum
      rw [← hcost]
      exact h
    exact hfinal
