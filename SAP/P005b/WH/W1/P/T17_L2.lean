import SAP.P005b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005b.WH.W1.P.T17_L2

open scoped BigOperators Matrix
open Finset SAP.P005b

theorem variance_congr_design {n m : ℕ} (f g : Finset (Fin n) → ℝ)
    (h : ∀ S ∈ design n m, f S = g S) : variance m f = variance m g := by
  have h' : ∀ S ∈ AronowAudit.P005.design n m, f S = g S := by
    simpa [SAP.P005b.design, AronowAudit.P005.design] using h
  have he : SAP.P005b.expectation m f = SAP.P005b.expectation m g := by
    simpa [SAP.P005b.expectation, SAP.P005b.design,
      AronowAudit.P005.expectation, AronowAudit.P005.design] using
      AronowAudit.P005.expectation_congr m _ _ h'
  unfold SAP.P005b.variance
  rw [he]
  apply AronowAudit.P005.expectation_congr
  intro S hS
  rw [h S (by simpa [SAP.P005b.design, AronowAudit.P005.design] using hS)]

theorem principal_singleton_eq_diag {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (hS : S ∈ design n 1) :
    (∑ i ∈ S, ∑ j ∈ S, Q i j) = ∑ i ∈ S, Q i i := by
  have hc : S.card = 1 := (Finset.mem_powersetCard.mp hS).2
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
  simp

theorem singleton_variance_bound {n : ℕ} (hn : 0 < n)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    variance 1 (fun S => ∑ i ∈ S, ∑ j ∈ S, Q i j) ≤
      (1 / (n : ℝ)) * (∑ i, ∑ j, (Q i j)^2) := by
  let d : Fin n → ℝ := fun i => Q i i
  let g : Finset (Fin n) → ℝ := fun S => ∑ i ∈ S, d i
  have hcongr : ∀ S ∈ design n 1,
      (∑ i ∈ S, ∑ j ∈ S, Q i j) = g S := by
    intro S hS
    exact SAP.P005b.WH.W1.P.T17_L2.principal_singleton_eq_diag Q S hS
  rw [SAP.P005b.WH.W1.P.T17_L2.variance_congr_design _ _ hcongr]
  calc
    variance 1 g ≤ expectation 1 (fun S => (g S)^2) := by
      have h := AronowAudit.P005.Wave1.t4_variance_le_second (n := n) (m := 1) (by omega) g
      simpa [SAP.P005b.variance, SAP.P005b.expectation, SAP.P005b.design,
        AronowAudit.P005.variance, AronowAudit.P005.expectation,
        AronowAudit.P005.design] using h
    _ = (∑ i, (Q i i)^2) / (n : ℝ) := by
      classical
      simp [expectation, design, g, d, Finset.powersetCard_one]
    _ ≤ (1 / (n : ℝ)) * (∑ i, ∑ j, (Q i j)^2) := by
      have hdiag : (∑ i, (Q i i)^2) ≤ ∑ i, ∑ j, (Q i j)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.single_le_sum (fun j hj => sq_nonneg (Q i j)) (Finset.mem_univ i)
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_right hdiag (inv_nonneg.mpr hnR.le)]

theorem principal_eq_complement_diag_three
    (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hr : ∀ i, (∑ j, Q i j) = 0) (hc : ∀ j, (∑ i, Q i j) = 0)
    (S : Finset (Fin 3)) (hS : S.card = 2) :
    (∑ i ∈ S, ∑ j ∈ S, Q i j) = ∑ i ∈ AronowAudit.P005.control S, Q i i := by
  classical
  have r0 := hr (0 : Fin 3)
  have r1 := hr (1 : Fin 3)
  have r2 := hr (2 : Fin 3)
  have c0 := hc (0 : Fin 3)
  have c1 := hc (1 : Fin 3)
  have c2 := hc (2 : Fin 3)
  norm_num [Fin.sum_univ_succ] at r0 r1 r2 c0 c1 c2
  have hdiag : (∑ i : Fin 3, Q i i) = Q 0 0 + Q 1 1 + Q 2 2 := by
    simp [Fin.sum_univ_succ]
    ring
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hS
  fin_cases i <;> fin_cases j <;> simp_all [AronowAudit.P005.control] <;> simp only [hdiag] at * <;> linarith

end SAP.P005b.WH.W1.P.T17_L2

open scoped BigOperators Matrix
open Finset SAP.P005b

theorem SAP.P005b.WH.W1.T17_L2_proof : SAP.P005b.WH.W1.T17_L2 := by
  intro n m hn hn4 hm hmn Q hr hc
  have hn_cases : n = 2 ∨ n = 3 := by omega
  rcases hn_cases with rfl | rfl
  · have hm1 : m = 1 := by omega
    subst m
    have h := SAP.P005b.WH.W1.P.T17_L2.singleton_variance_bound (n := 2) (by omega) Q
    norm_num at h ⊢
    nlinarith
  · have hm_cases : m = 1 ∨ m = 2 := by omega
    rcases hm_cases with rfl | rfl
    · have h := SAP.P005b.WH.W1.P.T17_L2.singleton_variance_bound (n := 3) (by omega) Q
      norm_num at h ⊢
      nlinarith
    · let f : Finset (Fin 3) → ℝ := fun S => ∑ i ∈ S, ∑ j ∈ S, Q i j
      let g : Finset (Fin 3) → ℝ := fun S => ∑ i ∈ S, Q i i
      have hcongr : ∀ S ∈ design 3 2, f S = g (AronowAudit.P005.control S) := by
        intro S hS
        exact SAP.P005b.WH.W1.P.T17_L2.principal_eq_complement_diag_three Q hr hc S
          ((Finset.mem_powersetCard.mp hS).2)
      calc
        variance 2 f = variance 2 (fun S => g (AronowAudit.P005.control S)) :=
          SAP.P005b.WH.W1.P.T17_L2.variance_congr_design _ _ hcongr
        _ = variance 1 g := by
          have h := AronowAudit.P005.Wave1.t4_complement_variance
            (n := 3) (m := 2) (by omega) g
          simpa [SAP.P005b.variance, SAP.P005b.expectation, SAP.P005b.design,
            AronowAudit.P005.variance, AronowAudit.P005.expectation,
            AronowAudit.P005.design, SAP.P005b.control,
            AronowAudit.P005.control] using h
        _ ≤ (1 / (3 : ℝ)) * (∑ i, ∑ j, (Q i j)^2) := by
          have hs : variance 1 g = variance 1 (fun S => ∑ i ∈ S, ∑ j ∈ S, Q i j) := by
            apply SAP.P005b.WH.W1.P.T17_L2.variance_congr_design
            intro S hS
            symm
            exact SAP.P005b.WH.W1.P.T17_L2.principal_singleton_eq_diag Q S hS
          rw [hs]
          have hh := SAP.P005b.WH.W1.P.T17_L2.singleton_variance_bound (n := 3) (by omega) Q
          exact hh
        _ = (2 : ℝ) * (3 - 2) / ((3 : ℝ) * (3 - 1)) *
              (∑ i, ∑ j, (Q i j)^2) := by norm_num

