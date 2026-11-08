import SAP.P025b.WH.W1.Leaves
import AronowAudit.P025.P025_Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b.WH.W1.P.T20_L1

open SAP.P025b
open scoped BigOperators

lemma sum_one_filter_eq {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ i, y i = 0 ∨ y i = 1) :
    (∑ i with y i = 1, (1 : ℝ)) = ∑ i, y i := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hy i with h | h
  · simp [h]
  · simp [h]

lemma sum_zero_filter_eq {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ i, y i = 0 ∨ y i = 1) :
    (∑ i with y i = 0, (1 : ℝ)) = ∑ i, (1-y i) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hy i with h | h
  · simp [h]
  · simp [h]

lemma sum_one_weight_filter_eq {n : ℕ} (y f : Fin n → ℝ)
    (hy : ∀ i, y i = 0 ∨ y i = 1) :
    (∑ i with y i = 1, f i) = ∑ i, f i * y i := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hy i with h | h
  · simp [h]
  · simp [h]

lemma sum_zero_weight_filter_eq {n : ℕ} (y f : Fin n → ℝ)
    (hy : ∀ i, y i = 0 ∨ y i = 1) :
    (∑ i with y i = 0, f i) = ∑ i, f i * (1-y i) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hy i with h | h
  · simp [h]
  · simp [h]

end SAP.P025b.WH.W1.P.T20_L1

open SAP.P025b SAP.P025b.WH.W1.P.T20_L1
open scoped BigOperators

theorem SAP.P025b.WH.W1.T20_L1_proof : SAP.P025b.WH.W1.T20_L1 := by
  intro n hn y hy α β hα hαβ hβ
  let p := populationMean y
  let γ := β / α
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsumY : (∑ i, y i) = (n : ℝ) * p := by
    dsimp [p, populationMean]
    field_simp [hnR.ne']
  have hsumOnes : (∑ i : Fin n, (1 : ℝ)) = (n : ℝ) := by simp
  have hsumComp : (∑ i, (1-y i)) = (n : ℝ) * (1-p) := by
    rw [Finset.sum_sub_distrib, hsumOnes, hsumY]
    ring
  have hcard1 : ((Finset.univ.filter (fun i : Fin n => y i = 1)).card : ℝ) =
      (n : ℝ) * p := by
    calc
      ((Finset.univ.filter (fun i : Fin n => y i = 1)).card : ℝ) =
          ∑ i with y i = 1, (1 : ℝ) := by simp
      _ = ∑ i, y i := sum_one_filter_eq y hy
      _ = (n : ℝ) * p := hsumY
  have hcard0 : ((Finset.univ.filter (fun i : Fin n => y i = 0)).card : ℝ) =
      (n : ℝ) * (1-p) := by
    calc
      ((Finset.univ.filter (fun i : Fin n => y i = 0)).card : ℝ) =
          ∑ i with y i = 0, (1 : ℝ) := by simp
      _ = ∑ i, (1-y i) := sum_zero_filter_eq y hy
      _ = (n : ℝ) * (1-p) := hsumComp
  change ((Finset.univ.filter (fun i : Fin n => y i = 1)).card : ℝ) =
      (n : ℝ) * p ∧
    ((Finset.univ.filter (fun i : Fin n => y i = 0)).card : ℝ) =
      (n : ℝ) * (1-p) ∧
    ∀ w : Fin n → ℝ, weightBox α β w →
      normBox γ (fun i => β*w i) ∧
      ratio y (fun _ => 1) w = binaryClassSum y w β 1 /
        (binaryClassSum y w β 1 + binaryClassSum y w β 0) ∧
      ((n : ℝ)*p ≤ binaryClassSum y w β 1 ∧
        binaryClassSum y w β 1 ≤ γ*((n : ℝ)*p)) ∧
      ((n : ℝ)*(1-p) ≤ binaryClassSum y w β 0 ∧
        binaryClassSum y w β 0 ≤ γ*((n : ℝ)*(1-p))) ∧
      (n : ℝ) ≤ binaryClassSum y w β 1 + binaryClassSum y w β 0 ∧
      0 < binaryClassSum y w β 1 + binaryClassSum y w β 0
  refine ⟨hcard1, hcard0, ?_⟩
  intro w hw
  let u : Fin n → ℝ := fun i => β*w i
  let A : ℝ := binaryClassSum y w β 1
  let C : ℝ := binaryClassSum y w β 0
  have hu : normBox γ u := by
    exact (AronowAudit.P025.normalize_box α β hα hαβ w).1 hw
  have hAform : A = ∑ i, u i * y i := by
    dsimp [A, binaryClassSum, u]
    exact sum_one_weight_filter_eq y (fun i => β*w i) hy
  have hCform : C = ∑ i, u i * (1-y i) := by
    dsimp [C, binaryClassSum, u]
    exact sum_zero_weight_filter_eq y (fun i => β*w i) hy
  have hsumU : (∑ i, u i) = A+C := by
    calc
      (∑ i, u i) = ∑ i, (u i*y i + u i*(1-y i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, u i*y i) + ∑ i, u i*(1-y i) := Finset.sum_add_distrib
      _ = A+C := by rw [← hAform, ← hCform]
  have hratioScaled : ratio y (fun _ => 1) u = A/(A+C) := by
    simp only [ratio, one_mul]
    rw [← hAform, hsumU]
  have hratio : ratio y (fun _ => 1) w = A/(A+C) := by
    calc
      ratio y (fun _ => 1) w = ratio y (fun _ => 1) u := by
        symm
        exact AronowAudit.P025.ratio_scale_weights y (fun _ => 1) w β
          (lt_of_lt_of_le hα hαβ).ne'
      _ = A/(A+C) := hratioScaled
  have hy01 (i : Fin n) : 0 ≤ y i ∧ y i ≤ 1 := by
    rcases hy i with h | h <;> simp [h]
  have hcomp0 (i : Fin n) : 0 ≤ 1-y i := by linarith [(hy01 i).2]
  have hAlo : (n : ℝ)*p ≤ A := by
    calc
      (n : ℝ)*p = ∑ i, y i := hsumY.symm
      _ ≤ A := by
        rw [hAform]
        apply Finset.sum_le_sum
        intro i hi
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hu i).1 (hy01 i).1
  have hAhi : A ≤ γ*((n : ℝ)*p) := by
    calc
      A = ∑ i, u i*y i := hAform
      _ ≤ ∑ i, γ*y i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hu i).2 (hy01 i).1
      _ = γ*((n : ℝ)*p) := by rw [← Finset.mul_sum, hsumY]
  have hClo : (n : ℝ)*(1-p) ≤ C := by
    calc
      (n : ℝ)*(1-p) = ∑ i, (1-y i) := hsumComp.symm
      _ ≤ C := by
        rw [hCform]
        apply Finset.sum_le_sum
        intro i hi
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hu i).1 (hcomp0 i)
  have hChi : C ≤ γ*((n : ℝ)*(1-p)) := by
    calc
      C = ∑ i, u i*(1-y i) := hCform
      _ ≤ ∑ i, γ*(1-y i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hu i).2 (hcomp0 i)
      _ = γ*((n : ℝ)*(1-p)) := by rw [← Finset.mul_sum, hsumComp]
  have hden : (n : ℝ) ≤ A+C := by
    calc
      (n : ℝ) = (n : ℝ)*p + (n : ℝ)*(1-p) := by ring
      _ ≤ A+C := add_le_add hAlo hClo
  refine ⟨hu, hratio, ⟨hAlo, hAhi⟩, ⟨hClo, hChi⟩, hden, ?_⟩
  exact lt_of_lt_of_le hnR hden
