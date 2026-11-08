import SAP.P002a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P002a.WH.W3.P.T6_L2

open SAP.P002a
open scoped BigOperators
noncomputable section

private theorem mean_add {n : ℕ} (f g : Fin n → ℝ) :
    mean (fun i => f i + g i) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, add_div]

private theorem mean_sub {n : ℕ} (f g : Fin n → ℝ) :
    mean (fun i => f i - g i) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

private theorem mean_mul {n : ℕ} (c : ℝ) (f : Fin n → ℝ) :
    mean (fun i => c * f i) = c * mean f := by
  simp only [mean, ← Finset.mul_sum]
  ring

private theorem mean_const {n : ℕ} (hn : 0 < n) (c : ℝ) :
    mean (fun _ : Fin n => c) = c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [mean, hn0]

private theorem mean_nonneg {n : ℕ} (_hn : 0 < n) {f : Fin n → ℝ}
    (hf : ∀ i, 0 ≤ f i) : 0 ≤ mean f := by
  unfold mean
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i hi => hf i)
  · exact_mod_cast (Nat.zero_le n)

private def gridU (m : ℕ) (j : Fin m) : ℝ :=
  t6Grid m j ^ 2 - t6V m

private def gridY (m : ℕ) (j : Fin m) : ℝ :=
  t6Grid m j + (1 / 10 : ℝ) * gridU m j

private theorem grid_aux (m : ℕ) (hm : 0 < m) (hg : T6GridFacts m) :
    mean (gridU m) = 0 ∧
    mean (fun j => t6Grid m j * gridU m j) = 0 ∧
    mean (gridY m) = 0 ∧
    mean (fun j => t6Grid m j * gridY m j) = t6V m ∧
    t6V m ≤ mean (fun j => gridY m j ^ 2) ∧
    (∀ j, |gridU m j| ≤ 1) ∧ (∀ j, |gridY m j| ≤ 11 / 10) := by
  have h1 : mean (t6Grid m) = 0 := hg.1
  have h2 : mean (fun j => t6Grid m j ^ 2) = t6V m := hg.2.1
  have h3 : mean (fun j => t6Grid m j ^ 3) = 0 := hg.2.2.1
  have hb : ∀ j, |t6Grid m j| ≤ 1 := hg.2.2.2.1
  have hu : mean (gridU m) = 0 := by
    change mean (fun j => t6Grid m j ^ 2 - t6V m) = 0
    rw [mean_sub, mean_const hm, h2]
    ring
  have htu : mean (fun j => t6Grid m j * gridU m j) = 0 := by
    have he : (fun j => t6Grid m j * gridU m j) =
        (fun j => t6Grid m j ^ 3 - t6V m * t6Grid m j) := by
      funext j
      dsimp [gridU]
      ring
    rw [he, mean_sub, mean_mul, h3, h1]
    ring
  have hy : mean (gridY m) = 0 := by
    change mean (fun j => t6Grid m j + (1 / 10 : ℝ) * gridU m j) = 0
    rw [mean_add, mean_mul, h1, hu]
    ring
  have hty : mean (fun j => t6Grid m j * gridY m j) = t6V m := by
    have he : (fun j => t6Grid m j * gridY m j) =
        (fun j => t6Grid m j ^ 2 + (1 / 10 : ℝ) * (t6Grid m j * gridU m j)) := by
      funext j
      dsimp [gridY]
      ring
    rw [he, mean_add, mean_mul, h2, htu]
    ring
  have hy2 : t6V m ≤ mean (fun j => gridY m j ^ 2) := by
    have he : (fun j => gridY m j ^ 2) =
        (fun j => (t6Grid m j ^ 2 + (1 / 5 : ℝ) * (t6Grid m j * gridU m j)) +
          (1 / 100 : ℝ) * gridU m j ^ 2) := by
      funext j
      dsimp [gridY]
      ring
    rw [he, mean_add, mean_add, mean_mul, mean_mul, h2, htu]
    have hsq : 0 ≤ mean (fun j => gridU m j ^ 2) :=
      mean_nonneg hm (fun j => sq_nonneg (gridU m j))
    nlinarith
  have hub : ∀ j, |gridU m j| ≤ 1 := by
    intro j
    have ht := hb j
    have ht2 : t6Grid m j ^ 2 ≤ 1 := by
      have hab := abs_le.mp ht
      nlinarith [sq_nonneg (t6Grid m j - 1),
        mul_nonneg (by linarith : 0 ≤ 1 - t6Grid m j)
          (by linarith : 0 ≤ 1 + t6Grid m j)]
    rw [abs_le]
    change -1 ≤ t6Grid m j ^ 2 - t6V m ∧ t6Grid m j ^ 2 - t6V m ≤ 1
    constructor
    · have hv := hg.2.2.2.2.2
      nlinarith [sq_nonneg (t6Grid m j)]
    · have hv := hg.2.2.2.2.1
      nlinarith [sq_nonneg (t6Grid m j)]
  refine ⟨hu, htu, hy, hty, hy2, hub, ?_⟩
  intro j
  calc
    |gridY m j| ≤ |t6Grid m j| + |(1 / 10 : ℝ) * gridU m j| := abs_add_le _ _
    _ ≤ 11 / 10 := by
      rw [abs_mul]
      norm_num
      linarith [hb j, hub j]

private def evenSign (m : ℕ) (i : Fin (2 * m)) : ℝ :=
  if i.val < m then 1 else -1

private def evenX (m : ℕ) (i : Fin (2 * m)) : ℝ :=
  evenSign m i + t6Eta m * t6T m i

private def evenY (m : ℕ) (i : Fin (2 * m)) : ℝ :=
  t6T m i + (1 / 10 : ℝ) * (t6T m i ^ 2 - t6V m)

theorem model_X (m : ℕ) : t6X m = evenX m := by
  funext i
  rfl

theorem model_Y (m : ℕ) : t6Y m = evenY m := by
  funext i
  rfl

private theorem even_sum (m : ℕ) (F : ℝ → ℝ → ℝ) :
    (∑ i, F (evenSign m i) (t6T m i)) =
      (∑ j : Fin m, F 1 (t6Grid m j)) + (∑ j : Fin m, F (-1) (t6Grid m j)) := by
  simp only [evenSign, t6T, t6Grid]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    F (if j < m then 1 else -1) ((2 * (j % m : ℕ) - (m : ℝ) + 1) / ((m : ℝ) - 1)))]
  rw [two_mul, Finset.sum_range_add]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
      F 1 ((2 * (j : ℝ) - (m : ℝ) + 1) / ((m : ℝ) - 1))),
    Fin.sum_univ_eq_sum_range (fun j =>
      F (-1) ((2 * (j : ℝ) - (m : ℝ) + 1) / ((m : ℝ) - 1)))]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjm := Finset.mem_range.mp hj
    simp [hjm, Nat.mod_eq_of_lt hjm]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjm := Finset.mem_range.mp hj
    have hnot : ¬ m + j < m := by omega
    simp [hnot, Nat.mod_eq_of_lt hjm]

private theorem even_mean (m : ℕ) (F : ℝ → ℝ → ℝ) :
    mean (fun i => F (evenSign m i) (t6T m i)) =
      (mean (fun j : Fin m => F 1 (t6Grid m j)) +
        mean (fun j : Fin m => F (-1) (t6Grid m j))) / 2 := by
  simp only [mean, even_sum, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem even_reduce (m : ℕ) (F : ℝ → ℝ → ℝ) (G : ℝ → ℝ)
    (h : ∀ t, (F 1 t + F (-1) t) / 2 = G t) :
    mean (fun i => F (evenSign m i) (t6T m i)) = mean (fun j => G (t6Grid m j)) := by
  rw [even_mean]
  calc
    _ = mean (fun j => (F 1 (t6Grid m j) + F (-1) (t6Grid m j)) / 2) := by
      simp only [mean, Finset.sum_add_distrib, ← Finset.sum_div]
      ring
    _ = _ := by congr 1; funext j; exact h _

private theorem eta_bounds (m : ℕ) (hm : 4 ≤ m) :
    0 < t6Eta m ∧ t6Eta m ≤ 1 / 4 := by
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ ((2 * m) ^ 2) := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  unfold t6Eta
  constructor
  · positivity
  · exact (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by nlinarith)

private theorem t_bound (m : ℕ) (hm : 0 < m) (hg : T6GridFacts m)
    (i : Fin (2 * m)) : |t6T m i| ≤ 1 := by
  have hmod : i.val % m < m := Nat.mod_lt _ hm
  exact hg.2.2.2.1 ⟨i.val % m, hmod⟩

theorem even_moments (m : ℕ) (hm : 4 ≤ m) (hg : T6GridFacts m) :
    mean (evenX m) = 0 ∧ mean (evenY m) = 0 ∧
    mean (fun i => evenX m i ^ 2) = 1 + t6Eta m ^ 2 * t6V m ∧
    mean (fun i => evenX m i * evenY m i) = t6Eta m * t6V m ∧
    t6V m ≤ mean (fun i => evenY m i ^ 2) := by
  have hm0 : 0 < m := by omega
  have h1 : mean (t6Grid m) = 0 := hg.1
  have h2 : mean (fun j => t6Grid m j ^ 2) = t6V m := hg.2.1
  obtain ⟨hu, htu, hy, hty, hy2, hub, hyb⟩ := grid_aux m hm0 hg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change mean (fun i => evenSign m i + t6Eta m * t6T m i) = 0
    rw [even_reduce m (fun s t => s + t6Eta m * t)
      (fun t => t6Eta m * t) (by intro t; ring), mean_mul, h1]
    ring
  · change mean (fun i => t6T m i + (1 / 10 : ℝ) * (t6T m i ^ 2 - t6V m)) = 0
    rw [even_reduce m (fun _ t => t + (1 / 10 : ℝ) * (t ^ 2 - t6V m))
      (fun t => t + (1 / 10 : ℝ) * (t ^ 2 - t6V m)) (by intro t; ring)]
    exact hy
  · change mean (fun i => (evenSign m i + t6Eta m * t6T m i) ^ 2) = _
    rw [even_reduce m (fun s t => (s + t6Eta m * t) ^ 2)
      (fun t => 1 + t6Eta m ^ 2 * t ^ 2) (by intro t; ring),
      mean_add, mean_const hm0, mean_mul, h2]
  · change mean (fun i => (evenSign m i + t6Eta m * t6T m i) *
      (t6T m i + (1 / 10 : ℝ) * (t6T m i ^ 2 - t6V m))) = _
    rw [even_reduce m
      (fun s t => (s + t6Eta m * t) * (t + (1 / 10 : ℝ) * (t ^ 2 - t6V m)))
      (fun t => t6Eta m * (t * (t + (1 / 10 : ℝ) * (t ^ 2 - t6V m))))
      (by intro t; ring), mean_mul]
    change t6Eta m * mean (fun j => t6Grid m j * gridY m j) = _
    rw [hty]
  · change mean (fun i => (t6T m i + (1 / 10 : ℝ) * (t6T m i ^ 2 - t6V m)) ^ 2) ≥ _
    rw [even_reduce m
      (fun _ t => (t + (1 / 10 : ℝ) * (t ^ 2 - t6V m)) ^ 2)
      (fun t => (t + (1 / 10 : ℝ) * (t ^ 2 - t6V m)) ^ 2)
      (by intro t; ring)]
    exact hy2

theorem even_bounds (m : ℕ) (hm : 4 ≤ m) (hg : T6GridFacts m) :
    (∀ i, |evenX m i| ≤ 5 / 4) ∧ (∀ i, |evenY m i| ≤ 11 / 10) := by
  obtain ⟨he0, he1⟩ := eta_bounds m hm
  have hm0 : 0 < m := by omega
  have hsign (i : Fin (2 * m)) : |evenSign m i| = 1 := by
    by_cases hi : i.val < m <;> simp [evenSign, hi]
  constructor
  · intro i
    calc
      |evenX m i| ≤ |evenSign m i| + |t6Eta m * t6T m i| := abs_add_le _ _
      _ ≤ 5 / 4 := by
        rw [hsign i, abs_mul, abs_of_pos he0]
        have ht := t_bound m hm0 hg i
        nlinarith
  · intro i
    obtain ⟨_, _, _, _, _, _, hyb⟩ := grid_aux m hm0 hg
    exact hyb ⟨i.val % m, Nat.mod_lt _ hm0⟩

end
end SAP.P002a.WH.W3.P.T6_L2

theorem SAP.P002a.WH.W3.T6_L2_proof : SAP.P002a.WH.W3.T6_L2 := by
  intro m hm hg
  obtain ⟨hx, hy, hx2, hxy, hy2⟩ :=
    SAP.P002a.WH.W3.P.T6_L2.even_moments m hm hg
  obtain ⟨hxb, hyb⟩ := SAP.P002a.WH.W3.P.T6_L2.even_bounds m hm hg
  simpa only [SAP.P002a.WH.W3.P.T6_L2.model_X,
    SAP.P002a.WH.W3.P.T6_L2.model_Y] using ⟨hx, hy, hx2, hxy, hy2, hxb, hyb⟩
