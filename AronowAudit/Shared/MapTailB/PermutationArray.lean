import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.PermutationMarginals
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.SteinMethod
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Finite exchangeable pairs for permutation arrays

The auxiliary space consists of all ordered pairs of positions, including the diagonal.
A diagonal pair makes no change. This convention gives regression coefficient `2 / N`
and the same normalized conditional square increment as distinct-pair sampling.
-/

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

namespace AronowAudit.MapTailB.PermutationArray

variable {N : ℕ}

/-- Uniform finite expectation, expressed without a measure. -/
noncomputable def average {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

theorem average_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_const_mul {α : Type*} [Fintype α] (a : ℝ) (f : α → ℝ) :
    average (fun x => a * f x) = a * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_const {α : Type*} [Fintype α] [Nonempty α] (a : ℝ) :
    average (fun _ : α => a) = a := by
  have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, h]

theorem average_nonneg {α : Type*} [Fintype α] {f : α → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ average f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun x _ => h x)

theorem average_mono {α : Type*} [Fintype α] {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    average f ≤ average g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem average_sum {α ι : Type*} [Fintype α] [Fintype ι] (f : ι → α → ℝ) :
    average (fun x => ∑ i, f i x) = ∑ i, average (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The array statistic. -/
noncomputable def statistic (c : Matrix (Fin N) (Fin N) ℝ)
    (π : Equiv.Perm (Fin N)) : ℝ := ∑ i, c i (π i)

/-- The statistic after transposing two positions. -/
noncomputable def swapped (c : Matrix (Fin N) (Fin N) ℝ)
    (π : Equiv.Perm (Fin N)) (k : Fin N × Fin N) : ℝ :=
  statistic c (π * Equiv.swap k.1 k.2)

/-- The rectangle increment associated with two positions. -/
noncomputable def rectangle (b : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) : ℝ :=
  b i j + b j i - b i i - b j j

/-- Total squared entries. -/
noncomputable def energy (c : Matrix (Fin N) (Fin N) ℝ) : ℝ := ∑ i, ∑ j, (c i j)^2

/-- Sum of the selected squared entries. -/
noncomputable def selectedEnergy (c : Matrix (Fin N) (Fin N) ℝ)
    (π : Equiv.Perm (Fin N)) : ℝ := ∑ i, (c i (π i))^2

/-- The crossed quadratic statistic. -/
noncomputable def traceSquare (b : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, b i j * b j i

noncomputable def crossed (c : Matrix (Fin N) (Fin N) ℝ)
    (π : Equiv.Perm (Fin N)) : ℝ := traceSquare (fun i j => c i (π j))

theorem swapped_sub (c : Matrix (Fin N) (Fin N) ℝ) (π : Equiv.Perm (Fin N))
    (i j : Fin N) :
    swapped c π (i,j) - statistic c π = rectangle (fun a b => c a (π b)) i j := by
  classical
  by_cases hij : i = j
  · subst j
    simp [swapped, statistic, rectangle, Equiv.Perm.mul_apply]
  have hterm : ∀ a : Fin N,
      c a (π (Equiv.swap i j a)) = c a (π a) +
        (if a = i then c i (π j) - c i (π i) else 0) +
        (if a = j then c j (π i) - c j (π j) else 0) := by
    intro a
    by_cases hai : a = i
    · subst a; simp [hij]
    by_cases haj : a = j
    · subst a; simp [hij, Ne.symm hij]
    simp [Equiv.swap_apply_of_ne_of_ne hai haj, hai, haj]
  unfold swapped statistic
  simp only [Equiv.Perm.mul_apply]
  rw [Finset.sum_congr rfl fun a _ => hterm a]
  simp [Finset.sum_add_distrib, rectangle]
  ring

/-- Exchangeability holds for every statistic on the permutation group. -/
theorem transposition_exchangeable (W : Equiv.Perm (Fin N) → ℝ) (F : ℝ → ℝ → ℝ) :
    (∑ π : Equiv.Perm (Fin N), ∑ k : Fin N × Fin N,
      F (W π) (W (π * Equiv.swap k.1 k.2))) =
    ∑ π : Equiv.Perm (Fin N), ∑ k : Fin N × Fin N,
      F (W (π * Equiv.swap k.1 k.2)) (W π) := by
  classical
  have hk : ∀ k : Fin N × Fin N,
      (∑ π : Equiv.Perm (Fin N), F (W π) (W (π * Equiv.swap k.1 k.2))) =
      ∑ π : Equiv.Perm (Fin N), F (W (π * Equiv.swap k.1 k.2)) (W π) := by
    intro k
    have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap k.1 k.2))
      (fun π : Equiv.Perm (Fin N) => F (W π) (W (π * Equiv.swap k.1 k.2)))
    simpa only [Equiv.coe_mulRight, mul_assoc, Equiv.swap_mul_self, mul_one] using h.symm
  calc _ = ∑ k : Fin N × Fin N, ∑ π : Equiv.Perm (Fin N),
          F (W π) (W (π * Equiv.swap k.1 k.2)) := Finset.sum_comm
    _ = ∑ k : Fin N × Fin N, ∑ π : Equiv.Perm (Fin N),
          F (W (π * Equiv.swap k.1 k.2)) (W π) := Finset.sum_congr rfl fun k _ => hk k
    _ = _ := Finset.sum_comm

theorem array_exchangeable (c : Matrix (Fin N) (Fin N) ℝ) (F : ℝ → ℝ → ℝ) :
    (∑ π : Equiv.Perm (Fin N), ∑ k : Fin N × Fin N,
      F (statistic c π) (swapped c π k)) =
    ∑ π : Equiv.Perm (Fin N), ∑ k : Fin N × Fin N,
      F (swapped c π k) (statistic c π) :=
  transposition_exchangeable (statistic c) F

theorem sum_rectangle (b : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, b i j = 0) (hc : ∀ j, ∑ i, b i j = 0) :
    (∑ i, ∑ j, rectangle b i j) = -2 * (N : ℝ) * ∑ i, b i i := by
  classical
  simp only [rectangle, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [hr, hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_zero, Finset.sum_const_zero, ← Finset.mul_sum]
  ring

/-- Exact finite linear regression, with diagonal null moves included. -/
theorem array_regression (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0)
    (π : Equiv.Perm (Fin N)) :
    (∑ k : Fin N × Fin N, (swapped c π k - statistic c π)) =
      -2 * (N : ℝ) * statistic c π := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [swapped_sub]
  apply sum_rectangle
  · intro i; rw [Equiv.sum_comp π]; exact hr i
  · intro j; exact hc (π j)

theorem array_regression_stein (hN : 0 < N) (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0)
    (π : Equiv.Perm (Fin N)) :
    (∑ k : Fin N × Fin N, (swapped c π k - statistic c π)) =
      -(2 / (N : ℝ)) * (Fintype.card (Fin N × Fin N) : ℝ) * statistic c π := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [array_regression c hr hc, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  field_simp

theorem abs_rectangle_le (c : Matrix (Fin N) (Fin N) ℝ) {β : ℝ}
    (hβ : ∀ i j, |c i j| ≤ β) (π : Equiv.Perm (Fin N)) (i j : Fin N) :
    |rectangle (fun a b => c a (π b)) i j| ≤ 4 * β := by
  unfold rectangle
  calc |c i (π j) + c j (π i) - c i (π i) - c j (π j)|
      ≤ |c i (π j)| + |c j (π i)| + |c i (π i)| + |c j (π j)| := by
        calc _ ≤ |c i (π j) + c j (π i) - c i (π i)| + |c j (π j)| := abs_sub _ _
             _ ≤ (|c i (π j) + c j (π i)| + |c i (π i)|) + |c j (π j)| :=
               add_le_add (abs_sub _ _) le_rfl
             _ ≤ _ := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ ≤ 4 * β := by linarith [hβ i (π j), hβ j (π i), hβ i (π i), hβ j (π j)]


theorem sum_rectangle_sq (b : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, b i j = 0) (hc : ∀ j, ∑ i, b i j = 0) :
    (∑ i, ∑ j, (rectangle b i j)^2) =
      2 * energy b + 2 * (N : ℝ) * (∑ i, (b i i)^2) +
        2 * (∑ i, b i i)^2 + 2 * ∑ i, ∑ j, b i j * b j i := by
  classical
  have h1 : (∑ i, ∑ j, b i j * b i i) = 0 := by
    simp_rw [← Finset.sum_mul, hr, zero_mul]
    simp
  have h2 : (∑ i, ∑ j, b i j * b j j) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hc, zero_mul]
    simp
  have h3 : (∑ i, ∑ j, b j i * b i i) = 0 := by
    simp_rw [← Finset.sum_mul, hc, zero_mul]
    simp
  have h4 : (∑ i, ∑ j, b j i * b j j) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hr, zero_mul]
    simp
  have h5 : (∑ i, ∑ j, b i i * b j j) = (∑ i, b i i)^2 := by
    rw [sq, Finset.sum_mul_sum]
  have h6 : (∑ i, ∑ j, (b j i)^2) = energy b := Finset.sum_comm
  have h7 : (∑ i, ∑ _j : Fin N, (b i i)^2) = (N : ℝ) * ∑ i, (b i i)^2 := by
    simp [← Finset.mul_sum]
  have h8 : (∑ _i : Fin N, ∑ j, (b j j)^2) = (N : ℝ) * ∑ i, (b i i)^2 := by
    simp
  have he : ∀ i j, (rectangle b i j)^2 =
      (b i j)^2 + (b j i)^2 + (b i i)^2 + (b j j)^2 +
        2 * (b i j * b j i) - 2 * (b i j * b i i) -
        2 * (b i j * b j j) - 2 * (b j i * b i i) -
        2 * (b j i * b j j) + 2 * (b i i * b j j) := by
    intro i j
    unfold rectangle
    ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [h1, h2, h3, h4, h6, h7, h8]
  rw [← Finset.sum_mul, ← sq]
  unfold energy
  ring

/-- Exact conditional square-increment identity for a doubly centered array. -/
theorem array_sum_sq_increment (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0)
    (π : Equiv.Perm (Fin N)) :
    (∑ k : Fin N × Fin N, (swapped c π k - statistic c π)^2) =
      2 * (energy c + (N : ℝ) * selectedEnergy c π +
        (statistic c π)^2 + crossed c π) := by
  classical
  have hr' : ∀ i, ∑ j, c i (π j) = 0 := by
    intro i; rw [Equiv.sum_comp π]; exact hr i
  have hc' : ∀ j, ∑ i, c i (π j) = 0 := fun j => hc (π j)
  have he : energy (fun a b => c a (π b)) = energy c := by
    unfold energy
    exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp π (fun j => (c i j)^2)
  rw [Fintype.sum_prod_type]
  simp_rw [swapped_sub]
  rw [sum_rectangle_sq _ hr' hc', he]
  unfold selectedEnergy statistic crossed traceSquare
  ring

theorem average_selectedEnergy (c : Matrix (Fin N) (Fin N) ℝ) :
    average (selectedEnergy c) = (N : ℝ)⁻¹ * energy c := by
  classical
  unfold selectedEnergy
  rw [average_sum]
  have h : ∀ i : Fin N,
      average (fun π : Equiv.Perm (Fin N) => (c i (π i))^2) =
        (N : ℝ)⁻¹ * ∑ j, (c i j)^2 := by
    intro i
    simpa [average] using StatLean.HypothesisTesting.avg_perm_apply i (fun j => (c i j)^2)
  simp_rw [h]
  rw [← Finset.mul_sum]
  rfl

theorem sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc _ = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem traceSquare_add (b e : Matrix (Fin N) (Fin N) ℝ) :
    traceSquare (fun i j => b i j + e i j) =
      traceSquare b + 2 * (∑ i, ∑ j, e i j * b j i) + traceSquare e := by
  classical
  have h : (∑ i, ∑ j, b i j * e j i) = ∑ i, ∑ j, e i j * b j i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [traceSquare, add_mul, mul_add, Finset.sum_add_distrib]
  rw [h]
  ring

theorem traceSquare_rankOne (d t : Fin N → ℝ) :
    traceSquare (fun i j => d i * t j) = (∑ i, d i * t i)^2 := by
  classical
  have h : ∀ i j, (d i * t j) * (d j * t i) = (d i * t i) * (d j * t j) := by
    intro i j; ring
  unfold traceSquare
  simp_rw [h]
  rw [← Finset.sum_mul_sum, ← sq]

/-- A column transposition is a rank-one perturbation. -/
theorem traceSquare_swap_sub (b : Matrix (Fin N) (Fin N) ℝ) (a z : Fin N) :
    traceSquare (fun i j => b i (Equiv.swap a z j)) - traceSquare b =
      2 * (∑ i, (b i z - b i a) * (b a i - b z i)) + (rectangle b a z)^2 := by
  classical
  let d : Fin N → ℝ := fun i => b i z - b i a
  let t : Fin N → ℝ := fun j => (if j = a then 1 else 0) - (if j = z then 1 else 0)
  have hs : (fun i j => b i (Equiv.swap a z j)) = (fun i j => b i j + d i * t j) := by
    funext i j
    by_cases haz : a = z
    · subst z; simp [d, t]
    by_cases hja : j = a
    · subst j; simp [d, t, haz] <;> ring
    by_cases hjz : j = z
    · subst j; simp [d, t, haz, Ne.symm haz] <;> ring
    simp [Equiv.swap_apply_of_ne_of_ne hja hjz, t, hja, hjz]
  have hd : (∑ i, d i * t i) = rectangle b a z := by
    simp [t, mul_sub, mul_ite, Finset.sum_sub_distrib, d, rectangle]
    ring
  have hz : (∑ i, ∑ j, (d i * t j) * b j i) =
      ∑ i, (b i z - b i a) * (b a i - b z i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [t, mul_sub, sub_mul, mul_ite, ite_mul, Finset.sum_sub_distrib, d] <;> ring
  rw [hs, traceSquare_add b (fun i j => d i * t j), traceSquare_rankOne d t, hd, hz]
  ring

theorem sum_traceSquare_swap_sub (b : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, b i j = 0) (hc : ∀ j, ∑ i, b i j = 0) :
    (∑ a, ∑ z, (traceSquare (fun i j => b i (Equiv.swap a z j)) - traceSquare b)) =
      -(4 * (N : ℝ) - 2) * traceSquare b + 2 * (N : ℝ) * (∑ i, (b i i)^2) +
        2 * (∑ i, b i i)^2 + 2 * energy b := by
  classical
  have hz : (∑ a, ∑ z, ∑ i, (b i z - b i a) * (b a i - b z i)) =
      -2 * (N : ℝ) * traceSquare b := by
    rw [sum_rotate]
    have hi : ∀ i : Fin N,
        (∑ a, ∑ z, (b i z - b i a) * (b a i - b z i)) =
          -2 * (N : ℝ) * ∑ a, b i a * b a i := by
      intro i
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      simp only [← Finset.sum_mul, ← Finset.mul_sum, hr, hc, zero_mul, mul_zero,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [mul_assoc, ← Finset.mul_sum]
      ring
    simp_rw [hi]
    rw [← Finset.mul_sum]
    rfl
  simp only [traceSquare_swap_sub, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hz, sum_rectangle_sq b hr hc]
  unfold traceSquare
  ring

/-- Unnormalized transposition generator, including diagonal null moves. -/
noncomputable def laplacian (f : Equiv.Perm (Fin N) → ℝ)
    (π : Equiv.Perm (Fin N)) : ℝ :=
  ∑ k : Fin N × Fin N, (f (π * Equiv.swap k.1 k.2) - f π)

theorem average_mulRight (f : Equiv.Perm (Fin N) → ℝ) (s : Equiv.Perm (Fin N)) :
    average (fun π => f (π * s)) = average f := by
  unfold average
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight s) f

theorem laplacian_add (f g : Equiv.Perm (Fin N) → ℝ) (π : Equiv.Perm (Fin N)) :
    laplacian (fun σ => f σ + g σ) π = laplacian f π + laplacian g π := by
  unfold laplacian
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem laplacian_const_mul (a : ℝ) (f : Equiv.Perm (Fin N) → ℝ)
    (π : Equiv.Perm (Fin N)) :
    laplacian (fun σ => a * f σ) π = a * laplacian f π := by
  unfold laplacian
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem laplacian_sub (f g : Equiv.Perm (Fin N) → ℝ) (π : Equiv.Perm (Fin N)) :
    laplacian (fun σ => f σ - g σ) π = laplacian f π - laplacian g π := by
  unfold laplacian
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem laplacian_sub_const (f : Equiv.Perm (Fin N) → ℝ) (a : ℝ)
    (π : Equiv.Perm (Fin N)) : laplacian (fun σ => f σ - a) π = laplacian f π := by
  unfold laplacian
  exact Finset.sum_congr rfl fun k _ => by ring

theorem average_laplacian (f : Equiv.Perm (Fin N) → ℝ) : average (laplacian f) = 0 := by
  unfold laplacian
  rw [average_sum]
  have h : ∀ k : Fin N × Fin N,
      average (fun π : Equiv.Perm (Fin N) => f (π * Equiv.swap k.1 k.2) - f π) = 0 := by
    intro k
    rw [average_sub, average_mulRight, sub_self]
  simp only [h, Finset.sum_const_zero]

/-- The transposition generator is symmetric for uniform finite expectation. -/
theorem laplacian_symmetric (f g : Equiv.Perm (Fin N) → ℝ) :
    average (fun π => f π * laplacian g π) =
      average (fun π => g π * laplacian f π) := by
  classical
  have h : ∀ k : Fin N × Fin N,
      average (fun π : Equiv.Perm (Fin N) => f π * g (π * Equiv.swap k.1 k.2)) =
      average (fun π : Equiv.Perm (Fin N) => g π * f (π * Equiv.swap k.1 k.2)) := by
    intro k
    have he := average_mulRight
      (fun π : Equiv.Perm (Fin N) => f π * g (π * Equiv.swap k.1 k.2))
      (Equiv.swap k.1 k.2)
    simp only [mul_assoc, Equiv.swap_mul_self, mul_one] at he
    rw [← he]
    congr 1
    funext π
    exact mul_comm _ _
  have hfg : average (fun π => f π * g π) = average (fun π => g π * f π) := by
    congr 1; funext π; ring
  simp only [laplacian, Finset.mul_sum, average_sum, mul_sub, average_sub, h, hfg]

theorem laplacian_square (f : Equiv.Perm (Fin N) → ℝ) (π : Equiv.Perm (Fin N)) :
    laplacian (fun σ => (f σ)^2) π = 2 * (f π * laplacian f π) +
      ∑ k : Fin N × Fin N, (f (π * Equiv.swap k.1 k.2) - f π)^2 := by
  unfold laplacian
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The Dirichlet identity, without a probabilistic or spectral assumption. -/
theorem average_sq_increment (f : Equiv.Perm (Fin N) → ℝ) :
    average (fun π => ∑ k : Fin N × Fin N, (f (π * Equiv.swap k.1 k.2) - f π)^2) =
      -2 * average (fun π => f π * laplacian f π) := by
  have h : average (fun π => laplacian (fun σ => (f σ)^2) π) = 0 :=
    average_laplacian (fun π => (f π)^2)
  simp only [laplacian_square, average_add, average_const_mul] at h
  linarith

theorem sum_rectangle_general (b : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, rectangle b i j) =
      2 * (∑ i, ∑ j, b i j) - 2 * (N : ℝ) * (∑ i, b i i) := by
  classical
  have h : (∑ i, ∑ j, b j i) = ∑ i, ∑ j, b i j := Finset.sum_comm
  simp only [rectangle, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  rw [h]
  ring

theorem laplacian_statistic_general (c : Matrix (Fin N) (Fin N) ℝ)
    (π : Equiv.Perm (Fin N)) :
    laplacian (statistic c) π = 2 * (∑ i, ∑ j, c i j) - 2 * (N : ℝ) * statistic c π := by
  classical
  unfold laplacian
  change (∑ k : Fin N × Fin N, (swapped c π k - statistic c π)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [swapped_sub]
  rw [sum_rectangle_general (fun a b => c a (π b))]
  have h : (∑ i, ∑ j, c i (π j)) = ∑ i, ∑ j, c i j :=
    Finset.sum_congr rfl fun i _ => Equiv.sum_comp π (c i)
  rw [h]
  rfl

theorem laplacian_selectedEnergy (c : Matrix (Fin N) (Fin N) ℝ)
    (π : Equiv.Perm (Fin N)) :
    laplacian (selectedEnergy c) π = 2 * energy c - 2 * (N : ℝ) * selectedEnergy c π :=
  laplacian_statistic_general (fun i j => (c i j)^2) π

theorem laplacian_statistic_sq (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0)
    (π : Equiv.Perm (Fin N)) :
    laplacian (fun σ => (statistic c σ)^2) π =
      -(4 * (N : ℝ) - 2) * (statistic c π)^2 +
        (2 * (N : ℝ)) * selectedEnergy c π + 2 * crossed c π + 2 * energy c := by
  rw [laplacian_square]
  have hl : laplacian (statistic c) π = -2 * (N : ℝ) * statistic c π :=
    array_regression c hr hc π
  change 2 * (statistic c π * laplacian (statistic c) π) +
    (∑ k : Fin N × Fin N, (swapped c π k - statistic c π)^2) = _
  rw [hl, array_sum_sq_increment c hr hc]
  ring

theorem laplacian_crossed (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0)
    (π : Equiv.Perm (Fin N)) :
    laplacian (crossed c) π = -(4 * (N : ℝ) - 2) * crossed c π +
      (2 * (N : ℝ)) * selectedEnergy c π + 2 * (statistic c π)^2 + 2 * energy c := by
  classical
  have hr' : ∀ i, ∑ j, c i (π j) = 0 := by
    intro i; rw [Equiv.sum_comp π]; exact hr i
  have hc' : ∀ j, ∑ i, c i (π j) = 0 := fun j => hc (π j)
  have he : energy (fun a b => c a (π b)) = energy c := by
    unfold energy
    exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp π (fun j => (c i j)^2)
  unfold laplacian crossed
  simp only [Equiv.Perm.mul_apply]
  rw [Fintype.sum_prod_type, sum_traceSquare_swap_sub _ hr' hc', he]
  unfold selectedEnergy statistic
  ring

/-- The exact second moment and the mean crossed statistic. No distributional assumption
is hidden here: both expectations are uniform sums over the permutation group. -/
theorem array_second_moments (hN : 2 ≤ N) (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0) :
    average (fun π => (statistic c π)^2) = energy c / ((N : ℝ) - 1) ∧
      average (crossed c) = energy c / ((N : ℝ) - 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hn1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hd : (N : ℝ) * average (selectedEnergy c) = energy c := by
    rw [average_selectedEnergy]
    field_simp
  have hw : average (fun π => laplacian (fun σ => (statistic c σ)^2) π) = 0 :=
    average_laplacian (fun π => (statistic c π)^2)
  have ht : average (fun π => laplacian (crossed c) π) = 0 :=
    average_laplacian (crossed c)
  simp only [laplacian_statistic_sq c hr hc, average_add, average_const_mul,
    average_const] at hw
  simp only [laplacian_crossed c hr hc, average_add, average_const_mul,
    average_const] at ht
  have hprod : 4 * (N : ℝ) *
      (average (fun π => (statistic c π)^2) - average (crossed c)) = 0 := by
    linear_combination ht - hw
  have heq : average (fun π => (statistic c π)^2) = average (crossed c) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (by positivity))
  have hw' : average (fun π => (statistic c π)^2) = energy c / ((N : ℝ) - 1) := by
    apply (eq_div_iff hn1).mpr
    rw [← heq] at ht
    nlinarith [hd]
  exact ⟨hw', heq ▸ hw'⟩

/-- The normalized conditional second moment used in Stein's method. -/
noncomputable def normalizedSquare (c : Matrix (Fin N) (Fin N) ℝ)
    (π : Equiv.Perm (Fin N)) : ℝ :=
  (energy c + (N : ℝ) * selectedEnergy c π + (statistic c π)^2 + crossed c π) /
    (2 * (N : ℝ))

theorem normalizedSquare_eq_condSqIncrement (hN : 0 < N)
    (c : Matrix (Fin N) (Fin N) ℝ) (hr : ∀ i, ∑ j, c i j = 0)
    (hc : ∀ j, ∑ i, c i j = 0) (π : Equiv.Perm (Fin N)) :
    (2 * (2 / (N : ℝ)))⁻¹ *
      StatLean.HypothesisTesting.condSqIncrement (statistic c) (swapped c) π =
        normalizedSquare c π := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [StatLean.HypothesisTesting.condSqIncrement, array_sum_sq_increment c hr hc,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, normalizedSquare]
  field_simp <;> ring


theorem eigenfunctions_orthogonal (f g : Equiv.Perm (Fin N) → ℝ) {r s : ℝ}
    (hf : ∀ π, laplacian f π = -r * f π)
    (hg : ∀ π, laplacian g π = -s * g π) (hrs : r ≠ s) :
    average (fun π => f π * g π) = 0 := by
  have h := laplacian_symmetric f g
  simp only [hf, hg] at h
  have h1 : average (fun π => f π * (-s * g π)) =
      -s * average (fun π => f π * g π) := by
    rw [← average_const_mul]
    congr 1; funext π; ring
  have h2 : average (fun π => g π * (-r * f π)) =
      -r * average (fun π => f π * g π) := by
    rw [← average_const_mul]
    congr 1; funext π; ring
  rw [h1, h2] at h
  have hz : (r - s) * average (fun π => f π * g π) = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hrs)

/-- A spectral-gap inequality on a span of three distinct eigenspaces. -/
theorem spectral_gap_three (f g h : Equiv.Perm (Fin N) → ℝ) {r s t m : ℝ}
    (hf : ∀ π, laplacian f π = -r * f π)
    (hg : ∀ π, laplacian g π = -s * g π)
    (hh : ∀ π, laplacian h π = -t * h π)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hmr : m ≤ r) (hms : m ≤ s) (hmt : m ≤ t) :
    m * average (fun π => (f π + g π + h π)^2) ≤
      -average (fun π => (f π + g π + h π) *
        laplacian (fun σ => f σ + g σ + h σ) π) := by
  have hfg := eigenfunctions_orthogonal f g hf hg hrs
  have hfh := eigenfunctions_orthogonal f h hf hh hrt
  have hgh := eigenfunctions_orthogonal g h hg hh hst
  have hn : average (fun π => (f π + g π + h π)^2) =
      average (fun π => (f π)^2) + average (fun π => (g π)^2) +
        average (fun π => (h π)^2) := by
    have he : (fun π => (f π + g π + h π)^2) =
        (fun π => (f π)^2 + (g π)^2 + (h π)^2 +
          2 * (f π * g π) + 2 * (f π * h π) + 2 * (g π * h π)) := by
      funext π; ring
    rw [he]
    simp only [average_add, average_const_mul, hfg, hfh, hgh]
    ring
  have hd : average (fun π => (f π + g π + h π) *
      laplacian (fun σ => f σ + g σ + h σ) π) =
      -r * average (fun π => (f π)^2) + -s * average (fun π => (g π)^2) +
        -t * average (fun π => (h π)^2) := by
    have he : (fun π => (f π + g π + h π) *
        laplacian (fun σ => f σ + g σ + h σ) π) =
        (fun π => -r * (f π)^2 + -s * (g π)^2 + -t * (h π)^2 +
          (-(r+s)) * (f π * g π) + (-(r+t)) * (f π * h π) +
          (-(s+t)) * (g π * h π)) := by
      funext π
      rw [laplacian_add, laplacian_add, hf, hg, hh]
      ring
    rw [he]
    simp only [average_add, average_const_mul, hfg, hfh, hgh]
    ring
  rw [hn, hd]
  have hfn := average_nonneg (fun π => sq_nonneg (f π))
  have hgn := average_nonneg (fun π => sq_nonneg (g π))
  have hhn := average_nonneg (fun π => sq_nonneg (h π))
  nlinarith [mul_nonneg (sub_nonneg.mpr hmr) hfn,
    mul_nonneg (sub_nonneg.mpr hms) hgn, mul_nonneg (sub_nonneg.mpr hmt) hhn]

/-- The crossed statistic has the transposition Poincare bound. The proof only uses
the explicitly computed quadratic eigenspaces; it assumes no general Poincare theorem. -/
theorem crossed_variance_le_gradient (hN : 3 ≤ N) (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0) :
    average (fun π => (crossed c π - energy c / ((N : ℝ) - 1))^2) ≤
      (4 * (N : ℝ))⁻¹ * average (fun π => ∑ k : Fin N × Fin N,
        (crossed c (π * Equiv.swap k.1 k.2) - crossed c π)^2) := by
  have hn3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (N : ℝ) ≠ 0 := by linarith
  have hn1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (N : ℝ) - 2 ≠ 0 := by linarith
  let d := fun π => selectedEnergy c π - energy c / (N : ℝ)
  let u := fun π => (statistic c π)^2 - crossed c π
  let A : ℝ := 2 * (N : ℝ) / ((N : ℝ) - 2)
  let e := fun π => ((statistic c π)^2 + crossed c π -
    2 * energy c / ((N : ℝ) - 1)) - A * d π
  have hd : ∀ π, laplacian d π = -(2 * (N : ℝ)) * d π := by
    intro π
    dsimp [d]
    rw [laplacian_sub_const, laplacian_selectedEnergy]
    field_simp
    ring
  have hu : ∀ π, laplacian u π = -(4 * (N : ℝ)) * u π := by
    intro π
    dsimp [u]
    rw [laplacian_sub, laplacian_statistic_sq c hr hc, laplacian_crossed c hr hc]
    ring
  have he : ∀ π, laplacian e π = -(4 * (N : ℝ) - 4) * e π := by
    intro π
    change laplacian (fun σ => ((statistic c σ)^2 + crossed c σ -
      2 * energy c / ((N : ℝ) - 1)) - A * d σ) π = _
    rw [laplacian_sub, laplacian_sub_const, laplacian_add, laplacian_const_mul,
      laplacian_statistic_sq c hr hc, laplacian_crossed c hr hc, hd]
    dsimp [e, A, d]
    field_simp
    ring
  let f := fun π => (A / 2) * d π
  let g := fun π => (1 / 2 : ℝ) * e π
  let h := fun π => (-1 / 2 : ℝ) * u π
  have hf : ∀ π, laplacian f π = -(2 * (N : ℝ)) * f π := by
    intro π; dsimp [f]; rw [laplacian_const_mul, hd]; ring
  have hg : ∀ π, laplacian g π = -(4 * (N : ℝ) - 4) * g π := by
    intro π; dsimp [g]; rw [laplacian_const_mul, he]; ring
  have hh : ∀ π, laplacian h π = -(4 * (N : ℝ)) * h π := by
    intro π; dsimp [h]; rw [laplacian_const_mul, hu]; ring
  have hsum : (fun π => f π + g π + h π) =
      (fun π => crossed c π - energy c / ((N : ℝ) - 1)) := by
    funext π
    dsimp [f, g, h, e, u]
    ring
  have hgap := spectral_gap_three f g h hf hg hh
    (by linarith : 2 * (N : ℝ) ≠ 4 * (N : ℝ) - 4)
    (by linarith : 2 * (N : ℝ) ≠ 4 * (N : ℝ))
    (by linarith : 4 * (N : ℝ) - 4 ≠ 4 * (N : ℝ))
    (le_refl (2 * (N : ℝ))) (by linarith) (by linarith)
  have hsum' : ∀ π, f π + g π + h π = crossed c π - energy c / ((N : ℝ) - 1) :=
    fun π => congrFun hsum π
  simp only [hsum', hsum] at hgap
  have heq := average_sq_increment (fun π => crossed c π - energy c / ((N : ℝ) - 1))
  have hincr : average (fun π => ∑ k : Fin N × Fin N,
      ((crossed c (π * Equiv.swap k.1 k.2) - energy c / ((N : ℝ) - 1)) -
        (crossed c π - energy c / ((N : ℝ) - 1)))^2) =
      average (fun π => ∑ k : Fin N × Fin N,
        (crossed c (π * Equiv.swap k.1 k.2) - crossed c π)^2) := by
    congr 1; funext π
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hincr] at heq
  have hp : (0 : ℝ) < 4 * (N : ℝ) := by linarith
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ hp).mpr
  nlinarith [hgap, heq]

noncomputable def rowEnergy (b : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : ℝ :=
  ∑ j, (b i j)^2

noncomputable def columnEnergy (b : Matrix (Fin N) (Fin N) ℝ) (j : Fin N) : ℝ :=
  ∑ i, (b i j)^2

theorem sq_sub_le_two (x y : ℝ) : (x-y)^2 ≤ 2 * (x^2 + y^2) := by
  nlinarith [sq_nonneg (x+y)]

theorem square_le_sum_square (f : Fin N → ℝ) (i : Fin N) : (f i)^2 ≤ ∑ j, (f j)^2 :=
  Finset.single_le_sum (fun j _ => sq_nonneg (f j)) (Finset.mem_univ i)

/-- A deterministic energy bound for one crossed-statistic transposition. -/
theorem traceSquare_swap_sub_sq_le (b : Matrix (Fin N) (Fin N) ℝ) (a z : Fin N) :
    (traceSquare (fun i j => b i (Equiv.swap a z j)) - traceSquare b)^2 ≤
      160 * (rowEnergy b a + rowEnergy b z) * (columnEnergy b a + columnEnergy b z) := by
  classical
  let d : Fin N → ℝ := fun i => b i z - b i a
  let v : Fin N → ℝ := fun i => b a i - b z i
  let P : ℝ := ∑ i, (d i)^2
  let Q : ℝ := ∑ i, (v i)^2
  let Z : ℝ := ∑ i, d i * v i
  have hp : 0 ≤ P := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hq : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : Z^2 ≤ P * Q := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ d v
  have hδd : rectangle b a z = d a - d z := by dsimp [d, rectangle]; ring
  have hδv : rectangle b a z = v z - v a := by dsimp [v, rectangle]; ring
  have hδp : (rectangle b a z)^2 ≤ 4 * P := by
    rw [hδd]
    nlinarith [sq_sub_le_two (d a) (d z), square_le_sum_square d a,
      square_le_sum_square d z]
  have hδq : (rectangle b a z)^2 ≤ 4 * Q := by
    rw [hδv]
    nlinarith [sq_sub_le_two (v z) (v a), square_le_sum_square v z,
      square_le_sum_square v a]
  have hfour : (rectangle b a z)^4 ≤ 16 * P * Q := by
    calc _ = (rectangle b a z)^2 * (rectangle b a z)^2 := by ring
      _ ≤ (4*P) * (4*Q) := mul_le_mul hδp hδq (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hP : P ≤ 2 * (columnEnergy b a + columnEnergy b z) := by
    calc P ≤ ∑ i, 2 * ((b i z)^2 + (b i a)^2) :=
          Finset.sum_le_sum fun i _ => sq_sub_le_two _ _
      _ = _ := by simp [columnEnergy, ← Finset.mul_sum, Finset.sum_add_distrib]; ring
  have hQ : Q ≤ 2 * (rowEnergy b a + rowEnergy b z) := by
    calc Q ≤ ∑ i, 2 * ((b a i)^2 + (b z i)^2) :=
          Finset.sum_le_sum fun i _ => sq_sub_le_two _ _
      _ = _ := by simp [rowEnergy, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hPQ : P * Q ≤ 4 * (rowEnergy b a + rowEnergy b z) *
      (columnEnergy b a + columnEnergy b z) := by
    calc P * Q ≤ (2 * (columnEnergy b a + columnEnergy b z)) *
          (2 * (rowEnergy b a + rowEnergy b z)) :=
            mul_le_mul hP hQ hq (by unfold columnEnergy; positivity)
      _ = _ := by ring
  rw [traceSquare_swap_sub]
  change (2*Z + (rectangle b a z)^2)^2 ≤ _
  have hs : (2*Z + (rectangle b a z)^2)^2 ≤ 8*Z^2 + 2*(rectangle b a z)^4 := by
    nlinarith [sq_nonneg (2*Z - (rectangle b a z)^2)]
  nlinarith [hcs, hfour, hPQ]

theorem rowEnergy_permute (c : Matrix (Fin N) (Fin N) ℝ) (π : Equiv.Perm (Fin N))
    (i : Fin N) : rowEnergy (fun a b => c a (π b)) i = rowEnergy c i :=
  Equiv.sum_comp π (fun j => (c i j)^2)

theorem average_columnEnergy_apply (c : Matrix (Fin N) (Fin N) ℝ) (a : Fin N) :
    average (fun π : Equiv.Perm (Fin N) => columnEnergy c (π a)) =
      (N : ℝ)⁻¹ * energy c := by
  have h := StatLean.HypothesisTesting.avg_perm_apply a (columnEnergy c)
  have hs : (∑ j, columnEnergy c j) = energy c := Finset.sum_comm
  simpa only [average, Fintype.card_fin, hs] using h

theorem average_row_column_product (hN : 0 < N) (c : Matrix (Fin N) (Fin N) ℝ) :
    average (fun π : Equiv.Perm (Fin N) => ∑ a, ∑ z,
      (rowEnergy c a + rowEnergy c z) * (columnEnergy c (π a) + columnEnergy c (π z))) =
      4 * (energy c)^2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : (∑ a, ∑ z, (rowEnergy c a + rowEnergy c z)) =
      2 * (N : ℝ) * energy c := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    change (N : ℝ) * energy c + (N : ℝ) * energy c = _
    ring
  rw [average_sum]
  simp_rw [average_sum, average_const_mul, average_add, average_columnEnergy_apply]
  simp only [← Finset.sum_mul]
  rw [hs]
  field_simp
  ring

theorem average_crossed_gradient_le (hN : 0 < N) (c : Matrix (Fin N) (Fin N) ℝ) :
    average (fun π => ∑ k : Fin N × Fin N,
      (crossed c (π * Equiv.swap k.1 k.2) - crossed c π)^2) ≤ 640 * (energy c)^2 := by
  have h : ∀ π : Equiv.Perm (Fin N),
      (∑ k : Fin N × Fin N, (crossed c (π * Equiv.swap k.1 k.2) - crossed c π)^2) ≤
      160 * ∑ a, ∑ z, (rowEnergy c a + rowEnergy c z) *
        (columnEnergy c (π a) + columnEnergy c (π z)) := by
    intro π
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    have hb := traceSquare_swap_sub_sq_le (fun i j => c i (π j)) a z
    simp only [rowEnergy_permute] at hb
    convert hb using 1 <;> simp only [crossed, Equiv.Perm.mul_apply, columnEnergy] <;> ring
  calc _ ≤ average (fun π : Equiv.Perm (Fin N) => 160 * ∑ a, ∑ z,
        (rowEnergy c a + rowEnergy c z) * (columnEnergy c (π a) + columnEnergy c (π z))) :=
        average_mono h
    _ = _ := by rw [average_const_mul, average_row_column_product hN]; ring

/-- Concentration of the crossed quadratic term, with an absolute numerical constant. -/
theorem crossed_variance_le (hN : 3 ≤ N) (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0) :
    average (fun π => (crossed c π - energy c / ((N : ℝ) - 1))^2) ≤
      160 * (energy c)^2 / (N : ℝ) := by
  have hn : 0 < N := by omega
  calc _ ≤ (4 * (N : ℝ))⁻¹ * average (fun π => ∑ k : Fin N × Fin N,
        (crossed c (π * Equiv.swap k.1 k.2) - crossed c π)^2) :=
        crossed_variance_le_gradient hN c hr hc
    _ ≤ (4 * (N : ℝ))⁻¹ * (640 * (energy c)^2) :=
        mul_le_mul_of_nonneg_left (average_crossed_gradient_le hn c) (by positivity)
    _ = _ := by ring

theorem average_square_sub {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) (a : ℝ) :
    average (fun x => (f x - a)^2) = average (fun x => (f x)^2) - 2*a*average f + a^2 := by
  have he : (fun x => (f x-a)^2) =
      (fun x => (f x)^2 + (-2*a) * f x + a^2) := by funext x; ring
  rw [he]
  simp only [average_add, average_const_mul, average_const]
  ring

/-- A useful second-moment upper bound for any nonnegative permutation array. -/
theorem nonnegative_array_second_moment_le (hN : 2 ≤ N)
    (d : Matrix (Fin N) (Fin N) ℝ) (hd : ∀ i j, 0 ≤ d i j) :
    average (fun π => (statistic d π)^2) ≤
      (∑ i, ∑ j, d i j)^2 / ((N : ℝ) * ((N : ℝ)-1)) + (N : ℝ)⁻¹ * energy d := by
  classical
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1pos : (0 : ℝ) < (N : ℝ)-1 := by linarith
  let r : Fin N → ℝ := fun i => ∑ j, d i j
  let b : ℝ := ((N : ℝ) * ((N : ℝ)-1))⁻¹
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hr : ∀ i, 0 ≤ r i := fun i => Finset.sum_nonneg fun j _ => hd i j
  have hp : ∀ i j : Fin N,
      average (fun π : Equiv.Perm (Fin N) => d i (π i) * d j (π j)) ≤
      b * r i * r j + if i = j then (N : ℝ)⁻¹ * ∑ l, (d i l)^2 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have hm : average (fun π : Equiv.Perm (Fin N) => d i (π i) * d i (π i)) =
          (N : ℝ)⁻¹ * ∑ l, (d i l)^2 := by
        calc _ = (N : ℝ)⁻¹ * ∑ l, d i l * d i l := by
              simpa only [average, Fintype.card_fin] using
                StatLean.HypothesisTesting.avg_perm_apply i (fun l => d i l * d i l)
          _ = _ := by
              congr 1
              exact Finset.sum_congr rfl fun l _ => by ring
      rw [hm]
      exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg hb (hr i)) (hr i))
    · rw [if_neg hij, add_zero]
      have hm := StatLean.HypothesisTesting.avg_perm_apply_pair hij
        (fun l k => d i l * d j k)
      rw [Fintype.card_fin] at hm
      change average (fun π : Equiv.Perm (Fin N) => d i (π i) * d j (π j)) =
        b * ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, d i p.1 * d j p.2 at hm
      rw [hm]
      have hs : (∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, d i p.1 * d j p.2) ≤
          r i * r j := by
        calc _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
              d i p.1 * d j p.2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (by intro p _; simp)
                (fun p _ _ => mul_nonneg (hd i p.1) (hd j p.2))
          _ = _ := by rw [Finset.sum_product, ← Finset.sum_mul_sum]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hb
  have hdiag : (∑ i : Fin N, ∑ j : Fin N,
      if i = j then (N : ℝ)⁻¹ * ∑ l, (d i l)^2 else 0) = (N : ℝ)⁻¹ * energy d := by
    simp [energy, ← Finset.mul_sum]
  have hfull : (∑ i, ∑ j, b * r i * r j) = b * (∑ i, ∑ j, d i j)^2 := by
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    dsimp [r]
    ring
  calc _ = ∑ i, ∑ j, average (fun π : Equiv.Perm (Fin N) => d i (π i) * d j (π j)) := by
        simp only [statistic, sq, Finset.sum_mul_sum, average_sum]
    _ ≤ ∑ i, ∑ j, (b * r i * r j +
        if i = j then (N : ℝ)⁻¹ * ∑ l, (d i l)^2 else 0) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hp i j
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [hfull, hdiag]
        dsimp [b]
        ring

/-- Concentration of the selected squared entries follows from the two-position marginal. -/
theorem selectedEnergy_variance_le (hN : 2 ≤ N) (c : Matrix (Fin N) (Fin N) ℝ)
    (hq : energy c = (N : ℝ)-1) {β : ℝ} (hβ : ∀ i j, |c i j| ≤ β) :
    average (fun π => (selectedEnergy c π - ((N : ℝ)-1)/(N : ℝ))^2) ≤ β^2 + 1/(N : ℝ) := by
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
  have hfour : energy (fun i j => (c i j)^2) ≤ β^2 * energy c := by
    unfold energy
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hsq : (c i j)^2 ≤ β^2 := sq_le_sq.mpr ((hβ i j).trans (le_abs_self β))
    simpa only [sq] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (c i j))
  have hs := nonnegative_array_second_moment_le hN (fun i j => (c i j)^2)
    (fun i j => sq_nonneg _)
  change average (fun π => (selectedEnergy c π)^2) ≤
    (energy c)^2 / ((N : ℝ) * ((N : ℝ)-1)) +
      (N : ℝ)⁻¹ * energy (fun i j => (c i j)^2) at hs
  have hm : average (selectedEnergy c) = ((N : ℝ)-1)/(N : ℝ) := by
    rw [average_selectedEnergy, hq, div_eq_inv_mul]
  have hv := average_square_sub (selectedEnergy c) (((N : ℝ)-1)/(N : ℝ))
  rw [hm] at hv
  have hvar : average (fun π => (selectedEnergy c π - ((N : ℝ)-1)/(N : ℝ))^2) ≤
      ((N : ℝ)-1)^2 / ((N : ℝ) * ((N : ℝ)-1)) +
        (N : ℝ)⁻¹ * (β^2 * ((N : ℝ)-1)) - (((N : ℝ)-1)/(N : ℝ))^2 := by
    have h4 := mul_le_mul_of_nonneg_left hfour (inv_nonneg.mpr hn.le)
    rw [hq] at hs h4
    nlinarith [hs, h4, hv]
  refine hvar.trans ?_
  have he : ((N : ℝ)-1)^2 / ((N : ℝ) * ((N : ℝ)-1)) +
      (N : ℝ)⁻¹ * (β^2 * ((N : ℝ)-1)) - (((N : ℝ)-1)/(N : ℝ))^2 =
      β^2 + 1/(N : ℝ) - (β^2/(N : ℝ) + 1/(N : ℝ)^2) := by
    field_simp
    ring
  rw [he]
  have hnn : 0 ≤ β^2/(N : ℝ) + 1/(N : ℝ)^2 := by positivity
  linarith

theorem abs_statistic_le (c : Matrix (Fin N) (Fin N) ℝ) {β : ℝ}
    (hβ : ∀ i j, |c i j| ≤ β) (π : Equiv.Perm (Fin N)) :
    |statistic c π| ≤ (N : ℝ) * β := by
  unfold statistic
  calc _ ≤ ∑ i, |c i (π i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, β := Finset.sum_le_sum fun i _ => hβ i (π i)
    _ = _ := by simp

theorem statistic_square_variance_le (hN : 2 ≤ N) (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0)
    (hq : energy c = (N : ℝ)-1) {β : ℝ} (hβ : ∀ i j, |c i j| ≤ β) :
    average (fun π => ((statistic c π)^2 - 1)^2) ≤ (N : ℝ)^2 * β^2 := by
  have hn1 : (N : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hm : average (fun π => (statistic c π)^2) = 1 := by
    rw [(array_second_moments hN c hr hc).1, hq, div_self hn1]
  have hp : ∀ π : Equiv.Perm (Fin N),
      ((statistic c π)^2)^2 ≤ ((N : ℝ)^2 * β^2) * (statistic c π)^2 := by
    intro π
    have hs : (statistic c π)^2 ≤ ((N : ℝ)*β)^2 :=
      sq_le_sq.mpr ((abs_statistic_le c hβ π).trans (le_abs_self _))
    have hmul := mul_le_mul_of_nonneg_right hs (sq_nonneg (statistic c π))
    convert hmul using 1 <;> ring
  have hf : average (fun π => ((statistic c π)^2)^2) ≤ (N : ℝ)^2 * β^2 := by
    calc _ ≤ average (fun π => ((N : ℝ)^2 * β^2) * (statistic c π)^2) := average_mono hp
      _ = _ := by rw [average_const_mul, hm, mul_one]
  have hv := average_square_sub (fun π => (statistic c π)^2) 1
  rw [hm] at hv
  nlinarith

theorem square_sum_three_le (x y z : ℝ) : (x+y+z)^2 ≤ 3*(x^2+y^2+z^2) := by
  nlinarith [sq_nonneg (x-y), sq_nonneg (x-z), sq_nonneg (y-z)]

/-- Conditional-square-increment concentration for normalized doubly centered arrays.
The constant is deliberately generous; the max-entry CLT requires only convergence to zero. -/
theorem array_conditional_square_concentration (hN : 3 ≤ N)
    (c : Matrix (Fin N) (Fin N) ℝ) (hr : ∀ i, ∑ j, c i j = 0)
    (hc : ∀ j, ∑ i, c i j = 0) (hq : energy c = (N : ℝ)-1)
    {β : ℝ} (hβ : ∀ i j, |c i j| ≤ β) :
    average (fun π => (normalizedSquare c π - 1)^2) ≤ 256 * (β^2 + 1/(N : ℝ)) := by
  have hn3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by linarith
  have hD := selectedEnergy_variance_le (by omega : 2 ≤ N) c hq hβ
  have hW := statistic_square_variance_le (by omega : 2 ≤ N) c hr hc hq hβ
  have hT : average (fun π => (crossed c π - 1)^2) ≤ 160 * (N : ℝ) := by
    have ht := crossed_variance_le hN c hr hc
    rw [hq, div_self hn1] at ht
    refine ht.trans ?_
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have he : ∀ π : Equiv.Perm (Fin N), normalizedSquare c π - 1 =
      (selectedEnergy c π - ((N : ℝ)-1)/(N : ℝ))/2 +
        ((statistic c π)^2-1)/(2*(N : ℝ)) + (crossed c π-1)/(2*(N : ℝ)) := by
    intro π
    rw [normalizedSquare, hq]
    field_simp
    ring
  have hp : ∀ π : Equiv.Perm (Fin N), (normalizedSquare c π-1)^2 ≤
      (3/4 : ℝ) * (selectedEnergy c π - ((N : ℝ)-1)/(N : ℝ))^2 +
        (3/(4*(N : ℝ)^2)) * ((statistic c π)^2-1)^2 +
        (3/(4*(N : ℝ)^2)) * (crossed c π-1)^2 := by
    intro π
    rw [he]
    have hh := square_sum_three_le
      ((selectedEnergy c π - ((N : ℝ)-1)/(N : ℝ))/2)
      (((statistic c π)^2-1)/(2*(N : ℝ))) ((crossed c π-1)/(2*(N : ℝ)))
    convert hh using 1 <;> ring
  have hb : average (fun π => (normalizedSquare c π-1)^2) ≤
      (3/4 : ℝ)*(β^2+1/(N : ℝ)) + (3/(4*(N : ℝ)^2))*((N : ℝ)^2*β^2) +
        (3/(4*(N : ℝ)^2))*(160*(N : ℝ)) := by
    calc _ ≤ average (fun π =>
          (3/4 : ℝ) * (selectedEnergy c π - ((N : ℝ)-1)/(N : ℝ))^2 +
          (3/(4*(N : ℝ)^2)) * ((statistic c π)^2-1)^2 +
          (3/(4*(N : ℝ)^2)) * (crossed c π-1)^2) := average_mono hp
      _ = _ := by simp only [average_add, average_const_mul]
      _ ≤ _ := add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hD (by norm_num))
          (mul_le_mul_of_nonneg_left hW (by positivity)))
        (mul_le_mul_of_nonneg_left hT (by positivity))
  refine hb.trans ?_
  have hcalc : (3/4 : ℝ)*(β^2+1/(N : ℝ)) +
      (3/(4*(N : ℝ)^2))*((N : ℝ)^2*β^2) + (3/(4*(N : ℝ)^2))*(160*(N : ℝ)) =
      (3/2 : ℝ)*β^2 + (483/4 : ℝ)*(1/(N : ℝ)) := by
    field_simp
    ring
  rw [hcalc]
  nlinarith [sq_nonneg β, one_div_pos.mpr hn]

theorem average_abs_le_sqrt_average_square {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : average (fun x => |f x|) ≤ Real.sqrt (average (fun x => (f x)^2)) := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcs : (∑ x, |f x|)^2 ≤ (Fintype.card α : ℝ) * ∑ x, (f x)^2 := by
    simpa [sq_abs] using Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset α) (fun _ => (1 : ℝ)) (fun x => |f x|)
  apply Real.le_sqrt_of_sq_le
  unfold average
  rw [mul_pow]
  calc _ ≤ ((Fintype.card α : ℝ)⁻¹)^2 * ((Fintype.card α : ℝ) * ∑ x, (f x)^2) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by field_simp

theorem array_average_sq_increment (hN : 2 ≤ N) (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0)
    (hq : energy c = (N : ℝ)-1) :
    average (fun π => ∑ k : Fin N × Fin N, (swapped c π k - statistic c π)^2) = 4*(N : ℝ) := by
  have hn1 : (N : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hm : average (fun π => (statistic c π)^2) = 1 := by
    rw [(array_second_moments hN c hr hc).1, hq, div_self hn1]
  have he : (fun π => statistic c π * laplacian (statistic c) π) =
      (fun π => (-2*(N : ℝ)) * (statistic c π)^2) := by
    funext π
    have hl : laplacian (statistic c) π = -2*(N : ℝ)*statistic c π :=
      array_regression c hr hc π
    rw [hl]
    ring
  have h := average_sq_increment (statistic c)
  rw [he, average_const_mul, hm] at h
  change average (fun π => ∑ k : Fin N × Fin N, (swapped c π k - statistic c π)^2) =
    -2 * (-2 * (N : ℝ) * 1) at h
  calc _ = -2 * (-2 * (N : ℝ) * 1) := h
    _ = _ := by ring

theorem array_average_cubic_increment_le (hN : 2 ≤ N) (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0)
    (hq : energy c = (N : ℝ)-1) {β : ℝ} (hβ : ∀ i j, |c i j| ≤ β) :
    average (fun π => ∑ k : Fin N × Fin N, |swapped c π k - statistic c π|^3) ≤
      16*(N : ℝ)*β := by
  have hp : ∀ (π : Equiv.Perm (Fin N)) (k : Fin N × Fin N),
      |swapped c π k - statistic c π|^3 ≤ 4*β*(swapped c π k - statistic c π)^2 := by
    intro π k
    have hb : |swapped c π k - statistic c π| ≤ 4*β := by
      rw [swapped_sub]
      exact abs_rectangle_le c hβ π k.1 k.2
    calc _ = |swapped c π k - statistic c π| * |swapped c π k - statistic c π|^2 := by ring
      _ = |swapped c π k - statistic c π| * (swapped c π k - statistic c π)^2 := by rw [sq_abs]
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  calc _ ≤ average (fun π => 4*β * ∑ k : Fin N × Fin N,
          (swapped c π k - statistic c π)^2) := by
        apply average_mono
        intro π
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ => hp π k
    _ = _ := by rw [average_const_mul, array_average_sq_increment hN c hr hc hq]; ring

/-- A finite-array bounded-Lipschitz estimate, weaker than a Bolthausen bound but sufficient
for the max-entry CLT. -/
theorem array_lipschitz_bound (hN : 3 ≤ N) (c : Matrix (Fin N) (Fin N) ℝ)
    (hr : ∀ i, ∑ j, c i j = 0) (hc : ∀ j, ∑ i, c i j = 0)
    (hq : energy c = (N : ℝ)-1) {β : ℝ} (hβ : ∀ i j, |c i j| ≤ β)
    (h : ℝ → ℝ) {L C : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x-h y| ≤ L*|x-y|) (hC : ∀ x, |h x| ≤ C) :
    |average (fun π => h (statistic c π)) - (∫ x, h x ∂gaussianReal 0 1)| ≤
      32*L*Real.sqrt (β^2+1/(N : ℝ)) + 10*L*β := by
  letI instNonemptyFinArray : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hh : Continuous h := StatLean.HypothesisTesting.continuous_of_lipschitz_bound hL hlip
  have hs := StatLean.HypothesisTesting.abs_avg_sub_le
    (W := statistic c) (W' := swapped c) (lam := 2/(N : ℝ)) (by positivity)
    (array_exchangeable c) (array_regression_stein (by omega) c hr hc)
    (h := h) (f := StatLean.HypothesisTesting.steinSolution h)
    (f' := deriv (StatLean.HypothesisTesting.steinSolution h))
    (c := StatLean.HypothesisTesting.stdGaussianExpect h) (B₁ := 2*L) (B₂ := 5*L)
    (by positivity)
    (fun x => (StatLean.HypothesisTesting.hasDerivAt_steinSolution hh hC x).differentiableAt.hasDerivAt)
    (StatLean.HypothesisTesting.steinSolution_sub_mul hh hC)
    (StatLean.HypothesisTesting.abs_deriv_steinSolution_le hL hlip hC)
    (StatLean.HypothesisTesting.lipschitz_deriv_steinSolution hL hlip hC)
  have hdef : average (fun π => |1-(2*(2/(N : ℝ)))⁻¹ *
      StatLean.HypothesisTesting.condSqIncrement (statistic c) (swapped c) π|) ≤
      16*Real.sqrt (β^2+1/(N : ℝ)) := by
    have he : (fun π => |1-(2*(2/(N : ℝ)))⁻¹ *
        StatLean.HypothesisTesting.condSqIncrement (statistic c) (swapped c) π|) =
        (fun π => |normalizedSquare c π - 1|) := by
      funext π
      rw [normalizedSquare_eq_condSqIncrement (by omega) c hr hc]
      exact abs_sub_comm _ _
    rw [he]
    calc _ ≤ Real.sqrt (average (fun π => (normalizedSquare c π-1)^2)) :=
          average_abs_le_sqrt_average_square _
      _ ≤ Real.sqrt (256*(β^2+1/(N : ℝ))) :=
          Real.sqrt_le_sqrt (array_conditional_square_concentration hN c hr hc hq hβ)
      _ = _ := by
        have hsqrt : Real.sqrt (256 : ℝ) = 16 := by
          rw [show (256 : ℝ) = (16 : ℝ)^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 16)]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 256), hsqrt]
  have hcub := array_average_cubic_increment_le (by omega : 2 ≤ N) c hr hc hq hβ
  have hthird : (4*(2/(N : ℝ)))⁻¹ * (5*L) *
      ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        (Fintype.card (Fin N × Fin N) : ℝ)⁻¹ * ∑ π, ∑ k : Fin N × Fin N,
          |swapped c π k-statistic c π|^3) ≤ 10*L*β := by
    have he : (4*(2/(N : ℝ)))⁻¹ * (5*L) *
        ((Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
          (Fintype.card (Fin N × Fin N) : ℝ)⁻¹ * ∑ π, ∑ k : Fin N × Fin N,
            |swapped c π k-statistic c π|^3) =
        ((4*(2/(N : ℝ)))⁻¹ * (5*L) * (Fintype.card (Fin N × Fin N) : ℝ)⁻¹) *
          average (fun π => ∑ k : Fin N × Fin N, |swapped c π k-statistic c π|^3) := by
      unfold average
      ring
    rw [he]
    calc _ ≤ ((4*(2/(N : ℝ)))⁻¹ * (5*L) * (Fintype.card (Fin N × Fin N) : ℝ)⁻¹) *
          (16*(N : ℝ)*β) := mul_le_mul_of_nonneg_left hcub (by positivity)
      _ = _ := by rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]; field_simp; ring
  change |average (fun π => h (statistic c π)) -
    StatLean.HypothesisTesting.stdGaussianExpect h| ≤ _ at hs
  calc _ ≤ _ := hs
    _ ≤ (2*L) * (16*Real.sqrt (β^2+1/(N : ℝ))) + 10*L*β :=
      add_le_add (mul_le_mul_of_nonneg_left hdef (by positivity)) hthird
    _ = _ := by ring

/-- Uniform finite laws, with no measurable-space choice on the finite carrier exposed. -/
noncomputable def finiteLaw {α : Type*} [Fintype α] [Nonempty α] (W : α → ℝ) :
    ProbabilityMeasure ℝ := ⟨((PMF.uniformOfFintype α).map W).toMeasure, inferInstance⟩

theorem integral_finiteLaw {α : Type*} [Fintype α] [Nonempty α] (W : α → ℝ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(finiteLaw W : Measure ℝ)) = average (fun a => f (W a)) := by
  letI instMeasurableFiniteArray : MeasurableSpace α := ⊤
  letI instSingletonFiniteArray : MeasurableSingletonClass α := ⟨fun _ => trivial⟩
  have hW : Measurable W := measurable_of_finite W
  change (∫ x, f x ∂((PMF.uniformOfFintype α).map W).toMeasure) = _
  rw [← PMF.toMeasure_map W (PMF.uniformOfFintype α) hW,
    integral_map hW.aemeasurable hf.aestronglyMeasurable, PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, average, ← Finset.mul_sum]

theorem array_lipschitz_clt (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (c : (q : ℕ) → Matrix (Fin (n q)) (Fin (n q)) ℝ)
    (β : ℕ → ℝ) (hβ : Tendsto β atTop (nhds 0))
    (hc : ∀ᶠ q in atTop, 2 ≤ n q ∧
      (∀ i, ∑ j, c q i j = 0) ∧ (∀ j, ∑ i, c q i j = 0) ∧
      (∑ i, ∑ j, (c q i j)^2) = (n q : ℝ)-1 ∧ (∀ i j, |c q i j| ≤ β q))
    (f : ℝ → ℝ) {L C : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x-f y| ≤ L*|x-y|) (hC : ∀ x, |f x| ≤ C) :
    Tendsto (fun q => average (fun π => f (statistic (c q) π))) atTop
      (nhds (∫ x, f x ∂gaussianReal 0 1)) := by
  have hnr : Tendsto (fun q => (n q : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hni : Tendsto (fun q => 1/(n q : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnr
  have ha : Tendsto (fun q => (β q)^2+1/(n q : ℝ)) atTop (nhds 0) := by
    simpa using (hβ.pow 2).add hni
  have hs : Tendsto (fun q => Real.sqrt ((β q)^2+1/(n q : ℝ))) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp ha
  have hb : Tendsto (fun q => 32*L*Real.sqrt ((β q)^2+1/(n q : ℝ)) + 10*L*β q)
      atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds.mul hs).add (tendsto_const_nhds.mul hβ))
  have he : ∀ᶠ q in atTop,
      |average (fun π => f (statistic (c q) π)) - (∫ x, f x ∂gaussianReal 0 1)| ≤
      32*L*Real.sqrt ((β q)^2+1/(n q : ℝ)) + 10*L*β q := by
    filter_upwards [hc, hn.eventually (eventually_ge_atTop 3)] with q hq hnq
    exact array_lipschitz_bound hnq (c q) hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2
      f hL hlip hC
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [he, (tendsto_order.mp hb).2 ε hε] with q hq hsmall
  simpa only [Real.dist_eq] using hq.trans_lt hsmall

end AronowAudit.MapTailB.PermutationArray

/-- General max-entry permutation-array CLT. -/
theorem TailB_permutation_array_clt
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (c : (q : ℕ) → Matrix (Fin (N q)) (Fin (N q)) ℝ)
    (β : ℕ → ℝ) (hβ : Tendsto β atTop (nhds 0))
    (hc : ∀ᶠ q in atTop, 2 ≤ N q ∧
      (∀ i, ∑ j, c q i j = 0) ∧ (∀ j, ∑ i, c q i j = 0) ∧
      (∑ i, ∑ j, (c q i j)^2) = (N q : ℝ) - 1 ∧
      (∀ i j, |c q i j| ≤ β q)) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun q =>
        (∑ π : Equiv.Perm (Fin (N q)), f (∑ i, c q i (π i))) /
          (Fintype.card (Equiv.Perm (Fin (N q))) : ℝ)) atTop
        (nhds (∫ x, f x ∂(gaussianReal 0 1))) := by
  classical
  let laws : ℕ → ProbabilityMeasure ℝ := fun q =>
    AronowAudit.MapTailB.PermutationArray.finiteLaw
      (AronowAudit.MapTailB.PermutationArray.statistic (c q))
  let γ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hw : Tendsto laws atTop (nhds γ) := by
    apply MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    intro f ⟨C, hC⟩ ⟨L, hL⟩
    have hbounded : ∀ x, |f x| ≤ C + |f 0| := by
      intro x
      have hd := hC x 0
      rw [Real.dist_eq] at hd
      calc |f x| ≤ |f x-f 0| + |f 0| := by
            have ht := abs_add_le (f x-f 0) (f 0)
            simpa using ht
        _ ≤ _ := add_le_add hd le_rfl
    have hlip : ∀ x y, |f x-f y| ≤ (L : ℝ)*|x-y| := by
      intro x y
      simpa only [Real.dist_eq] using hL.dist_le_mul x y
    have hh := AronowAudit.MapTailB.PermutationArray.array_lipschitz_clt
      N hN c β hβ hc f (NNReal.coe_nonneg L) hlip hbounded
    change Tendsto (fun q => ∫ x, f x ∂(laws q : Measure ℝ)) atTop
      (nhds (∫ x, f x ∂gaussianReal 0 1))
    simpa only [laws, AronowAudit.MapTailB.PermutationArray.integral_finiteLaw _ hL.continuous]
      using hh
  intro f
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw f
  simpa only [laws, γ, AronowAudit.MapTailB.PermutationArray.integral_finiteLaw _ f.continuous,
    ProbabilityMeasure.coe_mk,
    AronowAudit.MapTailB.PermutationArray.average,
    AronowAudit.MapTailB.PermutationArray.statistic, div_eq_inv_mul] using hh

