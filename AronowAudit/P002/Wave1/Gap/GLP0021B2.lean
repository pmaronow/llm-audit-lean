import AronowAudit.P002.Wave1.Gap.GP0021B1
import AronowAudit.P002.Wave1.Gap.GP0021B2
import AronowAudit.P002.Wave1.E61Eigenvalue.N6
import AronowAudit.P002.Wave1.E61Eigenvalue.N11

/-! Finite-moment proof of the corrected control remainder (E.29).
All expectations and probabilities below are the finite complete-randomization
operators. The proof allows singular sample Grams and zero oracle variance. -/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false


private theorem E29_expectation_mono {n} (P : Population n)
    {f g : Finset (Fin n) → ℝ}
    (h : ∀ S ∈ assignments P, f S ≤ g S) : expectation P f ≤ expectation P g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

private theorem E29_expectation_nonneg {n} (P : Population n)
    (f : Finset (Fin n) → ℝ) (h : ∀ S ∈ assignments P, 0 ≤ f S) :
    0 ≤ expectation P f :=
  div_nonneg (Finset.sum_nonneg h) (Nat.cast_nonneg _)

private theorem E29_expectation_add {n} (P : Population n)
    (f g : Finset (Fin n) → ℝ) :
    expectation P (fun S => f S + g S) = expectation P f + expectation P g := by
  simp only [expectation, Finset.sum_add_distrib, add_div]

private theorem E29_expectation_fintype_sum {n} {ι : Type*} [Fintype ι]
    (P : Population n) (f : ι → Finset (Fin n) → ℝ) :
    expectation P (fun S => ∑ i, f i S) = ∑ i, expectation P (f i) := by
  unfold expectation
  rw [Finset.sum_comm, Finset.sum_div]

private theorem E29_probability_nonneg {n} (P : Population n)
    (E : Finset (Fin n) → Prop) : 0 ≤ probability P E := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem E29_indicator {n} (P : Population n)
    (E : Finset (Fin n) → Prop) :
    expectation P (fun S => if E S then (1 : ℝ) else 0) = probability P E := by
  simp [expectation, probability, Finset.sum_ite]

private theorem E29_tail_majorant {n} (P : Population n)
    (E : Finset (Fin n) → Prop) (F : Finset (Fin n) → ℝ)
    (hF : ∀ S ∈ assignments P, 0 ≤ F S)
    (hE : ∀ S ∈ assignments P, E S → 1 ≤ F S) :
    probability P E ≤ expectation P F := by
  rw [← E29_indicator]
  apply E29_expectation_mono
  intro S hS
  split_ifs with h
  · exact hE S hS h
  · exact hF S hS

private theorem E29_mean_nonneg {n} (f : Fin n → ℝ) (h : ∀ i, 0 ≤ f i) :
    0 ≤ mean f := div_nonneg (Finset.sum_nonneg (fun i _ => h i)) (Nat.cast_nonneg _)


private theorem E29_mean_cauchy {n} (f g : Fin n → ℝ) :
    (mean (fun i => f i * g i)) ^ 2 ≤
      mean (fun i => f i ^ 2) * mean (fun i => g i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) f g
  calc
    _ = (∑ i, f i * g i)^2 / (n : ℝ)^2 := by simp only [mean, div_pow]
    _ ≤ ((∑ i, f i^2) * (∑ i, g i^2)) / (n : ℝ)^2 :=
      div_le_div_of_nonneg_right h (sq_nonneg _)
    _ = _ := by simp only [mean]; ring

private theorem E29_popVar_nonneg {n} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    0 ≤ popVar q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (by linarith)

private theorem E29_popVar_bound {n} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    popVar q ≤ 2 * mean (fun i => q i^2) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsum : ∑ i, q i = (n : ℝ) * mean q := by
    rw [mean, mul_div_cancel₀ _ hn0.ne']
  have hcenter : ∑ i, (q i - mean q)^2 =
      (∑ i, q i^2) - (n : ℝ) * (mean q)^2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hsum]
    ring
  have hle : ∑ i, (q i - mean q)^2 ≤ ∑ i, q i^2 := by
    rw [hcenter]
    nlinarith [sq_nonneg (mean q)]
  calc
    popVar q ≤ (∑ i, q i^2) / ((n : ℝ)-1) :=
      div_le_div_of_nonneg_right hle (by linarith)
    _ ≤ 2 * mean (fun i => q i^2) := by
      unfold mean
      apply (div_le_iff₀ (by linarith : 0 < (n : ℝ)-1)).mpr
      rw [show 2 * ((∑ i, q i^2) / (n : ℝ)) * ((n : ℝ)-1) =
        (2 * (∑ i, q i^2) * ((n : ℝ)-1)) / (n : ℝ) by ring]
      apply (le_div_iff₀ hn0).mpr
      have hsq : 0 ≤ ∑ i, q i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      nlinarith

private def E29_complement {n} (P : Population n) : Population n :=
  { P with n1 := n - P.n1 }

private theorem E29_complement_valid {n} (P : Population n) (h : ValidDesign P) :
    ValidDesign (E29_complement P) := by
  rcases h with ⟨hn, ht, htn⟩
  exact ⟨hn, by dsimp [E29_complement]; omega, by dsimp [E29_complement]; omega⟩

private theorem E29_complement_mem {n} (P : Population n) (h : ValidDesign P)
    (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    Sᶜ ∈ assignments (E29_complement P) := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.subset_univ _, ?_⟩
  rw [Finset.card_compl, Fintype.card_fin, (Finset.mem_powersetCard.mp hS).2]
  rfl

private theorem E29_complement_invol {n} (P : Population n) (h : ValidDesign P) :
    E29_complement (E29_complement P) = P := by
  cases P
  simp only [E29_complement, Population.mk.injEq, true_and]
  dsimp [ValidDesign] at h
  omega

private theorem E29_complement_sum {n} (P : Population n) (h : ValidDesign P)
    (f : Finset (Fin n) → ℝ) :
    (∑ S ∈ assignments P, f Sᶜ) = ∑ S ∈ assignments (E29_complement P), f S := by
  apply Finset.sum_bij (fun S _ => Sᶜ)
  · intro S hS
    exact E29_complement_mem P h S hS
  · intro S hS T hT hST
    simpa only [compl_compl] using congrArg (fun U : Finset (Fin n) => Uᶜ) hST
  · intro T hT
    refine ⟨Tᶜ, ?_, compl_compl T⟩
    have hh := E29_complement_mem (E29_complement P) (E29_complement_valid P h) T hT
    simpa only [E29_complement_invol P h] using hh
  · intro S hS
    rfl

private theorem E29_complement_expectation {n} (P : Population n) (h : ValidDesign P)
    (f : Finset (Fin n) → ℝ) :
    expectation P (fun S => f Sᶜ) = expectation (E29_complement P) f := by
  have hc := E29_complement_sum P h (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  unfold expectation
  rw [E29_complement_sum P h f, hc]

private theorem E29_control_second {n} (P : Population n) (h : ValidDesign P)
    (q : Fin n → ℝ) :
    expectation P (fun S => (groupMean Sᶜ q - mean q)^2) =
      (P.n1 : ℝ) / (controlSize P * (n : ℝ)) * popVar q := by
  rw [E29_complement_expectation P h (fun S => (groupMean S q - mean q)^2),
    sample_mean_variance_proof (E29_complement P) (E29_complement_valid P h)]
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := h.1; omega)
  have ht : (P.n1 : ℝ) ≤ n := by exact_mod_cast h.2.2.le
  have hN1 : (n : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast h.1
    linarith
  simp only [E29_complement, controlSize, Nat.cast_sub h.2.2.le, popVar]
  field_simp
  <;> ring

private theorem E29_control_moment {n} (P : Population n) (h : ValidDesign P)
    (r C : ℝ) (hr : 0 < r) (hbal : (P.n1 : ℝ) ≤ (1-r)*(n : ℝ))
    (q : Fin n → ℝ) (hq : mean (fun i => q i^2) ≤ C) :
    expectation P (fun S => (groupMean Sᶜ q - mean q)^2) ≤ 2*C/(r*(n : ℝ)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := h.1; omega)
  have ht : (P.n1 : ℝ) < n := by exact_mod_cast h.2.2
  have hc : 0 < controlSize P := by unfold controlSize; linarith
  have hrc : r*(n : ℝ) ≤ controlSize P := by unfold controlSize; nlinarith
  have hcoeff : (P.n1 : ℝ)/(controlSize P*(n : ℝ)) ≤ 1/(r*(n : ℝ)) := by
    calc
      _ ≤ 1 / controlSize P := by
        apply (div_le_div_iff₀ (mul_pos hc hn) hc).mpr
        nlinarith
      _ ≤ _ := one_div_le_one_div_of_le (mul_pos hr hn) hrc
  rw [E29_control_second P h q]
  calc
    _ ≤ (1/(r*(n : ℝ))) * (2*C) :=
      mul_le_mul hcoeff (le_trans (E29_popVar_bound h.1 q) (by linarith))
        (E29_popVar_nonneg h.1 q) (by positivity)
    _ = _ := by ring

private theorem E29_normSq_nonneg {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    0 ≤ normSq b := Finset.sum_nonneg (fun i _ => sq_nonneg _)

private theorem E29_normSq_zero {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (h : normSq b = 0) : b = 0 := by
  funext i
  have hi : b i^2 ≤ normSq b :=
    Finset.single_le_sum (fun j _ => sq_nonneg (b j)) (Finset.mem_univ i)
  rw [h] at hi
  exact (sq_nonpos_iff _).mp hi

private theorem E29_dot_sq {ι : Type*} [Fintype ι] (b h : ι → ℝ) :
    (dotProduct b h)^2 ≤ normSq b * normSq h :=
  Finset.sum_mul_sq_le_sq_mul_sq _ b h

private theorem E29_coercive_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hco : ∀ b, c * normSq b ≤ dotProduct b (H *ᵥ b)) : H.det ≠ 0 := by
  have hker (b : ι → ℝ) (hb : H *ᵥ b = 0) : b = 0 := by
    have hh := hco b
    rw [hb, dotProduct_zero] at hh
    exact E29_normSq_zero b (le_antisymm (nonpos_of_mul_nonpos_right hh hc)
      (E29_normSq_nonneg b))
  have hinj : Function.Injective H.mulVec := by
    intro b d hbd
    have hz : H *ᵥ (b-d) = 0 := by rw [Matrix.mulVec_sub, hbd]; simp
    exact sub_eq_zero.mp (hker (b-d) hz)
  have hu : IsUnit H := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det H).mp hu)

private theorem E29_inverse_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hco : ∀ b, c * normSq b ≤ dotProduct b (H *ᵥ b)) (h : ι → ℝ) :
    c^2 * normSq (H⁻¹ *ᵥ h) ≤ normSq h := by
  have hd := E29_coercive_det H c hc hco
  let b := H⁻¹ *ᵥ h
  have hHb : H *ᵥ b = h := by
    dsimp only [b]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), Matrix.one_mulVec]
  have hb := hco b
  rw [hHb] at hb
  have hsq : (c * normSq b)^2 ≤ (dotProduct b h)^2 :=
    (sq_le_sq₀ (mul_nonneg hc.le (E29_normSq_nonneg b)) (by
      exact le_trans (mul_nonneg hc.le (E29_normSq_nonneg b)) hb)).mpr hb
  have hcs := E29_dot_sq b h
  by_cases hz : normSq b = 0
  · simpa only [b, hz, mul_zero] using E29_normSq_nonneg h
  · have hp : 0 < normSq b := lt_of_le_of_ne (E29_normSq_nonneg b) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith

private theorem E29_population_coercive {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hP : Xi P δ e A B r) :
    ∀ b, min 1 e * normSq b ≤ dotProduct b (gram P.x Finset.univ *ᵥ b) := by
  rcases hP with ⟨hD, _, _, _, _, _, _, hx, _, hray⟩
  have hn : 0 < n := by have := hD.1; omega
  intro b
  have hh := (corrected_augmented_gram P.x hn e hx hray).2.2.2 b
  rw [gram_quadratic]
  simpa only [groupMean, mean, Finset.card_univ, Fintype.card_fin] using hh

private theorem E29_population_normal {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r)
    (a : Bool) (s : Option (Fin k)) :
    mean (fun i => augmented P.x i s * residual P a (late P.pop) i) = 0 := by
  have hg := E29_coercive_det (gram P.x Finset.univ) (min 1 e)
    (lt_min zero_lt_one he) (E29_population_coercive P δ e A B r hP)
  have hh : score P.x Finset.univ (residual P a (late P.pop)) = 0 := by
    change score P.x Finset.univ (fun i => w P.pop a (late P.pop) i -
      dotProduct (augmented P.x i) (ols P.x Finset.univ (w P.pop a (late P.pop)))) = 0
    rw [score_residual, ols_normal_equations P.x Finset.univ _ hg, sub_self]
  simpa only [score, groupMean, mean, Finset.card_univ, Fintype.card_fin, Pi.zero_apply]
    using congrFun hh s

private theorem E29_fourth_bound {n} (q : Fin n → ℝ) (B s : ℝ)
    (hB : 0 < B) (hs : 0 ≤ s) (hq : fourthNorm q ≤ B * Real.sqrt s) :
    mean (fun i => q i^4) ≤ B^4 * s^2 := by
  have hq4 : 0 ≤ mean (fun i => q i^4) := E29_mean_nonneg _ (fun i => by positivity)
  have hh := (sq_le_sq₀ (Real.sqrt_nonneg (Real.sqrt (mean (fun i => q i^4))))
    (mul_nonneg hB.le (Real.sqrt_nonneg s))).mpr hq
  simp only [Real.sq_sqrt (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hs] at hh
  have hh' := (sq_le_sq₀ (Real.sqrt_nonneg (mean (fun i => q i^4)))
    (mul_nonneg (sq_nonneg B) hs)).mpr hh
  rw [Real.sq_sqrt hq4] at hh'
  nlinarith

private theorem E29_augmented_fourth {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hP : Xi P δ e A B r) (s : Option (Fin k)) :
    mean (fun i => augmented P.x i s ^ 4) ≤ max 1 A := by
  rcases hP with ⟨hD, _, _, _, _, _, _, _, hx4, _⟩
  cases s with
  | none =>
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := hD.1; omega)
    simpa only [augmented, one_pow, mean, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, div_self hn] using le_max_left (1 : ℝ) A
  | some s => exact (hx4 s).trans (le_max_right _ _)

private theorem E29_score_square {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hB : 0 < B) (hP : Xi P δ e A B r)
    (s : Option (Fin k)) :
    mean (fun i => (augmented P.x i s * residual P false (late P.pop) i)^2) ≤
      (max 1 A + B^4 + 1) * popVar (residual P false (late P.pop)) := by
  let z := fun i => augmented P.x i s
  let q := residual P false (late P.pop)
  let v := popVar q
  let D := max (1 : ℝ) A
  let K := D + B^4 + 1
  have hv : 0 ≤ v := E29_popVar_nonneg hP.1.1 q
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hz4 : mean (fun i => z i^4) ≤ D := E29_augmented_fourth P δ e A B r hP s
  have hq4 : mean (fun i => q i^4) ≤ B^4*v^2 :=
    E29_fourth_bound q B v hB hv (hP.2.2.2.2.2.2.1 false)
  have hcs : (mean (fun i => (z i * q i)^2))^2 ≤
      mean (fun i => z i^4) * mean (fun i => q i^4) := by
    convert E29_mean_cauchy (fun i => z i^2) (fun i => q i^2) using 2 <;>
      congr 1 <;> funext i <;> ring
  have hcs' : (mean (fun i => (z i * q i)^2))^2 ≤ D * (B^4*v^2) :=
    hcs.trans (mul_le_mul hz4 hq4
      (E29_mean_nonneg _ (fun i => by positivity)) hD.le)
  have hKD : D*B^4 ≤ K^2 := by
    dsimp [K]
    nlinarith [sq_nonneg (D - B^4), pow_nonneg hB.le 4]
  have hlast : D*(B^4*v^2) ≤ (K*v)^2 := by
    have := mul_le_mul_of_nonneg_right hKD (sq_nonneg v)
    nlinarith
  exact (sq_le_sq₀ (E29_mean_nonneg _ (fun i => sq_nonneg _))
    (mul_nonneg hK hv)).mp (hcs'.trans hlast)

private def E29_controlMean {n k} (P : CovPopulation n k) (S : Finset (Fin n)) :
    Option (Fin k) → ℝ := fun s => groupMean Sᶜ (fun i => xCirc P.x i s)

private def E29_gramError {n k} (P : CovPopulation n k) (S : Finset (Fin n)) : ℝ :=
  ∑ s, ∑ t, (gram P.x Sᶜ s t - gram P.x Finset.univ s t)^2

private theorem E29_gramError_nonneg {n k} (P : CovPopulation n k) (S : Finset (Fin n)) :
    0 ≤ E29_gramError P S :=
  Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun t _ => sq_nonneg _))

private theorem E29_gram_moment {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hr : 0 < r) (hP : Xi P δ e A B r) :
    expectation P.pop (E29_gramError P) ≤
      2*((k : ℝ)+1)^2 * max 1 A / (r*(n : ℝ)) := by
  unfold E29_gramError
  rw [E29_expectation_fintype_sum]
  simp_rw [E29_expectation_fintype_sum]
  calc
    _ ≤ ∑ s : Option (Fin k), ∑ t : Option (Fin k), 2*max 1 A/(r*(n : ℝ)) := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      have hentry := E61Eigenvalue.n6_proof n k P δ e A B r hP s t
      simpa only [gram, groupMean, mean, Finset.card_univ, Fintype.card_fin] using
        E29_control_moment P.pop hP.1 r (max 1 A) hr hP.2.2.2.2.1
          (fun i => augmented P.x i s * augmented P.x i t) hentry
    _ = _ := by simp [Fintype.card_option]; ring

private theorem E29_score_moment {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hB : 0 < B) (hr : 0 < r)
    (hP : Xi P δ e A B r) :
    expectation P.pop (fun S => normSq (score P.x Sᶜ (residual P false (late P.pop)))) ≤
      2*((k : ℝ)+1)*(max 1 A+B^4+1)*popVar (residual P false (late P.pop))/(r*(n : ℝ)) := by
  unfold normSq
  rw [E29_expectation_fintype_sum]
  calc
    _ ≤ ∑ s : Option (Fin k),
        2*((max 1 A+B^4+1)*popVar (residual P false (late P.pop)))/(r*(n : ℝ)) := by
      apply Finset.sum_le_sum
      intro s _
      have hh := E29_control_moment P.pop hP.1 r
        ((max 1 A+B^4+1)*popVar (residual P false (late P.pop))) hr hP.2.2.2.2.1
        (fun i => augmented P.x i s * residual P false (late P.pop) i)
        (E29_score_square P δ e A B r hB hP s)
      simpa only [E29_population_normal P δ e A B r he hP false s, sub_zero, score]
        using hh
    _ = _ := by simp [Fintype.card_option]; ring

private theorem E29_controlMean_moment {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hr : 0 < r) (hP : Xi P δ e A B r) :
    expectation P.pop (fun S => normSq (E29_controlMean P S)) ≤
      2*((k : ℝ)+1)*max 1 A/(r*(n : ℝ)) := by
  have hx := hP.2.2.2.2.2.2.2.1
  unfold normSq
  rw [E29_expectation_fintype_sum]
  calc
    _ ≤ ∑ s : Option (Fin k), 2*max 1 A/(r*(n : ℝ)) := by
      apply Finset.sum_le_sum
      intro s _
      have hz : mean (fun i => xCirc P.x i s) = 0 := by
        cases s <;> simp [xCirc, mean, hx]
      have hsq : mean (fun i => xCirc P.x i s ^2) ≤ max 1 A := by
        cases s with
        | none => simp [xCirc, mean]
        | some s =>
          simpa only [augmented, mul_one, xCirc] using
            E61Eigenvalue.n6_proof n k P δ e A B r hP (some s) none
      simpa only [E29_controlMean, hz, sub_zero] using
        E29_control_moment P.pop hP.1 r (max 1 A) hr hP.2.2.2.2.1
          (fun i => xCirc P.x i s) hsq
    _ = _ := by simp [Fintype.card_option]; ring

private theorem E29_good_gram {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r)
    (S : Finset (Fin n))
    (hgood : E29_gramError P S < (min 1 e / (2*((k : ℝ)+1)))^2) :
    ∀ b, (min 1 e / 2) * normSq b ≤ dotProduct b (gram P.x Sᶜ *ᵥ b) := by
  let d : ℝ := (k : ℝ)+1
  let ell : ℝ := min 1 e
  let t : ℝ := ell/(2*d)
  have hd : 0 < d := by dsimp [d]; positivity
  have hell : 0 < ell := lt_min zero_lt_one he
  have ht : 0 < t := div_pos hell (by positivity)
  have hentry (s t' : Option (Fin k)) :
      |gram P.x Sᶜ s t' - gram P.x Finset.univ s t'| ≤ t := by
    have hi : (gram P.x Sᶜ s t' - gram P.x Finset.univ s t')^2 ≤ E29_gramError P S := by
      calc
        _ ≤ ∑ u, (gram P.x Sᶜ s u - gram P.x Finset.univ s u)^2 :=
          Finset.single_le_sum (fun u _ => sq_nonneg _) (Finset.mem_univ t')
        _ ≤ _ := by
          change (∑ u, (gram P.x Sᶜ s u - gram P.x Finset.univ s u)^2) ≤
            ∑ v, ∑ u, (gram P.x Sᶜ v u - gram P.x Finset.univ v u)^2
          exact Finset.single_le_sum
            (f := fun v : Option (Fin k) =>
              ∑ u : Option (Fin k), (gram P.x Sᶜ v u - gram P.x Finset.univ v u)^2)
            (fun v _ => Finset.sum_nonneg (fun u _ =>
              sq_nonneg (gram P.x Sᶜ v u - gram P.x Finset.univ v u))) (Finset.mem_univ s)
    have hj : (gram P.x Sᶜ s t' - gram P.x Finset.univ s t')^2 ≤ t^2 := hi.trans hgood.le
    nlinarith [sq_abs (gram P.x Sᶜ s t' - gram P.x Finset.univ s t')]
  intro b
  have hb := E61Eigenvalue.n11_proof k (gram P.x Sᶜ) (gram P.x Finset.univ) t hentry b
  have hG := E29_population_coercive P δ e A B r hP b
  have hdt : ((k : ℝ)+1)*t = ell/2 := by
    change d*(ell/(2*d)) = ell/2
    field_simp
  rw [hdt] at hb
  have hb' := (abs_le.mp hb).1
  change ell * normSq b ≤ _ at hG
  change ell / 2 * normSq b ≤ _
  linarith

private theorem E29_controlMean_dot {n k} (P : CovPopulation n k)
    (S : Finset (Fin n)) (b : Option (Fin k) → ℝ) :
    groupMean Sᶜ (fun i => dotProduct (xCirc P.x i) b) =
      dotProduct (E29_controlMean P S) b := by
  simp only [groupMean, dotProduct, E29_controlMean, Finset.sum_div,
    Finset.sum_mul, div_mul_eq_mul_div]
  exact Finset.sum_comm

private theorem E29_remainder_zero {n k} (P : CovPopulation n k)
    (hV : designVariance P.pop (oracleTau P (late P.pop)) = 0)
    (S : Finset (Fin n)) : controlRemainder P S = 0 := by
  simp [controlRemainder, hV]

private theorem E29_remainder_bound {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (he : 0 < e) (hP : Xi P δ e A B r)
    (S : Finset (Fin n))
    (hgood : E29_gramError P S < (min 1 e / (2*((k : ℝ)+1)))^2)
    (hV : 0 < designVariance P.pop (oracleTau P (late P.pop))) (m : ℝ) (hm : 0 < m) :
    min 1 e * |controlRemainder P S| ≤
      m * normSq (E29_controlMean P S) +
        normSq (score P.x Sᶜ (residual P false (late P.pop))) /
          (m * designVariance P.pop (oracleTau P (late P.pop))) := by
  let ell : ℝ := min 1 e
  let V := designVariance P.pop (oracleTau P (late P.pop))
  let h := score P.x Sᶜ (residual P false (late P.pop))
  let b := (gram P.x Sᶜ)⁻¹ *ᵥ h
  let u := E29_controlMean P S
  have hell : 0 < ell := lt_min zero_lt_one he
  have hi : (ell/2)^2 * normSq b ≤ normSq h :=
    E29_inverse_bound (gram P.x Sᶜ) (ell/2) (by positivity)
      (E29_good_gram P δ e A B r he hP S hgood) h
  have hcs := E29_dot_sq u b
  have hnum : controlRemainder P S = dotProduct u b / Real.sqrt V :=
    congrArg (fun z : ℝ => z / Real.sqrt V) (E29_controlMean_dot P S b)
  have hsq : (ell * |controlRemainder P S|)^2 ≤
      4 * normSq u * normSq h / V := by
    have hm0 := mul_le_mul_of_nonneg_left hi (E29_normSq_nonneg u)
    have hcs' := mul_le_mul_of_nonneg_left hcs (sq_nonneg (ell/2))
    rw [hnum, mul_pow, sq_abs, div_pow, Real.sq_sqrt hV.le, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hV.le
    nlinarith
  let W := m * normSq u + normSq h / (m*V)
  have hW : 0 ≤ W := add_nonneg (mul_nonneg hm.le (E29_normSq_nonneg u))
    (div_nonneg (E29_normSq_nonneg h) (mul_pos hm hV).le)
  have hAM : 4*normSq u*normSq h/V ≤ W^2 := by
    have hh := sq_nonneg (m * normSq u - normSq h / (m*V))
    have hid : 4*(m*normSq u)*(normSq h/(m*V)) = 4*normSq u*normSq h/V := by
      field_simp
    dsimp [W]
    nlinarith
  exact (sq_le_sq₀ (mul_nonneg hell.le (abs_nonneg _)) hW).mp (hsq.trans hAM)

private theorem E29_variance_lower {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hk : 0 < k) (hδ : δ < 1) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r ∧ r ≤ 1/2) (hP : Xi P δ e A B r) :
    ((1-max δ 0)*r) * popVar (residual P false (late P.pop)) / (n : ℝ) ≤
      designVariance P.pop (oracleTau P (late P.pop)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1.1; omega)
  have hr0 : 0 < r := hr.1
  have ht : (0 : ℝ) < P.pop.n1 := by exact_mod_cast hP.1.2.1
  have htn : (P.pop.n1 : ℝ) < n := by exact_mod_cast hP.1.2.2
  have hc : 0 < controlSize P.pop := by unfold controlSize; linarith
  have hg : 0 < 1-max δ 0 := sub_pos.mpr (max_lt hδ zero_lt_one)
  have hv0 := E29_popVar_nonneg hP.1.1 (residual P false (late P.pop))
  have hv1 := E29_popVar_nonneg hP.1.1 (residual P true (late P.pop))
  have hrc : r * controlSize P.pop ≤ (P.pop.n1 : ℝ) := by
    have hlo := hP.2.2.2.1
    have hcn : controlSize P.pop ≤ (n : ℝ) := by unfold controlSize; linarith
    exact (mul_le_mul_of_nonneg_left hcn hr.1.le).trans hlo
  have hcoef : r/(n : ℝ) ≤ (P.pop.n1 : ℝ)/((n : ℝ)*controlSize P.pop) := by
    apply (div_le_div_iff₀ hn (mul_pos hn hc)).mpr
    nlinarith
  calc
    _ = (1-max δ 0) * (r/(n : ℝ)) * popVar (residual P false (late P.pop)) := by ring
    _ ≤ (1-max δ 0) * ((P.pop.n1 : ℝ)/((n : ℝ)*controlSize P.pop)) *
        popVar (residual P false (late P.pop)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hg.le) hv0
    _ ≤ (1-max δ 0) * (controlSize P.pop/((n : ℝ)*(P.pop.n1 : ℝ))*
        popVar (residual P true (late P.pop)) +
        (P.pop.n1 : ℝ)/((n : ℝ)*controlSize P.pop)*popVar (residual P false (late P.pop))) := by
      have hh : 0 ≤ controlSize P.pop/((n : ℝ)*(P.pop.n1 : ℝ))*
          popVar (residual P true (late P.pop)) := by positivity
      nlinarith
    _ ≤ _ := corrected_E10_proof P δ e A B r hk hδ he hA hB hr hP

private def E29_bound1 (k : ℕ) (e A r : ℝ) : ℝ :=
  2*((k : ℝ)+1)^2*max 1 A /
    (r*(min 1 e / (2*((k : ℝ)+1)))^2)

private def E29_bound2 (k : ℕ) (δ e A B r κ : ℝ) : ℝ :=
  (2*((k : ℝ)+1)*max 1 A/r +
    2*((k : ℝ)+1)*(max 1 A+B^4+1)/(r*((1-max δ 0)*r))) / (min 1 e*κ)

private theorem E29_finite_tail {n k} (P : CovPopulation n k)
    (δ e A B r : ℝ) (hk : 0 < k) (hδ : δ < 1) (he : 0 < e)
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r ∧ r ≤ 1/2) (hP : Xi P δ e A B r)
    (κ : ℝ) (hκ : 0 < κ) :
    probability P.pop (fun S => κ ≤ |controlRemainder P S|) ≤
      E29_bound1 k e A r / (n : ℝ) + E29_bound2 k δ e A B r κ / Real.sqrt (n : ℝ) := by
  let d : ℝ := (k : ℝ)+1
  let D : ℝ := max 1 A
  let K : ℝ := D+B^4+1
  let ell : ℝ := min 1 e
  let a : ℝ := (1-max δ 0)*r
  let T : ℝ := (ell/(2*d))^2
  let m : ℝ := Real.sqrt (n : ℝ)
  let V : ℝ := designVariance P.pop (oracleTau P (late P.pop))
  let U := fun S => normSq (E29_controlMean P S)
  let H := fun S => normSq (score P.x Sᶜ (residual P false (late P.pop)))
  let Cg : ℝ := 2*d^2*D/r
  let Cu : ℝ := 2*d*D/r
  let Ch : ℝ := 2*d*K/r
  have hr0 : 0 < r := hr.1
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hP.1.1; omega)
  have hd : 0 < d := by dsimp [d]; positivity
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK : 0 < K := by dsimp [K]; positivity
  have hell : 0 < ell := lt_min zero_lt_one he
  have ha : 0 < a := mul_pos (sub_pos.mpr (max_lt hδ zero_lt_one)) hr.1
  have hT : 0 < T := sq_pos_of_pos (div_pos hell (by positivity))
  have hm : 0 < m := Real.sqrt_pos.mpr hn
  have hmsq : m^2 = (n : ℝ) := Real.sq_sqrt hn.le
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hCu : 0 ≤ Cu := by dsimp [Cu]; positivity
  have hCh : 0 ≤ Ch := by dsimp [Ch]; positivity
  have hV0 : 0 ≤ V := E29_expectation_nonneg P.pop _ (fun S _ => sq_nonneg _)
  have hGb : expectation P.pop (E29_gramError P) ≤ Cg/(n : ℝ) := by
    convert E29_gram_moment P δ e A B r hr.1 hP using 1 <;> dsimp [Cg, d, D] <;> ring
  have hUb : expectation P.pop U ≤ Cu/(n : ℝ) := by
    convert E29_controlMean_moment P δ e A B r hr.1 hP using 1 <;> dsimp [Cu, d, D] <;> ring
  have hHb : expectation P.pop H ≤ Ch*popVar (residual P false (late P.pop))/(n : ℝ) := by
    convert E29_score_moment P δ e A B r he hB hr.1 hP using 1 <;>
      dsimp [Ch, d, K, D] <;> ring
  have hVl : a*popVar (residual P false (late P.pop))/(n : ℝ) ≤ V :=
    E29_variance_lower P δ e A B r hk hδ he hA hB hr hP
  have h1 : E29_bound1 k e A r = Cg/T := by
    change (2*d^2*D)/(r*T) = ((2*d^2*D)/r)/T
    rw [div_div]
  have h2 : E29_bound2 k δ e A B r κ = (Cu+Ch/a)/(ell*κ) := by
    change (Cu + (2*d*K)/(r*a))/(ell*κ) = (Cu+(2*d*K/r)/a)/(ell*κ)
    rw [div_div]
  have htarget : 0 ≤ E29_bound1 k e A r/(n : ℝ) +
      E29_bound2 k δ e A B r κ/m := by
    rw [h1, h2]
    positivity
  by_cases hz : V = 0
  · have hz' : designVariance P.pop (oracleTau P (late P.pop)) = 0 := hz
    have hp : probability P.pop (fun S => κ ≤ |controlRemainder P S|) = 0 := by
      simp [probability, E29_remainder_zero P hz', not_le_of_gt hκ]
    rw [hp]
    exact htarget
  have hV : 0 < V := lt_of_le_of_ne hV0 (Ne.symm hz)
  have hHV : expectation P.pop H / V ≤ Ch/a := by
    apply (div_le_iff₀ hV).mpr
    have hh := mul_le_mul_of_nonneg_left hVl (div_nonneg hCh ha.le)
    have hid : (Ch/a)*(a*popVar (residual P false (late P.pop))/(n : ℝ)) =
        Ch*popVar (residual P false (late P.pop))/(n : ℝ) := by
      field_simp
    rw [hid] at hh
    exact hHb.trans hh
  let F := fun S => E29_gramError P S/T + (m*U S+H S/(m*V))/(ell*κ)
  have hF (S : Finset (Fin n)) : 0 ≤ F S := by
    dsimp only [F, U, H]
    exact add_nonneg (div_nonneg (E29_gramError_nonneg P S) hT.le)
      (div_nonneg (add_nonneg (mul_nonneg hm.le (E29_normSq_nonneg _))
        (div_nonneg (E29_normSq_nonneg _) (mul_pos hm hV).le)) (mul_pos hell hκ).le)
  have hp : probability P.pop (fun S => κ ≤ |controlRemainder P S|) ≤ expectation P.pop F := by
    apply E29_tail_majorant P.pop _ F (fun S _ => hF S)
    intro S hS htail
    by_cases hbad : T ≤ E29_gramError P S
    · have hfirst : 1 ≤ E29_gramError P S/T := (le_div_iff₀ hT).mpr (by simpa using hbad)
      have hsecond : 0 ≤ (m*U S+H S/(m*V))/(ell*κ) := by
        exact div_nonneg (add_nonneg (mul_nonneg hm.le (E29_normSq_nonneg _))
          (div_nonneg (E29_normSq_nonneg _) (mul_pos hm hV).le)) (mul_pos hell hκ).le
      exact le_trans hfirst (le_add_of_nonneg_right hsecond)
    · have hgood : E29_gramError P S < T := lt_of_not_ge hbad
      have hrem := E29_remainder_bound P δ e A B r he hP S hgood hV m hm
      have htail' : ell*κ ≤ m*U S+H S/(m*V) :=
        (mul_le_mul_of_nonneg_left htail hell.le).trans hrem
      have hsecond : 1 ≤ (m*U S+H S/(m*V))/(ell*κ) :=
        (le_div_iff₀ (mul_pos hell hκ)).mpr (by simpa using htail')
      have hfirst : 0 ≤ E29_gramError P S/T := div_nonneg (E29_gramError_nonneg P S) hT.le
      exact le_trans hsecond (le_add_of_nonneg_left hfirst)
  have hEF : expectation P.pop F = expectation P.pop (E29_gramError P)/T +
      (m*expectation P.pop U+(expectation P.pop H/V)/m)/(ell*κ) := by
    dsimp only [F]
    rw [E29_expectation_add, expectation_div, expectation_div, E29_expectation_add,
      expectation_mul, expectation_div]
    ring
  have hEFb : expectation P.pop F ≤ (Cg/(n : ℝ))/T +
      (m*(Cu/(n : ℝ))+(Ch/a)/m)/(ell*κ) := by
    rw [hEF]
    apply add_le_add
    · exact div_le_div_of_nonneg_right hGb hT.le
    · apply div_le_div_of_nonneg_right _ (mul_pos hell hκ).le
      exact add_le_add (mul_le_mul_of_nonneg_left hUb hm.le)
        (div_le_div_of_nonneg_right hHV hm.le)
  apply hp.trans (hEFb.trans_eq ?_)
  change (Cg/(n : ℝ))/T + (m*(Cu/(n : ℝ))+(Ch/a)/m)/(ell*κ) =
    E29_bound1 k e A r/(n : ℝ) + E29_bound2 k δ e A B r κ/m
  have hmn : m/(n : ℝ) = 1/m := by
    apply (div_eq_div_iff hn.ne' hm.ne').mpr
    nlinarith
  rw [h1, h2]
  calc
    _ = (Cg/T)/(n : ℝ) + (Cu*(m/(n : ℝ))+(Ch/a)/m)/(ell*κ) := by ring
    _ = _ := by rw [hmn]; ring

/-- The corrected control-arm remainder is negligible in design probability. -/
theorem corrected_E29_proof (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ n, CovPopulation (sizes n) k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : ∀ n, Xi (P n) δ e A B r) :
    ∀ κ : ℝ, 0 < κ → Tendsto (fun n => probability (P n).pop
      (fun S => κ ≤ |controlRemainder (P n) S|)) atTop (nhds 0) := by
  intro κ hκ
  have hN : Tendsto (fun n => (sizes n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hroot : Tendsto (fun n => Real.sqrt (sizes n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hN
  have hmajor : Tendsto (fun n => E29_bound1 k e A r/(sizes n : ℝ) +
      E29_bound2 k δ e A B r κ/Real.sqrt (sizes n : ℝ)) atTop (nhds 0) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.div_atTop hN).add (tendsto_const_nhds.div_atTop hroot)
  exact squeeze_zero (fun n => E29_probability_nonneg _ _)
    (fun n => E29_finite_tail (P n) δ e A B r hk hδ he hA hB hr (hP n) κ hκ) hmajor

end
end AronowAudit.P002.Wave1
