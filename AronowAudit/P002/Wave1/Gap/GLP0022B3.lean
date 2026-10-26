import AronowAudit.P002.P002_Audit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Bounds

/-! P002-T6: the explicit near-singular finite-population counterexample. -/
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
set_option pp.proofs false

private def FV_grid (n : ℕ) (i : Fin n) : ℝ :=
  (2 * (i.val : ℝ) - (n : ℝ) + 1) / ((n : ℝ) - 1)
private def FV_v (n : ℕ) : ℝ := ((n : ℝ) + 1) / (3 * ((n : ℝ) - 1))
private def FV_W (n : ℕ) : ℝ :=
  4 * ((n : ℝ) + 1) * ((n : ℝ) - 2) * ((n : ℝ) + 2) /
    (45 * ((n : ℝ) - 1)^3)

private lemma FV_power_sums (n : ℕ) :
    (∑ j ∈ Finset.range n, (j : ℝ)) = (n : ℝ) * ((n : ℝ)-1) / 2 ∧
    (∑ j ∈ Finset.range n, (j : ℝ)^2) =
      (n : ℝ) * ((n : ℝ)-1) * (2*(n : ℝ)-1) / 6 ∧
    (∑ j ∈ Finset.range n, (j : ℝ)^3) = (n : ℝ)^2 * ((n : ℝ)-1)^2 / 4 ∧
    (∑ j ∈ Finset.range n, (j : ℝ)^4) =
      (n : ℝ) * ((n : ℝ)-1) * (2*(n : ℝ)-1) *
        (3*(n : ℝ)^2-3*(n : ℝ)-1) / 30 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    rw [ih.1, ih.2.1, ih.2.2.1, ih.2.2.2]
    constructor
    · ring
    constructor
    · ring
    constructor <;> ring

private lemma FV_grid_sums (n : ℕ) (hn : 2 ≤ n) :
    (∑ i, FV_grid n i) = 0 ∧
    (∑ i, FV_grid n i ^ 2) = (n : ℝ) * FV_v n ∧
    (∑ i, FV_grid n i ^ 3) = 0 ∧
    (∑ i, FV_grid n i ^ 4) =
      (n : ℝ) * ((n : ℝ)+1) * (3*(n : ℝ)^2-7) / (15*((n : ℝ)-1)^3) := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (n : ℝ)-1 ≠ 0 := by linarith
  obtain ⟨h1,h2,h3,h4⟩ := FV_power_sums n
  simp only [FV_grid, div_pow]
  rw [Fin.sum_univ_eq_sum_range (fun j => (2*(j : ℝ)-(n : ℝ)+1)/((n : ℝ)-1)),
    Fin.sum_univ_eq_sum_range (fun j => (2*(j : ℝ)-(n : ℝ)+1)^2/((n : ℝ)-1)^2),
    Fin.sum_univ_eq_sum_range (fun j => (2*(j : ℝ)-(n : ℝ)+1)^3/((n : ℝ)-1)^3),
    Fin.sum_univ_eq_sum_range (fun j => (2*(j : ℝ)-(n : ℝ)+1)^4/((n : ℝ)-1)^4)]
  simp only [← Finset.sum_div]
  constructor
  · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, h1]
    field_simp
    <;> ring
  constructor
  · have he : (∑ i ∈ Finset.range n, (2*(i : ℝ)-(n : ℝ)+1)^2) =
        4 * (∑ i ∈ Finset.range n, (i : ℝ)^2) +
        (4-4*(n : ℝ)) * (∑ i ∈ Finset.range n, (i : ℝ)) +
        (n : ℝ) * ((n : ℝ)^2-2*(n : ℝ)+1) := by
      calc
        _ = ∑ i ∈ Finset.range n, (4*(i : ℝ)^2+(4-4*(n : ℝ))*(i : ℝ)+((n : ℝ)^2-2*(n : ℝ)+1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          <;> ring
    rw [he, h1, h2]
    dsimp [FV_v]
    field_simp [hd]
    <;> ring
  constructor
  · have he : (∑ i ∈ Finset.range n, (2*(i : ℝ)-(n : ℝ)+1)^3) =
        8 * (∑ i ∈ Finset.range n, (i : ℝ)^3) +
        (12-12*(n : ℝ)) * (∑ i ∈ Finset.range n, (i : ℝ)^2) +
        (6*(n : ℝ)^2-12*(n : ℝ)+6) * (∑ i ∈ Finset.range n, (i : ℝ)) +
        (n : ℝ) * (1-3*(n : ℝ)+3*(n : ℝ)^2-(n : ℝ)^3) := by
      calc
        _ = ∑ i ∈ Finset.range n, (8*(i : ℝ)^3+(12-12*(n : ℝ))*(i : ℝ)^2+(6*(n : ℝ)^2-12*(n : ℝ)+6)*(i : ℝ)+(1-3*(n : ℝ)+3*(n : ℝ)^2-(n : ℝ)^3)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          <;> ring
    rw [he, h1, h2, h3]
    have hz : 8 * ((n : ℝ)^2 * ((n : ℝ)-1)^2 / 4) +
        (12-12*(n : ℝ)) * ((n : ℝ)*((n : ℝ)-1)*(2*(n : ℝ)-1)/6) +
        (6*(n : ℝ)^2-12*(n : ℝ)+6) * ((n : ℝ)*((n : ℝ)-1)/2) +
        (n : ℝ)*(1-3*(n : ℝ)+3*(n : ℝ)^2-(n : ℝ)^3) = 0 := by ring
    rw [hz, zero_div]
  · have he : (∑ i ∈ Finset.range n, (2*(i : ℝ)-(n : ℝ)+1)^4) =
        16 * (∑ i ∈ Finset.range n, (i : ℝ)^4) +
        (32-32*(n : ℝ)) * (∑ i ∈ Finset.range n, (i : ℝ)^3) +
        (24*(n : ℝ)^2-48*(n : ℝ)+24) * (∑ i ∈ Finset.range n, (i : ℝ)^2) +
        (8-24*(n : ℝ)+24*(n : ℝ)^2-8*(n : ℝ)^3) *
          (∑ i ∈ Finset.range n, (i : ℝ)) +
        (n : ℝ)*((n : ℝ)^4-4*(n : ℝ)^3+6*(n : ℝ)^2-4*(n : ℝ)+1) := by
      calc
        _ = ∑ i ∈ Finset.range n, (16*(i : ℝ)^4+(32-32*(n : ℝ))*(i : ℝ)^3+(24*(n : ℝ)^2-48*(n : ℝ)+24)*(i : ℝ)^2+(8-24*(n : ℝ)+24*(n : ℝ)^2-8*(n : ℝ)^3)*(i : ℝ)+((n : ℝ)^4-4*(n : ℝ)^3+6*(n : ℝ)^2-4*(n : ℝ)+1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          <;> ring
    rw [he, h1, h2, h3, h4]
    field_simp [hd]
    <;> ring

private lemma FV_grid_bound (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    |FV_grid n i| ≤ 1 := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hi0 : (0 : ℝ) ≤ i.val := by positivity
  have hi1 : (i.val : ℝ) ≤ (n : ℝ)-1 := by
    have h : (i.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast i.isLt
    linarith
  rw [abs_le]
  dsimp [FV_grid]
  constructor
  · apply (le_div_iff₀ (by linarith : (0 : ℝ)<(n : ℝ)-1)).mpr
    linarith
  · apply (div_le_iff₀ (by linarith : (0 : ℝ)<(n : ℝ)-1)).mpr
    linarith

private lemma FV_grid_moments (n : ℕ) (hn : 2 ≤ n) :
    mean (FV_grid n) = 0 ∧ mean (fun i => FV_grid n i^2) = FV_v n ∧
    mean (fun i => FV_grid n i^3) = 0 ∧
    mean (fun i => (FV_grid n i^2-FV_v n)^2) = FV_W n := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hd : (n : ℝ)-1 ≠ 0 := by linarith
  obtain ⟨h1,h2,h3,h4⟩ := FV_grid_sums n hn
  refine ⟨by simp [mean, h1], by simp [mean, h2, hn0], by simp [mean, h3], ?_⟩
  have he (i : Fin n) : (FV_grid n i^2-FV_v n)^2 =
      FV_grid n i^4 - 2*FV_v n*(FV_grid n i^2) + (FV_v n)^2 := by ring
  simp only [mean, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h2,h4]
  dsimp [FV_v, FV_W]
  field_simp [hn0, hd]
  <;> ring

private lemma FV_v_bounds (n : ℕ) (hn : 2 ≤ n) : 1/3 ≤ FV_v n ∧ FV_v n ≤ 1 := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdp : (0 : ℝ)<(n : ℝ)-1 := by linarith
  dsimp [FV_v]
  constructor
  · apply (le_div_iff₀ (by positivity : (0 : ℝ)<3*((n : ℝ)-1))).mpr
    linarith
  · apply (div_le_iff₀ (by positivity : (0 : ℝ)<3*((n : ℝ)-1))).mpr
    linarith

private lemma FV_W_lower (n : ℕ) (hn : 3 ≤ n) : 4/45 ≤ FV_W n := by
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hdp : (0 : ℝ)<(n : ℝ)-1 := by linarith
  dsimp [FV_W]
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<45*((n : ℝ)-1)^3)).mpr
  nlinarith [sq_nonneg ((n : ℝ)-3), mul_nonneg (by linarith : (0 : ℝ)≤n-3)
    (sq_nonneg ((n : ℝ)-1))]

private lemma FV_mean_add {n} (f g : Fin n → ℝ) :
    mean (fun i => f i + g i) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, add_div]
private lemma FV_mean_sub {n} (f g : Fin n → ℝ) :
    mean (fun i => f i - g i) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, sub_div]
private lemma FV_mean_mul {n} (c : ℝ) (f : Fin n → ℝ) :
    mean (fun i => c * f i) = c * mean f := by
  simp only [mean, ← Finset.mul_sum]
  ring
private lemma FV_mean_const {n} (hn : 0 < n) (c : ℝ) :
    mean (fun _ : Fin n => c) = c := by
  have hz : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [mean, hz]
private lemma FV_mean_mono {n} {f g : Fin n → ℝ} (h : ∀ i, f i ≤ g i) :
    mean f ≤ mean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i hi => h i)) (Nat.cast_nonneg n)
private lemma FV_mean_nonneg {n} {f : Fin n → ℝ} (h : ∀ i, 0 ≤ f i) :
    0 ≤ mean f := by
  exact div_nonneg (Finset.sum_nonneg fun i hi => h i) (Nat.cast_nonneg n)

private lemma FV_fourth_bound {n} (hn : 0 < n) (f : Fin n → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ i, |f i| ≤ C) : fourthNorm f ≤ C := by
  have hm : mean (fun i => f i^4) ≤ C^4 := by
    calc
      _ ≤ mean (fun _ : Fin n => C^4) := FV_mean_mono (fun i => by
        simpa only [show (4 : ℕ) = 2*2 by omega, pow_mul, sq_abs] using pow_le_pow_left₀ (abs_nonneg (f i)) (hf i) 4)
      _ = _ := FV_mean_const hn _
  unfold fourthNorm
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hC, ?_⟩
  apply (Real.sqrt_le_iff).mpr
  exact ⟨sq_nonneg C, by nlinarith [hm]⟩

private lemma FV_popVar_ge_mean_sq {n} (hn : 2 ≤ n) (f : Fin n → ℝ)
    (hm : mean f = 0) : mean (fun i => f i^2) ≤ popVar f := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 ≤ ∑ i, f i^2 := Finset.sum_nonneg fun i hi => sq_nonneg _
  change (∑ i, f i^2)/(n : ℝ) ≤ (∑ i, (f i-mean f)^2)/((n : ℝ)-1)
  rw [hm]
  simp only [sub_zero]
  exact div_le_div_of_nonneg_left hs (by linarith : (0 : ℝ)<(n : ℝ)-1) (show (n : ℝ)-1 ≤ (n : ℝ) by linarith)

private lemma FV_det_two (M : Matrix (Option (Fin 1)) (Option (Fin 1)) ℝ) :
    M.det = M none none * M (some 0) (some 0) -
      M none (some 0) * M (some 0) none := by
  calc
    M.det = (M.reindex (finSuccEquiv 1).symm (finSuccEquiv 1).symm).det :=
      (Matrix.det_reindex_self _ M).symm
    _ = _ := by
      rw [Matrix.det_fin_two]
      rfl

private lemma FV_gram_det {n} (x : Fin n → Fin 1 → ℝ) (S : Finset (Fin n))
    (hS : S.Nonempty) :
    (gram x S).det = groupMean S (fun i => x i 0^2) - (groupMean S (fun i => x i 0))^2 := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  rw [FV_det_two]
  simp [gram, augmented, groupMean, hc, pow_two]

private lemma FV_gram_fullrank {n} (x : Fin n → Fin 1 → ℝ)
    (hx : Function.Injective (fun i => x i 0)) (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    (gram x S).det ≠ 0 := by
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hc : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  rw [FV_gram_det x S hSne]
  have he := square_centering S (fun i => x i 0) 0 hSne
  simp only [sub_zero] at he
  rw [← he]
  apply ne_of_gt
  apply div_pos _ hc
  apply (Finset.sum_pos_iff_of_nonneg (fun i hi => sq_nonneg _)).mpr
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  by_cases hxi : x i 0 = groupMean S (fun l => x l 0)
  · refine ⟨j,hj, sq_pos_of_ne_zero ?_⟩
    intro hz
    have hxj := sub_eq_zero.mp hz
    exact hij (hx (hxi.trans hxj.symm))
  · exact ⟨i,hi,sq_pos_of_ne_zero (sub_ne_zero.mpr hxi)⟩

private def FV_coef (a b : ℝ) : Option (Fin 1) → ℝ
  | none => a
  | some _ => b

private lemma FV_ols_unique {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n))
    (q : Fin n → ℝ) (c : Option (Fin k) → ℝ) (hg : (gram x S).det ≠ 0)
    (hc : gram x S *ᵥ c = score x S q) : ols x S q = c := by
  rw [ols, if_pos hg, ← hc, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg), Matrix.one_mulVec]

private lemma FV_scalar_ols {n} (x : Fin n → Fin 1 → ℝ) (S : Finset (Fin n))
    (q : Fin n → ℝ) (hS : S.Nonempty) (hg : (gram x S).det ≠ 0) (a b : ℝ)
    (h0 : a + b * groupMean S (fun i => x i 0) = groupMean S q)
    (h1 : a * groupMean S (fun i => x i 0) +
      b * groupMean S (fun i => x i 0^2) = groupMean S (fun i => x i 0*q i)) :
    ols x S q = FV_coef a b := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  apply FV_ols_unique _ _ _ _ hg
  ext s
  cases s with
  | none =>
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_option, gram, score, augmented,
      FV_coef, groupMean, hc, ← Finset.mul_sum, mul_comm] using h0
  | some s =>
    fin_cases s
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_option, gram, score, augmented,
      FV_coef, groupMean, hc, ← Finset.mul_sum, pow_two, mul_comm] using h1

private lemma FV_identical_late {n} (P : Population n)
    (hy : ∀ i, P.y i true = P.y i false) : late P = 0 := by
  simp [late, groupMean, hy]

private lemma FV_Xi_criterion {n} (P : CovPopulation n 1) (hn : 2 ≤ n)
    (hdesign : ValidDesign P.pop)
    (hd : ∀ i a, P.pop.d i a = a) (hl : late P.pop = 0)
    (hb : (1/3 : ℝ)*(n : ℝ) ≤ P.pop.n1 ∧ (P.pop.n1 : ℝ) ≤ (1-1/3)*(n : ℝ))
    (e : Fin n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ a, residual P a 0 = e) (he : ∀ i, |e i| ≤ C)
    (hv : C^2 ≤ 25*popVar e) (hv0 : 0 ≤ popVar e)
    (hx : ∑ i, P.x i 0 = 0) (hxb : ∀ i, |P.x i 0| ≤ 2)
    (hx2 : (1/4 : ℝ) ≤ mean (fun i => P.x i 0^2)) :
    Xi P 0 (1/4) 16 5 (1/3) := by
  have hn0 : 0 < n := by omega
  have hcomp : compliers P.pop = Finset.univ := by simp [compliers, hd]
  have hcov : popCov e e = popVar e := by simp [popCov, popVar, pow_two]
  have hmom : fourthNorm e ≤ 5*Real.sqrt (popVar e) := by
    have hs := Real.sq_sqrt hv0
    have hs0 := Real.sqrt_nonneg (popVar e)
    exact (FV_fourth_bound hn0 e C hC he).trans (by nlinarith)
  simp only [Xi, hl, hr, zero_mul, neg_zero, hcov]
  refine ⟨hdesign, ?_, ?_, hb.1, hb.2, hv0, fun a => hmom, ?_, ?_, ?_⟩
  · intro i hi
    simpa [hd] using hi
  · rw [hcomp]
    exact Finset.univ_nonempty_iff.mpr ⟨⟨0,hn0⟩⟩
  · intro s
    fin_cases s
    exact hx
  · intro s
    fin_cases s
    calc
      _ ≤ mean (fun _ : Fin n => (2 : ℝ)^4) := by
        apply FV_mean_mono
        intro i
        change P.x i 0^4 ≤ (2 : ℝ)^4
        simpa only [show (4 : ℕ) = 2*2 by omega, pow_mul, sq_abs] using
          pow_le_pow_left₀ (abs_nonneg (P.x i 0)) (hxb i) 4
      _ = 16 := by rw [FV_mean_const hn0]; norm_num
  · intro b
    simp only [normSq, dotProduct, Fin.sum_univ_one]
    have heq : mean (fun i => (P.x i 0*b 0)^2) =
        (b 0)^2*mean (fun i => P.x i 0^2) := by
      rw [← FV_mean_mul]
      congr 1
      funext i
      ring
    rw [heq]
    nlinarith [mul_nonneg (sq_nonneg (b 0)) (sub_nonneg.mpr hx2)]

private def FV_u (n : ℕ) (i : Fin n) : ℝ := FV_grid n i^2-FV_v n
private def FV_yGrid (n : ℕ) (i : Fin n) : ℝ := FV_grid n i+(1/10)*FV_u n i

private lemma FV_grid_extra (n : ℕ) (hn : 2 ≤ n) :
    mean (FV_u n) = 0 ∧ mean (fun i => FV_grid n i*FV_u n i) = 0 ∧
    mean (FV_yGrid n) = 0 ∧ mean (fun i => FV_grid n i*FV_yGrid n i) = FV_v n ∧
    mean (fun i => FV_yGrid n i^2) = FV_v n+(1/100)*FV_W n ∧
    (∀ i, |FV_u n i| ≤ 1) ∧ (∀ i, |FV_yGrid n i| ≤ 11/10) := by
  have hn0 : 0 < n := by omega
  obtain ⟨h1,h2,h3,hW⟩ := FV_grid_moments n hn
  obtain ⟨hv0,hv1⟩ := FV_v_bounds n hn
  have hu : mean (FV_u n) = 0 := by
    change mean (fun i => FV_grid n i^2-FV_v n) = 0
    rw [FV_mean_sub, FV_mean_const hn0, h2]
    ring
  have htu : mean (fun i => FV_grid n i*FV_u n i) = 0 := by
    have he : (fun i => FV_grid n i*FV_u n i) =
        (fun i => FV_grid n i^3-FV_v n*FV_grid n i) := by funext i; dsimp [FV_u]; ring
    rw [he, FV_mean_sub, FV_mean_mul, h3, h1]
    ring
  have hy : mean (FV_yGrid n) = 0 := by
    change mean (fun i => FV_grid n i+(1/10)*FV_u n i) = 0
    rw [FV_mean_add, FV_mean_mul, h1, hu]
    ring
  have hty : mean (fun i => FV_grid n i*FV_yGrid n i) = FV_v n := by
    have he : (fun i => FV_grid n i*FV_yGrid n i) =
        (fun i => FV_grid n i^2+(1/10)*(FV_grid n i*FV_u n i)) := by
      funext i; dsimp [FV_yGrid]; ring
    rw [he, FV_mean_add, FV_mean_mul, h2, htu]
    ring
  have hy2 : mean (fun i => FV_yGrid n i^2) = FV_v n+(1/100)*FV_W n := by
    have he : (fun i => FV_yGrid n i^2) =
        (fun i => (FV_grid n i^2+(1/5)*(FV_grid n i*FV_u n i))+(1/100)*(FV_u n i)^2) := by
      funext i; dsimp [FV_yGrid]; ring
    rw [he, FV_mean_add, FV_mean_add, FV_mean_mul, FV_mean_mul, h2, htu]
    change FV_v n + 1/5*0 + 1/100*mean (fun i => (FV_grid n i^2-FV_v n)^2) = _
    rw [hW]
    ring
  have hub (i : Fin n) : |FV_u n i| ≤ 1 := by
    have ht := FV_grid_bound n hn i
    have ht2 : FV_grid n i^2 ≤ 1 := by
      have h := (abs_le.mp ht)
      nlinarith [sq_nonneg (FV_grid n i-1), mul_nonneg (by linarith : 0 ≤ 1-FV_grid n i) (by linarith : 0 ≤ 1+FV_grid n i)]
    rw [abs_le]
    dsimp [FV_u]
    constructor <;> nlinarith [sq_nonneg (FV_grid n i)]
  refine ⟨hu,htu,hy,hty,hy2,hub,fun i => ?_⟩
  calc
    _ ≤ |FV_grid n i|+|(1/10 : ℝ)*FV_u n i| := abs_add_le _ _
    _ ≤ 11/10 := by rw [abs_mul]; norm_num; linarith [FV_grid_bound n hn i, hub i]

private def FV_t (m : ℕ) (i : Fin (2*m)) : ℝ :=
  (2*(i.val % m : ℕ)-(m : ℝ)+1)/((m : ℝ)-1)
private def FV_sign (m : ℕ) (i : Fin (2*m)) : ℝ := if i.val < m then 1 else -1
private def FV_eta (m : ℕ) : ℝ := 1/(2 : ℝ)^((2*m)^2)
private def FV_x (m : ℕ) (i : Fin (2*m)) : ℝ := FV_sign m i+FV_eta m*FV_t m i
private def FV_y (m : ℕ) (i : Fin (2*m)) : ℝ := FV_t m i+(1/10)*(FV_t m i^2-FV_v m)

private lemma FV_model_x (m : ℕ) (i : Fin (2*m)) (s : Fin 1) :
    (nearSingularModel m).x i s = FV_x m i := rfl
private lemma FV_model_y (m : ℕ) (i : Fin (2*m)) (a : Bool) :
    (nearSingularModel m).pop.y i a = FV_y m i := rfl

private lemma FV_even_sum (m : ℕ) (F : ℝ → ℝ → ℝ) :
    (∑ i, F (FV_sign m i) (FV_t m i)) =
      (∑ j : Fin m, F 1 (FV_grid m j)) + (∑ j : Fin m, F (-1) (FV_grid m j)) := by
  simp only [FV_t, FV_sign, FV_grid]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    F (if j < m then 1 else -1) ((2*(j % m : ℕ)-(m : ℝ)+1)/((m : ℝ)-1)))]
  rw [two_mul, Finset.sum_range_add]
  rw [Fin.sum_univ_eq_sum_range (fun j => F 1 ((2*(j : ℝ)-(m : ℝ)+1)/((m : ℝ)-1))),
    Fin.sum_univ_eq_sum_range (fun j => F (-1) ((2*(j : ℝ)-(m : ℝ)+1)/((m : ℝ)-1)))]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjm := Finset.mem_range.mp hj
    simp [hjm, Nat.mod_eq_of_lt hjm]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjm := Finset.mem_range.mp hj
    have hnot : ¬ m+j < m := by omega
    simp [hnot, Nat.add_mod, Nat.mod_eq_of_lt hjm]

private lemma FV_even_mean (m : ℕ) (F : ℝ → ℝ → ℝ) :
    mean (fun i => F (FV_sign m i) (FV_t m i)) =
      (mean (fun j : Fin m => F 1 (FV_grid m j)) +
        mean (fun j : Fin m => F (-1) (FV_grid m j)))/2 := by
  simp only [mean, FV_even_sum, Nat.cast_mul, Nat.cast_ofNat]
  ring

private lemma FV_eta_bounds (m : ℕ) (hm : 4 ≤ m) :
    0 < FV_eta m ∧ FV_eta m ≤ 1/4 := by
  have hpow : (4 : ℝ) ≤ (2 : ℝ)^((2*m)^2) := by
    calc
      (4 : ℝ) = (2 : ℝ)^2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  dsimp [FV_eta]
  constructor
  · positivity
  · exact (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by nlinarith)

private lemma FV_t_bound (m : ℕ) (hm : 4 ≤ m) (i : Fin (2*m)) : |FV_t m i| ≤ 1 := by
  have hm0 : 0 < m := by omega
  exact FV_grid_bound m (by omega) ⟨i.val % m, Nat.mod_lt _ hm0⟩

private lemma FV_odd_x (n : ℕ) (hn : 2 ≤ n) (i : Fin n) (s : Fin 1) :
    (oddNearModel n).x i s = FV_grid n i := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (n : ℝ)-1 ≠ 0 := by linarith
  dsimp [oddNearModel, FV_grid]
  field_simp [hd]
  <;> ring

private lemma FV_odd_y (n : ℕ) (hn : 2 ≤ n) (i : Fin n) (a : Bool) :
    (oddNearModel n).pop.y i a = (1/10)*FV_u n i := by
  have hx : (oddNearModel n).x = fun i _ => FV_grid n i := by
    funext i s; exact FV_odd_x n hn i s
  change (1/10)*((oddNearModel n).x i 0^2-mean (fun j => (oddNearModel n).x j 0^2)) = _
  rw [hx, (FV_grid_moments n hn).2.1]
  rfl

private lemma FV_odd_admissible (n : ℕ) (hn : 9 ≤ n) :
    Xi (oddNearModel n) 0 (1/4) 16 5 (1/3) := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnr : (9 : ℝ) ≤ n := by exact_mod_cast hn
  let P := oddNearModel n
  let e : Fin n → ℝ := fun i => (1/10)*FV_u n i
  have hx : P.x = fun i _ => FV_grid n i := by
    funext i s; exact FV_odd_x n hn2 i s
  obtain ⟨hg1,hg2,hg3,hgW⟩ := FV_grid_moments n hn2
  obtain ⟨hu,htu,hy,hty,hy2,hub,hyb⟩ := FV_grid_extra n hn2
  obtain ⟨hv0,hv1⟩ := FV_v_bounds n hn2
  have he0 : mean e = 0 := by
    change mean (fun i => (1/10)*FV_u n i) = 0
    rw [FV_mean_mul, hu]
    ring
  have hex : mean (fun i => FV_grid n i*e i) = 0 := by
    have hfun : (fun i => FV_grid n i*e i) = (fun i => (1/10)*(FV_grid n i*FV_u n i)) := by
      funext i; dsimp [e]; ring
    rw [hfun, FV_mean_mul, htu]
    ring
  have hg : (gram P.x Finset.univ).det ≠ 0 := by
    rw [FV_gram_det _ _ (Finset.univ_nonempty_iff.mpr ⟨⟨0,hn0⟩⟩)]
    simp only [hx, groupMean, Finset.card_univ, Fintype.card_fin]
    change mean (fun i => FV_grid n i^2)-(mean (FV_grid n))^2 ≠ 0
    rw [hg2,hg1]
    nlinarith
  have hols (a : Bool) : psi P a 0 = FV_coef 0 0 := by
    have hw : w P.pop a 0 = e := by
      funext i
      simp only [w, zero_mul, sub_zero]
      exact FV_odd_y n hn2 i _
    unfold psi
    rw [hw]
    apply FV_scalar_ols P.x Finset.univ e
      (Finset.univ_nonempty_iff.mpr ⟨⟨0,hn0⟩⟩) hg 0 0
    · simpa only [zero_mul, zero_add, groupMean, Finset.card_univ, Fintype.card_fin, mean] using he0.symm
    · simpa only [zero_mul, add_zero, hx, groupMean, Finset.card_univ, Fintype.card_fin, mean] using hex.symm
  have hr (a : Bool) : residual P a 0 = e := by
    funext i
    simp only [residual, hols, dotProduct, Fintype.sum_option, Fin.sum_univ_one,
      FV_coef, mul_zero, add_zero, sub_zero]
    simp only [w, zero_mul, sub_zero]
    exact FV_odd_y n hn2 i _
  have he2 : mean (fun i => e i^2) = (1/100)*FV_W n := by
    have hfun : (fun i => e i^2) = (fun i => (1/100)*(FV_u n i)^2) := by
      funext i; dsimp [e]; ring
    rw [hfun, FV_mean_mul]
    change 1/100*mean (fun i => (FV_grid n i^2-FV_v n)^2) = _
    rw [hgW]
  have hev : (1/1125 : ℝ) ≤ popVar e := by
    have h := FV_popVar_ge_mean_sq hn2 e he0
    rw [he2] at h
    have hw := FV_W_lower n (by omega)
    linarith
  have hdes : ValidDesign P.pop := by
    change 2 ≤ n ∧ 0 < n/2 ∧ n/2 < n
    omega
  have hb : (1/3 : ℝ)*(n : ℝ) ≤ P.pop.n1 ∧ (P.pop.n1 : ℝ) ≤ (1-1/3)*(n : ℝ) := by
    change (1/3 : ℝ)*(n : ℝ) ≤ (n/2 : ℕ) ∧ ((n/2 : ℕ) : ℝ) ≤ (1-1/3)*(n : ℝ)
    have h1 : n ≤ 3*(n/2) := by omega
    have h2 : 3*(n/2) ≤ 2*n := by omega
    have h1r : (n : ℝ) ≤ 3*((n/2 : ℕ) : ℝ) := by exact_mod_cast h1
    have h2r : 3*((n/2 : ℕ) : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast h2
    constructor <;> linarith
  apply FV_Xi_criterion P hn2 hdes (by intros; rfl)
    (FV_identical_late P.pop (by intros; rfl)) hb e (1/10) (by norm_num) hr
  · intro i
    dsimp [e]
    rw [abs_mul]
    norm_num
    linarith [hub i]
  · nlinarith
  · linarith
  · rw [hx]
    exact (FV_grid_sums n hn2).1
  · intro i
    rw [hx]
    exact (FV_grid_bound n hn2 i).trans (by norm_num)
  · rw [hx, hg2]
    linarith

private lemma FV_even_reduce (m : ℕ) (F : ℝ → ℝ → ℝ) (G : ℝ → ℝ)
    (h : ∀ t, (F 1 t+F (-1) t)/2 = G t) :
    mean (fun i => F (FV_sign m i) (FV_t m i)) = mean (fun j => G (FV_grid m j)) := by
  rw [FV_even_mean]
  calc
    _ = mean (fun j => (F 1 (FV_grid m j)+F (-1) (FV_grid m j))/2) := by
      simp only [mean, Finset.sum_add_distrib, ← Finset.sum_div]
      ring
    _ = _ := by congr 1; funext j; exact h _

private lemma FV_even_moments (m : ℕ) (hm : 4 ≤ m) :
    mean (FV_x m) = 0 ∧ mean (FV_y m) = 0 ∧
    mean (fun i => FV_x m i^2) = 1+FV_eta m^2*FV_v m ∧
    mean (fun i => FV_x m i*FV_y m i) = FV_eta m*FV_v m ∧
    mean (fun i => FV_y m i^2) = FV_v m+(1/100)*FV_W m := by
  have hm0 : 0 < m := by omega
  obtain ⟨h1,h2,h3,hW⟩ := FV_grid_moments m (by omega)
  obtain ⟨hu,htu,hy,hty,hy2,hub,hyb⟩ := FV_grid_extra m (by omega)
  constructor
  · change mean (fun i => FV_sign m i+FV_eta m*FV_t m i) = 0
    rw [FV_even_reduce m (fun s t => s+FV_eta m*t) (fun t => FV_eta m*t) (by intro t; ring),
      FV_mean_mul, h1]
    ring
  constructor
  · change mean (fun i => FV_t m i+(1/10)*(FV_t m i^2-FV_v m)) = 0
    rw [FV_even_reduce m (fun _ t => t+(1/10)*(t^2-FV_v m))
      (fun t => t+(1/10)*(t^2-FV_v m)) (by intro t; ring)]
    exact hy
  constructor
  · change mean (fun i => (FV_sign m i+FV_eta m*FV_t m i)^2) = _
    rw [FV_even_reduce m (fun s t => (s+FV_eta m*t)^2)
      (fun t => 1+FV_eta m^2*t^2) (by intro t; ring),
      FV_mean_add, FV_mean_const hm0, FV_mean_mul, h2]
  constructor
  · change mean (fun i => (FV_sign m i+FV_eta m*FV_t m i)*
      (FV_t m i+(1/10)*(FV_t m i^2-FV_v m))) = _
    rw [FV_even_reduce m (fun s t => (s+FV_eta m*t)*(t+(1/10)*(t^2-FV_v m)))
      (fun t => FV_eta m*(t*(t+(1/10)*(t^2-FV_v m)))) (by intro t; ring), FV_mean_mul]
    change FV_eta m*mean (fun j => FV_grid m j*FV_yGrid m j) = _
    rw [hty]
  · change mean (fun i => (FV_t m i+(1/10)*(FV_t m i^2-FV_v m))^2) = _
    rw [FV_even_reduce m (fun _ t => (t+(1/10)*(t^2-FV_v m))^2)
      (fun t => (t+(1/10)*(t^2-FV_v m))^2) (by intro t; ring)]
    exact hy2

private lemma FV_even_bounds (m : ℕ) (hm : 4 ≤ m) :
    (∀ i, |FV_x m i| ≤ 5/4) ∧ (∀ i, |FV_y m i| ≤ 11/10) := by
  obtain ⟨he0,he1⟩ := FV_eta_bounds m hm
  have hsign (i : Fin (2*m)) : |FV_sign m i| = 1 := by
    by_cases hi : i.val < m <;> simp [FV_sign,hi]
  constructor
  · intro i
    calc
      _ ≤ |FV_sign m i|+|FV_eta m*FV_t m i| := abs_add_le _ _
      _ ≤ 5/4 := by
        rw [hsign,abs_mul,abs_of_pos he0]
        have ht := FV_t_bound m hm i
        nlinarith [mul_nonneg he0.le (sub_nonneg.mpr ht)]
  · intro i
    have hm0 : 0 < m := by omega
    exact (FV_grid_extra m (by omega)).2.2.2.2.2.2 ⟨i.val % m,Nat.mod_lt _ hm0⟩

private def FV_gamma (m : ℕ) : ℝ := FV_eta m*FV_v m/(1+FV_eta m^2*FV_v m)
private def FV_e (m : ℕ) (i : Fin (2*m)) : ℝ := FV_y m i-FV_gamma m*FV_x m i

private lemma FV_even_population_fit (m : ℕ) (hm : 4 ≤ m) :
    (∀ a, psi (nearSingularModel m) a 0 = FV_coef 0 (FV_gamma m)) ∧
    (∀ a, residual (nearSingularModel m) a 0 = FV_e m) ∧
    mean (FV_e m) = 0 ∧ (1/6 : ℝ) ≤ popVar (FV_e m) ∧
    (∀ i, |FV_e m i| ≤ 2) := by
  have hm0 : 0 < m := by omega
  have hN0 : 0 < 2*m := by omega
  obtain ⟨hx,hy,hx2,hxy,hy2⟩ := FV_even_moments m hm
  obtain ⟨hv0,hv1⟩ := FV_v_bounds m (by omega)
  obtain ⟨he0,he1⟩ := FV_eta_bounds m hm
  have hvpos : 0 < FV_v m := by linarith
  have hden : 0 < 1+FV_eta m^2*FV_v m := by positivity
  have hg : (gram (nearSingularModel m).x Finset.univ).det ≠ 0 := by
    rw [FV_gram_det _ _ (Finset.univ_nonempty_iff.mpr ⟨⟨0,hN0⟩⟩)]
    simp only [FV_model_x, groupMean, Finset.card_univ, Fintype.card_fin]
    change mean (fun i => FV_x m i^2)-(mean (FV_x m))^2 ≠ 0
    rw [hx2,hx]
    nlinarith
  have hgamma : FV_gamma m*(1+FV_eta m^2*FV_v m) = FV_eta m*FV_v m := by
    dsimp [FV_gamma]
    field_simp
  have hgamma0 : 0 ≤ FV_gamma m := by dsimp [FV_gamma]; positivity
  have hgamma1 : FV_gamma m ≤ 1/4 := by
    have h1 : FV_eta m*FV_v m ≤ FV_eta m := by nlinarith
    have h2 : 0 ≤ FV_gamma m*(FV_eta m^2*FV_v m) := by positivity
    nlinarith
  have hfit (a : Bool) : psi (nearSingularModel m) a 0 = FV_coef 0 (FV_gamma m) := by
    have hw : w (nearSingularModel m).pop a 0 = FV_y m := by funext i; simp [w,FV_model_y]
    unfold psi
    rw [hw]
    apply FV_scalar_ols _ _ _ (Finset.univ_nonempty_iff.mpr ⟨⟨0,hN0⟩⟩) hg 0 (FV_gamma m)
    · simpa [FV_model_x, groupMean, mean, hx, hy] using (show (0 : ℝ)+FV_gamma m*mean (FV_x m) = mean (FV_y m) by rw [hx,hy]; ring)
    · simpa only [FV_model_x, groupMean, Finset.card_univ, Fintype.card_fin, mean,
        zero_mul, zero_add] using (show FV_gamma m*mean (fun i => FV_x m i^2) =
          mean (fun i => FV_x m i*FV_y m i) by rw [hx2,hxy]; exact hgamma)
  have hr (a : Bool) : residual (nearSingularModel m) a 0 = FV_e m := by
    funext i
    simp [residual,hfit,dotProduct,Fintype.sum_option,Fin.sum_univ_one,FV_coef,
      augmented,FV_model_x,w,FV_model_y,FV_e,mul_comm]
  have hem : mean (FV_e m) = 0 := by
    change mean (fun i => FV_y m i-FV_gamma m*FV_x m i) = 0
    rw [FV_mean_sub,FV_mean_mul,hx,hy]
    ring
  have he2 : mean (fun i => FV_e m i^2) = FV_v m/(1+FV_eta m^2*FV_v m)+(1/100)*FV_W m := by
    have hfun : (fun i => FV_e m i^2) =
        (fun i => (FV_y m i^2-2*FV_gamma m*(FV_x m i*FV_y m i))+
          FV_gamma m^2*FV_x m i^2) := by funext i; dsimp [FV_e]; ring
    rw [hfun,FV_mean_add,FV_mean_sub,FV_mean_mul,FV_mean_mul,hy2,hxy,hx2]
    dsimp [FV_gamma]
    field_simp [hden.ne']
    <;> ring
  have hvar : (1/6 : ℝ) ≤ popVar (FV_e m) := by
    have hW0 : 0 ≤ FV_W m := by
      rw [← (FV_grid_moments m (by omega)).2.2.2]
      exact FV_mean_nonneg fun i => sq_nonneg _
    have hdle : 1+FV_eta m^2*FV_v m ≤ 2 := by
      have he2 : FV_eta m^2 ≤ 1/16 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg (FV_eta m)) (sub_nonneg.mpr hv1)]
    have hvdiv : (1/6 : ℝ) ≤ FV_v m/(1+FV_eta m^2*FV_v m) := by
      apply (le_div_iff₀ hden).mpr
      linarith
    have hege : (1/6 : ℝ) ≤ mean (fun i => FV_e m i^2) := by rw [he2]; linarith
    exact hege.trans (FV_popVar_ge_mean_sq (by omega) _ hem)
  refine ⟨hfit,hr,hem,hvar,fun i => ?_⟩
  obtain ⟨hxb,hyb⟩ := FV_even_bounds m hm
  calc
    _ ≤ |FV_y m i|+|FV_gamma m*FV_x m i| := by
      simpa only [FV_e, sub_eq_add_neg, abs_neg] using abs_add_le (FV_y m i) (-(FV_gamma m*FV_x m i))
    _ ≤ 2 := by
      rw [abs_mul,abs_of_nonneg hgamma0]
      have hx0 := abs_nonneg (FV_x m i)
      nlinarith [hxb i,hyb i,mul_nonneg hgamma0 (sub_nonneg.mpr (hxb i))]

private lemma FV_x_injective (m : ℕ) (hm : 4 ≤ m) : Function.Injective (FV_x m) := by
  obtain ⟨he0,he1⟩ := FV_eta_bounds m hm
  have hmr : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : (m : ℝ)-1 ≠ 0 := by linarith
  have hmod (i j : Fin (2*m)) (h : FV_t m i = FV_t m j) : i.val % m = j.val % m := by
    have he := congrArg (fun z : ℝ => z*((m : ℝ)-1)) h
    simp only [FV_t,div_mul_cancel₀ _ hd] at he
    have : ((i.val % m : ℕ) : ℝ) = ((j.val % m : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  intro i j h
  have hti := abs_le.mp (FV_t_bound m hm i)
  have htj := abs_le.mp (FV_t_bound m hm j)
  have hip : -FV_eta m ≤ FV_eta m*FV_t m i ∧ FV_eta m*FV_t m i ≤ FV_eta m := by
    constructor <;> nlinarith
  have hjp : -FV_eta m ≤ FV_eta m*FV_t m j ∧ FV_eta m*FV_t m j ≤ FV_eta m := by
    constructor <;> nlinarith
  by_cases hi : i.val < m <;> by_cases hj : j.val < m
  · have he : FV_eta m*FV_t m i = FV_eta m*FV_t m j := by
      simpa only [FV_x,FV_sign,if_pos hi,if_pos hj,add_right_inj] using h
    have hmo := hmod i j (mul_left_cancel₀ he0.ne' he)
    apply Fin.ext
    simpa only [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using hmo
  · simp only [FV_x,FV_sign,if_pos hi,if_neg hj] at h
    linarith [hip.1,hjp.2]
  · simp only [FV_x,FV_sign,if_neg hi,if_pos hj] at h
    linarith [hjp.1,hip.2]
  · have he : FV_eta m*FV_t m i = FV_eta m*FV_t m j := by
      simpa only [FV_x,FV_sign,if_neg hi,if_neg hj,add_right_inj] using h
    have hmo := hmod i j (mul_left_cancel₀ he0.ne' he)
    have him : i.val%m = i.val-m := by
      have hr : i.val = m+(i.val-m) := by omega
      calc
        _ = (m+(i.val-m))%m := congrArg (fun k => k%m) hr
        _ = i.val-m := by rw [Nat.add_mod]; simp [Nat.mod_eq_of_lt (show i.val-m<m by have := i.isLt; omega)]
    have hjm : j.val%m = j.val-m := by
      have hr : j.val = m+(j.val-m) := by omega
      calc
        _ = (m+(j.val-m))%m := congrArg (fun k => k%m) hr
        _ = j.val-m := by rw [Nat.add_mod]; simp [Nat.mod_eq_of_lt (show j.val-m<m by have := j.isLt; omega)]
    apply Fin.ext
    rw [him,hjm] at hmo
    omega

private lemma FV_even_design (m : ℕ) (hm : 4 ≤ m) : ValidDesign (nearSingularModel m).pop := by
  change 2 ≤ 2*m ∧ 0 < m ∧ m < 2*m
  omega

private lemma FV_even_admissible (m : ℕ) (hm : 4 ≤ m) :
    Xi (nearSingularModel m) 0 (1/4) 16 5 (1/3) := by
  obtain ⟨hfit,hr,hem,hvar,heb⟩ := FV_even_population_fit m hm
  obtain ⟨hx,hy,hx2,hxy,hy2⟩ := FV_even_moments m hm
  obtain ⟨hv0,hv1⟩ := FV_v_bounds m (by omega)
  obtain ⟨hxb,hyb⟩ := FV_even_bounds m hm
  have hb : (1/3 : ℝ)*((2*m : ℕ) : ℝ) ≤ (nearSingularModel m).pop.n1 ∧
      ((nearSingularModel m).pop.n1 : ℝ) ≤ (1-1/3)*((2*m : ℕ) : ℝ) := by
    change (1/3 : ℝ)*((2*m : ℕ) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (1-1/3)*((2*m : ℕ) : ℝ)
    push_cast
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) m]
  apply FV_Xi_criterion (nearSingularModel m) (by omega) (FV_even_design m hm)
    (by intros; rfl) (FV_identical_late _ (by intros; rfl)) hb (FV_e m) 2
    (by norm_num) hr heb
  · nlinarith
  · linarith
  · simp only [FV_model_x]
    have hN : ((2*m : ℕ) : ℝ) ≠ 0 := by positivity
    exact (div_eq_zero_iff).mp hx |>.resolve_right hN
  · intro i
    exact (hxb i).trans (by norm_num)
  · simp only [FV_model_x,hx2]
    have he := (FV_eta_bounds m hm).1
    nlinarith [mul_nonneg (sq_nonneg (FV_eta m)) (show 0 ≤ FV_v m by linarith)]

private lemma FV_even_fullrank (m : ℕ) (hm : 4 ≤ m) (S : Finset (Fin (2*m)))
    (hS : S ∈ assignments (nearSingularModel m).pop) :
    (gram (nearSingularModel m).x S).det ≠ 0 ∧
      (gram (nearSingularModel m).x Sᶜ).det ≠ 0 := by
  have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
  have hsc : Sᶜ.card = m := by rw [Finset.card_compl,Fintype.card_fin,hs]; omega
  have hinj : Function.Injective (fun i => (nearSingularModel m).x i 0) := FV_x_injective m hm
  exact ⟨FV_gram_fullrank _ hinj _ (by omega),FV_gram_fullrank _ hinj _ (by omega)⟩

private def FV_A (m : ℕ) : Finset (Fin (2*m)) := Finset.univ.filter (fun i => i.val < m)

private lemma FV_block_sums (m : ℕ) (F : ℝ → ℝ) :
    (∑ i ∈ FV_A m, F (FV_t m i)) = ∑ j : Fin m, F (FV_grid m j) ∧
    (∑ i ∈ (FV_A m)ᶜ, F (FV_t m i)) = ∑ j : Fin m, F (FV_grid m j) := by
  have hplus := FV_even_sum m (fun s t => if s=1 then F t else 0)
  have hminus := FV_even_sum m (fun s t => if s=(-1) then F t else 0)
  have hp (i : Fin (2*m)) : (if FV_sign m i=1 then F (FV_t m i) else 0) =
      if i ∈ FV_A m then F (FV_t m i) else 0 := by
    by_cases hi : i.val < m <;> norm_num [FV_sign,FV_A,hi,show ¬m ≤ i.val ↔ i.val < m by omega]
  have hn (i : Fin (2*m)) : (if FV_sign m i=(-1) then F (FV_t m i) else 0) =
      if i ∈ (FV_A m)ᶜ then F (FV_t m i) else 0 := by
    by_cases hi : i.val < m <;> norm_num [FV_sign,FV_A,hi,show ¬m ≤ i.val ↔ i.val < m by omega]
  simp only [hp,Finset.sum_ite_mem_eq] at hplus
  simp only [hn,Finset.sum_ite_mem_eq] at hminus
  constructor
  · norm_num at hplus
    exact hplus
  · norm_num at hminus
    exact hminus

private lemma FV_block_cards (m : ℕ) : (FV_A m).card = m ∧ (FV_A m)ᶜ.card = m := by
  have h := FV_block_sums m (fun _ => 1)
  constructor
  · exact_mod_cast (by simpa using h.1 : ((FV_A m).card : ℝ) = m)
  · exact_mod_cast (by simpa using h.2 : ((FV_A m)ᶜ.card : ℝ) = m)

private lemma FV_A_mem (m : ℕ) : FV_A m ∈ assignments (nearSingularModel m).pop := by
  apply Finset.mem_powersetCard.mpr
  exact ⟨Finset.subset_univ _,(FV_block_cards m).1⟩

private lemma FV_block_mean (m : ℕ) (F : ℝ → ℝ) :
    groupMean (FV_A m) (fun i => F (FV_t m i)) = mean (fun j => F (FV_grid m j)) ∧
    groupMean (FV_A m)ᶜ (fun i => F (FV_t m i)) = mean (fun j => F (FV_grid m j)) := by
  obtain ⟨hp,hn⟩ := FV_block_sums m F
  obtain ⟨hcp,hcn⟩ := FV_block_cards m
  simp only [groupMean,mean,hcp,hcn,hp,hn,and_self]

private lemma FV_affine_block_fit (m : ℕ) (hm : 4 ≤ m) (B : Finset (Fin (2*m)))
    (hB : B.Nonempty) (hg : (gram (nearSingularModel m).x B).det ≠ 0) (s : ℝ)
    (hxs : ∀ i ∈ B, FV_x m i = s+FV_eta m*FV_t m i)
    (hmean : ∀ F : ℝ → ℝ, groupMean B (fun i => F (FV_t m i)) =
      mean (fun j => F (FV_grid m j))) :
    ols (nearSingularModel m).x B (FV_y m) = FV_coef (-s/FV_eta m) (1/FV_eta m) ∧
    groupMean B (fun i => FV_y m i-slopeDot ((nearSingularModel m).x i)
      (ols (nearSingularModel m).x B (FV_y m))) = -s/FV_eta m := by
  have hm0 : 0 < m := by omega
  have heta := (FV_eta_bounds m hm).1
  obtain ⟨ht,ht2,ht3,htW⟩ := FV_grid_moments m (by omega)
  obtain ⟨hu,htu,hy,hty,hy2,hub,hyb⟩ := FV_grid_extra m (by omega)
  have hmx : groupMean B (fun i => (nearSingularModel m).x i 0) = s := by
    calc
      _ = groupMean B (fun i => s+FV_eta m*FV_t m i) :=
        groupMean_congr _ _ _ (fun i hi => hxs i hi)
      _ = mean (fun j => s+FV_eta m*FV_grid m j) := hmean (fun t => s+FV_eta m*t)
      _ = s := by rw [FV_mean_add,FV_mean_const hm0,FV_mean_mul,ht]; ring
  have hmy : groupMean B (FV_y m) = 0 := by
    change groupMean B (fun i => FV_t m i+(1/10)*(FV_t m i^2-FV_v m)) = 0
    rw [hmean (fun t => t+(1/10)*(t^2-FV_v m))]
    exact hy
  have hmx2 : groupMean B (fun i => (nearSingularModel m).x i 0^2) = s^2+FV_eta m^2*FV_v m := by
    calc
      _ = groupMean B (fun i => (s+FV_eta m*FV_t m i)^2) :=
        groupMean_congr _ _ _ (fun i hi => by rw [FV_model_x,hxs i hi])
      _ = mean (fun j => (s+FV_eta m*FV_grid m j)^2) := hmean (fun t => (s+FV_eta m*t)^2)
      _ = mean (fun j => (s^2+(2*s*FV_eta m)*FV_grid m j)+FV_eta m^2*FV_grid m j^2) := by
        congr 1; funext j; ring
      _ = _ := by rw [FV_mean_add,FV_mean_add,FV_mean_const hm0,FV_mean_mul,FV_mean_mul,ht,ht2]; ring
  have hmxy : groupMean B (fun i => (nearSingularModel m).x i 0*FV_y m i) = FV_eta m*FV_v m := by
    calc
      _ = groupMean B (fun i => (s+FV_eta m*FV_t m i)*(FV_t m i+(1/10)*(FV_t m i^2-FV_v m))) :=
        groupMean_congr _ _ _ (fun i hi => by rw [FV_model_x,hxs i hi]; rfl)
      _ = mean (fun j => (s+FV_eta m*FV_grid m j)*FV_yGrid m j) := hmean (fun t => (s+FV_eta m*t)*(t+(1/10)*(t^2-FV_v m)))
      _ = mean (fun j => s*FV_yGrid m j+FV_eta m*(FV_grid m j*FV_yGrid m j)) := by
        congr 1; funext j; ring
      _ = _ := by rw [FV_mean_add,FV_mean_mul,FV_mean_mul,hy,hty]; ring
  have hfit : ols (nearSingularModel m).x B (FV_y m) = FV_coef (-s/FV_eta m) (1/FV_eta m) := by
    apply FV_scalar_ols _ _ _ hB hg
    · rw [hmx,hmy]
      field_simp
      <;> ring
    · rw [hmx,hmx2,hmxy]
      field_simp
      <;> ring
  refine ⟨hfit,?_⟩
  rw [hfit]
  have heq : (fun i => FV_y m i-slopeDot ((nearSingularModel m).x i)
      (FV_coef (-s/FV_eta m) (1/FV_eta m))) =
      (fun i => FV_y m i-(1/FV_eta m)*(nearSingularModel m).x i 0) := by
    funext i
    simp [slopeDot,Fin.sum_univ_one,FV_coef,mul_comm]
  rw [heq,groupMean_sub_smul,hmx,hmy]
  ring

private lemma FV_rare_statistic (m : ℕ) (hm : 4 ≤ m) :
    adjustedTau (nearSingularModel m) (FV_y m) (FV_A m) = -2/FV_eta m := by
  obtain ⟨hgp,hgn⟩ := FV_even_fullrank m hm (FV_A m) (FV_A_mem m)
  obtain ⟨hcp,hcn⟩ := FV_block_cards m
  have hp : (FV_A m).Nonempty := Finset.card_pos.mp (by omega)
  have hn : (FV_A m)ᶜ.Nonempty := Finset.card_pos.mp (by omega)
  have hfitp := FV_affine_block_fit m hm (FV_A m) hp hgp 1
    (by intro i hi; have hi' : i.val < m := (Finset.mem_filter.mp hi).2
        simp [FV_x,FV_sign,hi']) (fun F => (FV_block_mean m F).1)
  have hfitn := FV_affine_block_fit m hm (FV_A m)ᶜ hn hgn (-1)
    (by intro i hi; have hi' : ¬ i.val < m := by simpa [FV_A] using hi
        simp [FV_x,FV_sign,hi']) (fun F => (FV_block_mean m F).2)
  change groupMean (FV_A m) (fun i => FV_y m i-slopeDot ((nearSingularModel m).x i)
    (ols (nearSingularModel m).x (FV_A m) (FV_y m))) -
    groupMean (FV_A m)ᶜ (fun i => FV_y m i-slopeDot ((nearSingularModel m).x i)
    (ols (nearSingularModel m).x (FV_A m)ᶜ (FV_y m))) = _
  rw [hfitp.2,hfitn.2]
  ring

private lemma FV_tau_compl {n k} (P : CovPopulation n k) (q : Fin n → ℝ)
    (S : Finset (Fin n)) : adjustedTau P q Sᶜ = -adjustedTau P q S := by
  simp [adjustedTau,adjustedWith,fitted]
  <;> ring

private lemma FV_assignment_compl (m : ℕ) (S : Finset (Fin (2*m)))
    (hS : S ∈ assignments (nearSingularModel m).pop) :
    Sᶜ ∈ assignments (nearSingularModel m).pop := by
  have hs : S.card = m := (Finset.mem_powersetCard.mp hS).2
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.subset_univ _,?_⟩
  change Sᶜ.card = m
  rw [Finset.card_compl,Fintype.card_fin,hs]
  omega

private lemma FV_design_mean (m : ℕ) (q : Fin (2*m) → ℝ) :
    expectation (nearSingularModel m).pop (adjustedTau (nearSingularModel m) q) = 0 := by
  let P := nearSingularModel m
  have hs : (∑ S ∈ assignments P.pop, adjustedTau P q S) =
      ∑ S ∈ assignments P.pop, adjustedTau P q Sᶜ := by
    apply Finset.sum_bij (fun S hS => Sᶜ)
    · intro S hS
      exact FV_assignment_compl m S hS
    · intro S hS T hT he
      simpa using congrArg (fun U : Finset (Fin (2*m)) => Uᶜ) he
    · intro S hS
      exact ⟨Sᶜ,FV_assignment_compl m S hS,by simp⟩
    · intro S hS
      simp
  simp only [FV_tau_compl,Finset.sum_neg_distrib] at hs
  have hz : (∑ S ∈ assignments P.pop, adjustedTau P q S) = 0 := by linarith
  change (∑ S ∈ assignments P.pop, adjustedTau P q S) / ((assignments P.pop).card : ℝ) = 0
  rw [hz,zero_div]

private lemma FV_variance_lower (m : ℕ) (hm : 4 ≤ m) :
    8*(2 : ℝ)^(2*(2*m)^2)/(2 : ℝ)^(2*m) ≤
      designVariance (nearSingularModel m).pop (adjustedTau (nearSingularModel m) (FV_y m)) ∧
    8 ≤ designVariance (nearSingularModel m).pop (adjustedTau (nearSingularModel m) (FV_y m)) := by
  let P := nearSingularModel m
  let A := FV_A m
  let C : ℝ := (assignments P.pop).card
  let f := adjustedTau P (FV_y m)
  have hC : 0 < C := by
    change (0 : ℝ) < ((assignments P.pop).card : ℝ)
    exact_mod_cast Finset.card_pos.mpr ⟨A,FV_A_mem m⟩
  have he := (FV_eta_bounds m hm).1
  have hcard : C ≤ (2 : ℝ)^(2*m) := by
    dsimp [C,P]
    have hn : (assignments (nearSingularModel m).pop).card = (2*m).choose m := by
      simp [assignments,nearSingularModel]
    rw [hn]
    exact_mod_cast Nat.choose_le_two_pow (2*m) m
  have hA : A ∈ assignments P.pop := FV_A_mem m
  have hAc : Aᶜ ∈ assignments P.pop := FV_assignment_compl m A hA
  have hne : A ≠ Aᶜ := by
    have hN : 0 < 2*m := by omega
    let i : Fin (2*m) := ⟨0,hN⟩
    have hi : i ∈ A := by simp [A,FV_A,i,show 0<m by omega]
    intro heq
    have hic : i ∈ Aᶜ := by rw [← heq]; exact hi
    exact Finset.mem_compl.mp hic hi
  have hfA : f A = -2/FV_eta m := FV_rare_statistic m hm
  have hfAc : f Aᶜ = 2/FV_eta m := by
    change adjustedTau P (FV_y m) Aᶜ = _
    rw [FV_tau_compl]
    change -f A = _
    rw [hfA]
    ring
  have hs : 8/FV_eta m^2 ≤ ∑ S ∈ assignments P.pop, f S^2 := by
    calc
      _ = ∑ S ∈ ({A,Aᶜ} : Finset (Finset (Fin (2*m)))), f S^2 := by
        rw [Finset.sum_pair hne,hfA,hfAc]
        field_simp
        <;> ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (by intro S hS; simp only [Finset.mem_insert,Finset.mem_singleton] at hS
            rcases hS with rfl | rfl <;> assumption)
        (fun S hS hSn => sq_nonneg _)
  have hvar : (8/FV_eta m^2)/C ≤ designVariance P.pop f := by
    change (8/FV_eta m^2)/C ≤
      (∑ S ∈ assignments P.pop, (f S-expectation P.pop f)^2)/C
    have hmean : expectation P.pop f = 0 := FV_design_mean m (FV_y m)
    rw [hmean]
    simp only [sub_zero]
    exact div_le_div_of_nonneg_right hs hC.le
  have hbase : (8/FV_eta m^2)/(2 : ℝ)^(2*m) ≤ designVariance P.pop f := by
    exact (div_le_div_of_nonneg_left (by positivity) hC hcard).trans hvar
  have heta : 8/FV_eta m^2 = 8*(2 : ℝ)^(2*(2*m)^2) := by
    rw [show 2*(2*m)^2=(2*m)^2*2 by omega,pow_mul]
    dsimp [FV_eta]
    field_simp
  rw [heta] at hbase
  refine ⟨hbase,?_⟩
  have hpow : (2 : ℝ)^(2*m) ≤ (2 : ℝ)^(2*(2*m)^2) := by
    apply pow_le_pow_right₀ (by norm_num)
    nlinarith
  have h8 : (8 : ℝ) ≤ 8*(2 : ℝ)^(2*(2*m)^2)/(2 : ℝ)^(2*m) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<(2 : ℝ)^(2*m))).mpr
    linarith
  exact h8.trans hbase

private lemma FV_sigma_bound (m : ℕ) (hm : 4 ≤ m) (T : Finset (Fin (2*m)))
    (hT : T ∈ assignments (nearSingularModel m).pop) :
    0 ≤ adjustedSigma2 (nearSingularModel m) (FV_y m) T ∧
      adjustedSigma2 (nearSingularModel m) (FV_y m) T < 5/((2*m : ℕ) : ℝ) := by
  let P := nearSingularModel m
  have hs : T.card = m := (Finset.mem_powersetCard.mp hT).2
  have hsc : Tᶜ.card = m := by rw [Finset.card_compl,Fintype.card_fin,hs]; omega
  have hTp : T.Nonempty := Finset.card_pos.mp (by omega)
  have hTcp : Tᶜ.Nonempty := Finset.card_pos.mp (by omega)
  have hmr : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  obtain ⟨hgp,hgn⟩ := FV_even_fullrank m hm T hT
  have hr1 := ols_minimizer_fullrank P.x T (FV_y m) hTp hgp 0
  have hr0 := ols_minimizer_fullrank P.x Tᶜ (FV_y m) hTcp hgn 0
  simp only [rss,dotProduct_zero,sub_zero] at hr1 hr0
  have hcs : controlSize P.pop = (m : ℝ) := by dsimp [controlSize,P,nearSingularModel]; push_cast; ring
  have hnonneg : 0 ≤ adjustedSigma2 P (FV_y m) T := by
    unfold adjustedSigma2 rss
    positivity
  have hle : adjustedSigma2 P (FV_y m) T ≤ (∑ i, FV_y m i^2)/(m : ℝ)^2 := by
    change rss P.x T (FV_y m) (ols P.x T (FV_y m))/(m : ℝ)^2 +
      rss P.x Tᶜ (FV_y m) (ols P.x Tᶜ (FV_y m))/(controlSize P.pop)^2 ≤ _
    rw [hcs,← add_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have htotal := Finset.sum_add_sum_compl T (fun i => FV_y m i^2)
    exact (add_le_add hr1 hr0).trans_eq htotal
  have hyb := (FV_even_bounds m hm).2
  have hsum : (∑ i, FV_y m i^2) ≤ (2*(m : ℝ))*(121/100) := by
    calc
      _ ≤ ∑ _i : Fin (2*m), (121/100 : ℝ) := Finset.sum_le_sum (fun i hi => by
        have h := abs_le.mp (hyb i)
        nlinarith [mul_nonneg (by linarith : 0 ≤ 11/10-FV_y m i)
          (by linarith : 0 ≤ 11/10+FV_y m i)])
      _ = _ := by simp
  have hstrict : (2*(m : ℝ))*(121/100)/(m : ℝ)^2 < 5/(2*(m : ℝ)) := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hmr) (by positivity)).mpr
    nlinarith [sq_pos_of_pos hmr]
  refine ⟨hnonneg,?_⟩
  have hle2 := hle.trans (div_le_div_of_nonneg_right hsum (sq_nonneg (m : ℝ)))
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hle2.trans_lt hstrict

private lemma FV_error_probability (m : ℕ) (hm : 4 ≤ m) :
    probability (nearSingularModel m).pop (fun T =>
      |adjustedSigma2 (nearSingularModel m) (FV_y m) T /
        designVariance (nearSingularModel m).pop (adjustedTau (nearSingularModel m) (FV_y m))-1| ≥ 1/2) = 1 := by
  let P := nearSingularModel m
  let V := designVariance P.pop (adjustedTau P (FV_y m))
  have hV : 8 ≤ V := (FV_variance_lower m hm).2
  have hVpos : 0 < V := by linarith
  have hN : (8 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 8≤2*m by omega)
  have h5 : 5/((2*m : ℕ) : ℝ) ≤ (5/8 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN
  have hevent (T : Finset (Fin (2*m))) (hT : T ∈ assignments P.pop) :
      |adjustedSigma2 P (FV_y m) T/V-1| ≥ 1/2 := by
    obtain ⟨hs0,hs1⟩ := FV_sigma_bound m hm T hT
    have hsmall : adjustedSigma2 P (FV_y m) T < V*(1/2) := by linarith
    have hratio : adjustedSigma2 P (FV_y m) T/V < 1/2 := (div_lt_iff₀ hVpos).mpr (by linarith)
    rw [abs_of_neg (by linarith : adjustedSigma2 P (FV_y m) T/V-1<0)]
    linarith
  have hfilter : (assignments P.pop).filter
      (fun T => |adjustedSigma2 P (FV_y m) T/V-1| ≥ 1/2) = assignments P.pop :=
    Finset.filter_eq_self.mpr hevent
  have hc : ((assignments P.pop).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨FV_A m,FV_A_mem m⟩
  change (((assignments P.pop).filter (fun T => |adjustedSigma2 P (FV_y m) T/V-1| ≥ 1/2)).card : ℝ) /
    ((assignments P.pop).card : ℝ) = 1
  rw [hfilter,div_self hc]

private lemma FV_observed (m : ℕ) (S : Finset (Fin (2*m))) :
    observedW (nearSingularModel m).pop 0 S = FV_y m := by
  funext i
  simp [observedW,observedY,FV_model_y]

/-- The fully explicit counterexample to the feasible-variance version of (E.61). -/
theorem feasible_variance_counterexample_proof :
    (∀ m, 4 ≤ m →
      let P := nearSingularModel m
      Xi P 0 (1/4) 16 5 (1/3) ∧ late P.pop = 0 ∧
      (∀ S ∈ assignments P.pop, (gram P.x S).det ≠ 0 ∧ (gram P.x Sᶜ).det ≠ 0) ∧
      (∀ S ∈ assignments P.pop,
        let q := observedW P.pop 0 S
        designVariance P.pop (adjustedTau P q) ≥
          8*(2 : ℝ)^(2*(2*m)^2)/(2 : ℝ)^(2*m) ∧
        (∀ T ∈ assignments P.pop, 0 ≤ adjustedSigma2 P q T ∧
          adjustedSigma2 P q T < 5/((2*m : ℕ) : ℝ)) ∧
        probability P.pop (fun T => |adjustedSigma2 P q T /
          designVariance P.pop (adjustedTau P q)-1| ≥ 1/2) = 1)) ∧
    (∀ n, 9 ≤ n → Odd n → Xi (oddNearModel n) 0 (1/4) 16 5 (1/3)) ∧
    Tendsto (fun j =>
      let P := nearSingularModel (j+4)
      probability P.pop (fun T => |adjustedSigma2 P (fun i => P.pop.y i false) T /
        designVariance P.pop (adjustedTau P (fun i => P.pop.y i false))-1| ≥ 1/2))
      atTop (nhds 1) := by
  refine ⟨?_,?_,?_⟩
  · intro m hm
    refine ⟨FV_even_admissible m hm,FV_identical_late _ (by intro i; rfl),
      FV_even_fullrank m hm,?_⟩
    intro S hS
    change designVariance (nearSingularModel m).pop
      (adjustedTau (nearSingularModel m) (observedW (nearSingularModel m).pop 0 S)) ≥
      8*(2 : ℝ)^(2*(2*m)^2)/(2 : ℝ)^(2*m) ∧ _
    rw [FV_observed]
    exact ⟨(FV_variance_lower m hm).1,FV_sigma_bound m hm,FV_error_probability m hm⟩
  · intro n hn hodd
    exact FV_odd_admissible n hn
  · convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) using 1
    funext j
    simpa only [FV_model_y] using FV_error_probability (j+4) (by omega)

end
end AronowAudit.P002.Wave1
