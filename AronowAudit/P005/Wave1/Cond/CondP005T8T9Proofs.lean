import AronowAudit.Literature.CondP002P005P006
import AronowAudit.P005.Wave1.Gap.GP005B5

/-!
Conditional proofs of P005-T8 and P005-T9. The only literature premise is
`Tropp2011RowSampling`. Appending the intercept to the standardized covariates
controls both centered arm Gram matrices. A finite Markov bound for the sum
of the two arm scores then gives the remainder rate.
-/

noncomputable section
open scoped BigOperators Matrix
open Finset Filter
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace AronowAudit.P005.Wave1
open AronowAudit.Literature
local instance CondT8T9_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p

-- Coordinate-level augmented Gram calculation required by the Tropp application.
lemma CondT8T9_augmented_orthogonal {n d : ℕ}
    (P : Population n d) (hn : 0 < n) (hP : standardized P) :
    let W : Matrix (Fin n) (Fin (d + 1)) ℝ :=
      fun i j => Fin.cases 1 (fun k => P.x i k) j / Real.sqrt n
    ∀ a b, (∑ i, W i a * W i b) = if a = b then 1 else 0 := by
  dsimp only
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have sn0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr nr).ne'
  have sns : (Real.sqrt (n : ℝ))^2 = n := Real.sq_sqrt nr.le
  have hx : ∀ k, (∑ i, P.x i k) = 0 := by
    intro k
    have h := congrFun hP.1 k
    simp only [xMean, mean, Finset.card_univ, Fintype.card_fin, Pi.zero_apply] at h
    exact (div_eq_zero_iff).mp h |>.resolve_right nr.ne'
  have hg : ∀ a b : Fin d, (∑ i, P.x i a * P.x i b) =
      (n : ℝ) * (if a = b then 1 else 0) := by
    intro a b
    have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M a b) hP.2
    simp only [gram, popMean, mean, Finset.card_univ, Fintype.card_fin, Matrix.one_apply] at h
    exact (div_eq_iff nr.ne').mp h |>.trans (mul_comm _ _)
  intro a b
  refine Fin.cases ?_ (fun a => ?_) a
  · refine Fin.cases ?_ (fun b => ?_) b
    · simp only [Fin.cases_zero, one_div, mul_inv_rev, ← sq, sns, ↓reduceIte,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      exact sns.symm
    · simp only [Fin.cases_zero, Fin.cases_succ, ne_eq, Ne.symm (Fin.succ_ne_zero _), ↓reduceIte]
      simp only [div_mul_div_comm, one_mul, ← Finset.sum_div, hx, zero_div]
  · refine Fin.cases ?_ (fun b => ?_) b
    · simp only [Fin.cases_zero, Fin.cases_succ, ne_eq, Fin.succ_ne_zero, ↓reduceIte]
      simp only [div_mul_div_comm, mul_one, ← Finset.sum_div, hx, zero_div]
    · simp only [Fin.cases_succ, Fin.succ_inj]
      simp only [div_mul_div_comm, ← Finset.sum_div, ← pow_two, sns, hg]
      field_simp

lemma CondT8T9_augmented_row_bound {n d : ℕ}
    (P : Population n d) (hn : 0 < n) (hd : 1 ≤ d) (hP : standardized P) :
    let W : Matrix (Fin n) (Fin (d + 1)) ℝ :=
      fun i j => Fin.cases 1 (fun k => P.x i k) j / Real.sqrt n
    (n : ℝ) * sSup (Set.range (fun i => ∑ j, (W i j)^2)) ≤ 2 * n * kappa P := by
  dsimp only
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have sns : (Real.sqrt (n : ℝ))^2 = n := Real.sq_sqrt nr.le
  have hrow : ∀ i, (∑ j : Fin (d+1),
      (Fin.cases 1 (fun k => P.x i k) j / Real.sqrt n)^2) =
        (1 + leverage P i) / n := by
    intro i
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, div_pow, one_pow, sns,
      ← Finset.sum_div]
    unfold leverage dot
    simp only [pow_two]
    ring
  simp_rw [hrow]
  have hκ : (1 : ℝ) ≤ (n : ℝ) * kappa P := by
    have hk := (kappa_bounds P hn hP.2).1
    have hdn : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hh := (div_le_iff₀ nr).mp hk
    nlinarith
  have hs : sSup (Set.range (fun i => (1 + leverage P i) / (n : ℝ))) ≤ 2*kappa P := by
    apply csSup_le
    · exact ⟨_, Set.mem_range_self (⟨0, hn⟩ : Fin n)⟩
    · rintro r ⟨i, rfl⟩
      apply (div_le_iff₀ nr).mpr
      have hh := leverage_le_maximum P hn i
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs nr.le]

-- A uniform dimension bound for the two Chernoff tails.
lemma CondT8T9_chernoff_uniform (b : ℝ) (hb : 0 < b) (hb1 : b < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℝ, 2 ≤ k → k * Real.rpow b (A * Real.log k) < ε := by
  have hl : Real.log b < 0 := Real.log_neg hb hb1
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ht : Tendsto (fun A : ℝ => 2 * Real.rpow b (A * Real.log 2)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_atTop_of_base_lt_one b (by linarith) hb1).comp
      (Filter.Tendsto.atTop_mul_const hl2 tendsto_id)).const_mul (2 : ℝ)
  have he : ∀ᶠ A : ℝ in atTop, 2 * Real.rpow b (A * Real.log 2) < ε :=
    ht.eventually (gt_mem_nhds hε)
  obtain ⟨A, hA, hAB, hAE⟩ :=
    (eventually_gt_atTop (0 : ℝ) |>.and
      ((eventually_ge_atTop ((-1) / Real.log b)).and he)).exists
  refine ⟨A, hA, ?_⟩
  have hcoef : 1 + A * Real.log b ≤ 0 := by
    have hh := (div_le_iff_of_neg hl).mp hAB
    linarith
  intro k hk
  have hk0 : 0 < k := by linarith
  have hklog : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk
  have hbound : k * Real.rpow b (A * Real.log k) ≤
      2 * Real.rpow b (A * Real.log 2) := by
    change k * b ^ (A * Real.log k) ≤ 2 * b ^ (A * Real.log 2)
    rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hb,
      ← Real.exp_log hk0, ← Real.exp_log (by norm_num : (0 : ℝ) < 2),
      ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [Real.log_exp]
    nlinarith [mul_le_mul_of_nonpos_left hklog hcoef]
  exact hbound.trans_lt hAE

lemma CondT8T9_mean_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (S : Finset (Fin n)) (f : ι → Fin n → ℝ) :
    mean S (fun i => ∑ j, f j i) = ∑ j, mean S (f j) := by
  simp only [mean, Finset.sum_div]
  exact Finset.sum_comm

lemma CondT8T9_dot_mean {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (v : Fin d → ℝ) :
    mean S (fun i => dot (P.x i) v) = dot (xMean P S) v := mean_dot P S v

lemma CondT8T9_dot_mean_product {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (a : Fin n → ℝ) (v : Fin d → ℝ) :
    mean S (fun i => a i * dot (P.x i) v) =
      dot (fun k => mean S (fun i => a i * P.x i k)) v := by
  simp only [dot, Finset.mul_sum, ← mul_assoc]
  rw [CondT8T9_mean_sum]
  simp_rw [show ∀ k, mean S (fun i => a i * P.x i k * v k) =
      v k * mean S (fun i => a i * P.x i k) from fun k => by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          mean_mul S (fun i => a i * P.x i k) (v k)]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma CondT8T9_armN_fit {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (v : Fin d → ℝ) :
    armN P S (fun i => dot (P.x i) v) = armL P S *ᵥ v := by
  funext k
  simp only [armN, armL, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib]
  rw [CondT8T9_dot_mean]
  have hh := CondT8T9_dot_mean_product P S (fun i => P.x i k) v
  simp only [dot] at hh
  have hh' : mean S (fun i => dot (P.x i) v * P.x i k) =
      ∑ j, mean S (fun i => P.x i k * P.x i j) * v j := by
    simpa only [dot, mul_comm] using hh
  rw [hh']
  simp only [dot, xMean, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma CondT8T9_armN_sub {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (a b : Fin n → ℝ) :
    armN P S (fun i => a i - b i) = armN P S a - armN P S b := by
  funext k
  simp only [armN, sub_mul, mean_sub, Pi.sub_apply]
  ring

lemma CondT8T9_armN_centered {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (hS : S.Nonempty) (y : Fin n → ℝ) :
    armN P S (centered y) = armN P S y := by
  have hc : mean S (centered y) = mean S y - popMean y := by
    change mean S (fun i => y i - popMean y) = _
    rw [mean_sub, mean_const S hS]
  funext k
  simp only [armN, hc, centered, sub_mul, mean_sub, mean_mul, xMean]
  ring

lemma CondT8T9_residual_equation {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (hS : S.Nonempty) (y : Fin n → ℝ) :
    armN P S (armResidual P y) = armN P S y - armL P S *ᵥ populationSlope P y := by
  unfold armResidual
  rw [CondT8T9_armN_sub, CondT8T9_armN_centered P S hS, CondT8T9_armN_fit]

lemma CondT8T9_residual_mean {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (hS : S.Nonempty) (y : Fin n → ℝ) :
    mean S (armResidual P y) = mean S y - popMean y -
      dot (xMean P S) (populationSlope P y) := by
  change mean S (fun i => (y i - popMean y) - dot (P.x i) (populationSlope P y)) = _
  rw [mean_sub, mean_sub, mean_const S hS, mean_dot]

lemma CondT8T9_residual_slope {n d : ℕ} (P : Population n d)
    (hP : standardized P) (y : Fin n → ℝ) :
    populationSlope P (armResidual P y) = 0 := by
  have hs : ∀ a b : Fin n → ℝ, populationSlope P (fun i => a i-b i) =
      populationSlope P a - populationSlope P b := by
    intro a b
    funext k
    simp only [populationSlope, sub_mul, popMean, mean_sub, Pi.sub_apply]
  unfold armResidual
  rw [hs, populationSlope_centered P hP.1, populationSlope_projection P hP.2, sub_self]

lemma CondT8T9_residual_square {n d : ℕ} (P : Population n d)
    (hn : 0 < n) (hP : standardized P) (y : Fin n → ℝ) :
    popMean (fun i => (armResidual P y i)^2) ≤ popMean (fun i => y i^2) := by
  let β := populationSlope P y
  let e := armResidual P y
  have heβ : popMean (fun i => e i * dot (P.x i) β) = 0 := by
    change mean univ (fun i => e i * dot (P.x i) β) = 0
    rw [CondT8T9_dot_mean_product]
    change dot (populationSlope P (armResidual P y)) β = 0
    rw [CondT8T9_residual_slope P hP]
    simp [dot]
  have hident : popMean (fun i => (centered y i)^2) =
      popMean (fun i => e i^2) + popMean (fun i => (dot (P.x i) β)^2) := by
    have hf : (fun i => (centered y i)^2) =
        (fun i => e i^2 + (dot (P.x i) β)^2 + 2*(e i * dot (P.x i) β)) := by
      funext i
      dsimp [e, armResidual, β]
      ring
    change mean univ _ = mean univ _ + mean univ _
    rw [hf, mean_add, mean_add, mean_mul]
    change _ + 2 * popMean (fun i => e i * dot (P.x i) β) = _
    rw [heβ, mul_zero, add_zero]
  have hnon := mean_nonneg univ (fun i => (dot (P.x i) β)^2)
    (fun _ _ => sq_nonneg _)
  change 0 ≤ popMean (fun i => (dot (P.x i) β)^2) at hnon
  have hc := (mean_square_centering univ
    (show (univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, mem_univ _⟩) y).2
  change popMean (fun i => (centered y i)^2) ≤ popMean (fun i => y i^2) at hc
  change popMean (fun i => e i^2) ≤ _
  linarith

lemma CondT8T9_armL_quadratic {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (v : Fin d → ℝ) :
    dot v (armL P S *ᵥ v) = mean S (fun i => (dot (P.x i) v)^2) -
      (dot (xMean P S) v)^2 := by
  have hh := CondT8T9_dot_mean_product P S (fun i => dot (P.x i) v) v
  have ha := congrArg (fun w => dot w v) (CondT8T9_armN_fit P S v)
  have he : dot (armN P S (fun i => dot (P.x i) v)) v =
      dot (fun k => mean S (fun i => dot (P.x i) v * P.x i k)) v -
      mean S (fun i => dot (P.x i) v) * dot (xMean P S) v := by
    simp only [dot, armN, sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]
  rw [← dot_comm (armL P S *ᵥ v) v, ← ha, he, CondT8T9_dot_mean, ← hh]
  simp only [pow_two]

def CondT8T9_armError {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (y : Fin n → ℝ) : ℝ :=
  dot (xMean P S) ((armL P S)⁻¹ *ᵥ armN P S (armResidual P y))

lemma CondT8T9_intercept {n d : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (hS : S.Nonempty) (y : Fin n → ℝ)
    (hinv : (armL P S).det ≠ 0) :
    mean S y - dot (xMean P S) (armBetaHat P S y) - popMean y -
      mean S (armResidual P y) = -CondT8T9_armError P S y := by
  have hb : (armL P S)⁻¹ *ᵥ armN P S (armResidual P y) =
      armBetaHat P S y - populationSlope P y := by
    rw [CondT8T9_residual_equation P S hS, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hinv),
      Matrix.one_mulVec]
    rfl
  rw [CondT8T9_residual_mean P S hS, CondT8T9_armError, hb]
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

def CondT8T9_W {n d : ℕ} (P : Population n d) : Matrix (Fin n) (Fin (d+1)) ℝ :=
  fun i j => Fin.cases 1 (fun k => P.x i k) j / Real.sqrt n

def CondT8T9_bad {n d : ℕ} (P : Population n d) (s : ℕ)
    (S : Finset (Fin n)) : Prop :=
  ∃ v : Fin (d+1) → ℝ, coordinateNormSq (d+1) v = 1 ∧
    (restrictedNormSq n (d+1) (CondT8T9_W P) S v < (1-(1/2 : ℝ))*(s : ℝ)/n ∨
      (1+(1 : ℝ))*(s : ℝ)/n < restrictedNormSq n (d+1) (CondT8T9_W P) S v)

lemma CondT8T9_tail_constants :
    let b₁ := Real.exp (-(1/2 : ℝ)) / Real.rpow (1-(1/2 : ℝ)) (1-(1/2 : ℝ))
    let b₂ := Real.exp (1 : ℝ) / Real.rpow (1+(1 : ℝ)) (1+(1 : ℝ))
    0 < b₁ ∧ b₁ < 1 ∧ 0 < b₂ ∧ b₂ < 1 := by
  dsimp only
  have hlog : Real.log (2 : ℝ) < 1 := by
    have hh := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    norm_num at hh ⊢
    exact hh
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
    simpa using Real.log_inv (2 : ℝ)
  have hlog' : 1/2 < Real.log (2 : ℝ) := by
    have hh := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 1/2) (by norm_num)
    rw [hhalf] at hh
    linarith
  norm_num only [show (1 : ℝ)-1/2 = 1/2 by norm_num, show (1 : ℝ)+1 = 2 by norm_num]
  refine ⟨div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _), ?_,
    div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  · simp only [Real.rpow_eq_pow]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1/2), hhalf,
      ← Real.exp_sub, Real.exp_lt_one_iff]
    linarith
  · simp only [Real.rpow_eq_pow]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      ← Real.exp_sub, Real.exp_lt_one_iff]
    linarith

lemma CondT8T9_tropp_finite (H : Tropp2011RowSampling) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ {n d s : ℕ} (P : Population n d),
      0 < n → 1 ≤ d → standardized P → s ≤ n →
      A * (2*n*kappa P) * Real.log (d+1 : ℕ) ≤ (s : ℝ) →
      probability s (CondT8T9_bad P s) < ε := by
  let b₁ := Real.exp (-(1/2 : ℝ)) / Real.rpow (1-(1/2 : ℝ)) (1-(1/2 : ℝ))
  let b₂ := Real.exp (1 : ℝ) / Real.rpow (1+(1 : ℝ)) (1+(1 : ℝ))
  obtain ⟨hb₁, hb₁', hb₂, hb₂'⟩ := CondT8T9_tail_constants
  change 0 < b₁ at hb₁
  change b₁ < 1 at hb₁'
  change 0 < b₂ at hb₂
  change b₂ < 1 at hb₂'
  obtain ⟨A, hA, hbound⟩ := CondT8T9_chernoff_uniform (max b₁ b₂)
    (lt_max_of_lt_left hb₁) (max_lt hb₁' hb₂') (ε/2) (by positivity)
  refine ⟨A, hA, ?_⟩
  intro n d s P hn hd hP hsn hs
  have hk : (2 : ℝ) ≤ (d+1 : ℕ) := by exact_mod_cast (show 2 ≤ d+1 by omega)
  have hl : 0 ≤ Real.log (d+1 : ℕ) := Real.log_nonneg (by linarith)
  have hrow := CondT8T9_augmented_row_bound P hn hd hP
  change (n : ℝ) * sSup (Set.range (fun i => ∑ j, (CondT8T9_W P i j)^2)) ≤
    2*n*kappa P at hrow
  have hsample : A * ((n : ℝ) * sSup (Set.range
      (fun i => ∑ j, (CondT8T9_W P i j)^2))) * Real.log (d+1 : ℕ) ≤ s := by
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrow hA.le) hl).trans hs
  have hH := H n (d+1) s hn (by omega) hsn (CondT8T9_W P)
    (CondT8T9_augmented_orthogonal P hn hP) A (1/2) 1 hA
    (by norm_num) (by norm_num) (by norm_num) hsample
  change probability s (CondT8T9_bad P s) ≤
    (d+1 : ℕ) * Real.rpow b₁ (A*Real.log (d+1 : ℕ)) +
      (d+1 : ℕ) * Real.rpow b₂ (A*Real.log (d+1 : ℕ)) at hH
  have he : 0 ≤ A*Real.log (d+1 : ℕ) := mul_nonneg hA.le hl
  have h₁ := Real.rpow_le_rpow hb₁.le (le_max_left b₁ b₂) he
  have h₂ := Real.rpow_le_rpow hb₂.le (le_max_right b₁ b₂) he
  have hB := hbound (d+1 : ℕ) hk
  have hk0 : (0 : ℝ) ≤ (d+1 : ℕ) := by positivity
  simp only [Real.rpow_eq_pow] at hH hB
  linarith [mul_le_mul_of_nonneg_left h₁ hk0, mul_le_mul_of_nonneg_left h₂ hk0]

lemma CondT8T9_coordinate_div {k : ℕ} (v : Fin k → ℝ) (c : ℝ) :
    coordinateNormSq k (fun j => v j/c) = coordinateNormSq k v / c^2 := by
  simp only [coordinateNormSq, div_pow, Finset.sum_div]

lemma CondT8T9_restricted_div {n k : ℕ} (W : Matrix (Fin n) (Fin k) ℝ)
    (S : Finset (Fin n)) (v : Fin k → ℝ) (c : ℝ) :
    restrictedNormSq n k W S (fun j => v j/c) = restrictedNormSq n k W S v / c^2 := by
  simp only [restrictedNormSq, ← mul_div_assoc, ← Finset.sum_div, div_pow]

lemma CondT8T9_good_homogeneous {n d s : ℕ} (P : Population n d)
    (S : Finset (Fin n)) (hgood : ¬CondT8T9_bad P s S) (z : Fin (d+1) → ℝ) :
    (1/2 : ℝ)*(s : ℝ)/n * coordinateNormSq (d+1) z ≤
      restrictedNormSq n (d+1) (CondT8T9_W P) S z := by
  have hq : 0 ≤ coordinateNormSq (d+1) z := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hz : coordinateNormSq (d+1) z = 0
  · rw [hz, mul_zero]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · have hpos : 0 < coordinateNormSq (d+1) z := lt_of_le_of_ne hq (Ne.symm hz)
    have hsqrt : (Real.sqrt (coordinateNormSq (d+1) z))^2 =
        coordinateNormSq (d+1) z := Real.sq_sqrt hq
    have hunit : coordinateNormSq (d+1)
        (fun j => z j / Real.sqrt (coordinateNormSq (d+1) z)) = 1 := by
      rw [CondT8T9_coordinate_div, hsqrt, div_self hz]
    have hlow : (1/2 : ℝ)*(s : ℝ)/n ≤ restrictedNormSq n (d+1) (CondT8T9_W P) S
        (fun j => z j / Real.sqrt (coordinateNormSq (d+1) z)) := by
      by_contra hbad
      apply hgood
      refine ⟨_, hunit, Or.inl ?_⟩
      norm_num only [show (1 : ℝ)-1/2 = 1/2 by norm_num]
      exact lt_of_not_ge hbad
    rw [CondT8T9_restricted_div, hsqrt] at hlow
    exact (le_div_iff₀ hpos).mp hlow

lemma CondT8T9_augmented_centered {n d : ℕ} (P : Population n d)
    (hn : 0 < n) (S : Finset (Fin n)) (hS : S.Nonempty) (v : Fin d → ℝ) :
    restrictedNormSq n (d+1) (CondT8T9_W P) S
      (Fin.cases (-dot (xMean P S) v) v) =
      ((S.card : ℝ)/n) * dot v (armL P S *ᵥ v) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : (Real.sqrt (n : ℝ))^2 = n := Real.sq_sqrt hn'.le
  have hf : ∀ i, (∑ j : Fin (d+1), CondT8T9_W P i j *
      Fin.cases (-dot (xMean P S) v) v j) =
      (dot (P.x i) v - dot (xMean P S) v) / Real.sqrt n := by
    intro i
    simp only [CondT8T9_W, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
      div_mul_eq_mul_div, ← Finset.sum_div, one_mul, dot]
    ring
  simp only [restrictedNormSq, hf, div_pow, hsn, ← Finset.sum_div]
  have hm := (mean_square_centering S hS (fun i => dot (P.x i) v)).1
  rw [CondT8T9_dot_mean, ← CondT8T9_armL_quadratic] at hm
  have hs0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hm' : (∑ i ∈ S, (dot (P.x i) v - dot (xMean P S) v)^2) =
      (S.card : ℝ) * dot v (armL P S *ᵥ v) := by
    exact ((div_eq_iff hs0).mp hm).trans (mul_comm _ _)
  rw [hm']
  ring

lemma CondT8T9_coercive {n d s : ℕ} (P : Population n d) (hn : 0 < n)
    (hs : 0 < s) (S : Finset (Fin n)) (hSc : S.card = s)
    (hgood : ¬CondT8T9_bad P s S) :
    ∀ v : Fin d → ℝ, dot v v/4 ≤ dot v (armL P S *ᵥ v) := by
  intro v
  have hS : S.Nonempty := Finset.card_pos.mp (hSc ▸ hs)
  have hl := CondT8T9_good_homogeneous P S hgood (Fin.cases (-dot (xMean P S) v) v)
  rw [CondT8T9_augmented_centered P hn S hS, hSc] at hl
  have hz : coordinateNormSq (d+1) (Fin.cases (-dot (xMean P S) v) v) =
      (dot (xMean P S) v)^2 + dot v v := by
    simp only [coordinateNormSq, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
      neg_sq, dot, pow_two]
    ring
  rw [hz] at hl
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hc : 0 < (s : ℝ)/n := div_pos hs' hn'
  have hl' : (s : ℝ)/n * (((dot (xMean P S) v)^2 + dot v v)/2) ≤
      (s : ℝ)/n * dot v (armL P S *ᵥ v) := by
    convert hl using 1 <;> ring
  have hx : ((dot (xMean P S) v)^2 + dot v v)/2 ≤ dot v (armL P S *ᵥ v) := by
    exact (mul_le_mul_iff_right₀ hc).mp hl'
  linarith [sq_nonneg (dot (xMean P S) v), t8_dot_self_nonneg v]

lemma CondT8T9_probability_expectation {n : ℕ} (s : ℕ)
    (E : Finset (Fin n) → Prop) :
    probability s E = expectation s (fun S => if E S then 1 else 0) := by
  classical
  simp only [probability, expectation, Finset.sum_boole]

lemma CondT8T9_probability_mono {n : ℕ} (s : ℕ)
    (E F : Finset (Fin n) → Prop) (hEF : ∀ S ∈ design n s, E S → F S) :
    probability s E ≤ probability s F := by
  classical
  rw [CondT8T9_probability_expectation, CondT8T9_probability_expectation]
  apply t4_expectation_mono
  intro S hS
  by_cases hE : E S
  · simp [hE, hEF S hS hE]
  · by_cases hF : F S <;> simp [hE, hF]

lemma CondT8T9_probability_union {n : ℕ} (s : ℕ)
    (E F : Finset (Fin n) → Prop) :
    probability s (fun S => E S ∨ F S) ≤ probability s E + probability s F := by
  classical
  simp only [CondT8T9_probability_expectation, ← t4_expectation_add]
  apply t4_expectation_mono
  intro S _
  by_cases hE : E S <;> by_cases hF : F S <;> simp [hE, hF]

lemma CondT8T9_probability_control {n s : ℕ} (hsn : s ≤ n)
    (E : Finset (Fin n) → Prop) :
    probability s (fun S => E (control S)) = probability (n-s) E := by
  classical
  simp only [CondT8T9_probability_expectation]
  exact t4_complement_expectation hsn (fun S => if E S then (1 : ℝ) else 0)

lemma CondT8T9_markov {n : ℕ} (s : ℕ) (f : Finset (Fin n) → ℝ)
    (hf : ∀ S ∈ design n s, 0 ≤ f S) (B : ℝ) (hB : 0 < B) :
    probability s (fun S => B < f S) ≤ expectation s f / B := by
  classical
  rw [CondT8T9_probability_expectation]
  have hh : expectation s (fun S => if B < f S then 1 else 0) ≤
      expectation s (fun S => B⁻¹ * f S) := by
    apply t4_expectation_mono
    intro S hS
    by_cases he : B < f S
    · simp only [if_pos he]
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hB).mpr (by linarith)
    · simp only [if_neg he]
      exact mul_nonneg (inv_nonneg.mpr hB.le) (hf S hS)
  rw [expectation_mul] at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh

def CondT8T9_V {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (y : Fin n → ℝ) : Fin d → ℝ :=
  fun k => mean S (fun i => armResidual P y i * P.x i k)

/-- One nonnegative quantity controls the three factors in the arm remainder.
Its expectation has a bound independent of population size and dimension. -/
def CondT8T9_score {n d : ℕ} (P : Population n d) (S : Finset (Fin n))
    (y : Fin n → ℝ) : ℝ :=
  dot (xMean P S) (xMean P S) / ((d : ℝ)/n) +
    dot (CondT8T9_V P S y) (CondT8T9_V P S y) / kappa P +
    mean S (fun i => (armResidual P y i)^2)

lemma CondT8T9_score_nonneg {n d : ℕ} (P : Population n d)
    (hκ : 0 ≤ kappa P) (S : Finset (Fin n)) (y : Fin n → ℝ) :
    0 ≤ CondT8T9_score P S y := by
  exact add_nonneg (add_nonneg
    (div_nonneg (t8_dot_self_nonneg _) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (div_nonneg (t8_dot_self_nonneg _) hκ))
    (mean_nonneg _ _ (fun _ _ => sq_nonneg _))

lemma CondT8T9_X_moment {n d s : ℕ} (P : Population n d)
    (hn : 2 ≤ n) (hs : 0 < s) (hsn : s ≤ n) (hP : standardized P) :
    expectation s (fun S => dot (xMean P S) (xMean P S)) ≤
      (((n : ℝ)-s)/((s : ℝ)*(n-1))) * d := by
  have hx : ∀ k, popMean (fun i => P.x i k) = 0 := fun k => by
    simpa only [xMean, popMean, Pi.zero_apply] using congrFun hP.1 k
  have hg : ∀ k, popMean (fun i => (P.x i k)^2) = 1 := fun k => by
    simpa only [gram, Matrix.one_apply_eq, ← pow_two] using
      congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M k k) hP.2
  calc
    _ = ∑ k, expectation s (fun S => (mean S (fun i => P.x i k))^2) := by
      simp only [dot, xMean, ← pow_two, expectation_sum]
    _ ≤ ∑ k : Fin d, (((n : ℝ)-s)/((s : ℝ)*(n-1))) *
        popMean (fun i => (P.x i k)^2) := by
      exact Finset.sum_le_sum (fun k _ => t4_centered_mean_second hn hs hsn _ (hx k))
    _ = _ := by simp only [hg, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]; ring

lemma CondT8T9_V_moment {n d s : ℕ} (P : Population n d)
    (hn : 2 ≤ n) (hs : 0 < s) (hsn : s ≤ n) (hP : standardized P)
    (y : Fin n → ℝ) (K : ℝ) (hy : popMean (fun i => y i^2) ≤ K) :
    expectation s (fun S => dot (CondT8T9_V P S y) (CondT8T9_V P S y)) ≤
      (((n : ℝ)-s)/((s : ℝ)*(n-1))) * ((n : ℝ)*kappa P*K) := by
  let ρ : ℝ := ((n : ℝ)-s)/((s : ℝ)*(n-1))
  let e := armResidual P y
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hsn))
      (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  have hκ : 0 ≤ kappa P := (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans
    (kappa_bounds P (by omega) hP.2).1
  have he : ∀ k, popMean (fun i => e i * P.x i k) = 0 := by
    intro k
    simpa only [populationSlope, Pi.zero_apply] using
      congrFun (CondT8T9_residual_slope P hP y) k
  have hsum : (∑ k : Fin d, popMean (fun i => (e i * P.x i k)^2)) =
      popMean (fun i => leverage P i * e i^2) := by
    rw [← popMean_sum]
    congr 1
    funext i
    simp only [leverage, dot, Finset.sum_mul, mul_pow, pow_two]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have heK : popMean (fun i => e i^2) ≤ K :=
    (CondT8T9_residual_square P (by omega) hP y).trans hy
  calc
    _ = ∑ k, expectation s (fun S => (mean S (fun i => e i * P.x i k))^2) := by
      simp only [dot, CondT8T9_V, ← pow_two, expectation_sum, e]
    _ ≤ ∑ k : Fin d, ρ * popMean (fun i => (e i * P.x i k)^2) :=
      Finset.sum_le_sum (fun k _ => t4_centered_mean_second hn hs hsn _ (he k))
    _ = ρ * popMean (fun i => leverage P i * e i^2) := by rw [← Finset.mul_sum, hsum]
    _ ≤ ρ * popMean (fun i => ((n : ℝ)*kappa P)*e i^2) := by
      apply mul_le_mul_of_nonneg_left _ hρ
      exact mean_mono univ _ _ (fun i _ =>
        mul_le_mul_of_nonneg_right (leverage_le_maximum P (by omega) i) (sq_nonneg _))
    _ = ρ * ((n : ℝ)*kappa P * popMean (fun i => e i^2)) := by
      rw [popMean, mean_mul]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left heK (mul_nonneg (Nat.cast_nonneg _) hκ)) hρ

lemma CondT8T9_expectation_div {n : ℕ} (s : ℕ) (f : Finset (Fin n) → ℝ) (c : ℝ) :
    expectation s (fun S => f S/c) = expectation s f/c := by
  simpa only [div_eq_mul_inv, mul_comm] using expectation_mul s f c⁻¹

lemma CondT8T9_score_expectation {n d s : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hd : 1 ≤ d) (hs : 0 < s) (hsn : s ≤ n) (hP : standardized P)
    (a : ℝ) (ha : 0 < a) (halloc : a*(n : ℝ) ≤ s)
    (y : Fin n → ℝ) (K : ℝ) (hK : 0 ≤ K) (hy : popMean (fun i => y i^2) ≤ K) :
    expectation s (fun S => CondT8T9_score P S y) ≤ 2/a + 2*K/a + K := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hκ : 0 < kappa P := (div_pos hdpos hnpos).trans_le (kappa_bounds P (by omega) hP.2).1
  have hρ := t4_allocation_rho (n : ℝ) (s : ℝ) a hn' ha halloc (by exact_mod_cast hsn)
  have hX := (CondT8T9_X_moment P (by omega) hs hsn hP).trans
    (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg d))
  have hV := (CondT8T9_V_moment P (by omega) hs hsn hP y K hy).trans
    (mul_le_mul_of_nonneg_right hρ (by positivity : 0 ≤ (n : ℝ)*kappa P*K))
  have he := (CondT8T9_residual_square P (by omega) hP y).trans hy
  have hW : expectation s (fun S => mean S (fun i => (armResidual P y i)^2)) ≤ K := by
    rw [mean_unbiased (by omega) hs hsn]
    exact he
  have hX' : expectation s (fun S => dot (xMean P S) (xMean P S)) / ((d : ℝ)/n) ≤ 2/a := by
    apply (div_le_iff₀ (div_pos hdpos hnpos)).mpr
    convert hX using 1 <;> field_simp <;> ring
  have hV' : expectation s (fun S => dot (CondT8T9_V P S y) (CondT8T9_V P S y)) / kappa P ≤
      2*K/a := by
    apply (div_le_iff₀ hκ).mpr
    convert hV using 1 <;> field_simp <;> ring
  simp only [CondT8T9_score, t4_expectation_add, CondT8T9_expectation_div]
  linarith

lemma CondT8T9_sub_squared {d : ℕ} (u v : Fin d → ℝ) (c : ℝ) :
    dot (u-c • v) (u-c • v) ≤ 2*dot u u + 2*c^2*dot v v := by
  simp only [dot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  nlinarith [sq_nonneg (u k+c*v k)]

lemma CondT8T9_armError_bound {n d s : ℕ} (P : Population n d)
    (hn : 0 < n) (hd : 1 ≤ d) (hP : standardized P) (hs : 0 < s)
    (S : Finset (Fin n)) (hSc : S.card = s) (hinv : (armL P S).det ≠ 0)
    (hgood : ¬CondT8T9_bad P s S) (y : Fin n → ℝ)
    (B : ℝ) (hB : 0 < B) (hscore : CondT8T9_score P S y ≤ B) :
    |CondT8T9_armError P S y| ≤
      Real.sqrt (32*B^2*(1+B)) * Real.sqrt (kappa P*d/n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hq : 0 < (d : ℝ)/n := div_pos hd' hn'
  have hqκ := (kappa_bounds P hn hP.2).1
  have hκ : 0 < kappa P := hq.trans_le hqκ
  let X := xMean P S
  let V := CondT8T9_V P S y
  let e := armResidual P y
  let E := mean S e
  let U := armN P S e
  have hX0 : 0 ≤ dot X X := t8_dot_self_nonneg _
  have hV0 : 0 ≤ dot V V := t8_dot_self_nonneg _
  have hW0 : 0 ≤ mean S (fun i => e i^2) := mean_nonneg _ _ (fun _ _ => sq_nonneg _)
  change dot X X / ((d : ℝ)/n) + dot V V / kappa P + mean S (fun i => e i^2) ≤ B at hscore
  have hXd0 : 0 ≤ dot X X / ((d : ℝ)/n) := div_nonneg hX0 hq.le
  have hVd0 : 0 ≤ dot V V / kappa P := div_nonneg hV0 hκ.le
  have hX : dot X X ≤ B*((d : ℝ)/n) := (div_le_iff₀ hq).mp (by linarith)
  have hV : dot V V ≤ B*kappa P := (div_le_iff₀ hκ).mp (by linarith)
  have hW : mean S (fun i => e i^2) ≤ B := by linarith
  have hS : S.Nonempty := Finset.card_pos.mp (hSc ▸ hs)
  have hE : E^2 ≤ B := by
    have hc := (mean_square_centering S hS e).1
    have hc0 := mean_nonneg S (fun i => (e i-mean S e)^2) (fun _ _ => sq_nonneg _)
    change (mean S e)^2 ≤ B
    linarith
  have hUeq : U = V-E • X := by
    funext k
    simp only [U, V, E, X, armN, CondT8T9_V, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hU : dot U U ≤ (2*B*(1+B))*kappa P := by
    rw [hUeq]
    have hh := CondT8T9_sub_squared V X E
    have hp : E^2*dot X X ≤ B*(B*((d : ℝ)/n)) :=
      mul_le_mul hE hX hX0 hB.le
    have hqB := mul_le_mul_of_nonneg_left hqκ (sq_nonneg B)
    nlinarith [hh, hV, hp, hqB]
  have hInv := t8_coercive_inverse_squared (armL P S) hinv
    (CondT8T9_coercive P hn hs S hSc hgood) U
  have hInv' : dot ((armL P S)⁻¹ *ᵥ U) ((armL P S)⁻¹ *ᵥ U) ≤
      16*((2*B*(1+B))*kappa P) := hInv.trans (mul_le_mul_of_nonneg_left hU (by norm_num))
  have hsq : (CondT8T9_armError P S y)^2 ≤ (32*B^2*(1+B))*(kappa P*d/n) := by
    calc
      _ ≤ dot X X * dot ((armL P S)⁻¹ *ᵥ U) ((armL P S)⁻¹ *ᵥ U) :=
        t8_cauchy_schwarz X _
      _ ≤ (B*((d : ℝ)/n)) * (16*((2*B*(1+B))*kappa P)) :=
        mul_le_mul hX hInv' (t8_dot_self_nonneg _) (mul_nonneg hB.le hq.le)
      _ = _ := by ring
  have hC : 0 ≤ 32*B^2*(1+B) := by positivity
  have hr : 0 ≤ kappa P*d/n := by positivity
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hr]
  exact hsq

lemma CondT8T9_remainder_bound {n d s : ℕ} (P : Population n d)
    (hn : 0 < n) (hd : 1 ≤ d) (hP : standardized P) (hs : 0 < s) (hsn : s < n)
    (S : Finset (Fin n)) (hS : S ∈ design n s) (hinv : interactedRegular P s)
    (hgoodT : ¬CondT8T9_bad P s S)
    (hgoodC : ¬CondT8T9_bad P (n-s) (control S))
    (B : ℝ) (hB : 0 < B)
    (hscore : CondT8T9_score P S P.yT + CondT8T9_score P (control S) P.yC ≤ B) :
    |interactedATE P S - ate P - armLeading P S| ≤
      (2*Real.sqrt (32*B^2*(1+B))) * Real.sqrt (kappa P*d/n) := by
  have hcT : S.card = s := (Finset.mem_powersetCard.mp hS).2
  have hcC : (control S).card = n-s :=
    (Finset.mem_powersetCard.mp (t4_complement_mem hS)).2
  have hκ : 0 ≤ kappa P := (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans
    (kappa_bounds P hn hP.2).1
  have hT := CondT8T9_armError_bound P hn hd hP hs S hcT (hinv S hS).1 hgoodT P.yT B hB
    (by linarith [CondT8T9_score_nonneg P hκ (control S) P.yC])
  have hC := CondT8T9_armError_bound P hn hd hP (by omega) (control S) hcC
    (hinv S hS).2 hgoodC P.yC B hB
    (by linarith [CondT8T9_score_nonneg P hκ S P.yT])
  have hSt : S.Nonempty := Finset.card_pos.mp (hcT ▸ hs)
  have hSc : (control S).Nonempty := Finset.card_pos.mp (hcC ▸ Nat.sub_pos_of_lt hsn)
  have ht := CondT8T9_intercept P S hSt P.yT (hinv S hS).1
  have hc := CondT8T9_intercept P (control S) hSc P.yC (hinv S hS).2
  have heq : interactedATE P S - ate P - armLeading P S =
      -CondT8T9_armError P S P.yT + CondT8T9_armError P (control S) P.yC := by
    dsimp only [interactedATE, ate, armLeading]
    linarith
  rw [heq]
  have hh := abs_add_le (-CondT8T9_armError P S P.yT) (CondT8T9_armError P (control S) P.yC)
  rw [abs_neg] at hh
  nlinarith [hh, hT, hC]

lemma CondT8T9_sample_threshold {n d : ℕ} (P : Population n d)
    (hn : 0 < n) (hd : 1 ≤ d) (hκ : 0 ≤ kappa P)
    (A a : ℝ) (hA : 0 < A)
    (hsmall : kappa P * Real.log (max d 2 : ℕ) ≤ a/(4*A)) :
    A*(2*n*kappa P)*Real.log (d+1 : ℕ) ≤ a*n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : Real.log (d+1 : ℕ) ≤ 2*Real.log (max d 2 : ℕ) :=
    (Real.log_le_log (by positivity : (0 : ℝ) < (d+1 : ℕ))
      (by exact_mod_cast (show d+1 ≤ 2*d by omega))).trans (repaired_log_bounds d hd).2
  calc
    _ ≤ 4*A*n*(kappa P*Real.log (max d 2 : ℕ)) := by
      convert mul_le_mul_of_nonneg_left hl
        (by positivity : 0 ≤ A*(2*n*kappa P)) using 1 <;> ring
    _ ≤ 4*A*n*(a/(4*A)) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by field_simp <;> ring

/-- The corrected interacted expansion, conditional on the published
row-sampling theorem. -/
theorem corrected_interacted_expansion_max_conditional :
    AronowAudit.P005.corrected_interacted_expansion_max_conditional_statement := by
  intro H d m P h hinv hκ
  classical
  rcases h with ⟨hsize, ⟨K, hK, hym⟩, hstd, ⟨lo, hi, hlo, hlohi, hhi, halloc⟩⟩
  let a : ℝ := min lo (1-hi)
  have ha : 0 < a := lt_min hlo (sub_pos.mpr hhi)
  let C : ℝ := 2/a + 2*K/a + K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  intro ε hε
  let B : ℝ := 1+8*C/ε
  have hB : 0 < B := by dsimp [B]; positivity
  have hmark : 2*C/B ≤ ε/4 := by
    apply (div_le_iff₀ hB).mpr
    dsimp [B]
    have hε0 := hε.ne'
    field_simp
    nlinarith
  obtain ⟨A, hA, htropp⟩ := CondT8T9_tropp_finite H (ε/4) (by positivity)
  let M : ℝ := 2*Real.sqrt (32*B^2*(1+B))
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, Filter.eventually_atTop.mp ?_⟩
  have hsmall : ∀ᶠ n in atTop, kappa (P n)*Real.log (max (d n) 2 : ℕ) < a/(4*A) :=
    hκ.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < a/(4*A)))
  filter_upwards [hstd, hinv, hsmall, eventually_ge_atTop 3] with n hPn hreg hsm hn
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsz := hsize n hn
  have hkp : 0 ≤ kappa (P n) := (div_nonneg (Nat.cast_nonneg _) hn'.le).trans
    (kappa_bounds (P n) hn0 hPn.2).1
  have hallocT : a*(n : ℝ) ≤ m n := by
    have hh : lo*(n : ℝ) < m n := (lt_div_iff₀ hn').mp (halloc n hn).1
    exact (mul_le_mul_of_nonneg_right (min_le_left lo (1-hi)) hn'.le).trans hh.le
  have hallocC : a*(n : ℝ) ≤ (n-m n : ℕ) := by
    rw [Nat.cast_sub (by omega : m n ≤ n)]
    have hh : (m n : ℝ) < hi*n := (div_lt_iff₀ hn').mp (halloc n hn).2
    have hh' := mul_le_mul_of_nonneg_right (min_le_right lo (1-hi)) hn'.le
    change a*(n : ℝ) ≤ (1-hi)*n at hh'
    linarith
  have hthreshold := CondT8T9_sample_threshold (P n) hn0 hsz.1 hkp A a hA hsm.le
  have hbT := htropp (P n) hn0 hsz.1 hPn hsz.2.2.2.le (hthreshold.trans hallocT)
  have hbC : probability (m n)
      (fun S => CondT8T9_bad (P n) (n-m n) (control S)) < ε/4 := by
    rw [CondT8T9_probability_control hsz.2.2.2.le]
    exact htropp (P n) hn0 hsz.1 hPn (Nat.sub_le _ _) (hthreshold.trans hallocC)
  let Q : Finset (Fin n) → ℝ := fun S =>
    CondT8T9_score (P n) S (P n).yT + CondT8T9_score (P n) (control S) (P n).yC
  have hQ0 : ∀ S ∈ design n (m n), 0 ≤ Q S := fun S _ =>
    add_nonneg (CondT8T9_score_nonneg (P n) hkp S _) (CondT8T9_score_nonneg (P n) hkp (control S) _)
  have hQE : expectation (m n) Q ≤ 2*C := by
    dsimp only [Q]
    rw [t4_expectation_add, t4_complement_expectation hsz.2.2.2.le
      (fun S => CondT8T9_score (P n) S (P n).yC)]
    have ht := CondT8T9_score_expectation (P n) hn hsz.1 hsz.2.2.1 hsz.2.2.2.le hPn
      a ha hallocT (P n).yT K hK (hym n hn).1
    have hc := CondT8T9_score_expectation (P n) hn hsz.1 (by omega) (Nat.sub_le _ _) hPn
      a ha hallocC (P n).yC K hK (hym n hn).2.1
    change _ ≤ 2*(2/a+2*K/a+K)
    linarith
  have hbQ : probability (m n) (fun S => B < Q S) ≤ ε/4 :=
    ((CondT8T9_markov (m n) Q hQ0 B hB).trans
      (div_le_div_of_nonneg_right hQE hB.le)).trans hmark
  let ET := CondT8T9_bad (P n) (m n)
  let EC := fun S => CondT8T9_bad (P n) (n-m n) (control S)
  let EQ := fun S => B < Q S
  have hsub : probability (m n) (fun S =>
      |interactedATE (P n) S - ate (P n) - armLeading (P n) S| >
        M*Real.sqrt (kappa (P n)*d n/n)) ≤
      probability (m n) (fun S => ET S ∨ (EC S ∨ EQ S)) := by
    apply CondT8T9_probability_mono
    intro S hS hlarge
    by_cases ht : ET S
    · exact Or.inl ht
    by_cases hc : EC S
    · exact Or.inr (Or.inl hc)
    by_cases hq : EQ S
    · exact Or.inr (Or.inr hq)
    have hr := CondT8T9_remainder_bound (P n) hn0 hsz.1 hPn hsz.2.2.1 hsz.2.2.2 S hS hreg
      ht hc B hB (le_of_not_gt hq)
    exact (not_lt_of_ge hr hlarge).elim
  have hu := CondT8T9_probability_union (m n) ET (fun S => EC S ∨ EQ S)
  have hu' := CondT8T9_probability_union (m n) EC EQ
  change probability (m n) ET < ε/4 at hbT
  change probability (m n) EC < ε/4 at hbC
  change probability (m n) EQ ≤ ε/4 at hbQ
  linarith

/-- The equivalent corrected logarithm condition uses the same Tropp premise. -/
theorem corrected_interacted_expansion_two_conditional :
    AronowAudit.P005.corrected_interacted_expansion_two_conditional_statement := by
  intro H d m P h hinv hκ
  have hd : ∀ᶠ n in atTop, 1 ≤ d n := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact (h.1 n hn).1
  have hk : ∀ᶠ n in atTop, 0 ≤ kappa (P n) := by
    filter_upwards [eventually_ge_atTop 3, h.2.2.1] with n hn hP
    exact le_trans (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (kappa_bounds (P n) (by omega) hP.2).1
  exact corrected_interacted_expansion_max_conditional H d m P h hinv
    ((repaired_log_conditions d (fun n => kappa (P n)) hd hk).1.mp hκ)

end AronowAudit.P005.Wave1

