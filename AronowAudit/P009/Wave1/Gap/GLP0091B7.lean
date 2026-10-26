import AronowAudit.P009.Wave1.Gap.GLP0092B1

namespace AronowAudit.P009.Wave1

open scoped BigOperators Topology
open Filter
open BernoulliCompletion MixingBasics

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- Monotonicity of the finite expectation. -/
lemma t4_mean_mono {Ω : Type*} [Fintype Ω] (P : Law Ω)
    {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) : mean P f ≤ mean P g := by
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω)

/-- Recoding either finite random variable can only reduce its event supremum. -/
lemma t4_alpha_comp {Ω A B C D : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) (f : A → C) (g : B → D) :
    alpha P (fun ω => f (X ω)) (fun ω => g (Y ω)) ≤ alpha P X Y := by
  apply alpha_le_of_event_bound
  intro S T
  exact event_abs_le_alpha P X Y (f ⁻¹' S) (g ⁻¹' T)

/-- An indicator paired with a bounded function has covariance at most 2N alpha.
The bound follows from a finite signed-fiber argument. -/
lemma t4_indicator_bounded {Ω A B : Type*} [Fintype Ω] [Fintype B]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) (S : Set A)
    (g : B → ℝ) (N : ℝ) (hN : 0 ≤ N) (hg : ∀ y, |g y| ≤ N) :
    |cov P (fun ω => if X ω ∈ S then 1 else 0) (fun ω => g (Y ω))| ≤
      2 * N * alpha P X Y := by
  let Z : Ω → Bool := fun ω => decide (X ω ∈ S)
  have hz (ω) : Z ω = true ↔ X ω ∈ S := by simp [Z]
  have he : cov P (fun ω => if X ω ∈ S then 1 else 0) (fun ω => g (Y ω)) =
      ∑ y, t45_delta P Z Y true y * g y := by
    rw [covariance_product_formula]
    have hm : mean P (fun ω => (if X ω ∈ S then 1 else 0) * g (Y ω)) =
        mean P (fun ω => if Z ω = true then g (Y ω) else 0) := by
      congr 1
      funext ω
      by_cases hω : X ω ∈ S <;> simp [Z, hω]
    have hp : mean P (fun ω => if X ω ∈ S then (1:ℝ) else 0) =
        prob P (fun ω => Z ω = true) := by simp only [prob, hz]
    rw [hm, hp, t45_joint_fibers, t45_mean_fibers]
    simp only [t45_delta, sub_mul, Finset.sum_sub_distrib, mul_assoc,
      ← Finset.mul_sum]
  rw [he]
  calc
    _ ≤ ∑ y, |t45_delta P Z Y true y * g y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ y, |t45_delta P Z Y true y|) * N := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun y _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hg y) (abs_nonneg _)
    _ ≤ (2 * alpha P Z Y) * N :=
      mul_le_mul_of_nonneg_right (t45_binary_fiber_l1 P Z Y true) hN
    _ ≤ (2 * alpha P X Y) * N := by
      apply mul_le_mul_of_nonneg_right _ hN
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact t4_alpha_comp P X Y (fun x => decide (x ∈ S)) id
    _ = _ := by ring

/-- Finite bounded covariance inequality, including alpha = 0. -/
lemma t4_bounded_covariance {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) (f : A → ℝ) (g : B → ℝ)
    (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hf : ∀ x, |f x| ≤ M) (hg : ∀ y, |g y| ≤ N) :
    |cov P (fun ω => f (X ω)) (fun ω => g (Y ω))| ≤ 4*M*N*alpha P X Y := by
  let G := fun ω => g (Y ω)
  let v := fun x => ∑ ω, if X ω = x then P.mass ω * (G ω - mean P G) else 0
  have hm : mean P (fun ω => G ω - mean P G) = 0 := by
    rw [mean_sub, mean_const, sub_self]
  have hs : (∑ x, v x) = 0 := by
    have h := t45_sum_fibers X (fun ω => P.mass ω * (G ω - mean P G)) (fun _ => 1)
    have h' : (∑ x, v x) = mean P (fun ω => G ω - mean P G) := by
      simpa only [mul_one, v, mean] using h.symm
    exact h'.trans hm
  have hv : cov P (fun ω => f (X ω)) G = ∑ x, v x * f x := by
    rw [covariance_product_formula]
    calc
      _ = mean P (fun ω => f (X ω) * (G ω - mean P G)) := by
        simp only [mul_sub, mean_sub]
        rw [show mean P (fun ω => f (X ω) * mean P G) =
          mean P G * mean P (fun ω => f (X ω)) by
            simpa only [mul_comm] using mean_const_mul P (mean P G) (fun ω => f (X ω))]
        ring
      _ = _ := by
        simpa only [mean, mul_left_comm, mul_comm, mul_assoc, v] using
          t45_sum_fibers X (fun ω => P.mass ω * (G ω - mean P G)) f
  let S : Set A := {x | 0 ≤ v x}
  have he : (∑ x, if x ∈ S then v x else 0) =
      cov P (fun ω => if X ω ∈ S then 1 else 0) G := by
    have h := t45_sum_fibers X (fun ω => P.mass ω * (G ω - mean P G))
      (fun x => if x ∈ S then 1 else 0)
    have hcov : cov P (fun ω => if X ω ∈ S then 1 else 0) G =
        mean P (fun ω => (if X ω ∈ S then 1 else 0) * (G ω - mean P G)) := by
      rw [covariance_product_formula]
      simp only [mul_sub, mean_sub]
      rw [show mean P (fun ω => (if X ω ∈ S then 1 else 0) * mean P G) =
        mean P G * mean P (fun ω => if X ω ∈ S then 1 else 0) by
          simpa only [mul_comm] using mean_const_mul P (mean P G)
            (fun ω => if X ω ∈ S then 1 else 0)]
      ring
    rw [hcov]
    simpa only [mean, v, mul_ite, mul_one, mul_zero, mul_comm, mul_left_comm,
      mul_assoc, one_mul, zero_mul] using h.symm
  have hl1 : (∑ x, |v x|) = 2 * (∑ x, if x ∈ S then v x else 0) := by
    calc
      _ = ∑ x, (2 * (if x ∈ S then v x else 0) - v x) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : 0 ≤ v x
        · simp [S, hx, abs_of_nonneg hx] <;> ring
        · simp [S, hx, abs_of_neg (lt_of_not_ge hx)] <;> ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, sub_zero]
  rw [hv]
  calc
    _ ≤ ∑ x, |v x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ x, |v x|) * M := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun x _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
    _ = 2 * cov P (fun ω => if X ω ∈ S then 1 else 0) G * M := by rw [hl1, he]
    _ ≤ 2 * |cov P (fun ω => if X ω ∈ S then 1 else 0) G| * M := by
      gcongr
      exact le_abs_self _
    _ ≤ 2 * (2*N*alpha P X Y) * M := by
      gcongr
      exact t4_indicator_bounded P X Y S g N hN hg
    _ = _ := by ring


/-- Zero event mixing forces zero covariance for any two finite-image functions. -/
lemma t4_covariance_zero {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) (f : A → ℝ) (g : B → ℝ)
    (ha : alpha P X Y = 0) : cov P (fun ω => f (X ω)) (fun ω => g (Y ω)) = 0 := by
  let M := ∑ x, |f x|
  let N := ∑ y, |g y|
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hN : 0 ≤ N := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hf (x) : |f x| ≤ M := by
    exact Finset.single_le_sum (f := fun x => |f x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ x)
  have hg (y) : |g y| ≤ N := by
    exact Finset.single_le_sum (f := fun y => |g y|) (fun _ _ => abs_nonneg _) (Finset.mem_univ y)
  have h := t4_bounded_covariance P X Y f g M N hM hN hf hg
  rw [ha, mul_zero] at h
  exact abs_nonpos_iff.mp h

/-- Hard truncation preserves the absolute-value bound and finite-image structure. -/
def t4_trunc (U x : ℝ) : ℝ := if |x| ≤ U then x else 0

lemma t4_trunc_abs (U x : ℝ) (hU : 0 ≤ U) : |t4_trunc U x| ≤ U := by
  unfold t4_trunc
  split_ifs with hx
  · exact hx
  · simpa using hU

lemma t4_trunc_abs_self (U x : ℝ) : |t4_trunc U x| ≤ |x| := by
  unfold t4_trunc
  split_ifs <;> simp

/-- A tail product is controlled by the sum of the two q-th powers.
This elementary alternative to Holder is sufficient for the published constant 10. -/
lemma t4_tail_product (U q x y : ℝ) (hU : 0 < U) (hq : 2 ≤ q) (hx : U < |x|) :
    |x*y| ≤ Real.rpow U (2-q) * (Real.rpow |x| q + Real.rpow |y| q) := by
  simp only [Real.rpow_eq_pow] at *
  have hs (t : ℝ) (ht : U ≤ |t|) : |t|^2 ≤ Real.rpow U (2-q) * Real.rpow |t| q := by
    have ht0 := hU.trans_le ht
    have hr := Real.rpow_le_rpow_of_nonpos hU ht (by linarith : 2-q ≤ 0)
    calc
      _ = Real.rpow |t| (2-q) * Real.rpow |t| q := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add ht0]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg (abs_nonneg _) _)
  rw [abs_mul]
  by_cases hxy : |y| ≤ |x|
  · calc
      _ ≤ |x|^2 := by nlinarith [mul_le_mul_of_nonneg_left hxy (abs_nonneg x)]
      _ ≤ Real.rpow U (2-q)*Real.rpow |x| q := hs x hx.le
      _ ≤ _ := by
        have := Real.rpow_nonneg (abs_nonneg y) q
        have := Real.rpow_nonneg hU.le (2-q)
        simp only [Real.rpow_eq_pow] at *
        nlinarith
  · have hy : U ≤ |y| := hx.le.trans (le_of_not_ge hxy)
    calc
      _ ≤ |y|^2 := by nlinarith [mul_le_mul_of_nonneg_right (le_of_not_ge hxy) (abs_nonneg y)]
      _ ≤ Real.rpow U (2-q)*Real.rpow |y| q := hs y hy
      _ ≤ _ := by
        have := Real.rpow_nonneg (abs_nonneg x) q
        have := Real.rpow_nonneg hU.le (2-q)
        simp only [Real.rpow_eq_pow] at *
        nlinarith

lemma t4_tail_mean_pointwise (U q x : ℝ) (hU : 0 < U) (hq : 1 ≤ q) :
    |x-t4_trunc U x| ≤ Real.rpow U (1-q)*Real.rpow |x| q := by
  simp only [Real.rpow_eq_pow] at *
  by_cases hx : |x| ≤ U
  · simp [t4_trunc, hx]
    positivity
  · have hxU : U ≤ |x| := (lt_of_not_ge hx).le
    have hx0 := hU.trans_le hxU
    have hr := Real.rpow_le_rpow_of_nonpos hU hxU (by linarith : 1-q ≤ 0)
    calc
      _ = |x| := by simp [t4_trunc, hx]
      _ = Real.rpow |x| (1-q)*Real.rpow |x| q := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add hx0]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg (abs_nonneg _) _)

/-- The two tail contributions to a truncated covariance. -/
lemma t4_trunc_covariance_error {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (F G : Ω → ℝ) (k q U : ℝ) (hk : 0 < k) (hq : 2 ≤ q) (hU : 0 < U)
    (hF : mean P (fun ω => Real.rpow |F ω| q) ≤ Real.rpow k q)
    (hG : mean P (fun ω => Real.rpow |G ω| q) ≤ Real.rpow k q) :
    |cov P F G - cov P (fun ω => t4_trunc U (F ω)) (fun ω => t4_trunc U (G ω))| ≤
      4 * Real.rpow U (2-q) * Real.rpow k q +
        2 * k * Real.rpow U (1-q) * Real.rpow k q := by
  simp only [Real.rpow_eq_pow] at *
  let T := fun ω => t4_trunc U (F ω)
  let V := fun ω => t4_trunc U (G ω)
  have hmean (H : Ω → ℝ) (hH : mean P (fun ω => Real.rpow |H ω| q) ≤ Real.rpow k q) :
      |mean P H| ≤ k := (mean_abs_le P H).trans
        (mean_abs_of_moment P H k q hk (by linarith) hH)
  have htail (H : Ω → ℝ) (hH : mean P (fun ω => Real.rpow |H ω| q) ≤ Real.rpow k q) :
      |mean P (fun ω => H ω-t4_trunc U (H ω))| ≤ Real.rpow U (1-q)*Real.rpow k q := by
    calc
      _ ≤ mean P (fun ω => |H ω-t4_trunc U (H ω)|) := mean_abs_le P _
      _ ≤ mean P (fun ω => Real.rpow U (1-q)*Real.rpow |H ω| q) :=
        t4_mean_mono P fun ω => t4_tail_mean_pointwise U q (H ω) hU (by linarith)
      _ = Real.rpow U (1-q)*mean P (fun ω => Real.rpow |H ω| q) := mean_const_mul P _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hU.le _)
  have hprod (H J : Ω → ℝ)
      (hH : mean P (fun ω => Real.rpow |H ω| q) ≤ Real.rpow k q)
      (hJ : mean P (fun ω => Real.rpow |J ω| q) ≤ Real.rpow k q) :
      mean P (fun ω => |(H ω-t4_trunc U (H ω))*J ω|) ≤
        2 * Real.rpow U (2-q)*Real.rpow k q := by
    calc
      _ ≤ mean P (fun ω => Real.rpow U (2-q)*(Real.rpow |H ω| q + Real.rpow |J ω| q)) := by
        apply t4_mean_mono
        intro ω
        by_cases hω : |H ω| ≤ U
        · simp [t4_trunc, hω]
          positivity
        · simpa only [t4_trunc, hω, ite_false, sub_zero] using
            t4_tail_product U q (H ω) (J ω) hU hq (lt_of_not_ge hω)
      _ = Real.rpow U (2-q)*(mean P (fun ω => Real.rpow |H ω| q) +
          mean P (fun ω => Real.rpow |J ω| q)) := by rw [mean_const_mul, mean_add]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (add_le_add hH hJ)
          (Real.rpow_nonneg hU.le (2-q))
        simp only [Real.rpow_eq_pow] at *
        nlinarith only [hh]
  have hT : |mean P T| ≤ k := by
    calc
      _ ≤ mean P (fun ω => |T ω|) := mean_abs_le P _
      _ ≤ mean P (fun ω => |F ω|) := t4_mean_mono P fun ω => t4_trunc_abs_self U (F ω)
      _ ≤ k := mean_abs_of_moment P F k q hk (by linarith) hF
  have h1 : |mean P (fun ω => (F ω-T ω)*G ω)| ≤ 2*Real.rpow U (2-q)*Real.rpow k q :=
    (mean_abs_le P _).trans (hprod F G hF hG)
  have h2 : |mean P (fun ω => T ω*(G ω-V ω))| ≤ 2*Real.rpow U (2-q)*Real.rpow k q := by
    apply (mean_abs_le P _).trans
    apply le_trans _ (hprod G F hG hF)
    apply t4_mean_mono
    intro ω
    rw [abs_mul, abs_mul]
    exact (mul_le_mul_of_nonneg_right (t4_trunc_abs_self U (F ω)) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have h3 : |mean P (fun ω => F ω-T ω) * mean P G| ≤ k*Real.rpow U (1-q)*Real.rpow k q := by
    rw [abs_mul]
    have h := mul_le_mul (htail F hF) (hmean G hG) (abs_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hU.le _) (Real.rpow_nonneg hk.le _))
    nlinarith only [h]
  have h4 : |mean P T * mean P (fun ω => G ω-V ω)| ≤ k*Real.rpow U (1-q)*Real.rpow k q := by
    rw [abs_mul]
    have h := mul_le_mul hT (htail G hG) (abs_nonneg _) hk.le
    nlinarith only [h]
  have he : cov P F G - cov P T V =
      (mean P (fun ω => (F ω-T ω)*G ω) + mean P (fun ω => T ω*(G ω-V ω))) -
        (mean P (fun ω => F ω-T ω)*mean P G + mean P T*mean P (fun ω => G ω-V ω)) := by
    simp only [covariance_product_formula, mean_sub]
    rw [← mean_add]
    have hh : (fun ω => (F ω-T ω)*G ω+T ω*(G ω-V ω)) =
        (fun ω => F ω*G ω-T ω*V ω) := by funext ω; ring
    rw [hh, mean_sub]
    ring
  change |cov P F G-cov P T V| ≤ _
  rw [he]
  calc
    _ ≤ (|mean P (fun ω => (F ω-T ω)*G ω)| + |mean P (fun ω => T ω*(G ω-V ω))|) +
        (|mean P (fun ω => F ω-T ω)*mean P G|+|mean P T*mean P (fun ω => G ω-V ω)|) :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ _ := by
      simp only [Real.rpow_eq_pow] at *
      linarith


/-- Optimizing the truncation level gives the target's constant 10. -/
lemma t4_truncation_choice (k q a : ℝ) (hk : 0 < k) (hq : 2 < q)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    4*(k*Real.rpow a (-1/q))*(k*Real.rpow a (-1/q))*a +
      (4*Real.rpow (k*Real.rpow a (-1/q)) (2-q)*Real.rpow k q +
        2*k*Real.rpow (k*Real.rpow a (-1/q)) (1-q)*Real.rpow k q) ≤
          10*k^2*Real.rpow a ((q-2)/q) := by
  simp only [Real.rpow_eq_pow]
  have hq0 : q ≠ 0 := by linarith
  have h1 : (a ^ (-1/q))^2*a = a^((q-2)/q) := by
    rw [← Real.rpow_natCast (a ^ (-1/q)) 2, ← Real.rpow_mul ha.le]
    conv_lhs => rhs; rw [← Real.rpow_one a]
    rw [← Real.rpow_add ha]
    congr 1
    field_simp
    <;> ring
  have h2 : (k*a^(-1/q))^(2-q)*k^q = k^2*a^((q-2)/q) := by
    rw [Real.mul_rpow hk.le (Real.rpow_nonneg ha.le _), ← Real.rpow_mul ha.le]
    calc
      _ = (k^(2-q)*k^q)*a^((-1/q)*(2-q)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hk, show 2-q+q = (2:ℝ) by ring]
        have hex : (-1/q)*(2-q) = (q-2)/q := by field_simp; ring
        rw [hex, Real.rpow_two]
  have h3 : k*(k*a^(-1/q))^(1-q)*k^q = k^2*a^((q-1)/q) := by
    rw [Real.mul_rpow hk.le (Real.rpow_nonneg ha.le _), ← Real.rpow_mul ha.le]
    calc
      _ = k*(k^(1-q)*k^q)*a^((-1/q)*(1-q)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hk, show 1-q+q = (1:ℝ) by ring, Real.rpow_one]
        have hex : (-1/q)*(1-q) = (q-1)/q := by field_simp; ring
        rw [hex]
        ring
  have he : a^((q-1)/q) ≤ a^((q-2)/q) :=
    Real.rpow_le_rpow_of_exponent_ge ha ha1 (by
      apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ q)
      linarith)
  calc
    _ = 4*k^2*((a^(-1/q))^2*a) + 4*((k*a^(-1/q))^(2-q)*k^q) +
        2*(k*(k*a^(-1/q))^(1-q)*k^q) := by ring
    _ = 4*k^2*a^((q-2)/q)+4*(k^2*a^((q-2)/q))+2*(k^2*a^((q-1)/q)) := by rw [h1, h2, h3]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg k)]

/-- Finite-law covariance mixing bound proved directly, with no standard-input premise. -/
lemma t4_covariance_mixing {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) (f : A → ℝ) (g : B → ℝ)
    (k q : ℝ) (hk : 0 < k) (hq : 2 < q)
    (hf : mean P (fun ω => Real.rpow |f (X ω)| q) ≤ Real.rpow k q)
    (hg : mean P (fun ω => Real.rpow |g (Y ω)| q) ≤ Real.rpow k q) :
    |cov P (fun ω => f (X ω)) (fun ω => g (Y ω))| ≤
      10*k^2*mixPower (alpha P X Y) ((q-2)/q) := by
  by_cases ha : alpha P X Y = 0
  · rw [t4_covariance_zero P X Y f g ha]
    simp [mixPower, ha]
  have ha0 : 0 < alpha P X Y := (alpha_nonnegative P X Y).lt_of_ne' ha
  let U := k*Real.rpow (alpha P X Y) (-1/q)
  have hU : 0 < U := mul_pos hk (Real.rpow_pos_of_pos ha0 _)
  have hb := t4_bounded_covariance P X Y (fun x => t4_trunc U (f x))
    (fun y => t4_trunc U (g y)) U U hU.le hU.le
    (fun x => t4_trunc_abs U (f x) hU.le) (fun y => t4_trunc_abs U (g y) hU.le)
  have ht := t4_trunc_covariance_error P (fun ω => f (X ω)) (fun ω => g (Y ω))
    k q U hk hq.le hU hf hg
  have hc : |cov P (fun ω => f (X ω)) (fun ω => g (Y ω))| ≤
      4*U*U*alpha P X Y + (4*Real.rpow U (2-q)*Real.rpow k q+
        2*k*Real.rpow U (1-q)*Real.rpow k q) := by
    calc
      _ ≤ |cov P (fun ω => t4_trunc U (f (X ω))) (fun ω => t4_trunc U (g (Y ω)))| +
          |cov P (fun ω => f (X ω)) (fun ω => g (Y ω)) -
            cov P (fun ω => t4_trunc U (f (X ω))) (fun ω => t4_trunc U (g (Y ω)))| := by
        have h := abs_add_le
          (cov P (fun ω => f (X ω)) (fun ω => g (Y ω)) -
            cov P (fun ω => t4_trunc U (f (X ω))) (fun ω => t4_trunc U (g (Y ω))))
          (cov P (fun ω => t4_trunc U (f (X ω))) (fun ω => t4_trunc U (g (Y ω))))
        rw [sub_add_cancel] at h
        linarith only [h]
      _ ≤ _ := add_le_add hb ht
  exact hc.trans (by simpa only [U, mixPower, ha, ite_false] using
    t4_truncation_choice k q (alpha P X Y) hk hq ha0 (alpha_le_one P X Y))

/-- Every arm variable factors through its incoming-coordinate mask. -/
lemma t4_arm_mask {n : ℕ} (E : Experiment n) (b : Bool) (a : ℕ) (i : Fin n)
    (z : Assignment n) : armVariable E b a i (masked E i z) = armVariable E b a i z := by
  apply arm_dependsOn E i b a
  intro j hj
  simp only [masked, show Interferes E j i from hj, ite_true]

lemma t4_arm_moment {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (i : Fin n) (b : Bool) :
    mean E.design (fun z => Real.rpow |armVariable E b 1 i z| q) ≤ Real.rpow k q := by
  apply le_trans _ (hr.2.2.2.2.1 i)
  apply t4_mean_mono
  intro z
  apply Real.rpow_le_rpow (abs_nonneg _) _ (by linarith [hr.2.1])
  by_cases hz : z i = b <;> simp [armVariable, hz]

/-- The mixing covariance inequality also covers the q = 2 convention. -/
lemma t4_arm_mixing {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (b : Bool) (i j : Fin n) :
    |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
      10*k^2*mixPower (alpha E.design (masked E i) (masked E j)) ((q-2)/q) := by
  have he (l : Fin n) : (fun z => armVariable E b 1 l (masked E l z)) = armVariable E b 1 l := by
    funext z
    exact t4_arm_mask E b 1 l z
  by_cases ha : alpha E.design (masked E i) (masked E j) = 0
  · have hz := t4_covariance_zero E.design (masked E i) (masked E j)
      (armVariable E b 1 i) (armVariable E b 1 j) ha
    rw [he i, he j] at hz
    simp [hz, mixPower, ha]
  by_cases hq : q = 2
  · have hc := (corrected_moment_covariance E k q hr.1 hr.2.1 hr.2.2.2.2.1
      1 (by simpa using hr.2.1) i j b).2.2.2.2.2.2
    simp only [hq, sub_self, zero_div, mixPower, ha, ite_false, Real.rpow_zero]
    norm_num at hc ⊢
    nlinarith [sq_nonneg k]
  · have hq2 : 2 < q := lt_of_le_of_ne hr.2.1 (Ne.symm hq)
    have hh := t4_covariance_mixing E.design (masked E i) (masked E j)
      (armVariable E b 1 i) (armVariable E b 1 j) k q hr.1 hq2
      (by simpa only [t4_arm_mask] using t4_arm_moment E k q s hr i b)
      (by simpa only [t4_arm_mask] using t4_arm_moment E k q s hr j b)
    simpa only [he] using hh

/-- Weighted means and positive marginal bounds give the first chain. -/
lemma t4_arm_weighted {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (b : Bool) :
    var E.design (muHat E b) ≤ k^2/(n:ℝ)^2 *
      (∑ i, ∑ j, |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)|) := by
  have he : muHat E b = fun z => (∑ i, (marginal E i b)⁻¹*armVariable E b 1 i z)/(n:ℝ) := by
    funext z
    simp only [muHat, armVariable, pow_one, div_eq_mul_inv]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, variance_div]
  have hw := weighted_variance_absolute E.design (armVariable E b 1)
    (fun i => (marginal E i b)⁻¹) k (fun i =>
      ⟨inv_pos.mpr (regular_marginal_bounds E k q s hr i b).2.2.1,
        (regular_marginal_bounds E k q s hr i b).2.2.2⟩)
  exact (div_le_div_of_nonneg_right hw.2 (sq_nonneg _)).trans_eq (by ring)

lemma t4_covariance_cancellation {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (b : Bool) (a : ℕ) :
    (∑ i, ∑ j, |cov E.design (armVariable E b a i) (armVariable E b a j)|) =
      ∑ i, ∑ j, d E i j * |cov E.design (armVariable E b a i) (armVariable E b a j)| := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : Dependent E i j
  · simp [d, hij]
  · simp [d, hij, covariance_nonedge E hBER i j hij b a]

/-- The arbitrary-design outcome chain, including all diagonal contributions. -/
lemma t4_arbitrary_arm_variance {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (b : Bool) :
    var E.design (muHat E b) ≤ k^4/(n:ℝ)*dAvg E +
      10*k^4/(n:ℝ)*alphaExt E ((q-2)/q) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hc (i j : Fin n) : |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
      d E i j*k^2+(1-d E i j)*(10*k^2*mixPower
        (alpha E.design (masked E i) (masked E j)) ((q-2)/q)) := by
    by_cases hij : Dependent E i j
    · simpa only [d, hij, ite_true, one_mul, sub_self, zero_mul, add_zero,
        show 2*1=2 by norm_num] using
        (corrected_moment_covariance E k q hr.1 hr.2.1 hr.2.2.2.2.1
          1 (by simpa using hr.2.1) i j b).2.2.2.2.2.2
    · simpa only [d, hij, ite_false, zero_mul, sub_zero, one_mul, zero_add] using
        t4_arm_mixing E k q s hr b i j
  calc
    _ ≤ k^2/(n:ℝ)^2*(∑ i, ∑ j, |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)|) :=
      t4_arm_weighted E k q s hr b
    _ ≤ k^2/(n:ℝ)^2*(∑ i, ∑ j, (d E i j*k^2+(1-d E i j)*(10*k^2*mixPower
        (alpha E.design (masked E i) (masked E j)) ((q-2)/q)))) := by
      gcongr with i j
      exact hc i j
    _ = _ := by
      have he (i j : Fin n) : d E i j*k^2+(1-d E i j)*(10*k^2*mixPower
          (alpha E.design (masked E i) (masked E j)) ((q-2)/q)) =
            k^2*d E i j+10*k^2*((1-d E i j)*mixPower
              (alpha E.design (masked E i) (masked E j)) ((q-2)/q)) := by ring
      simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [alphaExt, dAvg, degree]
      field_simp
      <;> ring

lemma t4_indicator_alpha {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) (S : Set A) (T : Set B) :
    |cov P (fun ω => if X ω ∈ S then 1 else 0) (fun ω => if Y ω ∈ T then 1 else 0)| ≤
      alpha P X Y := by
  rw [covariance_product_formula]
  have he : mean P (fun ω => (if X ω ∈ S then 1 else 0)*(if Y ω ∈ T then 1 else 0)) =
      prob P (fun ω => X ω ∈ S ∧ Y ω ∈ T) := by
    unfold prob
    congr 1
    funext ω
    by_cases hx : X ω ∈ S <;> by_cases hy : Y ω ∈ T <;> simp [hx, hy]
  rw [he]
  exact event_abs_le_alpha P X Y S T

lemma t4_alpha_le_power (a θ : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : θ ≤ 1) :
    a ≤ mixPower a θ := by
  by_cases ha0 : a = 0
  · simp [mixPower, ha0]
  · have haP : 0 < a := ha.lt_of_ne' ha0
    simp only [mixPower, ha0, ite_false, Real.rpow_eq_pow]
    calc
      _ = a^(1:ℝ) := (Real.rpow_one a).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge haP ha1 hθ

/-- Masked-coordinate events give a count covariance bound with constant one. -/
lemma t4_count_covariance {n : ℕ} (E : Experiment n) (b : Bool) (i j : Fin n) :
    |cov E.design (fun z => if z i = b then 1 else 0) (fun z => if z j = b then 1 else 0)| ≤
      alpha E.design (masked E i) (masked E j) := by
  have he (l : Fin n) : (fun z => if (masked E l z) l = b then (1:ℝ) else 0) =
      (fun z => if z l = b then 1 else 0) := by
    funext z
    simp [masked, show Interferes E l l from Or.inl rfl]
  simpa only [Set.mem_setOf_eq, he] using
    t4_indicator_alpha E.design (masked E i) (masked E j) {z | z i = b} {z | z j = b}

lemma t4_count_weighted {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (b : Bool) :
    var E.design (fun z => nHat E b z / n) ≤ k^2/(n:ℝ)^2 *
      (∑ i, ∑ j, |cov E.design
        (fun z => if z i = b then 1 else 0) (fun z => if z j = b then 1 else 0)|) := by
  have he : (fun z => nHat E b z / n) = fun z =>
      (∑ i, (marginal E i b)⁻¹*(if z i = b then (1:ℝ) else 0))/(n:ℝ) := by
    funext z
    simp only [nHat, div_eq_mul_inv]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, variance_div]
  have hw := weighted_variance_absolute E.design (fun i z => if z i = b then (1:ℝ) else 0)
    (fun i => (marginal E i b)⁻¹) k (fun i =>
      ⟨inv_pos.mpr (regular_marginal_bounds E k q s hr i b).2.2.1,
        (regular_marginal_bounds E k q s hr i b).2.2.2⟩)
  exact (div_le_div_of_nonneg_right hw.2 (sq_nonneg _)).trans_eq (by ring)

lemma t4_arbitrary_count_variance {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hr : Regular E k q s) (b : Bool) :
    var E.design (fun z => nHat E b z / n) ≤
      k^2/(n:ℝ)*dAvg E + k^2/(n:ℝ)*alphaExt E ((q-2)/q) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hqP : 0 < q := by linarith [hr.2.1]
  have hθ : (q-2)/q ≤ 1 := (div_le_one hqP).mpr (by linarith)
  have hc (i j : Fin n) :
      |cov E.design (fun z => if z i = b then 1 else 0) (fun z => if z j = b then 1 else 0)| ≤
        d E i j+(1-d E i j)*mixPower (alpha E.design (masked E i) (masked E j)) ((q-2)/q) := by
    by_cases hij : Dependent E i j
    · simpa only [d, hij, ite_true, sub_self, zero_mul, add_zero] using
        (t4_count_covariance E b i j).trans (alpha_le_one E.design (masked E i) (masked E j))
    · simpa only [d, hij, ite_false, sub_zero, one_mul, zero_add] using
        (t4_count_covariance E b i j).trans (t4_alpha_le_power _ _
          (alpha_nonnegative E.design (masked E i) (masked E j))
          (alpha_le_one E.design (masked E i) (masked E j)) hθ)
  calc
    _ ≤ k^2/(n:ℝ)^2*(∑ i, ∑ j, |cov E.design
        (fun z => if z i = b then 1 else 0) (fun z => if z j = b then 1 else 0)|) :=
      t4_count_weighted E k q s hr b
    _ ≤ k^2/(n:ℝ)^2*(∑ i, ∑ j, (d E i j+(1-d E i j)*mixPower
        (alpha E.design (masked E i) (masked E j)) ((q-2)/q))) := by
      gcongr with i j
      exact hc i j
    _ = _ := by
      simp only [alphaExt, dAvg, degree, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_mul]
      field_simp
      <;> ring

/-- Positive squared marginal weights give the square-arm absolute-covariance chain. -/
lemma t4_square_weighted {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (b : Bool) :
    var E.design (fun z => ∑ i, armVariable E b 2 i z / marginal E i b ^ 2) ≤
      k^4*(∑ i, ∑ j, |cov E.design (armVariable E b 2 i) (armVariable E b 2 j)|) := by
  have hw (i : Fin n) : 0 < (marginal E i b)⁻¹^2 ∧ (marginal E i b)⁻¹^2 ≤ k^2 := by
    have hh := regular_marginal_bounds E k q s hr i b
    exact ⟨sq_pos_of_pos (inv_pos.mpr hh.2.2.1),
      pow_le_pow_left₀ (inv_nonneg.mpr hh.2.2.1.le) hh.2.2.2 2⟩
  have he : (fun z => ∑ i, armVariable E b 2 i z / marginal E i b ^ 2) =
      (fun z => ∑ i, (marginal E i b)⁻¹^2*armVariable E b 2 i z) := by
    funext z
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_eq_mul_inv, inv_pow, mul_comm]
  rw [he]
  convert (weighted_variance_absolute E.design _ _ _ hw).2 using 1 <;> ring

lemma t4_square_variance {n : ℕ} (hn : 0 < n) (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (hq : 4 ≤ q) (hBER : Bernoulli E) (b : Bool) :
    var E.design (fun z => ∑ i, armVariable E b 2 i z / marginal E i b ^ 2) ≤
      k^8*(n:ℝ)*dAvg E := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hc (i j : Fin n) : |cov E.design (armVariable E b 2 i) (armVariable E b 2 j)| ≤
      d E i j*k^4 := by
    by_cases hij : Dependent E i j
    · simpa only [d, hij, ite_true, one_mul, show 2*2=4 by norm_num] using
        (corrected_moment_covariance E k q hr.1 hr.2.1 hr.2.2.2.2.1
          2 (by norm_num; exact hq) i j b).2.2.2.2.2.2
    · simp only [covariance_nonedge E hBER i j hij b 2, abs_zero, d, hij,
        ite_false, zero_mul, le_refl]
  calc
    _ ≤ k^4*(∑ i, ∑ j, |cov E.design (armVariable E b 2 i) (armVariable E b 2 j)|) :=
      t4_square_weighted E k q s hr b
    _ ≤ k^4*(∑ i, ∑ j, d E i j*k^4) := by
      gcongr with i j
      exact hc i j
    _ = _ := by
      simp only [dAvg, degree, ← Finset.sum_mul]
      field_simp
      <;> ring

/-- Bernoulli fourth-moment variance concentration, independently of mixing inequalities. -/
theorem t4_vber_variance {n : ℕ} (hn : 0 < n) (E : Experiment n) (k q s : ℝ)
    (hr : Regular E k q s) (hq : 4 ≤ q) (hBER : Bernoulli E) :
    var E.design (fun z => (n:ℝ)*vBER E z) ≤ 4*k^8*dAvg E/(n:ℝ) := by
  let T := fun b : Bool => fun z : Assignment n =>
    (∑ i, armVariable E b 2 i z/marginal E i b^2)/(n:ℝ)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (fun z => (n:ℝ)*vBER E z) = fun z => T true z-(-T false z) := by
    funext z
    let R := fun i =>
      (if z i then E.outcome i z^2 else 0)/marginal E i true^2 +
      (if z i then 0 else E.outcome i z^2)/marginal E i false^2
    calc
      _ = (∑ i, R i)/(n:ℝ) := by
        change (n:ℝ)*((∑ i, R i)/(n:ℝ)^2) = _
        field_simp [hn0]
        <;> ring
      _ = T true z+T false z := by
        dsimp [T]
        rw [← add_div, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        dsimp [R]
        cases hzi : z i <;> simp [armVariable, hzi]
      _ = _ := by ring
  have hneg : var E.design (fun z => -T false z) = var E.design (T false) := by
    simp only [variance_second_moment]
    have hm : mean E.design (fun z => -T false z) = -mean E.design (T false) := by
      simpa using mean_const_mul E.design (-1) (T false)
    simp only [neg_sq, hm]
  have hb (b : Bool) : var E.design (T b) ≤ k^8*dAvg E/(n:ℝ) := by
    dsimp [T]
    rw [variance_div]
    apply (div_le_div_of_nonneg_right (t4_square_variance hn E k q s hr hq hBER b) (sq_nonneg _)).trans_eq
    field_simp
  rw [he]
  have hv := variance_sub_le E.design (T true) (fun z => -T false z)
  rw [hneg] at hv
  calc
    _ ≤ 2 * (var E.design (T true) + var E.design (T false)) := hv
    _ ≤ 2 * (k^8*dAvg E/(n:ℝ) + k^8*dAvg E/(n:ℝ)) := by linarith [hb true, hb false]
    _ = _ := by ring

/-- T4: variance bounds for weighted outcomes, treatment counts, and squared outcomes. -/
theorem corrected_variance_chains_proof {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hReg : Regular E k q s) :
    (∀ b, var E.design (muHat E b) ≤ k^2/(n:ℝ)^2 *
      (∑ i, ∑ j, |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)|)) ∧
    (Bernoulli E → ∀ b,
      (∑ i, ∑ j, |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)|) =
        ∑ i, ∑ j, d E i j * |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ∧
      var E.design (muHat E b) ≤ k^4/(n:ℝ) * dAvg E) ∧
    (∀ b, var E.design (muHat E b) ≤ k^4/(n:ℝ)*dAvg E +
      10*k^4/(n:ℝ)*alphaExt E ((q-2)/q)) ∧
    (∀ b, var E.design (fun z => nHat E b z / n) ≤ k^2/(n:ℝ)^2 *
      (∑ i, ∑ j, |cov E.design
        (fun z => if z i = b then 1 else 0) (fun z => if z j = b then 1 else 0)|) ∧
      var E.design (fun z => nHat E b z / n) ≤
        k^2/(n:ℝ)*dAvg E + k^2/(n:ℝ)*alphaExt E ((q-2)/q)) ∧
    (4 ≤ q → Bernoulli E →
      (∀ b, var E.design (fun z => ∑ i, armVariable E b 2 i z / marginal E i b ^ 2) ≤
        k^4 * (∑ i, ∑ j, |cov E.design (armVariable E b 2 i) (armVariable E b 2 j)|) ∧
        (∑ i, ∑ j, |cov E.design (armVariable E b 2 i) (armVariable E b 2 j)|) =
          ∑ i, ∑ j, d E i j * |cov E.design (armVariable E b 2 i) (armVariable E b 2 j)| ∧
        var E.design (fun z => ∑ i, armVariable E b 2 i z / marginal E i b ^ 2) ≤
          k^8*(n:ℝ)*dAvg E) ∧
      var E.design (fun z => (n:ℝ)*vBER E z) ≤ 4*k^8*dAvg E/(n:ℝ)) := by
  refine ⟨t4_arm_weighted E k q s hReg, ?_, t4_arbitrary_arm_variance hn E k q s hReg,
    ?_, ?_⟩
  · intro hBER b
    refine ⟨t4_covariance_cancellation E hBER b 1, ?_⟩
    simpa only [div_mul_eq_mul_div] using arm_variance_bound hn E k q s hReg hBER b
  · intro b
    exact ⟨t4_count_weighted E k q s hReg b, t4_arbitrary_count_variance hn E k q s hReg b⟩
  · intro hq hBER
    exact ⟨fun b => ⟨t4_square_weighted E k q s hReg b,
      t4_covariance_cancellation E hBER b 2, t4_square_variance hn E k q s hReg hq hBER b⟩,
      t4_vber_variance hn E k q s hReg hq hBER⟩

end
end AronowAudit.P009.Wave1
