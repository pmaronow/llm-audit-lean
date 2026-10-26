import AronowAudit.P009.Wave1.Gap.GLP0092B1

namespace AronowAudit.P009.Wave1

open scoped BigOperators
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

open BernoulliCompletion MixingBasics

/-- A finite signed measure tested against bounded functions. -/
theorem t46A_signed_sum {A : Type*} [Fintype A] (v f : A → ℝ) (C K : ℝ)
    (hC : 0 ≤ C) (hf : ∀ a, |f a| ≤ C)
    (hK : ∀ S : Set A, |∑ a, if a ∈ S then v a else 0| ≤ K) :
    |∑ a, v a * f a| ≤ 2 * C * K := by
  have hp := hK {a | 0 ≤ v a}
  have hn := hK {a | ¬ 0 ≤ v a}
  have he : (∑ a, |v a|) =
      (∑ a, if 0 ≤ v a then v a else 0) -
        ∑ a, if ¬ 0 ≤ v a then v a else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : 0 ≤ v a <;> simp [ha, abs_of_nonneg, abs_of_neg (lt_of_not_ge ha)]
  have hv : (∑ a, |v a|) ≤ 2*K := by
    rw [he]
    simp only [Set.mem_setOf_eq] at hp hn
    linarith [(abs_le.mp hp).2, (abs_le.mp hn).1]
  calc
    _ ≤ ∑ a, |v a * f a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |v a| * C := Finset.sum_le_sum (fun a _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf a) (abs_nonneg _))
    _ = C * ∑ a, |v a| := by rw [Finset.mul_sum]; simp only [mul_comm]
    _ ≤ C * (2*K) := mul_le_mul_of_nonneg_left hv hC
    _ = _ := by ring

theorem t46A_mean_product_fibers {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (U : Ω → A) (H : Ω → ℝ) (f : A → ℝ) :
    mean P (fun ω => f (U ω) * H ω) =
      ∑ a, mean P (fun ω => if U ω = a then H ω else 0) * f a := by
  have h := t45_sum_fibers U (fun ω => P.mass ω * H ω) f
  convert h using 1
  · unfold mean
    apply Finset.sum_congr rfl
    intro ω _
    ring
  · apply Finset.sum_congr rfl
    intro a _
    congr 1
    unfold mean
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : U ω = a <;> simp [hω]

theorem t46A_covariance_fibers {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (U : Ω → A) (H : Ω → ℝ) (f : A → ℝ) :
    cov P (fun ω => f (U ω)) H =
      ∑ a, (mean P (fun ω => if U ω = a then H ω else 0) -
        prob P (fun ω => U ω = a) * mean P H) * f a := by
  rw [covariance_product_formula, t46A_mean_product_fibers, t45_mean_fibers]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem t46A_peel {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (U : Ω → A) (H : Ω → ℝ) (f : A → ℝ) (C K : ℝ)
    (hC : 0 ≤ C) (hf : ∀ a, |f a| ≤ C)
    (hK : ∀ S : Set A, |cov P (fun ω => if U ω ∈ S then 1 else 0) H| ≤ K) :
    |cov P (fun ω => f (U ω)) H| ≤ 2*C*K := by
  rw [t46A_covariance_fibers]
  apply t46A_signed_sum _ f C K hC hf
  intro S
  have hh := hK S
  rw [t46A_covariance_fibers P U H (fun a => if a ∈ S then 1 else 0)] at hh
  simpa only [mul_ite, mul_one, mul_zero] using hh

theorem t46A_cov_symm {Ω : Type*} [Fintype Ω] (P : Law Ω) (f g : Ω → ℝ) :
    cov P f g = cov P g f := by
  unfold cov
  congr 1
  funext ω
  ring

theorem t46A_indicator_covariance {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (U : Ω → A) (V : Ω → B) (S : Set A) (T : Set B) :
    |cov P (fun ω => if U ω ∈ S then 1 else 0)
      (fun ω => if V ω ∈ T then 1 else 0)| ≤ alpha P U V := by
  rw [covariance_product_formula]
  have he : (fun ω => (if U ω ∈ S then (1:ℝ) else 0) *
      (if V ω ∈ T then (1:ℝ) else 0)) =
      (fun ω => if U ω ∈ S ∧ V ω ∈ T then 1 else 0) := by
    funext ω
    by_cases hU : U ω ∈ S <;> by_cases hV : V ω ∈ T <;> simp [hU, hV]
  rw [he]
  convert event_abs_le_alpha P U V S T using 1 <;> congr!
  unfold prob
  congr 1
  funext ω
  by_cases hU : U ω ∈ S <;> by_cases hV : V ω ∈ T <;> simp [hU, hV]

/-- The finite Billingsley inequality, obtained by peeling the two fibers. -/
theorem t46A_bounded_covariance {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (P : Law Ω) (U : Ω → A) (V : Ω → B) (f : A → ℝ) (g : B → ℝ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ a, |f a| ≤ C) (hg : ∀ b, |g b| ≤ D) :
    |cov P (fun ω => f (U ω)) (fun ω => g (V ω))| ≤
      4 * alpha P U V * C * D := by
  have h1 (T : Set B) :
      |cov P (fun ω => f (U ω)) (fun ω => if V ω ∈ T then 1 else 0)| ≤
        2*C*alpha P U V :=
    t46A_peel P U _ f C _ hC hf (fun S => t46A_indicator_covariance P U V S T)
  rw [t46A_cov_symm]
  have h2 := t46A_peel P V (fun ω => f (U ω)) g D (2*C*alpha P U V) hD hg
    (fun T => by rw [t46A_cov_symm]; exact h1 T)
  calc
    _ ≤ 2*D*(2*C*alpha P U V) := h2
    _ = _ := by ring

/-- Truncation at a common absolute cutoff. -/
def t46A_truncate (L x : ℝ) : ℝ := if |x| ≤ L then x else 0

theorem t46A_truncate_bound (L x : ℝ) (hL : 0 ≤ L) : |t46A_truncate L x| ≤ L := by
  unfold t46A_truncate
  split_ifs with h <;> simp [h, hL]

/-- On the union of the two tails, the product is bounded by the q-moments. -/
theorem t46A_product_tail (L q x y : ℝ) (hL : 0 < L) (hq : 2 ≤ q) :
    |x*y - t46A_truncate L x * t46A_truncate L y| ≤
      L ^ (2-q) * (|x| ^ q + |y| ^ q) := by
  have hq0 : 0 ≤ q := by linarith
  by_cases hx : |x| ≤ L
  · by_cases hy : |y| ≤ L
    · simp only [t46A_truncate, hx, hy, if_true, sub_self, abs_zero]
      positivity
    · have hm : L ≤ max |x| |y| := (le_of_not_ge hy).trans (le_max_right _ _)
      have hm0 : 0 < max |x| |y| := hL.trans_le hm
      have hprod : |x*y| ≤ (max |x| |y|)^2 := by
        rw [abs_mul, pow_two]
        exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (abs_nonneg _) hm0.le
      have hpow : (max |x| |y|)^q ≤ |x|^q+|y|^q := by
        rcases le_total |x| |y| with h | h
        · rw [max_eq_right h]; exact le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)
        · rw [max_eq_left h]; exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
      have he : (max |x| |y|)^2 = (max |x| |y|)^(2-q) * (max |x| |y|)^q := by
        rw [← Real.rpow_add hm0]
        norm_num
      simp only [t46A_truncate, hx, hy, if_true, if_false, mul_zero, sub_zero]
      calc
        _ ≤ (max |x| |y|)^2 := hprod
        _ = _ := he
        _ ≤ L^(2-q) * (|x|^q+|y|^q) :=
          mul_le_mul (Real.rpow_le_rpow_of_nonpos hL hm (by linarith)) hpow
            (Real.rpow_nonneg hm0.le _) (Real.rpow_nonneg hL.le _)
  · have hm : L ≤ max |x| |y| := (le_of_not_ge hx).trans (le_max_left _ _)
    have hm0 : 0 < max |x| |y| := hL.trans_le hm
    have hprod : |x*y| ≤ (max |x| |y|)^2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (abs_nonneg _) hm0.le
    have hpow : (max |x| |y|)^q ≤ |x|^q+|y|^q := by
      rcases le_total |x| |y| with h | h
      · rw [max_eq_right h]; exact le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _)
      · rw [max_eq_left h]; exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    have he : (max |x| |y|)^2 = (max |x| |y|)^(2-q) * (max |x| |y|)^q := by
      rw [← Real.rpow_add hm0]
      norm_num
    simp only [t46A_truncate, hx, if_false, zero_mul, sub_zero]
    calc
      _ ≤ (max |x| |y|)^2 := hprod
      _ = _ := he
      _ ≤ L^(2-q) * (|x|^q+|y|^q) :=
        mul_le_mul (Real.rpow_le_rpow_of_nonpos hL hm (by linarith)) hpow
          (Real.rpow_nonneg hm0.le _) (Real.rpow_nonneg hL.le _)

theorem t46A_mean_mono {Ω : Type*} [Fintype Ω] (P : Law Ω) (f g : Ω → ℝ)
    (h : ∀ ω, f ω ≤ g ω) : mean P f ≤ mean P g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω))

def t46A_productLaw {Ω : Type*} [Fintype Ω] (P : Law Ω) : Law (Ω × Ω) where
  mass ω := P.mass ω.1 * P.mass ω.2
  nonneg ω := mul_nonneg (P.nonneg _) (P.nonneg _)
  total := by simp only [Fintype.sum_prod_type, ← Finset.mul_sum, P.total, mul_one]

theorem t46A_product_mean {Ω : Type*} [Fintype Ω] (P : Law Ω) (f g : Ω → ℝ) :
    mean (t46A_productLaw P) (fun ω => f ω.1 * g ω.2) = mean P f * mean P g := by
  simp only [mean, t46A_productLaw, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem t46A_product_marginals {Ω : Type*} [Fintype Ω] (P : Law Ω) (f g : Ω → ℝ) :
    mean (t46A_productLaw P) (fun ω => f ω.1 + g ω.2) = mean P f + mean P g := by
  rw [mean_add]
  have h1 := t46A_product_mean P f (fun _ => 1)
  have h2 := t46A_product_mean P (fun _ => 1) g
  simp only [mul_one, one_mul, mean_const] at h1 h2
  rw [h1, h2]

theorem t46A_covariance_truncation {Ω : Type*} [Fintype Ω]
    (P : Law Ω) (f g : Ω → ℝ) (L q k : ℝ) (hL : 0 < L) (hq : 2 ≤ q)
    (hf : mean P (fun ω => |f ω|^q) ≤ k^q)
    (hg : mean P (fun ω => |g ω|^q) ≤ k^q) :
    |cov P f g - cov P (fun ω => t46A_truncate L (f ω))
      (fun ω => t46A_truncate L (g ω))| ≤ 4*k^q*L^(2-q) := by
  have h1 : |mean P (fun ω => f ω*g ω) -
      mean P (fun ω => t46A_truncate L (f ω)*t46A_truncate L (g ω))| ≤
      2*k^q*L^(2-q) := by
    rw [← mean_sub]
    calc
      _ ≤ mean P (fun ω => |f ω*g ω-t46A_truncate L (f ω)*t46A_truncate L (g ω)|) :=
        mean_abs_le P _
      _ ≤ mean P (fun ω => L^(2-q)*(|f ω|^q+|g ω|^q)) :=
        t46A_mean_mono P _ _ (fun ω => t46A_product_tail L q (f ω) (g ω) hL hq)
      _ = L^(2-q)*(mean P (fun ω => |f ω|^q)+mean P (fun ω => |g ω|^q)) := by
        rw [mean_const_mul, mean_add]
      _ ≤ L^(2-q)*(k^q+k^q) := mul_le_mul_of_nonneg_left (add_le_add hf hg)
        (Real.rpow_nonneg hL.le _)
      _ = _ := by ring
  have h2 : |mean P f * mean P g - mean P (fun ω => t46A_truncate L (f ω)) *
      mean P (fun ω => t46A_truncate L (g ω))| ≤ 2*k^q*L^(2-q) := by
    rw [← t46A_product_mean, ← t46A_product_mean, ← mean_sub]
    calc
      _ ≤ mean (t46A_productLaw P) (fun ω =>
          |f ω.1*g ω.2-t46A_truncate L (f ω.1)*t46A_truncate L (g ω.2)|) :=
        mean_abs_le _ _
      _ ≤ mean (t46A_productLaw P) (fun ω => L^(2-q)*(|f ω.1|^q+|g ω.2|^q)) :=
        t46A_mean_mono _ _ _ (fun ω => t46A_product_tail L q (f ω.1) (g ω.2) hL hq)
      _ = L^(2-q)*(mean P (fun ω => |f ω|^q)+mean P (fun ω => |g ω|^q)) := by
        rw [mean_const_mul, t46A_product_marginals P (fun ω => |f ω|^q) (fun ω => |g ω|^q)]
      _ ≤ L^(2-q)*(k^q+k^q) := mul_le_mul_of_nonneg_left (add_le_add hf hg)
        (Real.rpow_nonneg hL.le _)
      _ = _ := by ring
  rw [covariance_product_formula, covariance_product_formula]
  calc
    _ = |(mean P (fun ω => f ω*g ω)-mean P (fun ω =>
        t46A_truncate L (f ω)*t46A_truncate L (g ω))) -
        (mean P f*mean P g-mean P (fun ω => t46A_truncate L (f ω))*
          mean P (fun ω => t46A_truncate L (g ω)))| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ 2*k^q*L^(2-q)+2*k^q*L^(2-q) := add_le_add h1 h2
    _ = _ := by ring

theorem t46A_cutoff_choice (k q a : ℝ) (hk : 0 < k) (hq : 2 ≤ q) (ha : 0 < a) :
    4*a*(k*a^(-1/q))^2 + 4*k^q*(k*a^(-1/q))^(2-q) =
      8*k^2*a^((q-2)/q) := by
  have hq0 : q ≠ 0 := by linarith
  have h1 : a * (a^(-1/q))^2 = a^((q-2)/q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = a^(1:ℝ)*a^((-1/q)*2) := by rw [Real.rpow_one]
      _ = a^(1+(-1/q)*2) := (Real.rpow_add ha _ _).symm
      _ = _ := by congr 1; field_simp; ring
  have h2 : k^q*(k*a^(-1/q))^(2-q) = k^2*a^((q-2)/q) := by
    rw [Real.mul_rpow hk.le (Real.rpow_nonneg ha.le _),
      ← Real.rpow_mul ha.le, ← mul_assoc, ← Real.rpow_add hk]
    have he : q+(2-q) = 2 := by ring
    rw [he, Real.rpow_two]
    congr 1
    congr 1
    field_simp
    ring
  rw [mul_pow]
  calc
    _ = 4*k^2*(a*(a^(-1/q))^2) + 4*(k^q*(k*a^(-1/q))^(2-q)) := by ring
    _ = _ := by rw [h1, h2]; ring

/-- Equal-exponent finite Davydov bound, including the q=2 convention. -/
theorem t46A_moment_covariance {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (P : Law Ω) (U : Ω → A) (V : Ω → B) (f : A → ℝ) (g : B → ℝ)
    (k q : ℝ) (hk : 0 < k) (hq : 2 ≤ q)
    (hf : mean P (fun ω => |f (U ω)|^q) ≤ k^q)
    (hg : mean P (fun ω => |g (V ω)|^q) ≤ k^q) :
    |cov P (fun ω => f (U ω)) (fun ω => g (V ω))| ≤
      8*k^2*mixPower (alpha P U V) ((q-2)/q) := by
  by_cases ha : alpha P U V = 0
  · have hb := t46A_bounded_covariance P U V f g (∑ a, |f a|) (∑ b, |g b|)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      (fun a => Finset.single_le_sum (f := fun a => |f a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))
      (fun b => Finset.single_le_sum (f := fun b => |g b|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b))
    simpa only [ha, mixPower, if_true, mul_zero, zero_mul] using hb
  · have hap : 0 < alpha P U V := lt_of_le_of_ne (alpha_nonnegative P U V) (Ne.symm ha)
    let L := k*(alpha P U V)^(-1/q)
    have hL : 0 < L := mul_pos hk (Real.rpow_pos_of_pos hap _)
    have hb := t46A_bounded_covariance P U V
      (fun a => t46A_truncate L (f a)) (fun b => t46A_truncate L (g b))
      L L hL.le hL.le (fun a => t46A_truncate_bound L (f a) hL.le)
      (fun b => t46A_truncate_bound L (g b) hL.le)
    have ht := t46A_covariance_truncation P (fun ω => f (U ω))
      (fun ω => g (V ω)) L q k hL hq hf hg
    calc
      _ ≤ |cov P (fun ω => t46A_truncate L (f (U ω)))
          (fun ω => t46A_truncate L (g (V ω)))| +
          |cov P (fun ω => f (U ω)) (fun ω => g (V ω)) -
            cov P (fun ω => t46A_truncate L (f (U ω)))
              (fun ω => t46A_truncate L (g (V ω)))| := by
        simpa only [add_sub_cancel] using abs_add_le
          (cov P (fun ω => t46A_truncate L (f (U ω)))
            (fun ω => t46A_truncate L (g (V ω))))
          (cov P (fun ω => f (U ω)) (fun ω => g (V ω)) -
            cov P (fun ω => t46A_truncate L (f (U ω)))
              (fun ω => t46A_truncate L (g (V ω))))
      _ ≤ 4*alpha P U V*L*L+4*k^q*L^(2-q) := add_le_add hb ht
      _ = 8*k^2*(alpha P U V)^((q-2)/q) := by
        have he := t46A_cutoff_choice k q (alpha P U V) hk hq hap
        dsimp [L]
        nlinarith only [he]
      _ = _ := by rw [mixPower, if_neg ha, Real.rpow_eq_pow]

theorem t46A_arm_mask {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool) (a : ℕ) :
    ∀ z, armVariable E b a i z = armVariable E b a i (masked E i z) := by
  intro z
  apply arm_dependsOn E i b a
  intro j hj
  simp only [Set.mem_setOf_eq] at hj
  simp [masked, hj]

theorem t46A_mix_nonnegative {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (U : Ω → A) (V : Ω → B) (θ : ℝ) :
    0 ≤ mixPower (alpha P U V) θ := by
  unfold mixPower
  split_ifs <;> first | exact le_rfl | exact Real.rpow_nonneg (alpha_nonnegative P U V) θ

theorem t46A_alpha_le_power {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (U : Ω → A) (V : Ω → B) (θ : ℝ) (hθ : θ ≤ 1) :
    alpha P U V ≤ mixPower (alpha P U V) θ := by
  by_cases ha : alpha P U V = 0
  · simp [ha, mixPower]
  · rw [mixPower, if_neg ha, Real.rpow_eq_pow]
    have hap : 0 < alpha P U V := lt_of_le_of_ne (alpha_nonnegative P U V) (Ne.symm ha)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hap (alpha_le_one P U V) hθ

theorem t46A_weighted_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (b : Bool) (X : Fin n → Assignment n → ℝ) (k C D θ : ℝ)
    (hp : ∀ i, 0 < marginal E i b ∧ (marginal E i b)⁻¹ ≤ k)
    (hcov : ∀ i j, |cov E.design (X i) (X j)| ≤
      C*d E i j + D*((1-d E i j)*mixPower
        (alpha E.design (masked E i) (masked E j)) θ)) :
    var E.design (fun z => (∑ i, X i z / marginal E i b)/(n:ℝ)) ≤
      k^2*C*dAvg E/(n:ℝ) + k^2*D*alphaExt E θ/(n:ℝ) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (fun z => (∑ i, X i z / marginal E i b)/(n:ℝ)) =
      (fun z => (∑ i, (marginal E i b)⁻¹*X i z)/(n:ℝ)) := by
    funext z
    simp only [div_eq_mul_inv, mul_comm]
  rw [he, variance_div]
  have hw := weighted_variance_absolute E.design X (fun i => (marginal E i b)⁻¹) k
    (fun i => ⟨inv_pos.mpr (hp i).1, (hp i).2⟩)
  calc
    _ ≤ (k^2*(∑ i, ∑ j, |cov E.design (X i) (X j)|))/(n:ℝ)^2 :=
      div_le_div_of_nonneg_right hw.2 (sq_nonneg _)
    _ ≤ (k^2*(∑ i, ∑ j, (C*d E i j + D*((1-d E i j)*mixPower
        (alpha E.design (masked E i) (masked E j)) θ))))/(n:ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov i j))
    _ = _ := by
      simp only [dAvg, degree, alphaExt, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      field_simp
      <;> ring

theorem t46A_count_covariance {n : ℕ} (E : Experiment n) (b : Bool)
    (θ : ℝ) (hθ : θ ≤ 1) (i j : Fin n) :
    |cov E.design (fun z => if z i = b then 1 else 0)
      (fun z => if z j = b then 1 else 0)| ≤
      d E i j + (1-d E i j)*mixPower
        (alpha E.design (masked E i) (masked E j)) θ := by
  have hi (z : Assignment n) : masked E i z i = z i := by simp [masked, Interferes]
  have hj (z : Assignment n) : masked E j z j = z j := by simp [masked, Interferes]
  have hb := t46A_indicator_covariance E.design (masked E i) (masked E j)
    {w | w i = b} {w | w j = b}
  simp only [Set.mem_setOf_eq, hi, hj] at hb
  by_cases hd : Dependent E i j
  · simpa only [d, hd, if_true, sub_self, zero_mul, add_zero] using
      hb.trans (alpha_le_one E.design (masked E i) (masked E j))
  · simpa only [d, hd, if_false, sub_zero, one_mul, zero_add] using
      hb.trans (t46A_alpha_le_power E.design (masked E i) (masked E j) θ hθ)

theorem t46A_count_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (b : Bool) (k θ : ℝ) (hθ : θ ≤ 1)
    (hp : ∀ i, 0 < marginal E i b ∧ (marginal E i b)⁻¹ ≤ k) :
    var E.design (fun z => nHat E b z/(n:ℝ)) ≤
      k^2*dAvg E/(n:ℝ)+k^2*alphaExt E θ/(n:ℝ) := by
  have h := t46A_weighted_bound hn E b (fun i z => if z i = b then 1 else 0)
    k 1 1 θ hp (fun i j => by simpa using t46A_count_covariance E b θ hθ i j)
  simpa only [nHat, mul_one] using h

theorem t46A_arm_moment {n : ℕ} (E : Experiment n) (b : Bool) (i : Fin n)
    (q : ℝ) (hq : 0 < q) :
    mean E.design (fun z => |armVariable E b 1 i z|^q) ≤
      mean E.design (fun z => |E.outcome i z|^q) := by
  apply t46A_mean_mono
  intro z
  by_cases hz : z i = b
  · simp [armVariable, hz]
  · simp only [armVariable, hz, if_false, abs_zero, Real.zero_rpow hq.ne']
    exact Real.rpow_nonneg (abs_nonneg _) _

theorem t46A_finite_arm_covariance {n : ℕ} (E : Experiment n) (k q : ℝ)
    (hk : 0 < k) (hq : 2 ≤ q)
    (hM : ∀ i, mean E.design (fun z => |E.outcome i z|^q) ≤ k^q)
    (b : Bool) (i j : Fin n) :
    |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
      k^2*d E i j + (10*k^2)*((1-d E i j)*mixPower
        (alpha E.design (masked E i) (masked E j)) ((q-2)/q)) := by
  have hM' : ∀ i, mean E.design (fun z => Real.rpow |E.outcome i z| q) ≤ Real.rpow k q := by
    simpa only [Real.rpow_eq_pow] using hM
  have he (i : Fin n) : (fun z => armVariable E b 1 i (masked E i z)) = armVariable E b 1 i :=
    funext (fun z => (t46A_arm_mask E i b 1 z).symm)
  have hq0 : 0 < q := by linarith
  have hmix := t46A_moment_covariance E.design (masked E i) (masked E j)
    (armVariable E b 1 i) (armVariable E b 1 j) k q hk hq
    (by simp only [← t46A_arm_mask]; exact (t46A_arm_moment E b i q hq0).trans (hM i))
    (by simp only [← t46A_arm_mask]; exact (t46A_arm_moment E b j q hq0).trans (hM j))
  rw [he, he] at hmix
  by_cases hd : Dependent E i j
  · simpa only [d, hd, if_true, sub_self, zero_mul, mul_zero, add_zero, mul_one] using
      (corrected_moment_covariance E k q hk hq hM' 1 (by simpa using hq) i j b).2.2.2.2.2.2
  · simp only [d, hd, if_false, sub_zero, one_mul, mul_zero, zero_add]
    have hn := t46A_mix_nonnegative E.design (masked E i) (masked E j) ((q-2)/q)
    nlinarith [mul_nonneg (sq_nonneg k) hn]

theorem t46A_finite_variances {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q : ℝ) (hk : 0 < k) (hq : 2 ≤ q)
    (hp : ∀ i b, 0 < marginal E i b ∧ (marginal E i b)⁻¹ ≤ k)
    (hM : ∀ i, mean E.design (fun z => |E.outcome i z|^q) ≤ k^q) (b : Bool) :
    var E.design (muHat E b) ≤ k^4*dAvg E/(n:ℝ)+10*k^4*alphaExt E ((q-2)/q)/(n:ℝ) ∧
    var E.design (fun z => nHat E b z/(n:ℝ)) ≤
      k^2*dAvg E/(n:ℝ)+k^2*alphaExt E ((q-2)/q)/(n:ℝ) := by
  constructor
  · have h := t46A_weighted_bound hn E b (armVariable E b 1) k (k^2) (10*k^2)
      ((q-2)/q) (fun i => hp i b) (t46A_finite_arm_covariance E k q hk hq hM b)
    have he : (fun z => (∑ i, armVariable E b 1 i z/marginal E i b)/(n:ℝ)) = muHat E b := by
      funext z
      simp only [muHat, armVariable, pow_one]
    rw [he] at h
    convert h using 1 <;> ring
  · apply t46A_count_bound hn E b k ((q-2)/q) _ (fun i => hp i b)
    exact (div_le_one (by linarith : 0 < q)).mpr (by linarith)

theorem t46A_mean_congr_support {Ω : Type*} [Fintype Ω] (P : Law Ω) (f g : Ω → ℝ)
    (h : ∀ ω, 0 < P.mass ω → f ω = g ω) : mean P f = mean P g := by
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : P.mass ω = 0
  · simp [hω]
  · rw [h ω (lt_of_le_of_ne (P.nonneg ω) (Ne.symm hω))]

theorem t46A_cov_congr_support {Ω : Type*} [Fintype Ω]
    (P : Law Ω) (f g F G : Ω → ℝ)
    (hf : ∀ ω, 0 < P.mass ω → f ω = F ω)
    (hg : ∀ ω, 0 < P.mass ω → g ω = G ω) : cov P f g = cov P F G := by
  rw [covariance_product_formula, covariance_product_formula,
    t46A_mean_congr_support P f F hf, t46A_mean_congr_support P g G hg]
  congr 1
  exact t46A_mean_congr_support P _ _ (fun ω hω => by rw [hf ω hω, hg ω hω])

theorem t46A_second_covariance {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (f g : Ω → ℝ) (k : ℝ)
    (hf : mean P (fun ω => f ω^2) ≤ k^2)
    (hg : mean P (fun ω => g ω^2) ≤ k^2) : |cov P f g| ≤ k^2 := by
  have hfv : var P f ≤ k^2 := by rw [variance_second_moment]; nlinarith [sq_nonneg (mean P f)]
  have hgv : var P g ≤ k^2 := by rw [variance_second_moment]; nlinarith [sq_nonneg (mean P g)]
  calc
    _ ≤ Real.sqrt (var P f*var P g) := covariance_cauchy_schwarz P f g
    _ ≤ Real.sqrt (k^2*k^2) := Real.sqrt_le_sqrt
      (mul_le_mul hfv hgv (variance_nonnegative P g) (sq_nonneg k))
    _ = k^2 := by rw [← sq, Real.sqrt_sq (sq_nonneg k)]

theorem t46A_support_second {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (f : Ω → ℝ) (k : ℝ) (hk : 0 ≤ k)
    (hf : ∀ ω, 0 < P.mass ω → |f ω| ≤ k) : mean P (fun ω => f ω^2) ≤ k^2 := by
  calc
    _ = mean P (fun ω => (t46A_truncate k (f ω))^2) :=
      t46A_mean_congr_support P _ _ (fun ω hω => by simp [t46A_truncate, hf ω hω])
    _ ≤ mean P (fun _ => k^2) := t46A_mean_mono P _ _ (fun ω => by
      have h := (sq_le_sq₀ (abs_nonneg _) hk).mpr (t46A_truncate_bound k (f ω) hk)
      simpa only [sq_abs] using h)
    _ = _ := mean_const P _

theorem t46A_bounded_support_covariance {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] (P : Law Ω)
    (U : Ω → A) (V : Ω → B) (f : A → ℝ) (g : B → ℝ)
    (k : ℝ) (hk : 0 ≤ k)
    (hf : ∀ ω, 0 < P.mass ω → |f (U ω)| ≤ k)
    (hg : ∀ ω, 0 < P.mass ω → |g (V ω)| ≤ k) :
    |cov P (fun ω => f (U ω)) (fun ω => g (V ω))| ≤ 4*k^2*alpha P U V := by
  have he := t46A_cov_congr_support P (fun ω => f (U ω)) (fun ω => g (V ω))
    (fun ω => t46A_truncate k (f (U ω))) (fun ω => t46A_truncate k (g (V ω)))
    (fun ω hω => by simp [t46A_truncate, hf ω hω])
    (fun ω hω => by simp [t46A_truncate, hg ω hω])
  rw [he]
  have hb := t46A_bounded_covariance P U V (fun a => t46A_truncate k (f a))
    (fun b => t46A_truncate k (g b)) k k hk hk
    (fun a => t46A_truncate_bound k (f a) hk) (fun b => t46A_truncate_bound k (g b) hk)
  convert hb using 1 <;> ring

theorem t46A_bounded_arm_covariance {n : ℕ} (E : Experiment n) (k : ℝ) (hk : 0 ≤ k)
    (hM : ∀ i z, 0 < E.design.mass z → |E.outcome i z| ≤ k)
    (b : Bool) (i j : Fin n) :
    |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
      k^2*d E i j + (10*k^2)*((1-d E i j)*mixPower
        (alpha E.design (masked E i) (masked E j)) 1) := by
  have hA (i : Fin n) (z : Assignment n) (hz : 0 < E.design.mass z) :
      |armVariable E b 1 i z| ≤ k := by
    by_cases hi : z i = b
    · simpa [armVariable, hi] using hM i z hz
    · simp [armVariable, hi, hk]
  have hmix := t46A_bounded_support_covariance E.design (masked E i) (masked E j)
    (armVariable E b 1 i) (armVariable E b 1 j) k hk
    (fun z hz => by rw [← t46A_arm_mask]; exact hA i z hz)
    (fun z hz => by rw [← t46A_arm_mask]; exact hA j z hz)
  simp only [← t46A_arm_mask] at hmix
  have hpower : mixPower (alpha E.design (masked E i) (masked E j)) 1 =
      alpha E.design (masked E i) (masked E j) := by
    unfold mixPower
    split_ifs with h
    · exact h.symm
    · exact Real.rpow_one _
  by_cases hd : Dependent E i j
  · simpa only [d, hd, if_true, sub_self, zero_mul, mul_zero, add_zero, mul_one] using
      t46A_second_covariance E.design (armVariable E b 1 i) (armVariable E b 1 j) k
        (t46A_support_second E.design _ k hk (hA i))
        (t46A_support_second E.design _ k hk (hA j))
  · simp only [d, hd, if_false, sub_zero, one_mul, mul_zero, zero_add, hpower]
    nlinarith [mul_nonneg (sq_nonneg k) (alpha_nonnegative E.design (masked E i) (masked E j))]

theorem t46A_bounded_variances {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k : ℝ) (hk : 0 < k)
    (hp : ∀ i b, 0 < marginal E i b ∧ (marginal E i b)⁻¹ ≤ k)
    (hM : ∀ i z, 0 < E.design.mass z → |E.outcome i z| ≤ k) (b : Bool) :
    var E.design (muHat E b) ≤ k^4*dAvg E/(n:ℝ)+10*k^4*alphaExt E 1/(n:ℝ) ∧
    var E.design (fun z => nHat E b z/(n:ℝ)) ≤
      k^2*dAvg E/(n:ℝ)+k^2*alphaExt E 1/(n:ℝ) := by
  constructor
  · have h := t46A_weighted_bound hn E b (armVariable E b 1) k (k^2) (10*k^2)
      1 (fun i => hp i b) (t46A_bounded_arm_covariance E k hk.le hM b)
    have he : (fun z => (∑ i, armVariable E b 1 i z/marginal E i b)/(n:ℝ)) = muHat E b := by
      funext z
      simp only [muHat, armVariable, pow_one]
    rw [he] at h
    convert h using 1 <;> ring
  · exact t46A_count_bound hn E b k 1 le_rfl (fun i => hp i b)

theorem t46A_marginal_bounds {n : ℕ} (E : Experiment n) (k : ℝ) (hk : 0 < k)
    (hp : ∀ i, k⁻¹ ≤ marginal E i true ∧ marginal E i true ≤ 1-k⁻¹) :
    ∀ i b, 0 < marginal E i b ∧ (marginal E i b)⁻¹ ≤ k := by
  intro i b
  have h1 : k⁻¹ ≤ marginal E i b := by
    cases b
    · have he := marginal_partition E i
      linarith [(hp i).2]
    · exact (hp i).1
  have hp0 := (inv_pos.mpr hk).trans_le h1
  exact ⟨hp0, (inv_le_comm₀ hp0 hk).mpr h1⟩

theorem t46A_extended_variances {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k : ℝ) (q : MomentIndex) (hk : 0 < k) (hq : 2 ≤ q)
    (hp : ∀ i b, 0 < marginal E i b ∧ (marginal E i b)⁻¹ ≤ k)
    (hM : ∀ i, MomentBound E.design (E.outcome i) k q) (b : Bool) :
    var E.design (muHat E b) ≤ k^4*dAvg E/(n:ℝ)+10*k^4*alphaExt E (extExponent q)/(n:ℝ) ∧
    var E.design (fun z => nHat E b z/(n:ℝ)) ≤
      k^2*dAvg E/(n:ℝ)+k^2*alphaExt E (extExponent q)/(n:ℝ) := by
  cases q using WithTop.recTopCoe
  · simp only [extExponent, if_true]
    apply t46A_bounded_variances hn E k hk hp
    simpa only [MomentBound, if_true] using hM
  · rename_i r
    have hr : (2:ℝ) ≤ r := WithTop.coe_le_coe.mp hq
    simp only [extExponent, WithTop.coe_ne_top, if_false, WithTop.untopD_coe]
    apply t46A_finite_variances hn E k r hk hr hp
    simpa only [MomentBound, WithTop.coe_ne_top, if_false, WithTop.untopD_coe,
      Real.rpow_eq_pow] using hM

theorem t46A_extended_first {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (X : Ω → ℝ) (k : ℝ) (q : MomentIndex) (hk : 0 < k) (hq : 2 ≤ q)
    (hM : MomentBound P X k q) : mean P (fun ω => |X ω|) ≤ k := by
  cases q using WithTop.recTopCoe
  · have hX : ∀ ω, 0 < P.mass ω → |X ω| ≤ k := by
      simpa only [MomentBound, if_true] using hM
    calc
      _ = mean P (fun ω => |t46A_truncate k (X ω)|) :=
        t46A_mean_congr_support P _ _ (fun ω hω => by simp [t46A_truncate, hX ω hω])
      _ ≤ mean P (fun _ => k) := t46A_mean_mono P _ _ (fun ω => t46A_truncate_bound k (X ω) hk.le)
      _ = _ := mean_const P _
  · rename_i r
    have hr : (2:ℝ) ≤ r := WithTop.coe_le_coe.mp hq
    apply mean_abs_of_moment P X k r hk (by linarith)
    simpa only [MomentBound, WithTop.coe_ne_top, if_false, WithTop.untopD_coe] using hM

theorem t46A_muBreve_bound {n : ℕ} (hn : 0 < n) (E : Experiment n) (k : ℝ)
    (hk : 0 < k) (hp : ∀ i b, 0 < marginal E i b ∧ (marginal E i b)⁻¹ ≤ k)
    (hM : ∀ i, mean E.design (fun z => |E.outcome i z|) ≤ k) (b : Bool) :
    |muBreve E b| ≤ k^2 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hb (i : Fin n) : |cmean E.design (fun z => z i = b) (E.outcome i)| ≤ k^2 := by
    have hnum : |mean E.design (fun z => if z i = b then E.outcome i z else 0)| ≤ k := by
      calc
        _ ≤ mean E.design (fun z => |if z i = b then E.outcome i z else 0|) := mean_abs_le _ _
        _ ≤ mean E.design (fun z => |E.outcome i z|) := t46A_mean_mono _ _ _ (fun z => by
          by_cases hz : z i = b <;> simp [hz])
        _ ≤ k := hM i
    have he : cmean E.design (fun z => z i = b) (E.outcome i) =
        mean E.design (fun z => if z i = b then E.outcome i z else 0) / marginal E i b := by
      unfold cmean marginal
      congr 2
      funext z
      by_cases hz : z i = b <;> simp [hz]
    rw [he, abs_div, abs_of_pos (hp i b).1, div_eq_mul_inv]
    calc
      _ ≤ k*k := mul_le_mul hnum (hp i b).2 (inv_nonneg.mpr (hp i b).1.le) hk.le
      _ = _ := by ring
  unfold muBreve
  simp only [conditional_potential_eq_observed]
  rw [abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑ i, |cmean E.design (fun z => z i = b) (E.outcome i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, k^2 := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp [mul_comm]

theorem t46A_muBreve_difference {n : ℕ} (E : Experiment n) :
    muBreve E true-muBreve E false = adse E := by
  simp only [muBreve, conditional_potential_eq_observed, adse, Finset.sum_sub_distrib, sub_div]

theorem t46A_alphaExt_nonnegative {n : ℕ} (E : Experiment n) (θ : ℝ) : 0 ≤ alphaExt E θ := by
  unfold alphaExt
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  have hd : 0 ≤ 1-d E i j := by unfold d; split_ifs <;> norm_num
  exact mul_nonneg hd (t46A_mix_nonnegative E.design (masked E i) (masked E j) θ)

def t46A_rate (S : Study) (q : MomentIndex) (t : ℕ) : ℝ :=
  bernoulliRate S t + Real.sqrt (alphaExt (S.experiment t) (extExponent q))/Real.sqrt (size S t)

theorem t46A_rate_pos (S : Study) (q : MomentIndex) (t : ℕ) : 0 < t46A_rate S q t := by
  exact add_pos_of_pos_of_nonneg (bernoulli_rate_pos S t) (by unfold size; positivity)

theorem t46A_rate_zero (S : Study) (q : MomentIndex) (hR : Restricted S)
    (hE : LittleO (fun t => alphaExt (S.experiment t) (extExponent q)) (size S)) :
    Tendsto (t46A_rate S q) atTop (nhds 0) := by
  have he := hE.sqrt
  have he' : Tendsto (fun t => Real.sqrt (alphaExt (S.experiment t) (extExponent q))/
      Real.sqrt (size S t)) atTop (nhds 0) := by
    simpa only [Real.sqrt_div (t46A_alphaExt_nonnegative _ _), Real.sqrt_zero] using he
  change Tendsto (fun t => bernoulliRate S t +
    Real.sqrt (alphaExt (S.experiment t) (extExponent q))/Real.sqrt (size S t)) atTop (nhds 0)
  simpa only [add_zero] using (bernoulli_rate_zero S hR).add he'

theorem t46A_rate_domination (S : Study) (q : MomentIndex) (t : ℕ) :
    dAvg (S.experiment t)/size S t + alphaExt (S.experiment t) (extExponent q)/size S t ≤
      (t46A_rate S q t)^2 := by
  have hn : 0 < size S t := by unfold size; exact_mod_cast S.positive t
  have he : (Real.sqrt (alphaExt (S.experiment t) (extExponent q))/Real.sqrt (size S t))^2 =
      alphaExt (S.experiment t) (extExponent q)/size S t := by
    rw [div_pow, Real.sq_sqrt (t46A_alphaExt_nonnegative _ _), Real.sq_sqrt hn.le]
  rw [← bernoulli_rate_square, ← he]
  unfold t46A_rate
  have he0 : 0 ≤ Real.sqrt (alphaExt (S.experiment t) (extExponent q))/Real.sqrt (size S t) :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [mul_nonneg (bernoulli_rate_pos S t).le he0]

theorem t46A_component_mse (S : Study) (k : ℝ) (q s : MomentIndex)
    (hReg : RegularMix S k q s) (t : ℕ) (b : Bool) :
    mean (S.experiment t).design (fun z => (muHat (S.experiment t) b z-muBreve (S.experiment t) b)^2) ≤
      (40*k^4+k^2)*(t46A_rate S q t)^2 ∧
    mean (S.experiment t).design (fun z => (nHat (S.experiment t) b z/size S t-1)^2) ≤
      (40*k^4+k^2)*(t46A_rate S q t)^2 := by
  have hk := hReg.1
  have hn : 0 < size S t := by unfold size; exact_mod_cast S.positive t
  have hp := t46A_marginal_bounds (S.experiment t) k hk (hReg.2.2.2.1 t)
  have hv := t46A_extended_variances (S.positive t) (S.experiment t) k q hk hReg.2.1 hp
    (hReg.2.2.2.2.1 t) b
  have hm := mean_muHat_eq_muBreve (S.experiment t) b (fun i => (hp i b).1)
  have hc : mean (S.experiment t).design (fun z => nHat (S.experiment t) b z/size S t) = 1 := by
    rw [mean_div, expected_arm_count _ _ (fun i => (hp i b).1)]
    exact div_self hn.ne'
  have hd : 0 ≤ dAvg (S.experiment t)/size S t := div_nonneg
    (le_trans (by norm_num) (average_degree_at_least_one _ (S.positive t))) hn.le
  have ha : 0 ≤ alphaExt (S.experiment t) (extExponent q)/size S t :=
    div_nonneg (t46A_alphaExt_nonnegative _ _) hn.le
  have hdom := t46A_rate_domination S q t
  constructor
  · rw [← hm, centered_square_mean]
    calc
      _ ≤ k^4*dAvg (S.experiment t)/size S t+
          10*k^4*alphaExt (S.experiment t) (extExponent q)/size S t := hv.1
      _ ≤ 10*k^4*(dAvg (S.experiment t)/size S t+
          alphaExt (S.experiment t) (extExponent q)/size S t) := by
        simp only [mul_div_assoc]
        nlinarith [mul_nonneg (pow_nonneg hk.le 4) hd]
      _ ≤ (40*k^4+k^2)*(t46A_rate S q t)^2 :=
        mul_le_mul (by nlinarith [pow_nonneg hk.le 4, sq_nonneg k]) hdom
          (add_nonneg hd ha) (by positivity)
  · rw [← hc, centered_square_mean]
    calc
      _ ≤ k^2*dAvg (S.experiment t)/size S t+
          k^2*alphaExt (S.experiment t) (extExponent q)/size S t := hv.2
      _ = k^2*(dAvg (S.experiment t)/size S t+
          alphaExt (S.experiment t) (extExponent q)/size S t) := by ring
      _ ≤ (40*k^4+k^2)*(t46A_rate S q t)^2 :=
        mul_le_mul (by nlinarith [pow_nonneg hk.le 4]) hdom
          (add_nonneg hd ha) (by positivity)

theorem t46A_ht_mse (S : Study) (k : ℝ) (q s : MomentIndex)
    (hReg : RegularMix S k q s) (t : ℕ) :
    mean (S.experiment t).design (fun z => (ht (S.experiment t) z-adse (S.experiment t))^2) ≤
      (4*(40*k^4+k^2))*(t46A_rate S q t)^2 := by
  have h1 := (t46A_component_mse S k q s hReg t true).1
  have h0 := (t46A_component_mse S k q s hReg t false).1
  calc
    _ ≤ mean (S.experiment t).design (fun z =>
        2*((muHat (S.experiment t) true z-muBreve (S.experiment t) true)^2+
          (muHat (S.experiment t) false z-muBreve (S.experiment t) false)^2)) := by
      apply t46A_mean_mono
      intro z
      rw [← t46A_muBreve_difference]
      unfold ht
      nlinarith [sq_nonneg ((muHat (S.experiment t) true z-muBreve (S.experiment t) true)+
        (muHat (S.experiment t) false z-muBreve (S.experiment t) false))]
    _ = 2*(mean (S.experiment t).design (fun z =>
          (muHat (S.experiment t) true z-muBreve (S.experiment t) true)^2)+
        mean (S.experiment t).design (fun z =>
          (muHat (S.experiment t) false z-muBreve (S.experiment t) false)^2)) := by
      rw [mean_const_mul, mean_add]
    _ ≤ _ := by linarith

theorem t46A_hajek_error {n : ℕ} (hn : 0 < n) (E : Experiment n) (k δ : ℝ)
    (z : Assignment n) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/2)
    (hm : ∀ b, |muBreve E b| ≤ k^2)
    (hX : ∀ b, |muHat E b z-muBreve E b| ≤ δ)
    (hY : ∀ b, |nHat E b z/(n:ℝ)-1| ≤ δ) :
    |hajek E z-adse E| ≤ 4*(1+k^2)*δ := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hr (b : Bool) := ratio_error_bound (muHat E b z) (nHat E b z/(n:ℝ))
    (muBreve E b) δ (k^2) hδ hδ1 (hX b) (hY b) (hm b)
  have hnonzero (b : Bool) : nHat E b z ≠ 0 := by
    intro hz
    have hh := (hr b).1
    rw [hz, zero_div] at hh
    exact (lt_irrefl 0 hh)
  have ha : ArmsNonempty E z := ⟨hnonzero true, hnonzero false⟩
  have he (b : Bool) : (n:ℝ)*muHat E b z/nHat E b z = muHat E b z/(nHat E b z/(n:ℝ)) := by
    field_simp [hnR.ne', hnonzero b]
    <;> ring
  rw [hajek, if_pos ha, he true, he false, ← t46A_muBreve_difference]
  calc
    _ = |(muHat E true z/(nHat E true z/(n:ℝ))-muBreve E true)-
      (muHat E false z/(nHat E false z/(n:ℝ))-muBreve E false)| := by congr 1; ring
    _ ≤ |muHat E true z/(nHat E true z/(n:ℝ))-muBreve E true|+
      |muHat E false z/(nHat E false z/(n:ℝ))-muBreve E false| := abs_sub _ _
    _ ≤ 2*(1+k^2)*δ+2*(1+k^2)*δ := add_le_add (hr true).2 (hr false).2
    _ = _ := by ring

theorem t46A_hajek_op (S : Study) (k : ℝ) (q s : MomentIndex)
    (hReg : RegularMix S k q s) (hRestricted : Restricted S)
    (hExt : LittleO (fun t => alphaExt (S.experiment t) (extExponent q)) (size S)) :
    Op S (fun t z => hajek (S.experiment t) z-adse (S.experiment t)) (t46A_rate S q) := by
  intro ε hε
  let C := 40*k^4+k^2
  have hk := hReg.1
  have hC : 0 < C := by dsimp [C]; positivity
  let K := Real.sqrt (4*C/ε)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hs : C ≤ (ε/4)*K^2 := by
    have hr := Real.sq_sqrt (div_nonneg (by positivity : 0 ≤ 4*C) hε.le)
    have hsr := Real.sqrt_nonneg (4*C/ε)
    dsimp [K]
    nlinarith [div_mul_cancel₀ (4*C) hε.ne']
  have hlarge : 0 < 8*(1+k^2)*K := by positivity
  refine ⟨8*(1+k^2)*K, hlarge, ?_⟩
  have hlim : Tendsto (fun t => K*t46A_rate S q t) atTop (nhds 0) := by
    simpa using (t46A_rate_zero S q hRestricted hExt).const_mul K
  filter_upwards [hlim.eventually_le_const (by norm_num : (0:ℝ) < 1/2)] with t hδ1
  let δ := K*t46A_rate S q t
  have hδ : 0 < δ := mul_pos hK (t46A_rate_pos S q t)
  let A := fun b z => δ ≤ |muHat (S.experiment t) b z-muBreve (S.experiment t) b|
  let D := fun b z => δ ≤ |nHat (S.experiment t) b z/size S t-1|
  have hp (X : Assignment (S.N t) → ℝ)
      (hM : mean (S.experiment t).design (fun z => (X z)^2) ≤ C*(t46A_rate S q t)^2) :
      prob (S.experiment t).design (fun z => δ ≤ |X z|) ≤ ε/4 := by
    calc
      _ ≤ mean (S.experiment t).design (fun z => (X z)^2)/δ^2 := second_moment_tail _ _ δ hδ
      _ ≤ (C*(t46A_rate S q t)^2)/(K*t46A_rate S q t)^2 :=
        div_le_div_of_nonneg_right hM (sq_nonneg _)
      _ = C/K^2 := by field_simp [(t46A_rate_pos S q t).ne', hK.ne']
      _ ≤ ε/4 := (div_le_iff₀ (sq_pos_of_pos hK)).mpr hs
  have hA (b : Bool) : prob (S.experiment t).design (A b) ≤ ε/4 :=
    hp _ (t46A_component_mse S k q s hReg t b).1
  have hD (b : Bool) : prob (S.experiment t).design (D b) ≤ ε/4 :=
    hp _ (t46A_component_mse S k q s hReg t b).2
  have hi (z : Assignment (S.N t))
      (hz : (8*(1+k^2)*K)*t46A_rate S q t ≤ |hajek (S.experiment t) z-adse (S.experiment t)|) :
      (A true z ∨ A false z) ∨ (D true z ∨ D false z) := by
    by_contra hn
    have hneg : (¬A true z ∧ ¬A false z) ∧ (¬D true z ∧ ¬D false z) := by tauto
    have hX (b : Bool) : |muHat (S.experiment t) b z-muBreve (S.experiment t) b| ≤ δ := by
      cases b
      · exact (lt_of_not_ge hneg.1.2).le
      · exact (lt_of_not_ge hneg.1.1).le
    have hY (b : Bool) : |nHat (S.experiment t) b z/size S t-1| ≤ δ := by
      cases b
      · exact (lt_of_not_ge hneg.2.2).le
      · exact (lt_of_not_ge hneg.2.1).le
    have hpb := t46A_marginal_bounds (S.experiment t) k hk (hReg.2.2.2.1 t)
    have hm (b : Bool) : |muBreve (S.experiment t) b| ≤ k^2 :=
      t46A_muBreve_bound (S.positive t) (S.experiment t) k hk hpb
        (fun i => t46A_extended_first _ _ k q hk hReg.2.1 (hReg.2.2.2.2.1 t i)) b
    have hb := t46A_hajek_error (S.positive t) (S.experiment t) k δ z hδ.le hδ1 hm hX hY
    have hh := hz.trans hb
    change (8*(1+k^2)*K)*t46A_rate S q t ≤ 4*(1+k^2)*(K*t46A_rate S q t) at hh
    have hprod : 0 < (1+k^2)*(K*t46A_rate S q t) := mul_pos (by positivity) hδ
    nlinarith only [hh, hprod]
  calc
    _ ≤ prob (S.experiment t).design (fun z => A true z ∨ A false z)+
        prob (S.experiment t).design (fun z => D true z ∨ D false z) := probability_union_bound _ _ _ _ hi
    _ ≤ (prob (S.experiment t).design (A true)+prob (S.experiment t).design (A false))+
        (prob (S.experiment t).design (D true)+prob (S.experiment t).design (D false)) :=
      add_le_add (probability_union_bound _ _ _ _ (fun z hz => hz))
        (probability_union_bound _ _ _ _ (fun z hz => hz))
    _ ≤ ε := by linarith only [hA true, hA false, hD true, hD false]


/-- The finite arbitrary-design identities and the corrected absolute-covariance bounds. -/
theorem arbitrary_finite_lemmas_proof {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hReg : Regular E k q s) :
    mean E.design (ht E) = adse E ∧
    (∀ b, mean E.design (muHat E b) = muBreve E b ∧ mean E.design (nHat E b) = n ∧
      var E.design (muHat E b) ≤ k^4*dAvg E/(n:ℝ)+10*k^4*alphaExt E ((q-2)/q)/(n:ℝ) ∧
      var E.design (fun z => nHat E b z/n) ≤
        k^2*dAvg E/(n:ℝ)+k^2*alphaExt E ((q-2)/q)/(n:ℝ)) := by
  have hp := t46A_marginal_bounds E k hReg.1 hReg.2.2.2.1
  refine ⟨ht_unbiased_ADSE E (fun i => ⟨(hp i true).1, (hp i false).1⟩), ?_⟩
  intro b
  refine ⟨mean_muHat_eq_muBreve E b (fun i => (hp i b).1),
    expected_arm_count E b (fun i => (hp i b).1), ?_⟩
  apply t46A_finite_variances hn E k q hReg.1 hReg.2.1 hp
  simpa only [Real.rpow_eq_pow] using hReg.2.2.2.2.1

end
end AronowAudit.P009.Wave1
