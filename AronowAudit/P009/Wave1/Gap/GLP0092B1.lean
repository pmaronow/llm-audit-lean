import AronowAudit.P009.P009_MixingBasics

namespace AronowAudit.P009.Wave1

open scoped BigOperators
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 400000

/-- Potential outcomes only use the other incoming interference coordinates. -/
theorem t45_potential_mask_representation {n : ℕ} (E : Experiment n) (i : Fin n) :
    ∀ b, ∃ f : Assignment n → ℝ, ∀ z,
      potential E i b z = f (maskedOthers E i z) := by
  intro b
  refine ⟨fun w => E.outcome i (Function.update w i b), ?_⟩
  intro z
  apply BernoulliCompletion.outcome_dependsOn E i
  intro j hj
  change Interferes E j i at hj
  by_cases hji : j = i
  · subst j
    simp [Function.update_self]
  · simp [maskedOthers, masked, Function.update_of_ne hji, hj]

/-- Rearrange a weighted finite sum by the fibers of W. -/
theorem t45_sum_fibers {Ω A : Type*} [Fintype Ω] [Fintype A]
    (W : Ω → A) (g : Ω → ℝ) (f : A → ℝ) :
    (∑ ω, g ω * f (W ω)) =
      ∑ w, (∑ ω, if W ω = w then g ω else 0) * f w := by
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

theorem t45_mean_fibers {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (W : Ω → A) (f : A → ℝ) :
    mean P (fun ω => f (W ω)) =
      ∑ w, prob P (fun ω => W ω = w) * f w := by
  simpa [mean, prob, mul_ite] using t45_sum_fibers W P.mass f

theorem t45_joint_fibers {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (B : Ω → Bool) (W : Ω → A) (b : Bool) (f : A → ℝ) :
    mean P (fun ω => if B ω = b then f (W ω) else 0) =
      ∑ w, prob P (fun ω => B ω = b ∧ W ω = w) * f w := by
  have h := t45_sum_fibers W (fun ω => if B ω = b then P.mass ω else 0) f
  convert h using 1
  · unfold mean
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : B ω = b <;> simp [hω]
  · apply Finset.sum_congr rfl
    intro w _
    congr 1
    unfold prob mean
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : B ω = b <;> by_cases hw : W ω = w <;> simp [hω, hw]

/-- Signed joint-minus-product mass on a treatment/mask fiber. -/
def t45_delta {Ω A : Type*} [Fintype Ω]
    (P : Law Ω) (B : Ω → Bool) (W : Ω → A) (b : Bool) (w : A) : ℝ :=
  prob P (fun ω => B ω = b ∧ W ω = w) -
    prob P (fun ω => B ω = b) * prob P (fun ω => W ω = w)

theorem t45_delta_sum {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (B : Ω → Bool) (W : Ω → A) (b : Bool) :
    (∑ w, t45_delta P B W b w) = 0 := by
  have h1 := t45_joint_fibers P B W b (fun _ => 1)
  have h2 := t45_mean_fibers P W (fun _ => 1)
  simp only [mul_one] at h1 h2
  have h1' : prob P (fun ω => B ω = b) =
      ∑ w, prob P (fun ω => B ω = b ∧ W ω = w) := by
    calc
      _ = mean P (fun ω => if B ω = b then 1 else 0) := by
        unfold prob
        congr 1
        funext ω
        by_cases hω : B ω = b <;> simp [hω]
      _ = _ := h1
  rw [mean_const] at h2
  simp only [t45_delta, Finset.sum_sub_distrib, ← Finset.mul_sum, ← h1', ← h2]
  ring

theorem t45_delta_event {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (B : Ω → Bool) (W : Ω → A) (b : Bool) (T : Set A) :
    (∑ w, if w ∈ T then t45_delta P B W b w else 0) =
      prob P (fun ω => B ω = b ∧ W ω ∈ T) -
        prob P (fun ω => B ω = b) * prob P (fun ω => W ω ∈ T) := by
  have h1 := t45_joint_fibers P B W b (fun w => if w ∈ T then 1 else 0)
  have h2 := t45_mean_fibers P W (fun w => if w ∈ T then 1 else 0)
  have hj : mean P (fun ω => if B ω = b then (if W ω ∈ T then 1 else 0) else 0) =
      prob P (fun ω => B ω = b ∧ W ω ∈ T) := by
    unfold prob
    congr 1
    funext ω
    by_cases hb : B ω = b <;> by_cases hw : W ω ∈ T <;> simp [hb, hw]
  rw [hj] at h1
  change prob P (fun ω => W ω ∈ T) = _ at h2
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w ∈ T <;> simp [hw, t45_delta]

/-- The L1 signed-fiber bound, including the zero-alpha case. -/
theorem t45_binary_fiber_l1 {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (B : Ω → Bool) (W : Ω → A) (b : Bool) :
    (∑ w, |t45_delta P B W b w|) ≤ 2 * alpha P B W := by
  let T : Set A := {w | 0 ≤ t45_delta P B W b w}
  have he := MixingBasics.event_abs_le_alpha P B W ({b} : Set Bool) T
  simp only [Set.mem_singleton_iff] at he
  rw [← t45_delta_event] at he
  have hz := t45_delta_sum P B W b
  have hid : (∑ w, |t45_delta P B W b w|) =
      2 * (∑ w, if w ∈ T then t45_delta P B W b w else 0) := by
    calc
      _ = ∑ w, (2 * (if w ∈ T then t45_delta P B W b w else 0) -
          t45_delta P B W b w) := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases hw : 0 ≤ t45_delta P B W b w
        · simp [T, hw, abs_of_nonneg hw]
          <;> ring
        · simp [T, hw, abs_of_neg (lt_of_not_ge hw)]
          <;> ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz, sub_zero]
  rw [hid]
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans he) (by norm_num)

/-- Conditional-minus-unconditional expectation as a signed fiber sum. -/
theorem t45_discrepancy_fibers {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (B : Ω → Bool) (W : Ω → A) (b : Bool) (f : A → ℝ)
    (hp : 0 < prob P (fun ω => B ω = b)) :
    cmean P (fun ω => B ω = b) (fun ω => f (W ω)) -
      mean P (fun ω => f (W ω)) =
      (∑ w, t45_delta P B W b w * f w) / prob P (fun ω => B ω = b) := by
  simp only [cmean]
  rw [t45_joint_fibers P B W b f, t45_mean_fibers P W f]
  simp only [t45_delta, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  field_simp [hp.ne']

/-- Bounded functions of W have their bias controlled by the binary fibers. -/
theorem t45_bounded_discrepancy {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (B : Ω → Bool) (W : Ω → A) (b : Bool) (f : A → ℝ)
    (k L : ℝ) (hk : 0 < k) (hL : 0 ≤ L)
    (hp : 1 / k ≤ prob P (fun ω => B ω = b)) (hf : ∀ w, |f w| ≤ L) :
    |cmean P (fun ω => B ω = b) (fun ω => f (W ω)) -
      mean P (fun ω => f (W ω))| ≤ 2 * k * L * alpha P B W := by
  have hp0 : 0 < prob P (fun ω => B ω = b) := (one_div_pos.mpr hk).trans_le hp
  have hpinv : (prob P (fun ω => B ω = b))⁻¹ ≤ k :=
    (inv_le_comm₀ hp0 hk).mpr (by simpa using hp)
  rw [t45_discrepancy_fibers P B W b f hp0, abs_div, abs_of_pos hp0, div_eq_mul_inv]
  calc
    _ ≤ (∑ w, |t45_delta P B W b w * f w|) *
        (prob P (fun ω => B ω = b))⁻¹ :=
      mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hp0.le)
    _ ≤ ((∑ w, |t45_delta P B W b w|) * L) * k := by
      apply mul_le_mul _ hpinv (inv_nonneg.mpr hp0.le) (by positivity)
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro w _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf w) (abs_nonneg _)
    _ ≤ (2 * alpha P B W * L) * k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (t45_binary_fiber_l1 P B W b) hL) hk.le
    _ = _ := by ring

/-- A general tail discrepancy bound; the complement is kept in its coefficient. -/
theorem t45_tail_discrepancy {Ω : Type*} [Fintype Ω]
    (P : Law Ω) (B : Ω → Bool) (b : Bool) (F : Ω → ℝ)
    (k : ℝ) (hk : 0 < k) (hp : 1 / k ≤ prob P (fun ω => B ω = b)) :
    |cmean P (fun ω => B ω = b) F - mean P F| ≤
      k * mean P (fun ω => |F ω|) := by
  let p := prob P (fun ω => B ω = b)
  have hp0 : 0 < p := (one_div_pos.mpr hk).trans_le hp
  have hp1 : p ≤ 1 := MixingBasics.probability_le_one P _
  have hki : p⁻¹ ≤ k := (inv_le_comm₀ hp0 hk).mpr (by simpa [p] using hp)
  have hk1 : 1 ≤ k := by
    have : 1 ≤ p⁻¹ := (one_le_inv₀ hp0).mpr hp1
    linarith
  have hid : cmean P (fun ω => B ω = b) F - mean P F =
      mean P (fun ω => ((if B ω = b then p⁻¹ else 0) - 1) * F ω) := by
    have he : (fun ω => ((if B ω = b then p⁻¹ else 0) - 1) * F ω) =
        (fun ω => p⁻¹ * (if B ω = b then F ω else 0) - F ω) := by
      funext ω
      by_cases hω : B ω = b <;> simp [hω] <;> ring
    rw [he, mean_sub, mean_const_mul]
    unfold cmean
    change _ / p - _ = _
    ring
  rw [hid]
  calc
    _ ≤ mean P (fun ω => |((if B ω = b then p⁻¹ else 0) - 1) * F ω|) :=
      BernoulliCompletion.mean_abs_le P _
    _ ≤ mean P (fun ω => k * |F ω|) := by
      unfold mean
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (P.nonneg ω)
      dsimp only
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      by_cases hω : B ω = b
      · simp only [hω, ite_true]
        rw [abs_of_nonneg (by linarith [(one_le_inv₀ hp0).mpr hp1])]
        linarith
      · simpa [hω] using hk1
    _ = _ := mean_const_mul P k _

/-- The pointwise real-power tail estimate, also valid at s = 1. -/
theorem t45_tail_pointwise (u s L : ℝ) (hs : 1 ≤ s) (hL : 0 < L) :
    |if |u| < L then 0 else u| ≤ Real.rpow L (1-s) * Real.rpow |u| s := by
  simp only [Real.rpow_eq_pow]
  by_cases hu : |u| < L
  · simp only [hu, ite_true, abs_zero]
    positivity
  · simp only [hu, ite_false]
    have huL : L ≤ |u| := le_of_not_gt hu
    have hu0 : 0 < |u| := hL.trans_le huL
    have hr := Real.rpow_le_rpow_of_nonpos hL huL (by linarith : 1-s ≤ 0)
    have he : |u| ^ (1-s) * |u| ^ s = |u| := by
      rw [← Real.rpow_add hu0]
      simp
    calc
      |u| = |u| ^ (1-s) * |u| ^ s := he.symm
      _ ≤ L ^ (1-s) * |u| ^ s :=
        mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg (abs_nonneg u) s)

/-- The truncation bound includes finite-law, marginal, moment,
and W-factorization hypotheses. -/
theorem t45_truncation_core {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (B : Ω → Bool) (W : Ω → A) (F : Bool → Ω → ℝ)
    (k s L a : ℝ) (hk : 0 < k) (hs : 1 ≤ s) (hL : 0 < L)
    (ha : a = alpha P B W) (ha0 : 0 < a)
    (hp : ∀ b, 1 / k ≤ prob P (fun ω => B ω = b))
    (hm : ∀ b, mean P (fun ω => Real.rpow |F b ω| s) ≤ Real.rpow k s)
    (hfac : ∀ b, ∃ f : A → ℝ, ∀ ω, F b ω = f (W ω)) :
    (∑ b, |cmean P (fun ω => B ω = b) (F b) - mean P (F b)|) ≤
      4*k*L*a + 2*k*Real.rpow k s*Real.rpow L (1-s) := by
  have hb (b : Bool) : |cmean P (fun ω => B ω = b) (F b) - mean P (F b)| ≤
      2*k*L*a + k*Real.rpow L (1-s)*Real.rpow k s := by
    obtain ⟨f, hf⟩ := hfac b
    let G : Ω → ℝ := fun ω => if |F b ω| < L then F b ω else 0
    let T : Ω → ℝ := fun ω => if |F b ω| < L then 0 else F b ω
    have hsplit : F b = fun ω => G ω + T ω := by
      funext ω
      dsimp [G, T]
      split_ifs <;> ring
    have hG : |cmean P (fun ω => B ω = b) G - mean P G| ≤ 2*k*L*a := by
      rw [ha]
      have he : G = fun ω => (if |f (W ω)| < L then f (W ω) else 0) := by
        funext ω
        simp only [G, hf]
      rw [he]
      apply t45_bounded_discrepancy P B W b
        (fun w => if |f w| < L then f w else 0) k L hk hL.le (hp b)
      intro w
      split_ifs with hw
      · exact hw.le
      · simpa using hL.le
    have hTmean : mean P (fun ω => |T ω|) ≤
        Real.rpow L (1-s)*Real.rpow k s := by
      calc
        _ ≤ mean P (fun ω => Real.rpow L (1-s)*Real.rpow |F b ω| s) := by
          unfold mean
          apply Finset.sum_le_sum
          intro ω _
          exact mul_le_mul_of_nonneg_left (t45_tail_pointwise (F b ω) s L hs hL)
            (P.nonneg ω)
        _ = Real.rpow L (1-s) * mean P (fun ω => Real.rpow |F b ω| s) :=
          mean_const_mul P _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hm b) (Real.rpow_nonneg hL.le _)
    have hT := (t45_tail_discrepancy P B b T k hk (hp b)).trans
      (mul_le_mul_of_nonneg_left hTmean hk.le)
    have hc : cmean P (fun ω => B ω = b) (F b) =
        cmean P (fun ω => B ω = b) G + cmean P (fun ω => B ω = b) T := by
      rw [hsplit]
      unfold cmean
      rw [← add_div, ← mean_add]
      congr 2
      funext ω
      by_cases hω : B ω = b <;> simp [hω]
    rw [hc, hsplit, mean_add]
    calc
      _ = |(cmean P (fun ω => B ω = b) G - mean P G) +
          (cmean P (fun ω => B ω = b) T - mean P T)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by nlinarith [hG, hT]
  rw [Fintype.sum_bool]
  have ht := hb true
  have hf := hb false
  linarith

/-- Optimize the explicit truncation level without excluding s = 1. -/
theorem t45_truncation_choice (k s a : ℝ) (hk : 0 < k) (hs : 1 ≤ s) (ha : 0 < a) :
    4*k*(k*Real.rpow a (-1/s))*a +
      2*k*Real.rpow k s*Real.rpow (k*Real.rpow a (-1/s)) (1-s) =
        6*k^2*Real.rpow a ((s-1)/s) := by
  have hs0 : s ≠ 0 := by linarith
  have h1 : Real.rpow a (-1/s) * a = Real.rpow a ((s-1)/s) := by
    simp only [Real.rpow_eq_pow]
    calc
      _ = a ^ (-1/s) * a ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = a ^ (-1/s + 1) := (Real.rpow_add ha _ _).symm
      _ = _ := by congr 1; field_simp; ring
  have h2 : Real.rpow k s * Real.rpow (k*Real.rpow a (-1/s)) (1-s) =
      k * Real.rpow a ((s-1)/s) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow hk.le (Real.rpow_nonneg ha.le _),
      ← Real.rpow_mul ha.le]
    rw [← mul_assoc, ← Real.rpow_add hk]
    have hex : s + (1-s) = 1 := by ring
    rw [hex, Real.rpow_one]
    congr 1
    congr 1
    field_simp
    ring
  calc
    _ = 4*k^2*(Real.rpow a (-1/s)*a) +
        2*k*(Real.rpow k s*Real.rpow (k*Real.rpow a (-1/s)) (1-s)) := by ring
    _ = _ := by rw [h1, h2]; ring

/-- Zero alpha annihilates the bias of every function of W. -/
theorem t45_zero_discrepancy {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (B : Ω → Bool) (W : Ω → A) (b : Bool) (f : A → ℝ)
    (hp : 0 < prob P (fun ω => B ω = b)) (ha : alpha P B W = 0) :
    cmean P (fun ω => B ω = b) (fun ω => f (W ω)) =
      mean P (fun ω => f (W ω)) := by
  have hl := t45_binary_fiber_l1 P B W b
  rw [ha, mul_zero] at hl
  have hz (w : A) : t45_delta P B W b w = 0 := by
    have hw : |t45_delta P B W b w| ≤ ∑ v, |t45_delta P B W b v| :=
      Finset.single_le_sum (fun v _ => abs_nonneg (t45_delta P B W b v)) (Finset.mem_univ w)
    exact abs_eq_zero.mp (le_antisymm (hw.trans hl) (abs_nonneg _))
  apply sub_eq_zero.mp
  rw [t45_discrepancy_fibers P B W b f hp]
  simp [hz]

/-- The finite estimand expansion uses potential outcomes on their own arms. -/
theorem t45_bias_estimand_expansion {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    |adse E-eate E| ≤
      (∑ i, ∑ b, |cmean E.design (fun z => z i = b) (potential E i b) -
        mean E.design (potential E i b)|) / (n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rw [adse, eate_finite_identity, ← sub_div, abs_div, abs_of_pos hnR]
  apply div_le_div_of_nonneg_right _ hnR.le
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(cmean E.design (fun z => z i = true) (E.outcome i) -
        cmean E.design (fun z => z i = false) (E.outcome i)) -
        (mean E.design (potential E i true)-mean E.design (potential E i false))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [Fintype.sum_bool, ← BernoulliCompletion.conditional_potential_eq_observed E i true,
        ← BernoulliCompletion.conditional_potential_eq_observed E i false]
      calc
        _ = |(cmean E.design (fun z => z i = true) (potential E i true) -
            mean E.design (potential E i true)) -
            (cmean E.design (fun z => z i = false) (potential E i false) -
            mean E.design (potential E i false))| := by congr 1; ring
        _ ≤ _ := abs_sub _ _

/-- T45: finite bias lemma A20. -/
theorem arbitrary_bias_finite_proof {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (k q s : ℝ) (hReg : Regular E k q s) :
    |adse E-eate E| ≤ 6*k^2*alphaInt E ((s-1)/s)/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  apply (t45_bias_estimand_expansion hn E).trans
  apply div_le_div_of_nonneg_right _ hnR.le
  rw [alphaInt, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let a := alpha E.design (fun z => z i) (maskedOthers E i)
  have hp (b : Bool) : 1/k ≤ prob E.design (fun z => z i = b) := by
    simpa only [one_div, marginal] using
      (BernoulliCompletion.regular_marginal_bounds E k q s hReg i b).1
  have hp0 (b : Bool) : 0 < prob E.design (fun z => z i = b) :=
    (one_div_pos.mpr hReg.1).trans_le (hp b)
  have hfac := t45_potential_mask_representation E i
  by_cases ha : a = 0
  · have hb (b : Bool) : cmean E.design (fun z => z i = b) (potential E i b) =
        mean E.design (potential E i b) := by
      obtain ⟨f, hf⟩ := hfac b
      have he : potential E i b = fun z => f (maskedOthers E i z) := funext hf
      rw [he]
      exact t45_zero_discrepancy E.design (fun z => z i) (maskedOthers E i) b f
        (hp0 b) ha
    simp only [hb, sub_self, abs_zero, Finset.sum_const_zero]
    change 0 ≤ 6*k^2*mixPower a ((s-1)/s)
    simp [mixPower, ha]
  · have ha0 : 0 < a := lt_of_le_of_ne
      (MixingBasics.alpha_nonnegative E.design (fun z => z i) (maskedOthers E i))
      (Ne.symm ha)
    have hL : 0 < k*Real.rpow a (-1/s) :=
      mul_pos hReg.1 (Real.rpow_pos_of_pos ha0 _)
    have hcore := t45_truncation_core E.design (fun z => z i) (maskedOthers E i)
      (potential E i) k s (k*Real.rpow a (-1/s)) a hReg.1 hReg.2.2.1 hL rfl ha0 hp
      (hReg.2.2.2.2.2 i) hfac
    rw [t45_truncation_choice k s a hReg.1 hReg.2.2.1 ha0] at hcore
    simpa only [mixPower, show alpha E.design (fun z => z i) (maskedOthers E i) = a from rfl,
      if_neg ha] using hcore

end
end AronowAudit.P009.Wave1
