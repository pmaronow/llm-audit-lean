import AronowAudit.P009.P009_CompleteConditional

/-! Finite complete-randomization bounds for P009-T42. -/

namespace AronowAudit.P009.Wave1

open scoped BigOperators
open Filter MeasureTheory Topology

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000

open BernoulliCompletion CompleteConditional

def complete_finite_match {n : ℕ} (H : Finset (Fin n))
    (w z : Assignment n) : Prop := ∀ j ∈ H, z j = w j

def complete_finite_count {n : ℕ} (H : Finset (Fin n))
    (w : Assignment n) (b : Bool) : ℝ :=
  ∑ j ∈ H, if w j = b then 1 else 0

def complete_finite_total (n m : ℕ) (b : Bool) : ℝ :=
  if b then (m : ℝ) else (n : ℝ) - m

lemma complete_finite_count_bounds {n : ℕ} (H : Finset (Fin n))
    (w : Assignment n) (b : Bool) :
    0 ≤ complete_finite_count H w b ∧ complete_finite_count H w b ≤ H.card := by
  constructor
  · exact Finset.sum_nonneg (fun j hj => by split_ifs <;> norm_num)
  · calc
      _ ≤ ∑ _j ∈ H, (1 : ℝ) := Finset.sum_le_sum (fun j hj => by split_ifs <;> norm_num)
      _ = _ := by simp

lemma complete_finite_count_partition {n : ℕ} (H : Finset (Fin n))
    (w : Assignment n) :
    complete_finite_count H w false = H.card - complete_finite_count H w true := by
  have h (j : Fin n) : (if w j = false then (1 : ℝ) else 0) =
      1 - (if w j = true then 1 else 0) := by cases w j <;> simp
  simp only [complete_finite_count, h, Finset.sum_sub_distrib]
  simp

lemma complete_finite_match_depends {n : ℕ} (H : Finset (Fin n)) (w : Assignment n) :
    DependsOn (fun z => if complete_finite_match H w z then (1 : ℝ) else 0) H := by
  intro z z' h
  have he : complete_finite_match H w z ↔ complete_finite_match H w z' := by
    unfold complete_finite_match
    constructor <;> intro hz j hj
    · rw [← h j hj]; exact hz j hj
    · rw [h j hj]; exact hz j hj
  simp only [he]

lemma complete_finite_weighted_count {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (H : Finset (Fin n)) (i : Fin n) (hi : i ∉ H)
    (F : Assignment n → ℝ) (hF : DependsOn F H) (b : Bool) :
    ((n : ℝ) - H.card) * mean E.design (fun z => (if z i = b then 1 else 0) * F z) =
      complete_finite_total n m b * mean E.design F -
        mean E.design (fun z => complete_finite_count H z b * F z) := by
  have ht := conditional_weighted_count E m hCR H i hi F hF
  have hc (z : Assignment n) : complete_finite_count H z true = ∑ j ∈ H, bit (z j) := by
    apply Finset.sum_congr rfl
    intro j hj
    cases z j <;> simp [bit]
  cases b
  · have hi' : (fun z => (if z i = false then (1 : ℝ) else 0) * F z) =
        (fun z => F z - bit (z i) * F z) := by
      funext z; cases z i <;> simp [bit]
    have hH : (fun z => complete_finite_count H z false * F z) =
        (fun z => (H.card : ℝ) * F z - (∑ j ∈ H, bit (z j)) * F z) := by
      funext z
      rw [complete_finite_count_partition, hc]
      ring
    rw [hi', hH, mean_sub, mean_sub, mean_const_mul]
    simp only [complete_finite_total, Bool.false_eq_true, ite_false]
    nlinarith only [ht]
  · simpa only [complete_finite_total, ite_true, hc, bit, Bool.ite_true_left] using ht

lemma complete_finite_event_step {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (H : Finset (Fin n)) (i : Fin n) (hi : i ∉ H)
    (A : Assignment n → Prop)
    (hA : DependsOn (fun z => if A z then (1 : ℝ) else 0) H)
    (b : Bool) (c : ℝ) (hc : ∀ z, A z → complete_finite_count H z b = c) :
    prob E.design (fun z => A z ∧ z i = b) =
      (complete_finite_total n m b - c) / ((n : ℝ) - H.card) * prob E.design A := by
  have hnH : (H.card : ℝ) < n := by
    have hh : H.card < n := by
      simpa using (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ H, by intro he; exact hi (he ▸ Finset.mem_univ i)⟩))
    exact_mod_cast hh
  have h := complete_finite_weighted_count E m hCR H i hi
    (fun z => if A z then 1 else 0) hA b
  have h1 : mean E.design (fun z => (if z i = b then 1 else 0) *
      (if A z then 1 else 0)) = prob E.design (fun z => A z ∧ z i = b) := by
    unfold prob
    congr 1
    funext z
    by_cases ha : A z <;> by_cases hz : z i = b <;> simp [ha, hz]
  have h2 : mean E.design (fun z => complete_finite_count H z b *
      (if A z then 1 else 0)) = c * prob E.design A := by
    unfold prob
    rw [← mean_const_mul]
    congr 1
    funext z
    by_cases ha : A z
    · simp [ha, hc z ha]
    · simp [ha]
  rw [h1, h2] at h
  change ((n : ℝ) - H.card) * prob E.design (fun z => A z ∧ z i = b) =
    complete_finite_total n m b * prob E.design A - c * prob E.design A at h
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (by linarith : (n : ℝ) - H.card ≠ 0)).mpr
  nlinarith only [h]

lemma complete_finite_pow_bound (a : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (ha : (a : ℝ) * x ≤ 1 / 2) :
    (1 + x)^a - 1 ≤ 2 * a * x := by
  have hgen : ∀ j : ℕ, (j : ℝ) * x ≤ 1 → (1 + x)^j * (1 - j * x) ≤ 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hj' : (j : ℝ) * x ≤ 1 := by push_cast at hj; nlinarith
      have hp : 0 ≤ (1 + x)^j := pow_nonneg (by linarith) _
      have hsq : 0 ≤ (1 + x)^j * ((j : ℝ) + 1) * x^2 := by positivity
      have hh := ih hj'
      rw [pow_succ]
      push_cast
      nlinarith only [hh, hsq]
  have hh := hgen a (by linarith)
  have hp : 1 ≤ (1 + x)^a := one_le_pow₀ (by linarith)
  have hm := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hp)
  nlinarith

lemma complete_finite_step_bounds (T B N M c : ℝ) (hT : 0 < T) (hB : 0 ≤ B)
    (hM : T / 2 ≤ M) (hN : T / 2 ≤ N - B)
    (hc : 0 ≤ c ∧ c ≤ B) (hcM : c ≤ M) :
    0 ≤ (M - c) / (N - B) ∧
      |(M - c) / (N - B) - M / N| ≤ (2 * B / T) * (M / N) := by
  have hN0 : 0 < N := by linarith
  have hNB : 0 < N - B := by linarith
  have hM0 : 0 < M := by linarith
  have hx : B / (N - B) ≤ 2 * B / T := by
    apply (div_le_div_iff₀ hNB hT).mpr
    nlinarith only [mul_nonneg hB (sub_nonneg.mpr hN)]
  have hxM : B ≤ (2 * B / T) * M := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hT).mpr
    nlinarith only [mul_nonneg hB (sub_nonneg.mpr hM)]
  refine ⟨div_nonneg (sub_nonneg.mpr hcM) hNB.le, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hl : (M - B) / N ≤ (M - c) / (N - B) := by
      calc
        _ ≤ (M - c) / N := div_le_div_of_nonneg_right (by linarith [hc.2]) hN0.le
        _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hcM) hNB (by linarith)
    have hh : B / N ≤ ((2 * B / T) * M) / N :=
      div_le_div_of_nonneg_right hxM hN0.le
    rw [sub_div] at hl
    rw [mul_div_assoc] at hh
    linarith
  · have hu : (M - c) / (N - B) ≤ M / (N - B) :=
      div_le_div_of_nonneg_right (by linarith [hc.1]) hNB.le
    have he : M / (N - B) = (1 + B / (N - B)) * (M / N) := by
      field_simp
      ring
    have hh := mul_le_mul_of_nonneg_right hx (div_nonneg hM0.le hN0.le)
    rw [he] at hu
    nlinarith only [hu, hh]

lemma complete_finite_match_count {n : ℕ} (H : Finset (Fin n)) (w z : Assignment n)
    (h : complete_finite_match H w z) (b : Bool) :
    complete_finite_count H z b = complete_finite_count H w b := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j hj]

lemma complete_finite_match_agree {n : ℕ} (H : Finset (Fin n)) (w z z' : Assignment n)
    (h : ∀ j ∈ H, z j = z' j) :
    complete_finite_match H w z ↔ complete_finite_match H w z' := by
  constructor <;> intro hz j hj
  · rw [← h j hj]; exact hz j hj
  · rw [h j hj]; exact hz j hj

lemma complete_finite_pattern_step {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (H : Finset (Fin n)) (i : Fin n) (hi : i ∉ H)
    (w : Assignment n) :
    prob E.design (complete_finite_match (insert i H) w) =
      (complete_finite_total n m (w i) - complete_finite_count H w (w i)) /
        ((n : ℝ) - H.card) * prob E.design (complete_finite_match H w) := by
  have he : (complete_finite_match (insert i H) w) =
      (fun z => complete_finite_match H w z ∧ z i = w i) := by
    funext z
    apply propext
    simp only [complete_finite_match, Finset.forall_mem_insert]
    exact and_comm
  rw [he]
  exact complete_finite_event_step E m hCR H i hi _
    (complete_finite_match_depends H w) (w i) _
    (fun z hz => complete_finite_match_count H w z hz (w i))

lemma complete_finite_joint_step {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (H K : Finset (Fin n)) (hd : Disjoint H K)
    (i : Fin n) (hi : i ∉ H) (hiK : i ∉ K) (w v : Assignment n) :
    prob E.design (fun z => complete_finite_match (insert i H) w z ∧
      complete_finite_match K v z) =
      (complete_finite_total n m (w i) - complete_finite_count H w (w i) -
        complete_finite_count K v (w i)) / ((n : ℝ) - H.card - K.card) *
      prob E.design (fun z => complete_finite_match H w z ∧ complete_finite_match K v z) := by
  let A := fun z => complete_finite_match H w z ∧ complete_finite_match K v z
  have hA : DependsOn (fun z => @ite ℝ (A z) (Classical.propDecidable _) 1 0)
      (↑(H ∪ K) : Set (Fin n)) := by
    intro z z' hh
    have hhH := complete_finite_match_agree H w z z'
      (fun j hj => hh j (Finset.mem_union_left K hj))
    have hhK := complete_finite_match_agree K v z z'
      (fun j hj => hh j (Finset.mem_union_right H hj))
    have hhA : A z ↔ A z' := and_congr hhH hhK
    by_cases hz : A z
    · simp only [ite_eq_left hz, ite_eq_left (hhA.mp hz)]
    · simp only [ite_eq_right hz, ite_eq_right (mt hhA.mpr hz)]
  have hc : ∀ z, A z → complete_finite_count (H ∪ K) z (w i) =
      complete_finite_count H w (w i) + complete_finite_count K v (w i) := by
    intro z hz
    rw [complete_finite_count, Finset.sum_union hd]
    change complete_finite_count H z (w i) + complete_finite_count K z (w i) = _
    rw [complete_finite_match_count H w z hz.1,
      complete_finite_match_count K v z hz.2]
  have he : (fun z => complete_finite_match (insert i H) w z ∧ complete_finite_match K v z) =
      (fun z => A z ∧ z i = w i) := by
    funext z
    apply propext
    simp only [A, complete_finite_match, Finset.forall_mem_insert]
    tauto
  rw [he, complete_finite_event_step E m hCR (H ∪ K) i
    (by simp [hi, hiK]) A hA (w i) _ hc, Finset.card_union_of_disjoint hd,
    Nat.cast_add]
  congr 2 <;> ring

/- The pattern estimate uses only the preceding permutation/count recursion.
   All intermediate masks use one common scalar x, so a geometric bound controls
   the relative error without enumerating fixed-size subsets. -/
lemma complete_finite_pattern_induction {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (T : ℝ) (hT : 0 < T) (hTm : T ≤ m) (hTc : T ≤ (n : ℝ) - m)
    (A : ℕ) (hA : 1 ≤ A) (K : Finset (Fin n)) (hK : 1 ≤ K.card)
    (hsmall : 4 * (A : ℝ) * K.card ≤ T)
    (H : Finset (Fin n)) (hH : H.card ≤ A) (hd : Disjoint H K) (w v : Assignment n) :
    |prob E.design (fun z => complete_finite_match H w z ∧ complete_finite_match K v z) -
      prob E.design (complete_finite_match H w) * prob E.design (complete_finite_match K v)| ≤
      ((1 + 2 * (K.card : ℝ) / T)^H.card - 1) *
        prob E.design (complete_finite_match H w) * prob E.design (complete_finite_match K v) := by
  induction H using Finset.induction_on with
  | empty =>
    have he : (fun z => complete_finite_match ∅ w z ∧ complete_finite_match K v z) =
        complete_finite_match K v := by funext z; apply propext; simp [complete_finite_match]
    have hp : prob E.design (complete_finite_match ∅ w) = 1 := by
      simp [complete_finite_match, prob, mean_const]
    rw [he, hp]
    simp only [Finset.card_empty, pow_zero, sub_self, one_mul, zero_mul, abs_zero, le_refl]
  | @insert i H hi ih =>
    have hH' : H.card ≤ A := by rw [Finset.card_insert_of_notMem hi] at hH; omega
    have hd' : Disjoint H K := (Finset.disjoint_insert_left.mp hd).2
    have hiK : i ∉ K := (Finset.disjoint_insert_left.mp hd).1
    have hIH := ih hH' hd'
    let x : ℝ := 2 * K.card / T
    let P := prob E.design (complete_finite_match H w)
    let Q := prob E.design (complete_finite_match K v)
    let J := prob E.design (fun z => complete_finite_match H w z ∧ complete_finite_match K v z)
    let M := complete_finite_total n m (w i) - complete_finite_count H w (w i)
    let N : ℝ := n - H.card
    let c := complete_finite_count K v (w i)
    let α := M / N
    let β := (M - c) / (N - K.card)
    have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
    have hKr : (1 : ℝ) ≤ K.card := by exact_mod_cast hK
    have hHr : (H.card : ℝ) ≤ A := by exact_mod_cast hH'
    have hAB1 : (A : ℝ) ≤ (A : ℝ) * K.card := le_mul_of_one_le_right (by positivity) hKr
    have hAB2 : (K.card : ℝ) ≤ (A : ℝ) * K.card := le_mul_of_one_le_left (by positivity) hAr
    have htotal : T ≤ complete_finite_total n m (w i) := by
      cases w i <;> simp only [complete_finite_total, Bool.false_eq_true, ite_false, ite_true]
      · exact hTc
      · exact hTm
    have hcH := complete_finite_count_bounds H w (w i)
    have hcK := complete_finite_count_bounds K v (w i)
    have hM : T / 2 ≤ M := by dsimp [M]; linarith
    have hN : T / 2 ≤ N - K.card := by dsimp [N]; linarith
    have hcM : c ≤ M := by dsimp [c, M]; linarith
    have hs := complete_finite_step_bounds T K.card N M c hT (by positivity) hM hN hcK hcM
    have hα : 0 ≤ α := div_nonneg (by linarith) (by dsimp [N] at *; linarith)
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hP : 0 ≤ P := probability_nonnegative _ _
    have hQ : 0 ≤ Q := probability_nonnegative _ _
    have hpow : 0 ≤ (1 + x)^H.card - 1 := sub_nonneg.mpr (one_le_pow₀ (by linarith))
    change |J - P * Q| ≤ ((1 + x)^H.card - 1) * P * Q at hIH
    rw [complete_finite_pattern_step E m hCR H i hi w,
      complete_finite_joint_step E m hCR H K hd' i hi hiK w v,
      Finset.card_insert_of_notMem hi, pow_succ]
    change |β * J - α * P * Q| ≤ ((1 + x)^H.card * (1 + x) - 1) * (α * P) * Q
    calc
      _ = |β * (J - P * Q) + (β - α) * (P * Q)| := by congr 1; ring
      _ ≤ |β * (J - P * Q)| + |(β - α) * (P * Q)| := abs_add_le _ _
      _ = β * |J - P * Q| + |β - α| * (P * Q) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs.1,
          abs_of_nonneg (mul_nonneg hP hQ)]
      _ ≤ β * (((1 + x)^H.card - 1) * P * Q) + (x * α) * (P * Q) :=
        add_le_add (mul_le_mul_of_nonneg_left hIH hs.1)
          (mul_le_mul_of_nonneg_right hs.2 (mul_nonneg hP hQ))
      _ ≤ ((1 + x) * α) * (((1 + x)^H.card - 1) * P * Q) + (x * α) * (P * Q) := by
        have hβ : β ≤ (1 + x) * α := by
          have hh := (le_abs_self (β - α)).trans hs.2
          dsimp [x] at *
          nlinarith only [hh]
        exact add_le_add (mul_le_mul_of_nonneg_right hβ
          (mul_nonneg (mul_nonneg hpow hP) hQ)) le_rfl
      _ = _ := by ring

lemma complete_finite_pattern_bound {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (T : ℝ) (hT : 0 < T) (hTm : T ≤ m) (hTc : T ≤ (n : ℝ) - m)
    (H K : Finset (Fin n)) (hH : 1 ≤ H.card) (hK : 1 ≤ K.card) (hd : Disjoint H K)
    (hsmall : 4 * (H.card : ℝ) * K.card ≤ T) (w v : Assignment n) :
    |prob E.design (fun z => complete_finite_match H w z ∧ complete_finite_match K v z) -
      prob E.design (complete_finite_match H w) * prob E.design (complete_finite_match K v)| ≤
      (4 * (H.card : ℝ) * K.card / T) *
        prob E.design (complete_finite_match H w) * prob E.design (complete_finite_match K v) := by
  have hh := complete_finite_pattern_induction E m hCR T hT hTm hTc H.card hH K hK
    hsmall H le_rfl hd w v
  have hx : 0 ≤ 2 * (K.card : ℝ) / T := by positivity
  have ha : (H.card : ℝ) * (2 * K.card / T) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hT).mpr
    linarith only [hsmall]
  have hp := complete_finite_pow_bound H.card _ hx ha
  calc
    _ ≤ ((1 + 2 * (K.card : ℝ) / T)^H.card - 1) *
        prob E.design (complete_finite_match H w) * prob E.design (complete_finite_match K v) := hh
    _ ≤ (2 * H.card * (2 * (K.card : ℝ) / T)) *
        prob E.design (complete_finite_match H w) * prob E.design (complete_finite_match K v) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (probability_nonnegative _ _)) (probability_nonnegative _ _)
    _ = _ := by ring

lemma complete_finite_mean_fibers {Ω U : Type*} [Fintype Ω] [Fintype U]
    (P : Law Ω) (X : Ω → U) (f : U → ℝ) :
    mean P (fun z => f (X z)) = ∑ u, prob P (fun z => X z = u) * f u := by
  classical
  have he (u : U) : prob P (fun z => X z = u) * f u =
      mean P (fun z => if X z = u then f u else 0) := by
    unfold prob mean
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases h : X z = u <;> simp [h]
  simp_rw [he]
  rw [← mean_sum]
  congr 1
  funext z
  simp [eq_comm]

lemma complete_finite_covariance_fibers {Ω U V : Type*}
    [Fintype Ω] [Fintype U] [Fintype V]
    (P : Law Ω) (X : Ω → U) (Y : Ω → V) (f : U → ℝ) (g : V → ℝ) :
    cov P (fun z => f (X z)) (fun z => g (Y z)) =
      ∑ u, ∑ v, (prob P (fun z => X z = u ∧ Y z = v) -
        prob P (fun z => X z = u) * prob P (fun z => Y z = v)) * f u * g v := by
  classical
  rw [covariance_product_formula]
  have hj := complete_finite_mean_fibers P (fun z => (X z, Y z))
    (fun p => f p.1 * g p.2)
  simp only [Fintype.sum_prod_type, Prod.mk.injEq] at hj
  rw [hj, complete_finite_mean_fibers P X f, complete_finite_mean_fibers P Y g,
    Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  ring

lemma complete_finite_covariance_relative {Ω U V : Type*}
    [Fintype Ω] [Fintype U] [Fintype V]
    (P : Law Ω) (X : Ω → U) (Y : Ω → V) (f : U → ℝ) (g : V → ℝ) (C : ℝ)
    (h : ∀ u v, |prob P (fun z => X z = u ∧ Y z = v) -
      prob P (fun z => X z = u) * prob P (fun z => Y z = v)| ≤
      C * prob P (fun z => X z = u) * prob P (fun z => Y z = v)) :
    |cov P (fun z => f (X z)) (fun z => g (Y z))| ≤
      C * mean P (fun z => |f (X z)|) * mean P (fun z => |g (Y z)|) := by
  classical
  rw [complete_finite_covariance_fibers]
  calc
    _ ≤ ∑ u, |∑ v, (prob P (fun z => X z = u ∧ Y z = v) -
        prob P (fun z => X z = u) * prob P (fun z => Y z = v)) * f u * g v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u, ∑ v, |(prob P (fun z => X z = u ∧ Y z = v) -
        prob P (fun z => X z = u) * prob P (fun z => Y z = v)) * f u * g v| :=
      Finset.sum_le_sum (fun u hu => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ u, ∑ v, (C * prob P (fun z => X z = u) * prob P (fun z => Y z = v)) *
        |f u| * |g v| := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (h u v) (abs_nonneg _)) (abs_nonneg _)
    _ = _ := by
      rw [complete_finite_mean_fibers P X (fun u => |f u|),
        complete_finite_mean_fibers P Y (fun v => |g v|)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      ring

def complete_finite_restrict {n : ℕ} (H : Finset (Fin n)) (z : Assignment n) : H → Bool :=
  fun j => z j

def complete_finite_extend {n : ℕ} (H : Finset (Fin n)) (u : H → Bool) : Assignment n :=
  fun j => if hj : j ∈ H then u ⟨j, hj⟩ else false

lemma complete_finite_fiber_match {n : ℕ} (H : Finset (Fin n)) (u : H → Bool)
    (z : Assignment n) :
    complete_finite_restrict H z = u ↔ complete_finite_match H (complete_finite_extend H u) z := by
  constructor
  · intro h j hj
    have hh := congrFun h ⟨j, hj⟩
    simpa [complete_finite_restrict, complete_finite_extend, hj] using hh
  · intro h
    funext j
    have hh := h j j.property
    simpa [complete_finite_restrict, complete_finite_extend, j.property] using hh

lemma complete_finite_reconstruct {n : ℕ} (H : Finset (Fin n))
    (F : Assignment n → ℝ) (hF : DependsOn F H) :
    F = fun z => F (complete_finite_extend H (complete_finite_restrict H z)) := by
  funext z
  apply hF
  intro j hj
  have hj' : j ∈ H := hj
  simp [complete_finite_extend, complete_finite_restrict, hj']

lemma complete_finite_disjoint_covariance {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (T : ℝ) (hT : 0 < T) (hTm : T ≤ m) (hTc : T ≤ (n : ℝ) - m)
    (H K : Finset (Fin n)) (hH : 1 ≤ H.card) (hK : 1 ≤ K.card) (hd : Disjoint H K)
    (hsmall : 4 * (H.card : ℝ) * K.card ≤ T)
    (F G : Assignment n → ℝ) (hF : DependsOn F H) (hG : DependsOn G K) :
    |cov E.design F G| ≤ (4 * (H.card : ℝ) * K.card / T) *
      mean E.design (fun z => |F z|) * mean E.design (fun z => |G z|) := by
  have hh := complete_finite_covariance_relative E.design
    (complete_finite_restrict H) (complete_finite_restrict K)
    (fun u => F (complete_finite_extend H u)) (fun v => G (complete_finite_extend K v))
    (4 * (H.card : ℝ) * K.card / T) (fun u v => by
      simpa only [complete_finite_fiber_match] using
        complete_finite_pattern_bound E m hCR T hT hTm hTc H K hH hK hd hsmall
          (complete_finite_extend H u) (complete_finite_extend K v))
  have hFp (z) := congrFun (complete_finite_reconstruct H F hF) z
  have hGp (z) := congrFun (complete_finite_reconstruct K G hG) z
  simpa only [← hFp, ← hGp] using hh

lemma complete_finite_arm_absolute_mean {n : ℕ} (E : Experiment n) (k q s : ℝ)
    (hReg : Regular E k q s) (i : Fin n) (b : Bool) :
    mean E.design (fun z => |armVariable E b 1 i z|) ≤ k := by
  calc
    _ ≤ mean E.design (fun z => |E.outcome i z|) := by
      apply mean_mono
      intro z
      by_cases hz : z i = b <;> simp [armVariable, hz]
    _ ≤ k := mean_abs_of_moment E.design _ k q hReg.1
      (by linarith [hReg.2.1]) (hReg.2.2.2.2.1 i)

lemma complete_finite_arm_covariance {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (k q s : ℝ) (hReg : Regular E k q s)
    (T : ℝ) (hT : 0 < T) (hTm : T ≤ m) (hTc : T ≤ (n : ℝ) - m)
    (i j : Fin n) (hij : ¬ Dependent E i j) (b : Bool) :
    |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
      4 * k^2 * (incoming E i : ℝ) * incoming E j / T := by
  have htriv : |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤ k^2 := by
    simpa only [show 2 * 1 = 2 by norm_num] using
      (corrected_moment_covariance E k q hReg.1 hReg.2.1 hReg.2.2.2.2.1
        1 (by simpa using hReg.2.1) i j b).2.2.2.2.2.2
  by_cases hs : 4 * (incoming E i : ℝ) * incoming E j ≤ T
  · let H := Finset.univ.filter (fun l => Interferes E l i)
    let K := Finset.univ.filter (fun l => Interferes E l j)
    have hd : Disjoint H K := by
      apply Finset.disjoint_left.mpr
      intro l hl hl'
      exact hij ⟨l, (Finset.mem_filter.mp hl).2, (Finset.mem_filter.mp hl').2⟩
    have hF : DependsOn (armVariable E b 1 i) (↑H : Set (Fin n)) := by
      intro z z' hh
      exact arm_dependsOn E i b 1 (fun l hl => hh l (by simpa [H] using hl))
    have hG : DependsOn (armVariable E b 1 j) (↑K : Set (Fin n)) := by
      intro z z' hh
      exact arm_dependsOn E j b 1 (fun l hl => hh l (by simpa [K] using hl))
    have hH : 1 ≤ H.card := CompleteMixing.incoming_positive E i
    have hK : 1 ≤ K.card := CompleteMixing.incoming_positive E j
    have hh := complete_finite_disjoint_covariance E m hCR T hT hTm hTc H K hH hK hd hs
      (armVariable E b 1 i) (armVariable E b 1 j) hF hG
    have hC : 0 ≤ 4 * (H.card : ℝ) * K.card / T := by positivity
    have hmean : 0 ≤ mean E.design (fun z => |armVariable E b 1 j z|) :=
      Finset.sum_nonneg (fun z hz => mul_nonneg (E.design.nonneg z) (abs_nonneg _))
    calc
      _ ≤ (4 * (H.card : ℝ) * K.card / T) *
          mean E.design (fun z => |armVariable E b 1 i z|) *
          mean E.design (fun z => |armVariable E b 1 j z|) := hh
      _ ≤ (4 * (H.card : ℝ) * K.card / T) * k *
          mean E.design (fun z => |armVariable E b 1 j z|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (complete_finite_arm_absolute_mean E k q s hReg i b) hC) hmean
      _ ≤ (4 * (H.card : ℝ) * K.card / T) * k * k :=
        mul_le_mul_of_nonneg_left (complete_finite_arm_absolute_mean E k q s hReg j b)
          (mul_nonneg hC hReg.1.le)
      _ = _ := by change (4 * (incoming E i : ℝ) * incoming E j / T) * k * k = _; ring
  · apply htriv.trans
    apply (le_div_iff₀ hT).mpr
    have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hs) (sq_nonneg k)
    nlinarith only [hh]

lemma complete_finite_arm_variance {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (m : ℕ) (hCR : Complete E m) (k q s : ℝ) (hReg : Regular E k q s)
    (T : ℝ) (hT : 0 < T) (hTm : T ≤ m) (hTc : T ≤ (n : ℝ) - m) (b : Bool) :
    var E.design (muHat E b) ≤ k^4 * dAvg E / (n : ℝ) + 4 * k^4 * C1 E^2 / T := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc (i j : Fin n) : |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
      d E i j * k^2 + 4 * k^2 * (incoming E i : ℝ) * incoming E j / T := by
    by_cases hij : Dependent E i j
    · have hh : |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤ k^2 := by
        simpa only [show 2 * 1 = 2 by norm_num] using
          (corrected_moment_covariance E k q hReg.1 hReg.2.1 hReg.2.2.2.2.1
            1 (by simpa using hReg.2.1) i j b).2.2.2.2.2.2
      simp only [d, ite_eq_left hij, one_mul]
      exact hh.trans (le_add_of_nonneg_right (by positivity))
    · simpa only [d, ite_eq_right hij, zero_mul, zero_add] using
        complete_finite_arm_covariance E m hCR k q s hReg T hT hTm hTc i j hij b
  have he : muHat E b = fun z => (∑ i, (marginal E i b)⁻¹ * armVariable E b 1 i z) / (n : ℝ) := by
    funext z
    simp only [muHat, armVariable, pow_one, div_eq_mul_inv]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, variance_div]
  have hw := weighted_variance_absolute E.design (armVariable E b 1)
    (fun i => (marginal E i b)⁻¹) k (fun i =>
      ⟨inv_pos.mpr (regular_marginal_bounds E k q s hReg i b).2.2.1,
        (regular_marginal_bounds E k q s hReg i b).2.2.2⟩)
  have hs : (∑ i, ∑ j, (d E i j * k^2 +
      4 * k^2 * (incoming E i : ℝ) * incoming E j / T)) =
      (∑ i, degree E i) * k^2 + (4 * k^2 / T) * (∑ i, (incoming E i : ℝ))^2 := by
    simp only [Finset.sum_add_distrib, degree, pow_two, Finset.sum_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    _ ≤ (k^2 * (∑ i, ∑ j, |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)|)) /
        (n : ℝ)^2 := div_le_div_of_nonneg_right hw.2 (sq_nonneg _)
    _ ≤ (k^2 * (∑ i, ∑ j, (d E i j * k^2 +
        4 * k^2 * (incoming E i : ℝ) * incoming E j / T))) / (n : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg k)
      exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hc i j))
    _ = _ := by
      rw [hs, MixingBasics.sum_incoming hn E]
      unfold dAvg
      field_simp

lemma complete_finite_potential_depends {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool) :
    DependsOn (potential E i b)
      (↑(Finset.univ.filter (fun j => j ≠ i ∧ Interferes E j i)) : Set (Fin n)) := by
  intro z z' hh
  apply outcome_dependsOn E i
  intro j hj
  by_cases hji : j = i
  · subst j; simp
  · have hj' : Interferes E j i := hj
    simpa only [Function.update_of_ne hji] using hh j (by simp [hji, hj'])

lemma complete_finite_unit_bias {n : ℕ} (hn : 0 < n) (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (k q s : ℝ) (hReg : Regular E k q s) (i : Fin n) (b : Bool) :
    |cmean E.design (fun z => z i = b) (potential E i b) - mean E.design (potential E i b)| ≤
      2 * k^2 * (incoming E i : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let H := Finset.univ.filter (fun j => j ≠ i ∧ Interferes E j i)
  have hi : i ∉ H := by simp [H]
  have hcard : H.card ≤ incoming E i := Finset.card_le_card (by
    intro j hj
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [hj.2])
  have hm := mean_abs_of_moment E.design (potential E i b) k s hReg.1 hReg.2.2.1
    (hReg.2.2.2.2.2 i b)
  have hp := regular_marginal_bounds E k q s hReg i b
  have hh := complete_conditional_mean_bound E m hCR H i hi (potential E i b)
    (complete_finite_potential_depends E i b) b hp.2.2.1
  calc
    _ ≤ (2 * (H.card : ℝ) / (n : ℝ)) * (marginal E i b)⁻¹ *
        mean E.design (fun z => |potential E i b z|) := hh
    _ ≤ (2 * (H.card : ℝ) / (n : ℝ)) * (marginal E i b)⁻¹ * k :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (by positivity) (inv_nonneg.mpr hp.2.2.1.le))
    _ ≤ (2 * (incoming E i : ℝ) / (n : ℝ)) * k * k := by
      apply mul_le_mul_of_nonneg_right _ hReg.1.le
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right (by exact_mod_cast (Nat.mul_le_mul_left 2 hcard)) hnR.le
      · exact hp.2.2.2
      · exact inv_nonneg.mpr hp.2.2.1.le
      · positivity
    _ = _ := by ring

lemma complete_finite_bias {n : ℕ} (hn : 0 < n) (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (k q s : ℝ) (hReg : Regular E k q s) :
    |adse E - eate E| ≤ 4 * k^3 * C1 E / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk2 := regular_k_ge_two hn E k q s hReg
  have hC : 0 ≤ C1 E := by
    have hh := MixingBasics.sum_incoming hn E
    have hh0 : 0 ≤ ∑ i, (incoming E i : ℝ) := Finset.sum_nonneg (fun i hi => by positivity)
    nlinarith
  have he : adse E - eate E = (∑ i,
      ((cmean E.design (fun z => z i = true) (potential E i true) -
        mean E.design (potential E i true)) -
      (cmean E.design (fun z => z i = false) (potential E i false) -
        mean E.design (potential E i false)))) / (n : ℝ) := by
    unfold adse
    simp_rw [← conditional_potential_eq_observed]
    rw [eate_finite_identity, ← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, abs_div, abs_of_pos hnR]
  calc
    _ ≤ (∑ i, |(cmean E.design (fun z => z i = true) (potential E i true) -
          mean E.design (potential E i true)) -
        (cmean E.design (fun z => z i = false) (potential E i false) -
          mean E.design (potential E i false))|) / (n : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hnR.le
    _ ≤ (∑ i, 4 * k^2 * (incoming E i : ℝ) / (n : ℝ)) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      apply Finset.sum_le_sum
      intro i hi
      have hh := abs_sub_le (cmean E.design (fun z => z i = true) (potential E i true) -
        mean E.design (potential E i true)) 0
        (cmean E.design (fun z => z i = false) (potential E i false) -
          mean E.design (potential E i false))
      simp only [sub_zero, zero_sub, abs_neg] at hh
      calc
        _ ≤ _ := hh
        _ ≤ 2 * k^2 * (incoming E i : ℝ) / n +
            2 * k^2 * (incoming E i : ℝ) / n :=
          add_le_add (complete_finite_unit_bias hn E m hCR k q s hReg i true)
            (complete_finite_unit_bias hn E m hCR k q s hReg i false)
        _ = _ := by ring
    _ = 4 * k^2 * C1 E / (n : ℝ) := by
      rw [← Finset.sum_div, ← Finset.mul_sum, MixingBasics.sum_incoming hn E]
      field_simp
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hnR.le
      have hh : k^2 ≤ k^3 := by nlinarith [sq_nonneg k, mul_nonneg (sq_nonneg k) (by linarith : 0 ≤ k - 1)]
      nlinarith only [mul_nonneg hC (sub_nonneg.mpr hh)]

lemma complete_finite_marginal {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (i : Fin n) (b : Bool) :
    marginal E i b = complete_finite_total n m b / n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (lt_trans hCR.1 hCR.2.1).ne'
  cases b
  · rw [complete_marginal_false E m hCR i]
    simp only [complete_finite_total, Bool.false_eq_true, ite_false]
    field_simp
  · exact complete_marginal_true E m hCR i

lemma complete_finite_min_overlap {n : ℕ} (hn : 0 < n) (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (k q s : ℝ) (hReg : Regular E k q s) :
    (n : ℝ) ≤ k * (min m (n - m) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h (b : Bool) : (n : ℝ) ≤ k * complete_finite_total n m b := by
    have hp := (regular_marginal_bounds E k q s hReg ⟨0, hn⟩ b).1
    rw [complete_finite_marginal E m hCR] at hp
    have hh := mul_le_mul_of_nonneg_left ((le_div_iff₀ hnR).mp hp) hReg.1.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hReg.1.ne', one_mul] using hh
  rcases le_total (m : ℝ) ((n : ℝ) - m) with hm | hm
  · simpa only [min_eq_left hm, complete_finite_total, ite_true] using h true
  · simpa only [min_eq_right hm,
      complete_finite_total, Bool.false_eq_true, ite_false] using h false

lemma complete_finite_variances {n : ℕ} (hn : 0 < n) (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (k q s : ℝ) (hReg : Regular E k q s) (b : Bool) :
    var E.design (muHat E b) ≤ k^4*dAvg E/(n:ℝ)+4*k^4*C1 E^2/(min m (n-m):ℝ) ∧
    var E.design (muHat E b) ≤ k^4*dAvg E/(n:ℝ)+4*k^5*C1 E^2/(n:ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hT : (0 : ℝ) < min (m : ℝ) ((n : ℝ) - m) :=
    lt_min (by exact_mod_cast hCR.1) (sub_pos.mpr (by exact_mod_cast hCR.2.1))
  have hTm : (min m (n-m) : ℝ) ≤ m := min_le_left _ _
  have hTc : (min m (n-m) : ℝ) ≤ (n : ℝ) - m := by
    exact min_le_right _ _
  have hh := complete_finite_arm_variance hn E m hCR k q s hReg _ hT hTm hTc b
  refine ⟨hh, hh.trans (add_le_add le_rfl ?_)⟩
  apply (div_le_div_iff₀ hT hnR).mpr
  have hmin := complete_finite_min_overlap hn E m hCR k q s hReg
  have hmul := mul_le_mul_of_nonneg_left hmin (show 0 ≤ 4*k^4*C1 E^2 by positivity)
  nlinarith only [hmul]

lemma complete_finite_supported_count {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (z : Assignment n) (hz : 0 < E.design.mass z) (b : Bool) :
    complete_finite_count Finset.univ z b = complete_finite_total n m b := by
  have ht : complete_finite_count Finset.univ z true = (m : ℝ) := by
    have hh := supported_treated_count E m hCR z hz
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    cases z i <;> simp [bit]
  cases b
  · rw [complete_finite_count_partition, ht]
    simp [complete_finite_total]
  · exact ht

lemma complete_finite_supported_nHat {n : ℕ} (hn : 0 < n) (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (z : Assignment n) (hz : 0 < E.design.mass z) (b : Bool) :
    nHat E b z = n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have htotal : complete_finite_total n m b ≠ 0 := by
    have hm : (0 : ℝ) < m := by exact_mod_cast hCR.1
    have hmn : (m : ℝ) < n := by exact_mod_cast hCR.2.1
    cases b <;> simp only [complete_finite_total, Bool.false_eq_true, ite_false, ite_true] <;> linarith
  unfold nHat
  simp_rw [complete_finite_marginal E m hCR]
  rw [← Finset.sum_div]
  change complete_finite_count Finset.univ z b / (complete_finite_total n m b / n) = n
  rw [complete_finite_supported_count E m hCR z hz b]
  field_simp

lemma complete_finite_supported_estimators {n : ℕ} (hn : 0 < n) (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (z : Assignment n) (hz : 0 < E.design.mass z) :
    nHat E true z = n ∧ nHat E false z = n ∧ ht E z = hajek E z := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ht' := complete_finite_supported_nHat hn E m hCR z hz true
  have hf' := complete_finite_supported_nHat hn E m hCR z hz false
  have hnon : ArmsNonempty E z := by simp only [ArmsNonempty, ht', hf', ne_eq, hnR, not_false_eq_true, and_self]
  refine ⟨ht', hf', ?_⟩
  rw [hajek, ite_eq_left hnon, ht', hf']
  unfold ht
  field_simp

theorem complete_finite_lemmas_proof {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (m : ℕ) (hCR : Complete E m) (k q s : ℝ) (hReg : Regular E k q s) :
    (∑ i, (incoming E i:ℝ))/(n:ℝ) = C1 E ∧
    |adse E-eate E| ≤ 4*k^3*C1 E/(n:ℝ) ∧
    (∀ b, var E.design (muHat E b) ≤
      k^4*dAvg E/(n:ℝ)+4*k^4*C1 E^2/(min m (n-m):ℝ) ∧
      var E.design (muHat E b) ≤ k^4*dAvg E/(n:ℝ)+4*k^5*C1 E^2/(n:ℝ)) ∧
    (∀ z, 0 < E.design.mass z → nHat E true z = n ∧ nHat E false z = n ∧
      ht E z = hajek E z) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨?_, complete_finite_bias hn E m hCR k q s hReg,
    complete_finite_variances hn E m hCR k q s hReg,
    fun z hz => complete_finite_supported_estimators hn E m hCR z hz⟩
  rw [MixingBasics.sum_incoming hn E]
  field_simp

end
end AronowAudit.P009.Wave1
