import AronowAudit.P002.Wave1.Gap.GLP0022B2
import AronowAudit.P002.Wave1.Gap.GLP0021B2
import AronowAudit.P002.Wave1.Gap.GP0022B3
import AronowAudit.P002.Wave1.E61Eigenvalue.N6
import AronowAudit.P002.Wave1.E61Eigenvalue.N11

/-!
Regression bounds for P002-T5, corrected Theorem 2.

A finite, uniform Gram concentration bound gives an event controlling the quadratic form
for every coefficient vector and both arms at once. This event controls fitted
coefficients and residual sums of squares.
All probabilities below are the actual complete-randomization probabilities.
-/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

lemma T2C_probability_mono {n} (P : Population n)
    {E F : Finset (Fin n) → Prop} (h : ∀ S ∈ assignments P, E S → F S) :
    probability P E ≤ probability P F := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (assignments P).filter E ⊆
    (assignments P).filter F from fun S hS =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS).1,
        h S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2⟩)

lemma T2C_probability_congr {n} (P : Population n)
    {E F : Finset (Fin n) → Prop} (h : ∀ S ∈ assignments P, E S ↔ F S) :
    probability P E = probability P F :=
  le_antisymm (T2C_probability_mono P (fun S hS => (h S hS).mp))
    (T2C_probability_mono P (fun S hS => (h S hS).mpr))

lemma T2C_expectation_sum {n} {ι : Type*} [Fintype ι] (P : Population n)
    (f : ι → Finset (Fin n) → ℝ) :
    expectation P (fun S => ∑ i, f i S) = ∑ i, expectation P (f i) := by
  simp only [expectation, Finset.sum_div]
  congr 1
  exact Finset.sum_comm

lemma T2C_probability_exists {n} {ι : Type*} [Fintype ι] (P : Population n)
    (E : ι → Finset (Fin n) → Prop) :
    probability P (fun S => ∃ i, E i S) ≤ ∑ i, probability P (E i) := by
  simp only [DecisionLemma12_probability_eq_expectation]
  rw [← T2C_expectation_sum]
  apply DecisionLemma12_expectation_mono
  intro S hS
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    exact (by simp only [hi, ite_true] : (1 : ℝ) = if E i S then 1 else 0).le.trans
      (Finset.single_le_sum (f := fun i => if E i S then (1 : ℝ) else 0)
        (fun i _ => by positivity) (Finset.mem_univ i))
  · exact Finset.sum_nonneg fun i _ => by positivity

lemma T2C_popVar_bound {n} (hn : 2 ≤ n) (q : Fin n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hq : mean (fun i => q i ^ 2) ≤ M) : popVar q ≤ 2*M := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  unfold popVar
  rw [DecisionLemma12_sum_centered_sq (by omega)]
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < n-1)).mpr
  have hsum := (div_le_iff₀ hn0).mp hq
  nlinarith [mul_nonneg hn0.le (sq_nonneg (mean q)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ n-2) hM]

lemma T2C_arm_size {n} (P : Population n) (r : ℝ)
    (hl : r*n ≤ (P.n1 : ℝ)) (hu : (P.n1 : ℝ) ≤ (1-r)*n) (a : Bool) :
    r*n ≤ (if a then (P.n1 : ℝ) else controlSize P) := by
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte, controlSize] <;> linarith

/-- The scalar finite-sampling estimate used for both Gram entries and scores. -/
lemma T2C_arm_mse {n} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (hc : 2 ≤ n-P.n1) (r M : ℝ) (hr : 0 < r)
    (hl : r*n ≤ (P.n1 : ℝ)) (hu : (P.n1 : ℝ) ≤ (1-r)*n)
    (q : Fin n → ℝ) (hM : 0 ≤ M) (hq : mean (fun i => q i^2) ≤ M) (a : Bool) :
    expectation P (fun S => (armMean q S a-mean q)^2) ≤ 2*M/(r*n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hP.1; omega : 0 < n)
  have hs := T2C_arm_size P r hl hu a
  have hpos := (mul_pos hr hn).trans_le hs
  calc
    _ ≤ popVar q/(if a then (P.n1 : ℝ) else controlSize P) :=
      DecisionLemma12_mse_arm P hP hm hc q a
    _ ≤ (2*M)/(if a then (P.n1 : ℝ) else controlSize P) :=
      div_le_div_of_nonneg_right (T2C_popVar_bound hP.1 q M hM hq) hpos.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos hr hn) hs

lemma T2C_arm_tail {n} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (hc : 2 ≤ n-P.n1) (r M τ : ℝ) (hr : 0 < r)
    (hl : r*n ≤ (P.n1 : ℝ)) (hu : (P.n1 : ℝ) ≤ (1-r)*n)
    (q : Fin n → ℝ) (hM : 0 ≤ M) (hq : mean (fun i => q i^2) ≤ M)
    (hτ : 0 < τ) (a : Bool) :
    probability P (fun S => τ ≤ |armMean q S a-mean q|) ≤ 2*M/(r*n*τ^2) := by
  have h := DecisionLemma12_markov P (fun S => τ ≤ |armMean q S a-mean q|)
    (fun S => (armMean q S a-mean q)^2) (τ^2)
    (fun _ _ => sq_nonneg _) (fun S _ hS => by nlinarith [sq_abs (armMean q S a-mean q)])
  rw [← div_div]
  apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
  calc
    _ = τ^2 * probability P (fun S => τ ≤ |armMean q S a-mean q|) := mul_comm _ _
    _ ≤ expectation P (fun S => (armMean q S a-mean q)^2) := h
    _ ≤ 2*M/(r*n) := T2C_arm_mse P hP hm hc r M hr hl hu q hM hq a

/-- Covariate-only assumptions, so the same lemmas apply to fixed responses. -/
def T2C_covariates {n k} (x : Fin n → Fin k → ℝ) (e A : ℝ) : Prop :=
  (∀ s, ∑ i, x i s = 0) ∧
  (∀ s, mean (fun i => x i s^4) ≤ A) ∧
  (∀ b : Fin k → ℝ, e*normSq b ≤ mean (fun i => (dotProduct (x i) b)^2))

lemma T2C_augmented_fourth {n k} (x : Fin n → Fin k → ℝ) (hn : 0 < n)
    (A : ℝ) (hx : ∀ s, mean (fun i => x i s^4) ≤ A) (s : Option (Fin k)) :
    mean (fun i => augmented x i s^4) ≤ max 1 A := by
  cases s with
  | none => simpa [mean, augmented, (by exact_mod_cast Nat.ne_of_gt hn : (n : ℝ) ≠ 0)]
      using le_max_left (1 : ℝ) A
  | some s => exact (hx s).trans (le_max_right _ _)

lemma T2C_entry_second {n k} (x : Fin n → Fin k → ℝ) (hn : 0 < n)
    (A : ℝ) (hx : ∀ s, mean (fun i => x i s^4) ≤ A) (s t : Option (Fin k)) :
    mean (fun i => (augmented x i s*augmented x i t)^2) ≤ max 1 A := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := (div_le_iff₀ hnR).mp (T2C_augmented_fourth x hn A hx s)
  have ht := (div_le_iff₀ hnR).mp (T2C_augmented_fourth x hn A hx t)
  have hpoint : 2*(∑ i, (augmented x i s*augmented x i t)^2) ≤
      (∑ i, augmented x i s^4)+(∑ i, augmented x i t^4) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      nlinarith [sq_nonneg (augmented x i s^2-augmented x i t^2)]
  exact (div_le_iff₀ hnR).mpr (by nlinarith)

/-- A common coercivity event for both fitted arm Gram matrices. -/
def T2C_gramGood {n k} (x : Fin n → Fin k → ℝ) (e : ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ (a : Bool) (b : Option (Fin k) → ℝ),
    (min 1 e/2)*normSq b ≤ dotProduct b (gram x (if a then S else Sᶜ) *ᵥ b)

lemma T2C_gramGood_of_entries {n k} (x : Fin n → Fin k → ℝ) (e A : ℝ)
    (hn : 0 < n) (hx : T2C_covariates x e A) (S : Finset (Fin n))
    (hentry : ∀ (a : Bool) (s t : Option (Fin k)),
      |gram x (if a then S else Sᶜ) s t-gram x Finset.univ s t| ≤
        min 1 e/(2*((k : ℝ)+1))) : T2C_gramGood x e S := by
  intro a b
  have hpop := (corrected_augmented_gram x hn e hx.1 hx.2.2).2.2.2 b
  have hg : groupMean Finset.univ (fun i => (dotProduct (augmented x i) b)^2) =
      mean (fun i => (dotProduct (augmented x i) b)^2) := by simp [groupMean, mean]
  rw [← hg, ← gram_quadratic] at hpop
  have herr := E61Eigenvalue.n11_proof k (gram x (if a then S else Sᶜ))
    (gram x Finset.univ) (min 1 e/(2*((k : ℝ)+1))) (hentry a) b
  have hd : (k : ℝ)+1 ≠ 0 := by positivity
  have heq : ((k : ℝ)+1)*(min 1 e/(2*((k : ℝ)+1))) = min 1 e/2 := by
    field_simp; <;> ring
  rw [heq] at herr
  linarith [neg_abs_le (dotProduct b (gram x (if a then S else Sᶜ) *ᵥ b)-
    dotProduct b (gram x Finset.univ *ᵥ b))]

/-- An explicit O(1/n) bound, uniform in the response and both arms. -/
theorem T2C_gram_bad_bound {n k} (P : CovPopulation n k) (e A r : ℝ)
    (hP : ValidDesign P.pop) (hm : 2 ≤ P.pop.n1) (hc : 2 ≤ n-P.pop.n1)
    (he : 0 < e) (hr : 0 < r) (hl : r*n ≤ (P.pop.n1 : ℝ))
    (hu : (P.pop.n1 : ℝ) ≤ (1-r)*n) (hx : T2C_covariates P.x e A) :
    probability P.pop (fun S => ¬ T2C_gramGood P.x e S) ≤
      (2*((k : ℝ)+1)^2) *
        (2*max 1 A/(r*n*(min 1 e/(2*((k : ℝ)+1)))^2)) := by
  let τ : ℝ := min 1 e/(2*((k : ℝ)+1))
  have hτ : 0 < τ := div_pos (lt_min zero_lt_one he) (by positivity)
  have hn : 0 < n := by have := hP.1; omega
  let E : (Bool × Option (Fin k) × Option (Fin k)) → Finset (Fin n) → Prop :=
    fun z S => τ ≤ |gram P.x (if z.1 then S else Sᶜ) z.2.1 z.2.2-
      gram P.x Finset.univ z.2.1 z.2.2|
  have hbad : probability P.pop (fun S => ¬ T2C_gramGood P.x e S) ≤
      probability P.pop (fun S => ∃ z, E z S) := by
    apply T2C_probability_mono
    intro S hS hnot
    by_contra hnone
    apply hnot
    apply T2C_gramGood_of_entries P.x e A hn hx S
    intro a s t
    exact (lt_of_not_ge (fun h => hnone ⟨(a,s,t),h⟩)).le
  have htail (z : Bool × Option (Fin k) × Option (Fin k)) :
      probability P.pop (E z) ≤ 2*max 1 A/(r*n*τ^2) := by
    have h := T2C_arm_tail P.pop hP hm hc r (max 1 A) τ hr hl hu
      (fun i => augmented P.x i z.2.1*augmented P.x i z.2.2)
      (zero_le_one.trans (le_max_left _ _))
      (T2C_entry_second P.x hn A hx.2.1 z.2.1 z.2.2) hτ z.1
    simpa only [E, gram, armMean, groupMean, mean, Finset.card_univ,
      Fintype.card_fin] using h
  calc
    _ ≤ probability P.pop (fun S => ∃ z, E z S) := hbad
    _ ≤ ∑ z, probability P.pop (E z) := T2C_probability_exists P.pop E
    _ ≤ ∑ _z : Bool × Option (Fin k) × Option (Fin k), 2*max 1 A/(r*n*τ^2) :=
      Finset.sum_le_sum fun z _ => htail z
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_bool, Fintype.card_option, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      dsimp [τ]
      ring

/-- Gram concentration along growing arrays; arm sizes one are harmless finite initial rows. -/
theorem T2C_gram_bad_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (e A r : ℝ)
    (he : 0 < e) (hr : 0 < r) (hP : ∀ j, ValidDesign (P j).pop)
    (hl : ∀ j, r*sizes j ≤ ((P j).pop.n1 : ℝ))
    (hu : ∀ j, ((P j).pop.n1 : ℝ) ≤ (1-r)*sizes j)
    (hx : ∀ j, T2C_covariates (P j).x e A) :
    Tendsto (fun j => probability (P j).pop (fun S => ¬ T2C_gramGood (P j).x e S))
      atTop (nhds 0) := by
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hbound : Tendsto (fun j => (2*((k : ℝ)+1)^2) *
      (2*max 1 A/(r*sizes j*(min 1 e/(2*((k : ℝ)+1)))^2))) atTop (nhds 0) := by
    have h := (tendsto_const_nhds.div_atTop hN :
      Tendsto (fun j => ((2*((k : ℝ)+1)^2)*(2*max 1 A)/
        (r*(min 1 e/(2*((k : ℝ)+1)))^2))/(sizes j : ℝ)) atTop (nhds 0))
    convert h using 1 <;> funext j <;> ring
  apply squeeze_zero' (Eventually.of_forall fun _ =>
    DecisionLemma12_probability_nonneg _ _) _ hbound
  filter_upwards [(hN.const_mul_atTop hr).eventually_ge_atTop 2] with j hj
  have hm : 2 ≤ (P j).pop.n1 := by exact_mod_cast hj.trans (hl j)
  have hc : 2 ≤ sizes j-(P j).pop.n1 := by
    have hh : (2 : ℝ) ≤ ((sizes j-(P j).pop.n1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (hP j).2.2.le]
      linarith [hu j]
    exact_mod_cast hh
  exact T2C_gram_bad_bound (P j) e A r (hP j) hm hc he hr (hl j) (hu j) (hx j)

lemma T2C_normSq_nonneg {ι : Type*} [Fintype ι] (b : ι → ℝ) : 0 ≤ normSq b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma T2C_normSq_eq_zero {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    normSq b = 0 ↔ b = 0 := by
  constructor
  · intro h
    funext i
    have hi := Finset.single_le_sum (f := fun j => b j^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    change b i = 0
    rw [show (∑ j, b j^2) = 0 from h] at hi
    nlinarith [sq_nonneg (b i)]
  · rintro rfl
    simp [normSq]

/-- Coercivity gives full rank without choosing an eigenbasis. -/
lemma T2C_coercive_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hM : ∀ b, c*normSq b ≤ dotProduct b (M *ᵥ b)) : M.det ≠ 0 := by
  apply (Matrix.isUnit_iff_isUnit_det M).mp _ |>.ne_zero
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro b d hbd
  have hz : M *ᵥ (b-d) = 0 := by rw [Matrix.mulVec_sub, hbd, sub_self]
  have h := hM (b-d)
  rw [hz, dotProduct_zero] at h
  have hn : normSq (b-d) = 0 := by
    have := T2C_normSq_nonneg (b-d)
    nlinarith
  exact sub_eq_zero.mp ((T2C_normSq_eq_zero _).mp hn)

/-- Bounded inverse and bounded projection energy, by completing squares. -/
lemma T2C_inverse_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hM : ∀ b, c*normSq b ≤ dotProduct b (M *ᵥ b)) (h : ι → ℝ) :
    0 ≤ dotProduct h (M⁻¹ *ᵥ h) ∧
    normSq (M⁻¹ *ᵥ h) ≤ normSq h/c^2 ∧
    dotProduct h (M⁻¹ *ᵥ h) ≤ normSq h/c := by
  let b := M⁻¹ *ᵥ h
  have hdet := T2C_coercive_det M c hc hM
  have hMb : M *ᵥ b = h := by
    dsimp [b]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hb := hM b
  rw [hMb] at hb
  have hnorm := T2C_normSq_nonneg b
  have hquad : 0 ≤ normSq h-2*c*dotProduct b h+c^2*normSq b := by
    have hpos := T2C_normSq_nonneg (fun i => h i-c*b i)
    have heq : normSq (fun i => h i-c*b i) =
        normSq h-2*c*dotProduct b h+c^2*normSq b := by
      dsimp only [normSq, dotProduct]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rwa [heq] at hpos
  have hmul := mul_le_mul_of_nonneg_left hb hc.le
  have henergy : c*dotProduct b h ≤ normSq h := by nlinarith
  have hnormbound : c^2*normSq b ≤ normSq h := by nlinarith
  rw [dotProduct_comm h b]
  exact ⟨(mul_nonneg hc.le hnorm).trans hb,
    (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith),
    (le_div_iff₀ hc).mpr (by nlinarith)⟩

lemma T2C_population_coercive {n k} (x : Fin n → Fin k → ℝ) (e A : ℝ)
    (hn : 0 < n) (hx : T2C_covariates x e A) (b : Option (Fin k) → ℝ) :
    min 1 e*normSq b ≤ dotProduct b (gram x Finset.univ *ᵥ b) := by
  rw [gram_quadratic]
  simpa only [groupMean, mean, Finset.card_univ, Fintype.card_fin] using
    (corrected_augmented_gram x hn e hx.1 hx.2.2).2.2.2 b

lemma T2C_population_det {n k} (x : Fin n → Fin k → ℝ) (e A : ℝ)
    (hn : 0 < n) (he : 0 < e) (hx : T2C_covariates x e A) :
    (gram x Finset.univ).det ≠ 0 :=
  T2C_coercive_det _ _ (lt_min zero_lt_one he) (T2C_population_coercive x e A hn hx)

lemma T2C_population_score_zero {n k} (x : Fin n → Fin k → ℝ)
    (q : Fin n → ℝ) (hG : (gram x Finset.univ).det ≠ 0) :
    score x Finset.univ (fun i => q i-dotProduct (augmented x i) (ols x Finset.univ q)) = 0 := by
  rw [score_residual, ols_normal_equations _ _ _ hG, sub_self]

lemma T2C_score_centered {n k} (x : Fin n → Fin k → ℝ) (q : Fin n → ℝ)
    (hq : score x Finset.univ q = 0) (s : Option (Fin k)) :
    mean (fun i => augmented x i s*q i) = 0 := by
  simpa only [score, groupMean, mean, Finset.card_univ, Fintype.card_fin,
    Pi.zero_apply] using congrFun hq s

lemma T2C_residual_centered {n k} (x : Fin n → Fin k → ℝ) (q : Fin n → ℝ)
    (hq : score x Finset.univ q = 0) : mean q = 0 := by
  simpa only [augmented, one_mul] using T2C_score_centered x q hq none

/-- Mixed second moments are controlled even when outcome scales vary with n. -/
lemma T2C_product_second {n} (hn : 0 < n) (u q : Fin n → ℝ)
    (H M K : ℝ) (hH : 0 < H) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hu : mean (fun i => u i^4) ≤ M) (hq : mean (fun i => q i^4) ≤ K*H^2) :
    mean (fun i => (u i*q i)^2) ≤ (M+K)*H := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hu' := (div_le_iff₀ hnR).mp hu
  have hq' := (div_le_iff₀ hnR).mp hq
  have hpoint : 2*H*(∑ i, (u i*q i)^2) ≤ H^2*(∑ i, u i^4)+(∑ i, q i^4) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (H*u i^2-q i^2)]
  have hhu := mul_le_mul_of_nonneg_left hu' (sq_nonneg H)
  apply (div_le_iff₀ hnR).mpr
  have haux : (∑ i, (u i*q i)^2) ≤ (M+K)*H*n/2 := by nlinarith
  have hpos : 0 ≤ (M+K)*H*n := by positivity
  linarith

/-- The score estimate, with constants depending only on covariates/kurtosis. -/
theorem T2C_score_mse {n k} (P : CovPopulation n k) (e A r H K : ℝ)
    (hP : ValidDesign P.pop) (hm : 2 ≤ P.pop.n1) (hc : 2 ≤ n-P.pop.n1)
    (hr : 0 < r) (hH : 0 < H) (hK : 0 ≤ K)
    (hl : r*n ≤ (P.pop.n1 : ℝ)) (hu : (P.pop.n1 : ℝ) ≤ (1-r)*n)
    (hx : T2C_covariates P.x e A) (q : Fin n → ℝ)
    (hq0 : score P.x Finset.univ q = 0) (hq4 : mean (fun i => q i^4) ≤ K*H^2)
    (a : Bool) :
    expectation P.pop (fun S => normSq (score P.x (if a then S else Sᶜ) q)) ≤
      ((k : ℝ)+1)*2*(max 1 A+K)*H/(r*n) := by
  have hn : 0 < n := by have := hP.1; omega
  have hM : 0 ≤ max 1 A := zero_le_one.trans (le_max_left _ _)
  change expectation P.pop (fun S => ∑ s, (score P.x (if a then S else Sᶜ) q s)^2) ≤ _
  rw [T2C_expectation_sum]
  calc
    _ ≤ ∑ _s : Option (Fin k), 2*((max 1 A+K)*H)/(r*n) := by
      apply Finset.sum_le_sum
      intro s _
      have hh := T2C_arm_mse P.pop hP hm hc r ((max 1 A+K)*H) hr hl hu
        (fun i => augmented P.x i s*q i) (by positivity)
        (T2C_product_second hn _ _ H (max 1 A) K hH hM hK
          (T2C_augmented_fourth P.x hn A hx.2.1 s) hq4) a
      simp_rw [T2C_score_centered P.x q hq0 s, sub_zero] at hh
      exact hh
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

lemma T2C_probability_union {n} (P : Population n) (E F : Finset (Fin n) → Prop) :
    probability P (fun S => E S ∨ F S) ≤ probability P E+probability P F := by
  simp only [DecisionLemma12_probability_eq_expectation]
  rw [← DecisionLemma12_expectation_add]
  apply DecisionLemma12_expectation_mono
  intro S hS
  by_cases hE : E S <;> by_cases hF : F S <;> simp [hE, hF]

lemma T2C_markov_bound {n} (P : Population n) (X : Finset (Fin n) → ℝ) (t : ℝ)
    (ht : 0 < t) (hX : ∀ S ∈ assignments P, 0 ≤ X S) :
    probability P (fun S => t ≤ X S) ≤ expectation P X/t := by
  apply (le_div_iff₀ ht).mpr
  simpa only [mul_comm] using DecisionLemma12_markov P (fun S => t ≤ X S) X t
    hX (fun S hS h => h)

/-- Product errors require only separate second-moment bounds, not independence. -/
lemma T2C_product_tail {n} (P : Population n) (G : Finset (Fin n) → Prop)
    (D X Y : Finset (Fin n) → ℝ) (L η s : ℝ) (hL : 0 < L) (hη : 0 < η) (hs : 0 < s)
    (hX : ∀ S ∈ assignments P, 0 ≤ X S) (hY : ∀ S ∈ assignments P, 0 ≤ Y S)
    (hD : ∀ S ∈ assignments P, G S → D S^2 ≤ X S*Y S) :
    probability P (fun S => G S ∧ η*Real.sqrt L ≤ |D S|) ≤
      expectation P X/s+expectation P Y/(η^2*L/s) := by
  have ht : 0 < η^2*L/s := by positivity
  calc
    _ ≤ probability P (fun S => s ≤ X S ∨ η^2*L/s ≤ Y S) := by
      apply T2C_probability_mono
      intro S hS h
      by_contra hnot
      have hx : X S < s := lt_of_not_ge (fun hx => hnot (Or.inl hx))
      have hy : Y S < η^2*L/s := lt_of_not_ge (fun hy => hnot (Or.inr hy))
      have hxy : X S*Y S < η^2*L := by
        calc
          _ ≤ s*Y S := mul_le_mul_of_nonneg_right hx.le (hY S hS)
          _ < s*(η^2*L/s) := mul_lt_mul_of_pos_left hy hs
          _ = _ := by field_simp; <;> ring
      have hsq := (sq_le_sq₀ (by positivity : 0 ≤ η*Real.sqrt L) (abs_nonneg _)).mpr h.2
      rw [mul_pow, Real.sq_sqrt hL.le, sq_abs] at hsq
      linarith [hD S hS h.1]
    _ ≤ probability P (fun S => s ≤ X S)+probability P (fun S => η^2*L/s ≤ Y S) :=
      T2C_probability_union _ _ _
    _ ≤ _ := add_le_add (T2C_markov_bound P X s hs hX)
      (T2C_markov_bound P Y _ ht hY)

lemma T2C_dot_sq {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (dotProduct a b)^2 ≤ normSq a*normSq b :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b

lemma T2C_gramGood_det {n k} (x : Fin n → Fin k → ℝ) (e : ℝ) (he : 0 < e)
    (S : Finset (Fin n)) (hS : T2C_gramGood x e S) (a : Bool) :
    (gram x (if a then S else Sᶜ)).det ≠ 0 :=
  T2C_coercive_det _ _ (by positivity : 0 < min 1 e/2) (hS a)


lemma T2C_xmean_mse {n k} (P : CovPopulation n k) (e A r : ℝ)
    (hP : ValidDesign P.pop) (hm : 2 ≤ P.pop.n1) (hc : 2 ≤ n-P.pop.n1)
    (hr : 0 < r) (hl : r*n ≤ (P.pop.n1 : ℝ)) (hu : (P.pop.n1 : ℝ) ≤ (1-r)*n)
    (hx : T2C_covariates P.x e A) (a : Bool) :
    expectation P.pop (fun S => normSq (fun s =>
      armMean (fun i => xCirc P.x i s) S a)) ≤
      ((k : ℝ)+1)*2*(1+max 1 A)/(r*n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hP.1; omega : 0 < n)
  have hzero (s : Option (Fin k)) : mean (fun i => xCirc P.x i s) = 0 := by
    cases s with
    | none => simp [mean, xCirc]
    | some s => simp [mean, xCirc, hx.1 s]
  have hsecond (s : Option (Fin k)) : mean (fun i => xCirc P.x i s^2) ≤ 1+max 1 A := by
    cases s with
    | none => simp only [xCirc, zero_pow (by decide : 2 ≠ 0), mean, Finset.sum_const_zero,
        zero_div]; positivity
    | some s =>
      have hfour := T2C_augmented_fourth P.x (by have := hP.1; omega) A hx.2.1 (some s)
      change mean (fun i => P.x i s^4) ≤ max 1 A at hfour
      have hs : (∑ i, P.x i s^2) ≤ (n : ℝ)+(∑ i, P.x i s^4) := by
        rw [← show (∑ _i : Fin n, (1 : ℝ)) = n by simp, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (P.x i s^2-1)]
      change (∑ i, P.x i s^2)/(n : ℝ) ≤ _
      exact (div_le_iff₀ hn).mpr (by nlinarith [(div_le_iff₀ hn).mp hfour])
  change expectation P.pop (fun S => ∑ s, (armMean (fun i => xCirc P.x i s) S a)^2) ≤ _
  rw [T2C_expectation_sum]
  calc
    _ ≤ ∑ _s : Option (Fin k), 2*(1+max 1 A)/(r*n) := by
      apply Finset.sum_le_sum
      intro s _
      have h := T2C_arm_mse P.pop hP hm hc r (1+max 1 A) hr hl hu
        (fun i => xCirc P.x i s) (by positivity) (hsecond s) a
      simpa only [hzero s, sub_zero] using h
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- A rate for the product of covariate imbalance and regression score. -/
theorem T2C_regression_product_bound {n k} (P : CovPopulation n k) (e A r H K η : ℝ)
    (hP : ValidDesign P.pop) (hm : 2 ≤ P.pop.n1) (hc : 2 ≤ n-P.pop.n1)
    (he : 0 < e) (hr : 0 < r) (hH : 0 < H) (hK : 0 ≤ K) (hη : 0 < η)
    (hl : r*n ≤ (P.pop.n1 : ℝ)) (hu : (P.pop.n1 : ℝ) ≤ (1-r)*n)
    (hx : T2C_covariates P.x e A) (q : Fin n → ℝ)
    (hq0 : score P.x Finset.univ q = 0) (hq4 : mean (fun i => q i^4) ≤ K*H^2)
    (a : Bool) :
    probability P.pop (fun S => T2C_gramGood P.x e S ∧
      η*Real.sqrt (H/n) ≤ |dotProduct (fun s => armMean (fun i => xCirc P.x i s) S a)
        ((gram P.x (if a then S else Sᶜ))⁻¹ *ᵥ score P.x (if a then S else Sᶜ) q)|) ≤
      (((k : ℝ)+1)*2*(1+max 1 A)/r+
        ((k : ℝ)+1)*2*(max 1 A+K)/(r*(min 1 e/2)^2*η^2))/Real.sqrt n := by
  let X := fun S => normSq (fun s => armMean (fun i => xCirc P.x i s) S a)
  let Y := fun S => normSq (score P.x (if a then S else Sᶜ) q)/(min 1 e/2)^2
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hP.1; omega : 0 < n)
  have hc0 : 0 < min 1 e/2 := by positivity
  have hroot : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have h := T2C_product_tail P.pop (T2C_gramGood P.x e)
    (fun S => dotProduct (fun s => armMean (fun i => xCirc P.x i s) S a)
      ((gram P.x (if a then S else Sᶜ))⁻¹ *ᵥ score P.x (if a then S else Sᶜ) q))
    X Y (H/n) η (1/Real.sqrt n) (div_pos hH hn) hη (by positivity)
    (fun S _ => T2C_normSq_nonneg _) (fun S _ => div_nonneg (T2C_normSq_nonneg _) (sq_nonneg _))
    (by
      intro S hS hG
      exact (T2C_dot_sq _ _).trans (mul_le_mul_of_nonneg_left
        (T2C_inverse_bounds _ _ hc0 (hG a) _).2.1 (T2C_normSq_nonneg _)))
  have hX := T2C_xmean_mse P e A r hP hm hc hr hl hu hx a
  have hY : expectation P.pop Y ≤
      (((k : ℝ)+1)*2*(max 1 A+K)*H/(r*n))/(min 1 e/2)^2 := by
    dsimp only [Y]
    rw [expectation_div]
    exact div_le_div_of_nonneg_right
      (T2C_score_mse P e A r H K hP hm hc hr hH hK hl hu hx q hq0 hq4 a) (sq_nonneg _)
  apply h.trans
  calc
    expectation P.pop X/(1/Real.sqrt n)+expectation P.pop Y/(η^2*(H/n)/(1/Real.sqrt n)) ≤
        (((k : ℝ)+1)*2*(1+max 1 A)/(r*n))/(1/Real.sqrt n)+
          ((((k : ℝ)+1)*2*(max 1 A+K)*H/(r*n))/(min 1 e/2)^2)/
            (η^2*(H/n)/(1/Real.sqrt n)) :=
      add_le_add (div_le_div_of_nonneg_right hX (by positivity))
        (div_le_div_of_nonneg_right hY (by positivity))
    _ = _ := by
      have hsq := Real.sq_sqrt hn.le
      rw [← hsq]
      simp only [Real.sqrt_sq (Real.sqrt_nonneg (n : ℝ))]
      field_simp
      <;> ring

def T2C_rssReduced {n k} (x : Fin n → Fin k → ℝ) (q : Fin n → ℝ)
    (S : Finset (Fin n)) (a : Bool) : ℝ :=
  armMean (fun i => q i^2) S a -
    dotProduct (score x (if a then S else Sᶜ) q)
      ((gram x (if a then S else Sᶜ))⁻¹ *ᵥ score x (if a then S else Sᶜ) q)

/-- RSS consistency relative to the population residual second moment. -/
theorem T2C_rss_relative_bound {n k} (P : CovPopulation n k) (e A r H K η : ℝ)
    (hP : ValidDesign P.pop) (hm : 2 ≤ P.pop.n1) (hc : 2 ≤ n-P.pop.n1)
    (he : 0 < e) (hr : 0 < r) (hH : 0 < H) (hK : 0 ≤ K) (hη : 0 < η)
    (hl : r*n ≤ (P.pop.n1 : ℝ)) (hu : (P.pop.n1 : ℝ) ≤ (1-r)*n)
    (hx : T2C_covariates P.x e A) (q : Fin n → ℝ)
    (hq0 : score P.x Finset.univ q = 0) (hqH : mean (fun i => q i^2) = H)
    (hq4 : mean (fun i => q i^4) ≤ K*H^2) (a : Bool) :
    probability P.pop (fun S => T2C_gramGood P.x e S ∧
      η ≤ |T2C_rssReduced P.x q S a/H-1|) ≤
      8*K/(r*n*η^2)+4*((k : ℝ)+1)*(max 1 A+K)/(r*n*(min 1 e/2)*η) := by
  let c : ℝ := min 1 e/2
  let E := fun S => η*H/2 ≤ |armMean (fun i => q i^2) S a-H|
  let F := fun S => η*H*c/2 ≤ normSq (score P.x (if a then S else Sᶜ) q)
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hP.1; omega : 0 < n)
  have hinc : probability P.pop (fun S => T2C_gramGood P.x e S ∧
      η ≤ |T2C_rssReduced P.x q S a/H-1|) ≤ probability P.pop (fun S => E S ∨ F S) := by
    apply T2C_probability_mono
    intro S hS h
    by_contra hnot
    have hE : |armMean (fun i => q i^2) S a-H| < η*H/2 :=
      lt_of_not_ge (fun hh => hnot (Or.inl hh))
    have hF : normSq (score P.x (if a then S else Sᶜ) q) < η*H*c/2 :=
      lt_of_not_ge (fun hh => hnot (Or.inr hh))
    let v := armMean (fun i => q i^2) S a
    let energy := dotProduct (score P.x (if a then S else Sᶜ) q)
      ((gram P.x (if a then S else Sᶜ))⁻¹ *ᵥ score P.x (if a then S else Sᶜ) q)
    have hb := T2C_inverse_bounds _ c hc0 (h.1 a) (score P.x (if a then S else Sᶜ) q)
    have henergy : energy < η*H/2 := by
      apply hb.2.2.trans_lt
      exact (div_lt_iff₀ hc0).mpr (by nlinarith)
    have ha : |v-H-energy| ≤ |v-H|+energy := by
      have hen0 : 0 ≤ energy := hb.1
      simpa only [abs_of_nonneg hen0] using abs_sub (v-H) energy
    have heq : T2C_rssReduced P.x q S a/H-1 = (v-H-energy)/H := by
      dsimp [T2C_rssReduced, v, energy]
      field_simp
      <;> ring
    rw [heq, abs_div, abs_of_pos hH] at h
    have hlarge := (le_div_iff₀ hH).mp h.2
    linarith
  have hE : probability P.pop E ≤ 8*K/(r*n*η^2) := by
    have hb := T2C_arm_tail P.pop hP hm hc r (K*H^2) (η*H/2) hr hl hu
      (fun i => q i^2) (by positivity) (by simpa only [← pow_mul] using hq4)
      (by positivity) a
    simp_rw [hqH] at hb
    apply hb.trans_eq
    field_simp
    <;> ring
  have hF : probability P.pop F ≤ 4*((k : ℝ)+1)*(max 1 A+K)/(r*n*c*η) := by
    have hmark := T2C_markov_bound P.pop
      (fun S => normSq (score P.x (if a then S else Sᶜ) q)) (η*H*c/2)
      (by positivity) (fun S _ => T2C_normSq_nonneg _)
    have hb := T2C_score_mse P e A r H K hP hm hc hr hH hK hl hu hx q hq0 hq4 a
    apply hmark.trans
    calc
      _ ≤ (((k : ℝ)+1)*2*(max 1 A+K)*H/(r*n))/(η*H*c/2) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = _ := by field_simp <;> ring_nf <;> norm_num
  exact hinc.trans ((T2C_probability_union _ _ _).trans (add_le_add hE hF))

lemma T2C_arms_eventually (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ j, Population (sizes j)) (r : ℝ) (hr : 0 < r)
    (hP : ∀ j, ValidDesign (P j))
    (hl : ∀ j, r*sizes j ≤ ((P j).n1 : ℝ))
    (hu : ∀ j, ((P j).n1 : ℝ) ≤ (1-r)*sizes j) :
    ∀ᶠ j in atTop, 2 ≤ (P j).n1 ∧ 2 ≤ sizes j-(P j).n1 := by
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  filter_upwards [(hN.const_mul_atTop hr).eventually_ge_atTop 2] with j hj
  constructor
  · exact_mod_cast hj.trans (hl j)
  · have hh : (2 : ℝ) ≤ ((sizes j-(P j).n1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (hP j).2.2.le]
      linarith [hu j]
    exact_mod_cast hh

theorem T2C_regression_product_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (e A r K η : ℝ)
    (he : 0 < e) (hr : 0 < r) (hK : 0 ≤ K) (hη : 0 < η)
    (hP : ∀ j, ValidDesign (P j).pop)
    (hl : ∀ j, r*sizes j ≤ ((P j).pop.n1 : ℝ))
    (hu : ∀ j, ((P j).pop.n1 : ℝ) ≤ (1-r)*sizes j)
    (hx : ∀ j, T2C_covariates (P j).x e A)
    (q : ∀ j, Fin (sizes j) → ℝ) (H : ℕ → ℝ) (hH : ∀ j, 0 < H j)
    (hq0 : ∀ j, score (P j).x Finset.univ (q j) = 0)
    (hq4 : ∀ j, mean (fun i => q j i^4) ≤ K*(H j)^2) (a : Bool) :
    Tendsto (fun j => probability (P j).pop (fun S => T2C_gramGood (P j).x e S ∧
      η*Real.sqrt (H j/sizes j) ≤
        |dotProduct (fun s => armMean (fun i => xCirc (P j).x i s) S a)
          ((gram (P j).x (if a then S else Sᶜ))⁻¹ *ᵥ
            score (P j).x (if a then S else Sᶜ) (q j))|)) atTop (nhds 0) := by
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hroot := Real.tendsto_sqrt_atTop.comp hN
  have hb : Tendsto (fun j => (((k : ℝ)+1)*2*(1+max 1 A)/r+
      ((k : ℝ)+1)*2*(max 1 A+K)/(r*(min 1 e/2)^2*η^2))/Real.sqrt (sizes j))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hroot
  apply squeeze_zero' (Eventually.of_forall fun _ =>
    DecisionLemma12_probability_nonneg _ _) _ hb
  filter_upwards [T2C_arms_eventually sizes hsizes (fun j => (P j).pop) r hr hP hl hu]
    with j hj
  exact T2C_regression_product_bound (P j) e A r (H j) K η (hP j) hj.1 hj.2
    he hr (hH j) hK hη (hl j) (hu j) (hx j) (q j) (hq0 j) (hq4 j) a


lemma T2C_Xi_covariates {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (hP : Xi P δ e A B r) : T2C_covariates P.x e A :=
  ⟨hP.2.2.2.2.2.2.2.1, hP.2.2.2.2.2.2.2.2.1, hP.2.2.2.2.2.2.2.2.2⟩

lemma T2C_Xi_residual_score {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (a : Bool) :
    score P.x Finset.univ (residual P a (late P.pop)) = 0 := by
  exact T2C_population_score_zero P.x (w P.pop a (late P.pop))
    (T2C_population_det P.x e A (by have := hP.1.1; omega) he
      (T2C_Xi_covariates P δ e A B r hP))

lemma T2C_fourth_from_norm {n} (hn : 2 ≤ n) (q : Fin n → ℝ) (B : ℝ)
    (hq0 : mean q = 0) (hB : fourthNorm q ≤ B*Real.sqrt (popVar q)) :
    mean (fun i => q i^4) ≤ 4*B^4*(mean (fun i => q i^2))^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hH : 0 ≤ mean (fun i => q i^2) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hnpos.le
  have hV : 0 ≤ popVar q := div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (by linarith)
  have hVbound : popVar q ≤ 2*mean (fun i => q i^2) := by
    apply T2C_popVar_bound hn q _ hH le_rfl
  have h4 : 0 ≤ mean (fun i => q i^4) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) hnpos.le
  have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) hB 4
  have hroot : (fourthNorm q)^4 = mean (fun i => q i^4) := by
    unfold fourthNorm
    calc
      _ = ((Real.sqrt (Real.sqrt (mean (fun i => q i^4))))^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt h4]
  change (fourthNorm q)^4 ≤ (B*Real.sqrt (popVar q))^4 at hpow
  rw [hroot, mul_pow, show (Real.sqrt (popVar q))^4 =
      ((Real.sqrt (popVar q))^2)^2 by ring, Real.sq_sqrt hV] at hpow
  have hdiff : 0 ≤ 4*(mean (fun i => q i^2))^2-(popVar q)^2 := by nlinarith
  exact hpow.trans (by nlinarith [mul_nonneg (by positivity : 0 ≤ B^4) hdiff])

lemma T2C_observed_rss {n k} (P : CovPopulation n k) (β : ℝ)
    (hP : ValidDesign P.pop) (e : ℝ) (he : 0 < e)
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) (hG : T2C_gramGood P.x e S)
    (a : Bool) :
    rss P.x (if a then S else Sᶜ) (observedW P.pop β S)
        (fitted P (observedW P.pop β S) S a)/
      ((if a then S else Sᶜ).card : ℝ) = T2C_rssReduced P.x (residual P a β) S a := by
  let T := if a then S else Sᶜ
  have hcard := (Finset.mem_powersetCard.mp hS).2
  have hT : T.Nonempty := by
    cases a
    · apply Finset.card_pos.mp
      dsimp [T]
      rw [Finset.card_compl, Fintype.card_fin, hcard]
      exact Nat.sub_pos_of_lt hP.2.2
    · apply Finset.card_pos.mp
      simpa [T, hcard] using hP.2.1
  have hresponse : ∀ i ∈ T, observedW P.pop β S i-
      dotProduct (augmented P.x i) (psi P a β) = residual P a β i := by
    intro i hi
    cases a
    · rw [observedW_control P.pop β S i (by simpa only [T, Bool.false_eq_true, ↓reduceIte] using hi)]
      rfl
    · rw [observedW_treated P.pop β S i (by simpa only [T, ↓reduceIte] using hi)]
      rfl
  have hscore := score_congr P.x T _ _ hresponse
  have hmean := groupMean_congr T _ _ (fun i hi => congrArg (fun z : ℝ => z^2) (hresponse i hi))
  have hid := residual_sum_squares_identity P.x T (observedW P.pop β S) (psi P a β)
    hT (T2C_gramGood_det P.x e he S hG a)
  rw [hscore, hmean] at hid
  simpa only [T2C_rssReduced, fitted, T, armMean] using hid

def T2C_residualH {n k} (P : CovPopulation n k) (a : Bool) : ℝ :=
  mean (fun i => residual P a (late P.pop) i^2)

def T2C_totalH {n k} (P : CovPopulation n k) : ℝ :=
  T2C_residualH P true+T2C_residualH P false

lemma T2C_residualH_nonneg {n k} (P : CovPopulation n k) (a : Bool) :
    0 ≤ T2C_residualH P a :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

lemma T2C_residualH_le_total {n k} (P : CovPopulation n k) (a : Bool) :
    T2C_residualH P a ≤ T2C_totalH P := by
  have h1 := T2C_residualH_nonneg P true
  have h0 := T2C_residualH_nonneg P false
  cases a <;> dsimp only [T2C_totalH] <;> linarith

lemma T2C_Xi_residual_fourth {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (a : Bool) :
    mean (fun i => residual P a (late P.pop) i^4) ≤ 4*B^4*(T2C_residualH P a)^2 :=
  T2C_fourth_from_norm hP.1.1 _ B
    (T2C_residual_centered P.x _ (T2C_Xi_residual_score P δ e A B r he hP a))
    (hP.2.2.2.2.2.2.1 a)

lemma T2C_Xi_total_fourth {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (a : Bool) :
    mean (fun i => residual P a (late P.pop) i^4) ≤ 4*B^4*(T2C_totalH P)^2 := by
  apply (T2C_Xi_residual_fourth P δ e A B r he hP a).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (T2C_residualH_nonneg P a) (T2C_residualH_le_total P a) 2)
    (by positivity)

lemma T2C_groupMean_dot {n} {ι : Type*} [Fintype ι]
    (S : Finset (Fin n)) (u : Fin n → ι → ℝ) (b : ι → ℝ) :
    groupMean S (fun i => dotProduct (u i) b) =
      dotProduct (fun s => groupMean S (fun i => u i s)) b := by
  simp only [groupMean, dotProduct, Finset.sum_div, Finset.sum_mul, div_mul_eq_mul_div]
  exact Finset.sum_comm

def T2C_correction {n k} (P : CovPopulation n k) (q : Fin n → ℝ)
    (S : Finset (Fin n)) (a : Bool) : ℝ :=
  dotProduct (fun s => armMean (fun i => xCirc P.x i s) S a)
    ((gram P.x (if a then S else Sᶜ))⁻¹ *ᵥ score P.x (if a then S else Sᶜ) q)

lemma T2C_observed_difference {n k} (P : CovPopulation n k) (β e : ℝ) (he : 0 < e)
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) (hG : T2C_gramGood P.x e S) :
    adjustedTau P (observedW P.pop β S) S-oracleTau P β S =
      -T2C_correction P (residual P true β) S true+
        T2C_correction P (residual P false β) S false := by
  rw [corrected_E21_E23 P β S hS (T2C_gramGood_det P.x e he S hG true)
    (T2C_gramGood_det P.x e he S hG false)]
  simp only [T2C_groupMean_dot]
  rfl

/-- Observed numerator conclusion at the residual sampling scale. -/
theorem T2C_observed_numerator_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (he : 0 < e) (hr : 0 < r) (hP : ∀ j, Xi (P j) δ e A B r)
    (hH : ∀ j, 0 < T2C_totalH (P j)) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun j => probability (P j).pop (fun S =>
      η*Real.sqrt (T2C_totalH (P j)/sizes j) ≤
        |adjustedTau (P j) (observedW (P j).pop (late (P j).pop) S) S-
          oracleTau (P j) (late (P j).pop) S|)) atTop (nhds 0) := by
  have hcov (j) := T2C_Xi_covariates (P j) δ e A B r (hP j)
  have hD (j) := (hP j).1
  have hl (j) := (hP j).2.2.2.1
  have hu (j) := (hP j).2.2.2.2.1
  let E := fun j S => ¬ T2C_gramGood (P j).x e S
  let F := fun (a : Bool) j S => T2C_gramGood (P j).x e S ∧
    (η/2)*Real.sqrt (T2C_totalH (P j)/sizes j) ≤
      |T2C_correction (P j) (residual (P j) a (late (P j).pop)) S a|
  have hE : Tendsto (fun j => probability (P j).pop (E j)) atTop (nhds 0) :=
    T2C_gram_bad_limit sizes hsizes k P e A r he hr hD hl hu hcov
  have hF (a : Bool) : Tendsto (fun j => probability (P j).pop (F a j)) atTop (nhds 0) :=
    T2C_regression_product_limit sizes hsizes k P e A r (4*B^4) (η/2) he hr
      (by positivity) (by positivity) hD hl hu hcov
      (fun j => residual (P j) a (late (P j).pop)) (fun j => T2C_totalH (P j)) hH
      (fun j => T2C_Xi_residual_score (P j) δ e A B r he (hP j) a)
      (fun j => T2C_Xi_total_fourth (P j) δ e A B r he (hP j) a) a
  have hb : Tendsto (fun j => probability (P j).pop (E j)+
      (probability (P j).pop (F true j)+probability (P j).pop (F false j)))
      atTop (nhds 0) := by simpa using hE.add ((hF true).add (hF false))
  apply squeeze_zero (fun _ => DecisionLemma12_probability_nonneg _ _) _ hb
  intro j
  calc
    _ ≤ probability (P j).pop (fun S => E j S ∨ (F true j S ∨ F false j S)) := by
      apply T2C_probability_mono
      intro S hS hbad
      by_cases hG : T2C_gramGood (P j).x e S
      · apply Or.inr
        by_contra hnot
        have h1 : |T2C_correction (P j) (residual (P j) true (late (P j).pop)) S true| <
            (η/2)*Real.sqrt (T2C_totalH (P j)/sizes j) :=
          lt_of_not_ge fun hh => hnot (Or.inl ⟨hG,hh⟩)
        have h0 : |T2C_correction (P j) (residual (P j) false (late (P j).pop)) S false| <
            (η/2)*Real.sqrt (T2C_totalH (P j)/sizes j) :=
          lt_of_not_ge fun hh => hnot (Or.inr ⟨hG,hh⟩)
        rw [T2C_observed_difference (P j) (late (P j).pop) e he S hS hG] at hbad
        have htri := abs_add_le
          (-T2C_correction (P j) (residual (P j) true (late (P j).pop)) S true)
          (T2C_correction (P j) (residual (P j) false (late (P j).pop)) S false)
        rw [abs_neg] at htri
        linarith
      · exact Or.inl hG
    _ ≤ _ := (T2C_probability_union _ _ _).trans
      (add_le_add le_rfl (T2C_probability_union _ _ _))

lemma T2C_second_le_popVar {n} (hn : 2 ≤ n) (q : Fin n → ℝ) (hq : mean q = 0) :
    mean (fun i => q i^2) ≤ popVar q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  change (∑ i, q i^2)/(n : ℝ) ≤ (∑ i, (q i-mean q)^2)/((n : ℝ)-1)
  simp_rw [hq, sub_zero]
  exact div_le_div_of_nonneg_left
    (show (0 : ℝ) ≤ ∑ i, q i^2 from Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (by linarith : (0 : ℝ) < n-1) (by linarith : (n : ℝ)-1 ≤ n)

/-- The literal oracle variance controls the sampling scale used above. -/
theorem T2C_observed_variance_lower {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : Xi P δ e A B r) :
    ((1-max δ 0)*r)*T2C_totalH P/n ≤ designVariance P.pop (oracleTau P (late P.pop)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hP.1.1; omega : 0 < n)
  have hm : (0 : ℝ) < P.pop.n1 := by exact_mod_cast hP.1.2.1
  have hmn : (P.pop.n1 : ℝ) < n := by exact_mod_cast hP.1.2.2
  have hc : 0 < controlSize P.pop := by dsimp [controlSize]; linarith
  have hd : 0 < 1-max δ 0 := sub_pos.mpr (max_lt hδ zero_lt_one)
  have hvar (a : Bool) : T2C_residualH P a ≤ popVar (residual P a (late P.pop)) :=
    T2C_second_le_popVar hP.1.1 _
      (T2C_residual_centered P.x _ (T2C_Xi_residual_score P δ e A B r he hP a))
  have hs1 : r/n ≤ controlSize P.pop/(n*(P.pop.n1 : ℝ)) := by
    apply (div_le_div_iff₀ hn (mul_pos hn hm)).mpr
    have hrc : r*(P.pop.n1 : ℝ) ≤ controlSize P.pop := by
      have := hP.2.2.2.2.1
      dsimp [controlSize]
      nlinarith [mul_le_mul_of_nonneg_left hmn.le hr.1.le]
    nlinarith
  have hs0 : r/n ≤ (P.pop.n1 : ℝ)/(n*controlSize P.pop) := by
    apply (div_le_div_iff₀ hn (mul_pos hn hc)).mpr
    have hrc : r*controlSize P.pop ≤ (P.pop.n1 : ℝ) := by
      have := hP.2.2.2.1
      have hcn : controlSize P.pop ≤ (n : ℝ) := by dsimp [controlSize]; linarith
      exact (mul_le_mul_of_nonneg_left hcn hr.1.le).trans this
    nlinarith
  have h1 := mul_le_mul hs1 (hvar true) (T2C_residualH_nonneg P true) (by positivity)
  have h0 := mul_le_mul hs0 (hvar false) (T2C_residualH_nonneg P false) (by positivity)
  have hsum := mul_le_mul_of_nonneg_left (add_le_add h1 h0) hd.le
  have hE := corrected_E10_proof P δ e A B r hk hδ he hA hB hr hP
  apply le_trans _ hE
  convert hsum using 1 <;> dsimp [T2C_totalH] <;> ring

lemma T2C_mean_square_zero {n} (hn : 0 < n) (q : Fin n → ℝ)
    (hq : mean (fun i => q i^2) = 0) : q = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (T2C_normSq_eq_zero _).mp
  exact (div_eq_zero_iff.mp hq).resolve_right hnR

/-- The zero-residual branch is exact on the common full-rank event. -/
theorem T2C_zero_residual_accepted {n k} (P : CovPopulation n k) (δ e A B r α : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) (hH : T2C_totalH P = 0)
    (S : Finset (Fin n)) (hS : S ∈ assignments P.pop) (hG : T2C_gramGood P.x e S) :
    adjustedAccepted P (late P.pop) α S := by
  have hn : 0 < n := by have := hP.1.1; omega
  have hres (a : Bool) : residual P a (late P.pop) = 0 := by
    have ha := T2C_residualH_nonneg P a
    have hat := T2C_residualH_le_total P a
    rw [hH] at hat
    exact T2C_mean_square_zero hn _ (le_antisymm hat ha)
  have hdiff := T2C_observed_difference P (late P.pop) e he S hS hG
  simp only [hres] at hdiff
  have hscore0 (T : Finset (Fin n)) : score P.x T (0 : Fin n → ℝ) = 0 := by
    ext s
    change groupMean T (fun i => augmented P.x i s*(0 : Fin n → ℝ) i) = 0
    simp [groupMean]
  simp only [T2C_correction, hscore0, Matrix.mulVec_zero, dotProduct_zero,
    neg_zero, zero_add] at hdiff
  have hcov := T2C_Xi_covariates P δ e A B r hP
  have hpop := T2C_population_det P.x e A hn he hcov
  have horacle := (corrected_oracle_expansion P hP.1 hP.2.1 hP.2.2.1 hcov.1 hpop S hS).2
  simp only [hres, Pi.zero_apply, groupMean, Finset.sum_const_zero,
    zero_div, sub_self] at horacle
  have hnum : adjustedTau P (observedW P.pop (late P.pop) S) S = 0 := by linarith
  unfold adjustedAccepted adjustedAR
  simp only [hnum, absStudent, abs_zero, ENNReal.ofReal_zero, zero_div, ite_true, ite_self]
  exact bot_le

theorem T2C_observed_numerator_oracle_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : ∀ j, Xi (P j) δ e A B r)
    (hH : ∀ j, 0 < T2C_totalH (P j)) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun j => probability (P j).pop (fun S => κ ≤
      |(adjustedTau (P j) (observedW (P j).pop (late (P j).pop) S) S-
        oracleTau (P j) (late (P j).pop) S)/
          Real.sqrt (designVariance (P j).pop (oracleTau (P j) (late (P j).pop)))|))
      atTop (nhds 0) := by
  let C := (1-max δ 0)*r
  have hC : 0 < C := mul_pos (sub_pos.mpr (max_lt hδ zero_lt_one)) hr.1
  have hb := T2C_observed_numerator_limit sizes hsizes k P δ e A B r he hr.1 hP hH
    (κ*Real.sqrt C) (mul_pos hκ (Real.sqrt_pos.mpr hC))
  apply squeeze_zero (fun _ => DecisionLemma12_probability_nonneg _ _) _ hb
  intro j
  apply T2C_probability_mono
  intro S hS hbad
  have hn : (0 : ℝ) < sizes j := by
    exact_mod_cast (by have := (hP j).1.1; omega : 0 < sizes j)
  have hL : 0 < T2C_totalH (P j)/sizes j := div_pos (hH j) hn
  have hlow := T2C_observed_variance_lower (P j) δ e A B r hk hδ he hA hB hr (hP j)
  have hbase : 0 < C*T2C_totalH (P j)/sizes j := by
    simpa only [mul_div_assoc] using mul_pos hC hL
  have hV : 0 < designVariance (P j).pop (oracleTau (P j) (late (P j).pop)) :=
    hbase.trans_le hlow
  have hroot := Real.sqrt_le_sqrt hlow
  have hform : C*T2C_totalH (P j)/sizes j = C*(T2C_totalH (P j)/sizes j) := by ring
  rw [hform, Real.sqrt_mul hC.le] at hroot
  rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hV)] at hbad
  have hmul := (le_div_iff₀ (Real.sqrt_pos.mpr hV)).mp hbad
  have hcompare : (κ*Real.sqrt C)*Real.sqrt (T2C_totalH (P j)/sizes j) ≤
      κ*Real.sqrt (designVariance (P j).pop (oracleTau (P j) (late (P j).pop))) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hroot hκ.le
  exact hcompare.trans hmul

lemma T2C_weighted_ratio (m c H1 H0 R1 R0 η : ℝ) (hm : 0 < m) (hc : 0 < c)
    (hC : 0 < H1/m+H0/c) (h1 : |R1-H1| ≤ η*H1) (h0 : |R0-H0| ≤ η*H0) :
    |(R1/m+R0/c)/(H1/m+H0/c)-1| ≤ η := by
  have heq : (R1/m+R0/c)/(H1/m+H0/c)-1 =
      ((R1-H1)/m+(R0-H0)/c)/(H1/m+H0/c) := by
    calc
      _ = ((R1/m+R0/c)-(H1/m+H0/c))/(H1/m+H0/c) := by
        rw [sub_div, div_self hC.ne']
      _ = _ := by congr 1; ring
  rw [heq, abs_div, abs_of_pos hC]
  apply (div_le_iff₀ hC).mpr
  calc
    _ ≤ |(R1-H1)/m|+|(R0-H0)/c| := abs_add_le _ _
    _ = |R1-H1|/m+|R0-H0|/c := by rw [abs_div, abs_div, abs_of_pos hm, abs_of_pos hc]
    _ ≤ (η*H1)/m+(η*H0)/c := add_le_add
      (div_le_div_of_nonneg_right h1 hm.le) (div_le_div_of_nonneg_right h0 hc.le)
    _ = _ := by ring

def T2C_sigmaH {n k} (P : CovPopulation n k) : ℝ :=
  T2C_residualH P true/(P.pop.n1 : ℝ)+T2C_residualH P false/controlSize P.pop

lemma T2C_sigmaH_pos {n k} (P : CovPopulation n k) (hP : ValidDesign P.pop)
    (hH : 0 < T2C_totalH P) : 0 < T2C_sigmaH P := by
  have hm : (0 : ℝ) < P.pop.n1 := by exact_mod_cast hP.2.1
  have hc : 0 < controlSize P.pop := by
    have := (show (P.pop.n1 : ℝ) < n by exact_mod_cast hP.2.2)
    dsimp [controlSize]
    linarith
  have h1 := T2C_residualH_nonneg P true
  have h0 := T2C_residualH_nonneg P false
  by_cases ht : 0 < T2C_residualH P true
  · exact add_pos_of_pos_of_nonneg (div_pos ht hm) (div_nonneg h0 hc.le)
  · have ht0 : T2C_residualH P true = 0 := le_antisymm (le_of_not_gt ht) h1
    have h0p : 0 < T2C_residualH P false := by
      simpa only [T2C_totalH, ht0, zero_add] using hH
    exact add_pos_of_nonneg_of_pos (div_nonneg h1 hm.le) (div_pos h0p hc)

lemma T2C_observed_sigma_identity {n k} (P : CovPopulation n k) (β e : ℝ)
    (hP : ValidDesign P.pop) (he : 0 < e) (S : Finset (Fin n))
    (hS : S ∈ assignments P.pop) (hG : T2C_gramGood P.x e S) :
    adjustedSigma2 P (observedW P.pop β S) S =
      T2C_rssReduced P.x (residual P true β) S true/(P.pop.n1 : ℝ)+
        T2C_rssReduced P.x (residual P false β) S false/controlSize P.pop := by
  have hcard := (Finset.mem_powersetCard.mp hS).2
  have h1 := T2C_observed_rss P β hP e he S hS hG true
  have h0 := T2C_observed_rss P β hP e he S hS hG false
  have hccard : (Sᶜ.card : ℝ) = controlSize P.pop := by
    rw [Finset.card_compl, Fintype.card_fin, hcard, Nat.cast_sub hP.2.2.le]
    rfl
  simp only [↓reduceIte, hcard] at h1
  simp only [Bool.false_eq_true, ↓reduceIte, hccard] at h0
  calc
    _ = (rss P.x S (observedW P.pop β S) (fitted P (observedW P.pop β S) S true)/
        (P.pop.n1 : ℝ))/(P.pop.n1 : ℝ)+
      (rss P.x Sᶜ (observedW P.pop β S) (fitted P (observedW P.pop β S) S false)/
        controlSize P.pop)/controlSize P.pop := by unfold adjustedSigma2; ring
    _ = _ := by rw [h1, h0]

lemma T2C_rssReduced_zero {n k} (x : Fin n → Fin k → ℝ) (S : Finset (Fin n)) (a : Bool) :
    T2C_rssReduced x (0 : Fin n → ℝ) S a = 0 := by
  have hs : score x (if a then S else Sᶜ) (0 : Fin n → ℝ) = 0 := by
    ext s
    simp [score, groupMean]
  simp [T2C_rssReduced, hs, armMean, groupMean]

/-- Both residual variances may vanish individually; only their sum is positive. -/
theorem T2C_observed_sigmaH_bound {n k} (P : CovPopulation n k) (δ e A B r η : ℝ)
    (he : 0 < e) (hr : 0 < r) (hη : 0 < η) (hP : Xi P δ e A B r)
    (hm : 2 ≤ P.pop.n1) (hc : 2 ≤ n-P.pop.n1) (hH : 0 < T2C_totalH P) :
    probability P.pop (fun S => η ≤
      |adjustedSigma2 P (observedW P.pop (late P.pop) S) S/T2C_sigmaH P-1|) ≤
      probability P.pop (fun S => ¬ T2C_gramGood P.x e S)+
        2*(8*(4*B^4)/(r*n*(η/2)^2)+
          4*((k : ℝ)+1)*(max 1 A+4*B^4)/(r*n*(min 1 e/2)*(η/2))) := by
  let E := fun a S => T2C_gramGood P.x e S ∧ 0 < T2C_residualH P a ∧
    η/2 ≤ |T2C_rssReduced P.x (residual P a (late P.pop)) S a/T2C_residualH P a-1|
  let bound : ℝ := 8*(4*B^4)/(r*n*(η/2)^2)+
    4*((k : ℝ)+1)*(max 1 A+4*B^4)/(r*n*(min 1 e/2)*(η/2))
  have hbound (a : Bool) : probability P.pop (E a) ≤ bound := by
    by_cases ha : 0 < T2C_residualH P a
    · have hmono : probability P.pop (E a) ≤ probability P.pop (fun S =>
          T2C_gramGood P.x e S ∧ η/2 ≤
            |T2C_rssReduced P.x (residual P a (late P.pop)) S a/T2C_residualH P a-1|) :=
        T2C_probability_mono P.pop (fun S hS h => ⟨h.1,h.2.2⟩)
      apply hmono.trans
      exact T2C_rss_relative_bound P e A r (T2C_residualH P a) (4*B^4) (η/2)
        hP.1 hm hc he hr ha (by positivity) (by positivity) hP.2.2.2.1 hP.2.2.2.2.1
        (T2C_Xi_covariates P δ e A B r hP) (residual P a (late P.pop))
        (T2C_Xi_residual_score P δ e A B r he hP a) rfl
        (T2C_Xi_residual_fourth P δ e A B r he hP a) a
    · have hz : probability P.pop (E a) = 0 := by simp [E, ha, probability]
      rw [hz]
      dsimp [bound]
      positivity
  have hinc : probability P.pop (fun S => η ≤
      |adjustedSigma2 P (observedW P.pop (late P.pop) S) S/T2C_sigmaH P-1|) ≤
      probability P.pop (fun S => ¬ T2C_gramGood P.x e S ∨ (E true S ∨ E false S)) := by
    apply T2C_probability_mono
    intro S hS hbad
    by_cases hG : T2C_gramGood P.x e S
    · apply Or.inr
      by_contra hnot
      have herr (a : Bool) : |T2C_rssReduced P.x (residual P a (late P.pop)) S a-
          T2C_residualH P a| ≤ (η/2)*T2C_residualH P a := by
        by_cases ha : 0 < T2C_residualH P a
        · have hsmall : |T2C_rssReduced P.x (residual P a (late P.pop)) S a/
              T2C_residualH P a-1| < η/2 := by
            apply lt_of_not_ge
            intro hh
            have hE : E a S := ⟨hG,ha,hh⟩
            cases a
            · exact hnot (Or.inr hE)
            · exact hnot (Or.inl hE)
          have heq : T2C_rssReduced P.x (residual P a (late P.pop)) S a/
              T2C_residualH P a-1 =
            (T2C_rssReduced P.x (residual P a (late P.pop)) S a-T2C_residualH P a)/
              T2C_residualH P a := by field_simp; <;> ring
          rw [heq, abs_div, abs_of_pos ha] at hsmall
          nlinarith [(div_lt_iff₀ ha).mp hsmall]
        · have ha0 : T2C_residualH P a = 0 :=
            le_antisymm (le_of_not_gt ha) (T2C_residualH_nonneg P a)
          have hz := T2C_mean_square_zero (by have := hP.1.1; omega)
            (residual P a (late P.pop)) ha0
          rw [hz, T2C_rssReduced_zero, ha0]
          simp
      have hmR : (0 : ℝ) < P.pop.n1 := by exact_mod_cast hP.1.2.1
      have hcR : 0 < controlSize P.pop := by
        have := (show (P.pop.n1 : ℝ) < n by exact_mod_cast hP.1.2.2)
        dsimp [controlSize]
        linarith
      have hratio := T2C_weighted_ratio (P.pop.n1 : ℝ) (controlSize P.pop)
        (T2C_residualH P true) (T2C_residualH P false)
        (T2C_rssReduced P.x (residual P true (late P.pop)) S true)
        (T2C_rssReduced P.x (residual P false (late P.pop)) S false)
        (η/2) hmR hcR (T2C_sigmaH_pos P hP.1 hH) (herr true) (herr false)
      rw [T2C_observed_sigma_identity P (late P.pop) e hP.1 he S hS hG] at hbad
      dsimp only [T2C_sigmaH] at hbad
      linarith
    · exact Or.inl hG
  have hU := (T2C_probability_union P.pop (fun S => ¬ T2C_gramGood P.x e S)
    (fun S => E true S ∨ E false S)).trans
    (add_le_add le_rfl ((T2C_probability_union _ _ _).trans
      (add_le_add (hbound true) (hbound false))))
  apply hinc.trans
  convert hU using 1 <;> dsimp [bound] <;> ring

theorem T2C_observed_sigmaH_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (he : 0 < e) (hr : 0 < r) (hP : ∀ j, Xi (P j) δ e A B r)
    (hH : ∀ j, 0 < T2C_totalH (P j)) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun j => probability (P j).pop (fun S => η ≤
      |adjustedSigma2 (P j) (observedW (P j).pop (late (P j).pop) S) S/
        T2C_sigmaH (P j)-1|)) atTop (nhds 0) := by
  have hD (j) := (hP j).1
  have hl (j) := (hP j).2.2.2.1
  have hu (j) := (hP j).2.2.2.2.1
  have hcov (j) := T2C_Xi_covariates (P j) δ e A B r (hP j)
  have hGram := T2C_gram_bad_limit sizes hsizes k P e A r he hr hD hl hu hcov
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hR : Tendsto (fun j => 2*(8*(4*B^4)/(r*sizes j*(η/2)^2)+
      4*((k : ℝ)+1)*(max 1 A+4*B^4)/(r*sizes j*(min 1 e/2)*(η/2)))) atTop (nhds 0) := by
    have h := (tendsto_const_nhds.div_atTop hN : Tendsto (fun j =>
      (2*(8*(4*B^4)/(r*(η/2)^2)+
        4*((k : ℝ)+1)*(max 1 A+4*B^4)/(r*(min 1 e/2)*(η/2))))/(sizes j : ℝ))
      atTop (nhds 0))
    convert h using 1 <;> funext j <;> ring
  have hb := hGram.add hR
  simp only [add_zero] at hb
  apply squeeze_zero' (Eventually.of_forall fun _ =>
    DecisionLemma12_probability_nonneg _ _) _ hb
  filter_upwards [T2C_arms_eventually sizes hsizes (fun j => (P j).pop) r hr hD hl hu]
    with j hj
  exact T2C_observed_sigmaH_bound (P j) δ e A B r η he hr hη (hP j) hj.1 hj.2 (hH j)

def T2C_oracleConservative {n k} (P : CovPopulation n k) : ℝ :=
  popVar (residual P true (late P.pop))/(P.pop.n1 : ℝ)+
    popVar (residual P false (late P.pop))/controlSize P.pop

lemma T2C_centered_variance {n} (hn : 0 < n) (q : Fin n → ℝ) (hq : mean q = 0) :
    popVar q = (n : ℝ)/((n : ℝ)-1)*mean (fun i => q i^2) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change (∑ i, (q i-mean q)^2)/((n : ℝ)-1) =
    (n : ℝ)/((n : ℝ)-1)*((∑ i, q i^2)/(n : ℝ))
  simp_rw [hq, sub_zero]
  field_simp
  <;> ring

lemma T2C_oracleConservative_eq {n k} (P : CovPopulation n k) (δ e A B r : ℝ)
    (he : 0 < e) (hP : Xi P δ e A B r) :
    T2C_oracleConservative P = (n : ℝ)/((n : ℝ)-1)*T2C_sigmaH P := by
  have hn : 0 < n := by have := hP.1.1; omega
  have hmean (a : Bool) := T2C_residual_centered P.x _
    (T2C_Xi_residual_score P δ e A B r he hP a)
  unfold T2C_oracleConservative T2C_sigmaH T2C_residualH
  rw [T2C_centered_variance hn _ (hmean true), T2C_centered_variance hn _ (hmean false)]
  ring

lemma T2C_finite_factor_error (N X H : ℝ) (hN : 2 ≤ N) (hH : 0 < H) :
    |X/(N/(N-1)*H)-1| ≤ |X/H-1|+1/N := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N-1 := by linarith
  have hf0 : 0 ≤ (N-1)/N := by positivity
  have hf1 : (N-1)/N ≤ 1 := (div_le_one hN0).mpr (by linarith)
  have heq : X/(N/(N-1)*H)-1 = ((N-1)/N)*(X/H-1)-1/N := by
    field_simp
    <;> ring
  rw [heq]
  calc
    _ ≤ |((N-1)/N)*(X/H-1)|+|1/N| := abs_sub _ _
    _ = ((N-1)/N)*|X/H-1|+1/N := by
      rw [abs_mul, abs_of_nonneg hf0, abs_of_pos (by positivity : (0 : ℝ) < 1/N)]
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right hf1 (abs_nonneg (X/H-1))
      simpa only [one_mul] using add_le_add hm (le_refl (1/N))

/-- Observed denominator: normalization is by the conservative oracle expression. -/
theorem T2C_observed_sigma_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (δ e A B r : ℝ)
    (he : 0 < e) (hr : 0 < r) (hP : ∀ j, Xi (P j) δ e A B r)
    (hH : ∀ j, 0 < T2C_totalH (P j)) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun j => probability (P j).pop (fun S => κ ≤
      |adjustedSigma2 (P j) (observedW (P j).pop (late (P j).pop) S) S/
        T2C_oracleConservative (P j)-1|)) atTop (nhds 0) := by
  have hb := T2C_observed_sigmaH_limit sizes hsizes k P δ e A B r he hr hP hH
    (κ/2) (by positivity)
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hi : Tendsto (fun j => 1/(sizes j : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hN
  apply squeeze_zero' (Eventually.of_forall fun _ =>
    DecisionLemma12_probability_nonneg _ _) _ hb
  filter_upwards [(tendsto_order.1 hi).2 (κ/2) (by positivity)] with j hj
  apply T2C_probability_mono
  intro S hS hbad
  have hnR : (2 : ℝ) ≤ sizes j := by exact_mod_cast (hP j).1.1
  rw [T2C_oracleConservative_eq (P j) δ e A B r he (hP j)] at hbad
  have he := T2C_finite_factor_error (sizes j)
    (adjustedSigma2 (P j) (observedW (P j).pop (late (P j).pop) S) S)
    (T2C_sigmaH (P j)) hnR (T2C_sigmaH_pos (P j) (hP j).1 (hH j))
  linarith

end
end AronowAudit.P002.Wave1
