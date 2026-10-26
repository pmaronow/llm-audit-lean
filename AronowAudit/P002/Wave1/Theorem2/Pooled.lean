import AronowAudit.P002.Wave1.Theorem2.Observed

/-! Moments of the response and its pooled projection. -/

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

lemma T2C_mean_nonneg {n} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) : 0 ≤ mean q :=
  div_nonneg (Finset.sum_nonneg fun i _ => hq i) (Nat.cast_nonneg _)

lemma T2C_mean_mono {n} {q t : Fin n → ℝ} (h : ∀ i, q i ≤ t i) : mean q ≤ mean t :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => h i) (Nat.cast_nonneg _)

lemma T2C_mean_add {n} (q t : Fin n → ℝ) :
    mean (fun i => q i+t i) = mean q+mean t := by
  simp only [mean, Finset.sum_add_distrib, add_div]

lemma T2C_mean_sub {n} (q t : Fin n → ℝ) :
    mean (fun i => q i-t i) = mean q-mean t := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

lemma T2C_mean_mul {n} (c : ℝ) (q : Fin n → ℝ) :
    mean (fun i => c*q i) = c*mean q := by
  simp only [mean, ← Finset.mul_sum]
  ring

lemma T2C_mean_sum {n} {ι : Type*} [Fintype ι] (q : ι → Fin n → ℝ) :
    mean (fun i => ∑ s, q s i) = ∑ s, mean (q s) := by
  simp only [mean, Finset.sum_div]
  exact Finset.sum_comm

def T2C_frozen {n} (R : Bool → Fin n → ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ S then R true i else R false i

def T2C_frozenMean {n} (P : Population n) (R : Bool → Fin n → ℝ) : ℝ :=
  fraction P*mean (R true)+(1-fraction P)*mean (R false)

lemma T2C_frozen_mean {n} (P : Population n) (hP : ValidDesign P)
    (R : Bool → Fin n → ℝ) (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    mean (T2C_frozen R S) = mean (R false)+
      fraction P*groupMean S (fun i => R true i-R false i) := by
  have hcard := (Finset.mem_powersetCard.mp hS).2
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (by have := hP.1; omega : n ≠ 0)
  have hm : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast hP.2.1.ne'
  have hpoint (i : Fin n) : T2C_frozen R S i =
      R false i+(if i ∈ S then R true i-R false i else 0) := by
    by_cases hi : i ∈ S <;> simp [T2C_frozen, hi]
  change mean (fun i => T2C_frozen R S i) = _
  simp_rw [hpoint]
  rw [T2C_mean_add]
  simp only [mean, Finset.sum_ite_mem_eq, fraction, groupMean, hcard]
  field_simp
  <;> ring

lemma T2C_frozen_centered {n} (P : Population n) (hP : ValidDesign P)
    (R : Bool → Fin n → ℝ) (S : Finset (Fin n)) (hS : S ∈ assignments P) :
    mean (T2C_frozen R S)-T2C_frozenMean P R =
      fraction P*(groupMean S (fun i => R true i-R false i)-
        mean (fun i => R true i-R false i)) := by
  rw [T2C_frozen_mean P hP R S hS, T2C_mean_sub]
  unfold T2C_frozenMean
  ring

lemma T2C_fraction_bounds {n} (P : Population n) (hP : ValidDesign P) :
    0 ≤ fraction P ∧ fraction P ≤ 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hP.1; omega : 0 < n)
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hn.le
  · exact (div_le_one hn).mpr (by exact_mod_cast hP.2.2.le)

/-- A centered response mean is a centered sample mean times the treatment fraction. -/
theorem T2C_frozen_mse {n} (P : Population n) (hP : ValidDesign P)
    (hm : 2 ≤ P.n1) (hc : 2 ≤ n-P.n1) (r M : ℝ) (hr : 0 < r)
    (hl : r*n ≤ (P.n1 : ℝ)) (hu : (P.n1 : ℝ) ≤ (1-r)*n)
    (R : Bool → Fin n → ℝ) (hM : 0 ≤ M)
    (hR : mean (fun i => (R true i-R false i)^2) ≤ M) :
    expectation P (fun S => (mean (T2C_frozen R S)-T2C_frozenMean P R)^2) ≤ 2*M/(r*n) := by
  have hp := T2C_fraction_bounds P hP
  have hp2 : (fraction P)^2 ≤ 1 := by nlinarith
  have he := DecisionLemma12_expectation_congr P (fun S hS =>
    congrArg (fun z : ℝ => z^2) (T2C_frozen_centered P hP R S hS))
  rw [he]
  simp_rw [mul_pow]
  rw [expectation_mul]
  have hnonneg := DecisionLemma12_expectation_nonneg P
    (fun S => (groupMean S (fun i => R true i-R false i)-
      mean (fun i => R true i-R false i))^2) (fun S _ => sq_nonneg _)
  calc
    _ ≤ expectation P (fun S => (groupMean S (fun i => R true i-R false i)-
        mean (fun i => R true i-R false i))^2) :=
      mul_le_of_le_one_left hnonneg hp2
    _ ≤ _ := T2C_arm_mse P hP hm hc r M hr hl hu
      (fun i => R true i-R false i) hM hR true

lemma T2C_fourth_difference {n} (R : Bool → Fin n → ℝ) (L K : ℝ)
    (hR : ∀ a, mean (fun i => R a i^4) ≤ K*L^2) :
    mean (fun i => (R true i^2-R false i^2)^2) ≤ 4*K*L^2 := by
  calc
    _ ≤ mean (fun i => 2*(R true i^4+R false i^4)) :=
      T2C_mean_mono fun i => by nlinarith [sq_nonneg (R true i^2+R false i^2)]
    _ = 2*(mean (fun i => R true i^4)+mean (fun i => R false i^4)) := by
      rw [T2C_mean_mul, T2C_mean_add]
    _ ≤ _ := by linarith [hR true, hR false]

lemma T2C_frozen_square {n} (R : Bool → Fin n → ℝ) (S : Finset (Fin n)) :
    (fun i => (T2C_frozen R S i)^2) = T2C_frozen (fun a i => R a i^2) S := by
  funext i
  by_cases hi : i ∈ S <;> simp [T2C_frozen, hi]

/-- Concentration of the raw pooled second moment. -/
theorem T2C_frozen_second_mse {n k} (P : CovPopulation n k) (r L K : ℝ)
    (hP : ValidDesign P.pop) (hm : 2 ≤ P.pop.n1) (hc : 2 ≤ n-P.pop.n1)
    (hr : 0 < r) (hK : 0 ≤ K)
    (hl : r*n ≤ (P.pop.n1 : ℝ)) (hu : (P.pop.n1 : ℝ) ≤ (1-r)*n)
    (R : Bool → Fin n → ℝ)
    (hL : T2C_frozenMean P.pop (fun a i => R a i^2) = L)
    (hR : ∀ a, mean (fun i => R a i^4) ≤ K*L^2) :
    expectation P.pop (fun S => (mean (fun i => (T2C_frozen R S i)^2)-L)^2) ≤
      8*K*L^2/(r*n) := by
  have h := T2C_frozen_mse P.pop hP hm hc r (4*K*L^2) hr hl hu
    (fun a i => R a i^2) (by positivity) (T2C_fourth_difference R L K hR)
  simp_rw [← T2C_frozen_square, hL] at h
  convert h using 1 <;> ring

lemma T2C_frozen_fourth {n} (R : Bool → Fin n → ℝ) (L K : ℝ)
    (hR : ∀ a, mean (fun i => R a i^4) ≤ K*L^2) (S : Finset (Fin n)) :
    mean (fun i => (T2C_frozen R S i)^4) ≤ 2*K*L^2 := by
  calc
    _ ≤ mean (fun i => R true i^4+R false i^4) := by
      apply T2C_mean_mono
      intro i
      by_cases hi : i ∈ S <;> simp only [T2C_frozen, hi, ite_true, ite_false] <;>
        nlinarith [sq_nonneg (R true i^2), sq_nonneg (R false i^2)]
    _ = mean (fun i => R true i^4)+mean (fun i => R false i^4) := T2C_mean_add _ _
    _ ≤ _ := by linarith [hR true, hR false]

/-- The pooled score has zero population mean and sampling-size variance. -/
theorem T2C_frozen_score_mse {n k} (P : CovPopulation n k) (e A r L K : ℝ)
    (hP : ValidDesign P.pop) (hm : 2 ≤ P.pop.n1) (hc : 2 ≤ n-P.pop.n1)
    (hr : 0 < r) (hL : 0 < L) (hK : 0 ≤ K)
    (hl : r*n ≤ (P.pop.n1 : ℝ)) (hu : (P.pop.n1 : ℝ) ≤ (1-r)*n)
    (hx : T2C_covariates P.x e A) (R : Bool → Fin n → ℝ)
    (hzero : ∀ s, T2C_frozenMean P.pop (fun a i => augmented P.x i s*R a i) = 0)
    (hR : ∀ a, mean (fun i => R a i^4) ≤ K*L^2) :
    expectation P.pop (fun S => normSq (score P.x Finset.univ (T2C_frozen R S))) ≤
      8*((k : ℝ)+1)*(max 1 A+K)*L/(r*n) := by
  have hn : 0 < n := by have := hP.1; omega
  have hM : 0 ≤ max 1 A := zero_le_one.trans (le_max_left _ _)
  change expectation P.pop (fun S => ∑ s, (score P.x Finset.univ (T2C_frozen R S) s)^2) ≤ _
  rw [T2C_expectation_sum]
  calc
    _ ≤ ∑ _s : Option (Fin k), 8*(max 1 A+K)*L/(r*n) := by
      apply Finset.sum_le_sum
      intro s _
      let U := fun a i => augmented P.x i s*R a i
      have hprod (a : Bool) : mean (fun i => (U a i)^2) ≤ (max 1 A+K)*L :=
        T2C_product_second hn _ _ L (max 1 A) K hL hM hK
          (T2C_augmented_fourth P.x hn A hx.2.1 s) (hR a)
      have hdiff : mean (fun i => (U true i-U false i)^2) ≤ 4*(max 1 A+K)*L := by
        calc
          _ ≤ mean (fun i => 2*((U true i)^2+(U false i)^2)) :=
            T2C_mean_mono fun i => by nlinarith [sq_nonneg (U true i+U false i)]
          _ = 2*(mean (fun i => (U true i)^2)+mean (fun i => (U false i)^2)) := by
            rw [T2C_mean_mul, T2C_mean_add]
          _ ≤ _ := by linarith [hprod true, hprod false]
      have hmse := T2C_frozen_mse P.pop hP hm hc r (4*(max 1 A+K)*L) hr hl hu
        U (by positivity) hdiff
      have hmeans (S : Finset (Fin n)) : mean (T2C_frozen U S) =
          score P.x Finset.univ (T2C_frozen R S) s := by
        simp only [mean, score, groupMean, Finset.card_univ, Fintype.card_fin]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S <;> simp [T2C_frozen, U, hi]
      have hUzero : T2C_frozenMean P.pop U = 0 := hzero s
      simp_rw [hUzero, sub_zero, hmeans] at hmse
      convert hmse using 1 <;> ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- Fixed fourth moments of covariate coordinates control every linear predictor. -/
lemma T2C_predictor_fourth {n k} (x : Fin n → Fin k → ℝ) (hn : 0 < n) (A : ℝ)
    (hx : ∀ s, mean (fun i => x i s^4) ≤ A) (b : Option (Fin k) → ℝ) :
    mean (fun i => (dotProduct (augmented x i) b)^4) ≤
      ((k : ℝ)+1)^2*max 1 A*(normSq b)^2 := by
  have hnorm (i : Fin n) : (normSq (augmented x i))^2 =
      ∑ s, ∑ t, (augmented x i s*augmented x i t)^2 := by
    dsimp only [normSq]
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum, mul_pow]
  have havg : mean (fun i => (normSq (augmented x i))^2) ≤ ((k : ℝ)+1)^2*max 1 A := by
    simp_rw [hnorm, T2C_mean_sum]
    calc
      _ ≤ ∑ _s : Option (Fin k), ∑ _t : Option (Fin k), max 1 A := by
        apply Finset.sum_le_sum
        intro s _
        exact Finset.sum_le_sum fun t _ => T2C_entry_second x hn A hx s t
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring
  calc
    _ ≤ mean (fun i => (normSq b)^2*(normSq (augmented x i))^2) := by
      apply T2C_mean_mono
      intro i
      have h := pow_le_pow_left₀ (sq_nonneg (dotProduct (augmented x i) b))
        (T2C_dot_sq (augmented x i) b) 2
      convert h using 1 <;> ring
    _ = (normSq b)^2*mean (fun i => (normSq (augmented x i))^2) := T2C_mean_mul _ _
    _ ≤ (normSq b)^2*(((k : ℝ)+1)^2*max 1 A) :=
      mul_le_mul_of_nonneg_left havg (sq_nonneg _)
    _ = _ := by ring

lemma T2C_fourth_sub (a b : ℝ) : (a-b)^4 ≤ 8*(a^4+b^4) := by
  nlinarith [sq_nonneg ((a+b)^2), sq_nonneg (a^2-b^2)]

def T2C_pooledResidual {n k} (x : Fin n → Fin k → ℝ) (q : Fin n → ℝ) (i : Fin n) : ℝ :=
  q i-dotProduct (augmented x i) (ols x Finset.univ q)

def T2C_pooledH {n k} (x : Fin n → Fin k → ℝ) (q : Fin n → ℝ) : ℝ :=
  mean (fun i => T2C_pooledResidual x q i^2)

lemma T2C_pooledH_identity {n k} (x : Fin n → Fin k → ℝ) (q : Fin n → ℝ)
    (hn : 0 < n) (hg : (gram x Finset.univ).det ≠ 0) :
    T2C_pooledH x q = mean (fun i => q i^2)-
      dotProduct (score x Finset.univ q) ((gram x Finset.univ)⁻¹ *ᵥ score x Finset.univ q) := by
  have h := residual_sum_squares_identity x Finset.univ q 0
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)) hg
  simpa only [T2C_pooledH, T2C_pooledResidual, rss,
    Finset.card_univ, Fintype.card_fin, mean, dotProduct_zero, sub_zero, groupMean] using h

def T2C_pooledK (k : ℕ) (e A K : ℝ) : ℝ :=
  32*(2*K+((k : ℝ)+1)^2*max 1 A/(min 1 e)^4)

/-- Bounded pooled score and a positive second moment imply fixed kurtosis. -/
theorem T2C_pooled_fourth_bound {n k} (x : Fin n → Fin k → ℝ) (e A L K : ℝ)
    (hn : 0 < n) (he : 0 < e) (hL : 0 < L) (hK : 0 ≤ K)
    (hx : T2C_covariates x e A) (q : Fin n → ℝ)
    (hq4 : mean (fun i => q i^4) ≤ 2*K*L^2)
    (hscore : normSq (score x Finset.univ q) ≤ L)
    (hH : L/2 ≤ T2C_pooledH x q) :
    0 < T2C_pooledH x q ∧
      mean (fun i => T2C_pooledResidual x q i^4) ≤ T2C_pooledK k e A K*(T2C_pooledH x q)^2 := by
  let c : ℝ := min 1 e
  have hc : 0 < c := lt_min zero_lt_one he
  have hdet := T2C_population_det x e A hn he hx
  have hols : ols x Finset.univ q = (gram x Finset.univ)⁻¹ *ᵥ score x Finset.univ q := by
    simp only [ols, if_pos hdet]
  have hnb : normSq (ols x Finset.univ q) ≤ L/c^2 := by
    rw [hols]
    exact (T2C_inverse_bounds _ c hc (T2C_population_coercive x e A hn hx) _).2.1.trans
      (div_le_div_of_nonneg_right hscore (sq_nonneg _))
  have hnb2 : (normSq (ols x Finset.univ q))^2 ≤ L^2/c^4 := by
    have hh := pow_le_pow_left₀ (T2C_normSq_nonneg _) hnb 2
    convert hh using 1 <;> ring
  have hpred := T2C_predictor_fourth x hn A hx.2.1 (ols x Finset.univ q)
  have hpredbound : mean (fun i => (dotProduct (augmented x i) (ols x Finset.univ q))^4) ≤
      (((k : ℝ)+1)^2*max 1 A/c^4)*L^2 := by
    apply hpred.trans
    have hh := mul_le_mul_of_nonneg_left hnb2
      (by positivity : 0 ≤ ((k : ℝ)+1)^2*max 1 A)
    convert hh using 1 <;> ring
  have hfour : mean (fun i => T2C_pooledResidual x q i^4) ≤
      8*(2*K+((k : ℝ)+1)^2*max 1 A/c^4)*L^2 := by
    calc
      _ ≤ mean (fun i => 8*(q i^4+(dotProduct (augmented x i) (ols x Finset.univ q))^4)) :=
        T2C_mean_mono fun i => T2C_fourth_sub _ _
      _ = 8*(mean (fun i => q i^4)+
          mean (fun i => (dotProduct (augmented x i) (ols x Finset.univ q))^4)) := by
        rw [T2C_mean_mul, T2C_mean_add]
      _ ≤ _ := by linarith
  have hL2 : L^2 ≤ 4*(T2C_pooledH x q)^2 := by nlinarith
  refine ⟨by linarith, hfour.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left hL2
    (by positivity : 0 ≤ 8*(2*K+((k : ℝ)+1)^2*max 1 A/c^4))
  convert hh using 1 <;> dsimp [T2C_pooledK, c] <;> ring

lemma T2C_projection_error_bound {n} (P : Population n)
    (f g Y : Finset (Fin n) → ℝ) (L c η Mf MY : ℝ)
    (hL : 0 < L) (hc : 0 < c) (hη : 0 < η)
    (hY : ∀ S ∈ assignments P, 0 ≤ Y S)
    (hg : ∀ S ∈ assignments P, 0 ≤ g S ∧ g S ≤ Y S/c)
    (hf : expectation P (fun S => (f S-L)^2) ≤ Mf) (hMY : expectation P Y ≤ MY) :
    probability P (fun S => η ≤ |(f S-g S)/L-1|) ≤
      Mf/(η*L/2)^2+MY/(η*L*c/2) := by
  let E := fun S => η*L/2 ≤ |f S-L|
  let F := fun S => η*L*c/2 ≤ Y S
  have hinc : probability P (fun S => η ≤ |(f S-g S)/L-1|) ≤
      probability P (fun S => E S ∨ F S) := by
    apply T2C_probability_mono
    intro S hS hbad
    by_contra hnot
    have hfsmall : |f S-L| < η*L/2 := lt_of_not_ge fun hh => hnot (Or.inl hh)
    have hYsmall : Y S < η*L*c/2 := lt_of_not_ge fun hh => hnot (Or.inr hh)
    have hgsmall : g S < η*L/2 := (hg S hS).2.trans_lt
      ((div_lt_iff₀ hc).mpr (by nlinarith))
    have habs : |f S-L-g S| ≤ |f S-L|+g S := by
      simpa only [abs_of_nonneg (hg S hS).1] using abs_sub (f S-L) (g S)
    have heq : (f S-g S)/L-1 = (f S-L-g S)/L := by
      field_simp
      <;> ring
    rw [heq, abs_div, abs_of_pos hL] at hbad
    have hlarge := (le_div_iff₀ hL).mp hbad
    linarith
  have hE : probability P E ≤ Mf/(η*L/2)^2 := by
    have hmono : probability P E ≤ probability P (fun S => (η*L/2)^2 ≤ (f S-L)^2) := by
      apply T2C_probability_mono
      intro S hS hh
      have hsq := (sq_le_sq₀ (by positivity : 0 ≤ η*L/2) (abs_nonneg _)).mpr hh
      simpa only [sq_abs] using hsq
    apply hmono.trans
    exact (T2C_markov_bound P (fun S => (f S-L)^2) _ (by positivity)
      (fun S _ => sq_nonneg _)).trans (div_le_div_of_nonneg_right hf (sq_nonneg _))
  have hF : probability P F ≤ MY/(η*L*c/2) :=
    (T2C_markov_bound P Y _ (by positivity) hY).trans
      (div_le_div_of_nonneg_right hMY (by positivity))
  exact hinc.trans ((T2C_probability_union _ _ _).trans (add_le_add hE hF))

/-- Pooled projection removes a negligible part of the raw energy. -/
theorem T2C_frozen_pooled_ratio_bound {n k} (P : CovPopulation n k) (e A r L K η : ℝ)
    (hP : ValidDesign P.pop) (hm : 2 ≤ P.pop.n1) (hc : 2 ≤ n-P.pop.n1)
    (he : 0 < e) (hr : 0 < r) (hL : 0 < L) (hK : 0 ≤ K) (hη : 0 < η)
    (hl : r*n ≤ (P.pop.n1 : ℝ)) (hu : (P.pop.n1 : ℝ) ≤ (1-r)*n)
    (hx : T2C_covariates P.x e A) (R : Bool → Fin n → ℝ)
    (hzero : ∀ s, T2C_frozenMean P.pop (fun a i => augmented P.x i s*R a i) = 0)
    (hmean : T2C_frozenMean P.pop (fun a i => R a i^2) = L)
    (hR : ∀ a, mean (fun i => R a i^4) ≤ K*L^2) :
    probability P.pop (fun S => η ≤ |T2C_pooledH P.x (T2C_frozen R S)/L-1|) ≤
      32*K/(r*n*η^2)+16*((k : ℝ)+1)*(max 1 A+K)/(r*n*η*min 1 e) := by
  have hn : 0 < n := by have := hP.1; omega
  have hc0 : 0 < min 1 e := lt_min zero_lt_one he
  have hdet := T2C_population_det P.x e A hn he hx
  let f := fun S => mean (fun i => T2C_frozen R S i^2)
  let g := fun S => dotProduct (score P.x Finset.univ (T2C_frozen R S))
    ((gram P.x Finset.univ)⁻¹ *ᵥ score P.x Finset.univ (T2C_frozen R S))
  let Y := fun S => normSq (score P.x Finset.univ (T2C_frozen R S))
  have h := T2C_projection_error_bound P.pop f g Y L (min 1 e) η
    (8*K*L^2/(r*n)) (8*((k : ℝ)+1)*(max 1 A+K)*L/(r*n)) hL hc0 hη
    (fun S _ => T2C_normSq_nonneg _) (by
      intro S hS
      have hb := T2C_inverse_bounds _ _ hc0 (T2C_population_coercive P.x e A hn hx)
        (score P.x Finset.univ (T2C_frozen R S))
      exact ⟨hb.1,hb.2.2⟩)
    (T2C_frozen_second_mse P r L K hP hm hc hr hK hl hu R hmean hR)
    (T2C_frozen_score_mse P e A r L K hP hm hc hr hL hK hl hu hx R hzero hR)
  have hid (S : Finset (Fin n)) : T2C_pooledH P.x (T2C_frozen R S) = f S-g S :=
    T2C_pooledH_identity P.x _ hn hdet
  simp_rw [← hid] at h
  apply h.trans_eq
  field_simp
  <;> ring

/-- An explicit probability bound for the complete pooled-residual kurtosis event. -/
theorem T2C_frozen_pooled_bad_bound {n k} (P : CovPopulation n k) (e A r L K : ℝ)
    (hP : ValidDesign P.pop) (hm : 2 ≤ P.pop.n1) (hc : 2 ≤ n-P.pop.n1)
    (he : 0 < e) (hr : 0 < r) (hL : 0 < L) (hK : 0 ≤ K)
    (hl : r*n ≤ (P.pop.n1 : ℝ)) (hu : (P.pop.n1 : ℝ) ≤ (1-r)*n)
    (hx : T2C_covariates P.x e A) (R : Bool → Fin n → ℝ)
    (hzero : ∀ s, T2C_frozenMean P.pop (fun a i => augmented P.x i s*R a i) = 0)
    (hmean : T2C_frozenMean P.pop (fun a i => R a i^2) = L)
    (hR : ∀ a, mean (fun i => R a i^4) ≤ K*L^2) :
    probability P.pop (fun S => ¬ (0 < T2C_pooledH P.x (T2C_frozen R S) ∧
      mean (fun i => T2C_pooledResidual P.x (T2C_frozen R S) i^4) ≤
        T2C_pooledK k e A K*(T2C_pooledH P.x (T2C_frozen R S))^2)) ≤
      32*K/(r*n*(1/2)^2)+16*((k : ℝ)+1)*(max 1 A+K)/(r*n*(1/2)*min 1 e)+
        8*((k : ℝ)+1)*(max 1 A+K)/(r*n) := by
  let E := fun S => (1/2 : ℝ) ≤ |T2C_pooledH P.x (T2C_frozen R S)/L-1|
  let F := fun S => L ≤ normSq (score P.x Finset.univ (T2C_frozen R S))
  have hinc : probability P.pop (fun S => ¬ (0 < T2C_pooledH P.x (T2C_frozen R S) ∧
      mean (fun i => T2C_pooledResidual P.x (T2C_frozen R S) i^4) ≤
        T2C_pooledK k e A K*(T2C_pooledH P.x (T2C_frozen R S))^2)) ≤
      probability P.pop (fun S => E S ∨ F S) := by
    apply T2C_probability_mono
    intro S hS hbad
    by_contra hnot
    have heps : |T2C_pooledH P.x (T2C_frozen R S)/L-1| < (1/2 : ℝ) :=
      lt_of_not_ge fun hh => hnot (Or.inl hh)
    have hsmall : normSq (score P.x Finset.univ (T2C_frozen R S)) < L :=
      lt_of_not_ge fun hh => hnot (Or.inr hh)
    have hlower : L/2 ≤ T2C_pooledH P.x (T2C_frozen R S) := by
      have hlo := (abs_lt.mp heps).1
      have hhalf : (1/2 : ℝ) < T2C_pooledH P.x (T2C_frozen R S)/L := by linarith
      nlinarith [(lt_div_iff₀ hL).mp hhalf]
    exact hbad (T2C_pooled_fourth_bound P.x e A L K (by have := hP.1; omega) he hL hK hx
      (T2C_frozen R S) (T2C_frozen_fourth R L K hR S) hsmall.le hlower)
  have hF : probability P.pop F ≤ 8*((k : ℝ)+1)*(max 1 A+K)/(r*n) := by
    apply (T2C_markov_bound P.pop
      (fun S => normSq (score P.x Finset.univ (T2C_frozen R S))) L hL
      (fun S _ => T2C_normSq_nonneg _)).trans
    calc
      _ ≤ (8*((k : ℝ)+1)*(max 1 A+K)*L/(r*n))/L :=
        div_le_div_of_nonneg_right
          (T2C_frozen_score_mse P e A r L K hP hm hc hr hL hK hl hu hx R hzero hR) hL.le
      _ = _ := by field_simp; <;> ring
  have hE := T2C_frozen_pooled_ratio_bound P e A r L K (1/2) hP hm hc he hr hL hK
    (by norm_num) hl hu hx R hzero hmean hR
  exact hinc.trans ((T2C_probability_union _ _ _).trans (add_le_add hE hF))

theorem T2C_frozen_pooled_limit (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ j, CovPopulation (sizes j) k) (e A r K : ℝ)
    (he : 0 < e) (hr : 0 < r) (hK : 0 ≤ K)
    (hP : ∀ j, ValidDesign (P j).pop)
    (hl : ∀ j, r*sizes j ≤ ((P j).pop.n1 : ℝ))
    (hu : ∀ j, ((P j).pop.n1 : ℝ) ≤ (1-r)*sizes j)
    (hx : ∀ j, T2C_covariates (P j).x e A)
    (R : ∀ j, Bool → Fin (sizes j) → ℝ) (L : ℕ → ℝ) (hL : ∀ j, 0 < L j)
    (hzero : ∀ j s, T2C_frozenMean (P j).pop (fun a i => augmented (P j).x i s*R j a i) = 0)
    (hmean : ∀ j, T2C_frozenMean (P j).pop (fun a i => R j a i^2) = L j)
    (hR : ∀ j a, mean (fun i => R j a i^4) ≤ K*(L j)^2) :
    Tendsto (fun j => probability (P j).pop (fun S =>
      ¬ (0 < T2C_pooledH (P j).x (T2C_frozen (R j) S) ∧
        mean (fun i => T2C_pooledResidual (P j).x (T2C_frozen (R j) S) i^4) ≤
          T2C_pooledK k e A K*(T2C_pooledH (P j).x (T2C_frozen (R j) S))^2)))
      atTop (nhds 0) := by
  have hN : Tendsto (fun j => (sizes j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes.tendsto_atTop
  have hb : Tendsto (fun j =>
      32*K/(r*sizes j*(1/2)^2)+16*((k : ℝ)+1)*(max 1 A+K)/(r*sizes j*(1/2)*min 1 e)+
        8*((k : ℝ)+1)*(max 1 A+K)/(r*sizes j)) atTop (nhds 0) := by
    have h := (tendsto_const_nhds.div_atTop hN : Tendsto (fun j =>
      (32*K/(r*(1/2)^2)+16*((k : ℝ)+1)*(max 1 A+K)/(r*(1/2)*min 1 e)+
        8*((k : ℝ)+1)*(max 1 A+K)/r)/(sizes j : ℝ)) atTop (nhds 0))
    convert h using 1 <;> funext j <;> ring
  apply squeeze_zero' (Eventually.of_forall fun _ =>
    DecisionLemma12_probability_nonneg _ _) _ hb
  filter_upwards [T2C_arms_eventually sizes hsizes (fun j => (P j).pop) r hr hP hl hu]
    with j hj
  exact T2C_frozen_pooled_bad_bound (P j) e A r (L j) K (hP j) hj.1 hj.2 he hr (hL j) hK
    (hl j) (hu j) (hx j) (R j) (hzero j) (hmean j) (hR j)

end
end AronowAudit.P002.Wave1
