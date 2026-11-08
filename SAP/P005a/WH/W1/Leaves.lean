import SAP.P005a.WH.W1.Existing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W1

noncomputable section
open SAP.P005a SAP.P005a.Bridge Finset Filter
open scoped BigOperators Matrix Topology
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000

/-- The four-unit witness has centered, standardized covariates, an ordinary
inverse on all four assignments, zero population slope, and wrong/correct
control residual sums 1/3 and 1. Enumerate singleton assignments with
Finset.card_eq_one, use Matrix.det_fin_one, and evaluate the four finite sums.
All moment and allocation checks are rational arithmetic. -/
def T14_L1 : Prop := W1WrongSumFacts

/-- Exact first moment and variance of a product of centered unnormalized sums.
Apply qtc_expectation_positive and qtc_matrix_second_moment to Q(i,j)=u_i v_j.
The row and column sums vanish. Its contractions are AB, G², G and H;
subtract (αG)² using GP005B4c_variance_identity, and simplify the inclusion
coefficients to ℓ and α-6ℓ by field_simp and ring. Singleton arms are included. -/
def T2_L1 : Prop :=
  ∀ {n s : ℕ}, 4 ≤ n → 0 < s → s < n → ∀ u v : Fin n → ℝ,
    (∑ i, u i) = 0 → (∑ i, v i) = 0 →
    expectation s (W1Z u v) = W1Alpha n s * (∑ i, u i*v i) ∧
    variance s (W1Z u v) =
      (W1Alpha n s-6*W1Ell n s)*(∑ i, u i^2*v i^2) +
      W1Ell n s*(∑ i, u i^2)*(∑ i, v i^2) +
      (2*W1Ell n s-(W1Alpha n s)^2)*(∑ i, u i*v i)^2

/-- The three probabilities for selecting zero, one or two high-leverage labels.
Express event indicators as polynomials in the two label indicators. Their
means are 1/2 and their product mean is 7/30 by GP005B4b_T3_pair_inclusion.
Identify probability with the expectation of an event indicator using
Finset.sum_filter. This avoids enumerating 12870 assignments. -/
def T3_L1 : Prop :=
  probability 8 (fun S => W1HighCount S = 0) = (7/30 : ℝ) ∧
  probability 8 (fun S => W1HighCount S = 1) = (8/15 : ℝ) ∧
  probability 8 (fun S => W1HighCount S = 2) = (7/30 : ℝ)

/-- Uniform real algebra for both allocation coefficients and the numerical
leverage RHS, including κ=0 and D=0. Use p*N≤s≤N and positive denominators to
bound A≤2/(p(N-1)) and B≤2/(p³N(N-1)); then N/(N-1)≤2 gives the displayed
constant. No division by κ, D or K is needed. Each step is ordered-field algebra. -/
def T4_L1 : Prop :=
  ∀ N s p κ D K : ℝ, 4 ≤ N → 0 < s → s ≤ N → 0 < p → p*N ≤ s →
    0 ≤ κ → 0 ≤ D → 0 ≤ K →
    let A := 2*(N-s)/(s*(N-1))
    let B := 2*(N-s)*N/(s^3*(N-1))
    A ≤ 2/(p*(N-1)) ∧ B ≤ 2/(p^3*N*(N-1)) ∧
    0 ≤ A*N^2*κ^2*K+B*N*κ*D*K ∧
    A*N^2*κ^2*K+B*N*κ*D*K ≤
      (4*K*(1/p+1/p^3))*(N*κ^2+κ*D/N)

theorem T1_assembly : T1WholeStatement := by
  have h := T1_correspondence.mp AronowAudit.P005.covariance_counterexample
  rcases h with ⟨hn, hm, hmn, hcard, ha, hb, hab, he, hv, hbound, hfail⟩
  have hU : (univ : Finset (Fin 6)) = {0,1,2,3,4,5} := AronowAudit.P005.univ_six
  have hprod : popMean (fun i => witnessA i*witnessB i) = -(19/6 : ℝ) := by
    norm_num [popMean, mean, hU, witnessA, witnessB]
  have hM : popMean (fun i => (witnessA i*witnessB i-
      popMean (fun j => witnessA j*witnessB j))^2) = (113/36 : ℝ) := by
    norm_num [hprod, popMean, mean, hU, witnessA, witnessB]
  have hAA : popMean (fun i => witnessA i^2) = (13/2 : ℝ) := by
    norm_num [popMean, mean, hU, witnessA]
  have hBB : popMean (fun i => witnessB i^2) = (25/6 : ℝ) := by
    norm_num [popMean, mean, hU, witnessB]
  have hcenter : covarianceBound 4 (centered witnessA) (centered witnessB) = (835/128 : ℝ) := by
    norm_num [covarianceBound, centered, popMean, mean, hU, witnessA, witnessB]
  have hloc : ∀ (S : Finset (Fin 6)), S.Nonempty → ∀ c e : ℝ,
      sampleCov S (fun i => witnessA i+c) (fun i => witnessB i+e) = sampleCov S witnessA witnessB := by
    intro S hS c e
    change AronowAudit.P005.sampleCov S (fun i => witnessA i+c) (fun i => witnessB i+e) =
      AronowAudit.P005.sampleCov S witnessA witnessB
    simpa only [sub_neg_eq_add] using
      AronowAudit.P005.covariance_location_invariant S hS witnessA witnessB (-c) (-e)
  refine ⟨⟨hn, hm, hmn, hcard, ha, hb, hab, he, hv, hbound, hfail⟩, hprod, ?_,
    ?_, ?_, hM, hAA, hBB, ?_, ?_, ?_, ?_, ?_, hloc, ?_, ?_, hcenter, ?_, ?_⟩
  · rw [he, hab]; norm_num
  · norm_num [W1A]
  · norm_num [W1B]
  · rw [hM]; norm_num [W1A]
  · rw [hAA, hBB]; norm_num [W1B]
  · rw [hbound]; norm_num
  · rw [hv, hbound]; norm_num
  · norm_num
  · intro c e
    apply AronowAudit.P005.Wave1.CondP002P005P006_variance_congr
    intro S hS
    have hc : S.card = 4 := (Finset.mem_powersetCard.mp hS).2
    exact hloc S (Finset.card_pos.mp (by omega)) c e
  · intro S hS
    have hc : S.card = 4 := (Finset.mem_powersetCard.mp hS).2
    exact AronowAudit.P005.covariance_location_invariant S
      (Finset.card_pos.mp (by omega)) witnessA witnessB (popMean witnessA) (popMean witnessB)
  · rw [hv, hcenter]; norm_num
  · rw [hcenter, hbound]; norm_num

theorem T14_assembly (h1 : T14_L1) : T14WholeStatement := by
  refine ⟨t14_existing, h1, ?_, ?_⟩
  · rcases h1 with ⟨_, _, _, _, _, _, _, _, _, hwrong, hright⟩
    rw [hwrong, hright]
    norm_num
  · intro n d m _hn _hm _hmn
    obtain ⟨F, hF⟩ := observable_general n d m
    exact ⟨F, fun P S _hS _hinv => hF P S⟩

/-- Assembly helper: only the new exact moment identities are supplied by a
leaf; the norm bound and normalization are existing quadratic-sampling results. -/
theorem product_uniform (h1 : T2_L1) {n s : ℕ} (hn : 4 ≤ n) (hs : 0 < s) (hsn : s < n)
    (u v : Fin n → ℝ) (hu : (∑ i, u i) = 0) (hv : (∑ i, v i) = 0) :
    W1ProductFacts s .treated u v := by
  have hraw := h1 hn hs hsn u v hu hv
  have hbound := AronowAudit.P005.Wave1.qtc_principal_variance hn hsn.le
    (fun i j => u i*v j)
    (fun i => by rw [← Finset.mul_sum, hv, mul_zero])
    (fun j => by rw [← Finset.sum_mul, hu, zero_mul])
  have houter : AronowAudit.Literature.principalSum n (fun i j => u i*v j) = W1Z u v := by
    funext S
    exact AronowAudit.P005.Wave1.CondP002P005P006_outer n u v S
  have hfrob : (∑ i, ∑ j, (u i*v j)^2) = (∑ i, u i^2)*(∑ j, v j^2) := by
    simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [houter, hfrob] at hbound
  have hbound' : variance s (W1Z u v) ≤ W1Alpha n s*(∑ i, u i^2)*(∑ i, v i^2) := by
    calc
      _ ≤ (s : ℝ)*((n : ℝ)-s)/((n : ℝ)*(n-1))*((∑ i, u i^2)*(∑ i, v i^2)) := hbound
      _ = _ := by unfold W1Alpha; ring
  have hscale : variance s (fun S => mean S u*mean S v) = variance s (W1Z u v)/(s : ℝ)^4 := by
    have hform : ∀ S ∈ design n s, mean S u*mean S v = W1Z u v S/(s : ℝ)^2 := by
      intro S hS
      have hc : S.card = s := (Finset.mem_powersetCard.mp hS).2
      dsimp [mean, W1Z]
      rw [hc]
      ring
    rw [variance_congr s _ _ hform, variance_div]
    congr 1
    ring
  exact ⟨hraw.1, hraw.2, hbound', hscale,
    AronowAudit.P005.Wave1.CondP002P005P006_variance_product
      AronowAudit.Literature.leiDing2021QuadraticSampling_proof hn hs hsn.le u v hu hv⟩

theorem T2_assembly (h1 : T2_L1) : T2WholeStatement := by
  have hbase : T2Statement := by
    intro n m hn hm hmn t a b
    cases t with
    | treated => exact AronowAudit.P005.Wave1.qtc_corrected_covariance_lemma hn hm hmn .treated a b
    | control => exact AronowAudit.P005.Wave1.qtc_corrected_covariance_lemma hn hm hmn .control a b
  refine ⟨hbase, ?_, ?_, ?_⟩
  · intro n S hS a b c e
    exact AronowAudit.P005.covariance_location_invariant S hS a b c e
  · intro n m hn hm hmn t a b
    let u := centered a
    let v := centered b
    have hu : (∑ i, u i) = 0 := AronowAudit.P005.Wave1.GP005B4c_centered_sum (by omega) a
    have hv : (∑ i, v i) = 0 := AronowAudit.P005.Wave1.GP005B4c_centered_sum (by omega) b
    have hup : popMean u = 0 := AronowAudit.P005.Wave1.CondP002P005P006_centered_mean (by omega) a
    have hvp : popMean v = 0 := AronowAudit.P005.Wave1.CondP002P005P006_centered_mean (by omega) b
    have hUV : popMean (fun i => u i*v i) = popCov a b := by
      have h := AronowAudit.P005.covariance_location_invariant (univ : Finset (Fin n))
        ⟨⟨0, by omega⟩, mem_univ _⟩ a b (popMean a) (popMean b)
      change popMean (fun i => u i*v i)-popMean u*popMean v = popCov a b at h
      simpa only [hup, hvp, zero_mul, sub_zero] using h
    refine ⟨hu, hv, hUV, ?_, ?_, ?_, ?_⟩
    · intro S hS
      have hc : (armSet t S).card = armSize n m t := by
        cases t with
        | treated => exact (Finset.mem_powersetCard.mp hS).2
        | control => exact AronowAudit.P005.Wave1.control_arm_complement_card S hS
      have hs : 0 < armSize n m t := by cases t <;> simp only [armSize] <;> omega
      exact (AronowAudit.P005.covariance_location_invariant (armSet t S)
        (Finset.card_pos.mp (by omega)) a b (popMean a) (popMean b)).symm
    · cases t with
      | treated => exact AronowAudit.P005.Wave1.GP005B4c_variance_mean hn hm hmn.le (fun i => u i*v i)
      | control =>
        change variance m (fun S => mean (control S) (fun i => u i*v i)) = _
        rw [variance_control hmn.le (fun A => mean A (fun i => u i*v i))]
        exact AronowAudit.P005.Wave1.GP005B4c_variance_mean hn (by omega) (by omega) (fun i => u i*v i)
    · cases t with
      | treated => exact product_uniform h1 hn hm hmn u v hu hv
      | control =>
        have h := product_uniform h1 hn (by omega : 0 < n-m) (by omega : n-m < n) u v hu hv
        change W1ProductFacts m .control u v
        dsimp only [W1ProductFacts, armSize, armSet] at h ⊢
        rw [expectation_control hmn.le (W1Z u v),
          variance_control hmn.le (W1Z u v),
          variance_control hmn.le (fun A => mean A u*mean A v)]
        exact h
    · intro ha hb
      have hua : centered a = a := by funext i; simp [centered, ha]
      have hvb : centered b = b := by funext i; simp [centered, hb]
      simpa only [hua, hvb] using (hbase hn hm hmn t a b).2
  · intro n m _hn _hm _hmn U V
    exact AronowAudit.P005.variance_difference_bound m U V

theorem T3_assembly (h1 : T3_L1) : T3WholeStatement := by
  classical
  have h := T3_correspondence.mp AronowAudit.P005.Wave1.leverage_variance_counterexample_proof
  rcases h with ⟨hstd, hireg, hnreg, hYbound, hYC, hlo, hhi, hcard, hk, hhy, hv, hb1, hfail1, hb2, hfail2⟩
  have hU : (univ : Finset (Fin 16)) = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15} :=
    AronowAudit.P005.Wave1.GP005B4b_T3_univ16
  have hlev : leverage leveragePopulation =
      (fun i => if i.val < 2 then (512/71 : ℝ) else 8/71) :=
    AronowAudit.P005.Wave1.GP005B4b_T3_leverage_values
  have hYexact : popMean (fun i => leverageY i^2) = (28673/32768 : ℝ) := by
    norm_num [popMean, mean, hU, leverageY]
  have hmean : popMean (leverage leveragePopulation) = 1 := by
    norm_num [hlev, popMean, mean, hU]
  have hprod : popMean (fun i => (leverage leveragePopulation i*leverageY i-
      popMean (fun j => leverage leveragePopulation j*leverageY j))^2) = 0 := by
    norm_num [hlev, popMean, mean, hU, leverageY]
  have hthird : W1ThirdBound = (60758087/9678720 : ℝ) := by
    rw [W1ThirdBound, hk, hmean, hYexact]
    norm_num [W1A, W1B]
  have hcenter : covarianceBound 8 (fun i => leverage leveragePopulation i-1) (centered leverageY) =
      (5550293259/13214679040 : ℝ) := by
    norm_num [covarianceBound, centered, hlev, popMean, mean, hU, leverageY]
  refine ⟨⟨hstd, hireg, hnreg, hYbound, hYC, hlo, hhi, hcard, hk, hhy, hv, hb1, hfail1, hb2, hfail2⟩,
    hYexact, ?_, ?_, ?_, hlev, hmean, hprod, h1.1, h1.2.1, h1.2.2, ?_, ?_, ?_, ?_, ?_,
    hthird, ?_, hcenter, ?_⟩
  · norm_num [pT]
  · intro i
    have hs0 : Real.sqrt (8/71 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hp : (fun j => leveragePopulation.x j 0 = leveragePopulation.x i 0) =
        (fun j => leverageA j = leverageA i) := by
      funext j
      apply propext
      change (Real.sqrt (8/71 : ℝ)*leverageA j = Real.sqrt (8/71 : ℝ)*leverageA i) ↔
        leverageA j = leverageA i
      exact ⟨fun hh => mul_left_cancel₀ hs0 hh, fun hh => congrArg (fun z => Real.sqrt (8/71 : ℝ)*z) hh⟩
    have hb : ((univ : Finset (Fin 16)).filter (fun j => leverageA j = leverageA i)).card ≤ 7 :=
      AronowAudit.P005.Wave1.GP005B4b_T3_fiber_bound i
    simpa only [hp] using hb
  · intro S hS
    have hs : S.card = 8 := (Finset.mem_powersetCard.mp hS).2
    have hc : (control S).card = 8 := AronowAudit.P005.Wave1.GP005B4b_T3_control_card S hs
    have hpos : ∀ A : Finset (Fin 16), A.card = 8 →
        0 < sampleCov A (fun i => leveragePopulation.x i 0) (fun i => leveragePopulation.x i 0) := by
      intro A hA
      change 0 < AronowAudit.P005.sampleCov A
        (fun i => Real.sqrt (8/71 : ℝ)*leverageA i) (fun i => Real.sqrt (8/71 : ℝ)*leverageA i)
      rw [AronowAudit.P005.sampleCov_scale_both, Real.sq_sqrt (by norm_num)]
      exact mul_pos (by norm_num) (AronowAudit.P005.Wave1.GP005B4b_T3_arm_cov_pos A hA)
    exact ⟨hpos S hs, hpos (control S) hc⟩
  · intro S hS
    have hc : S ∩ {0,1} = ({0,1} : Finset (Fin 16)).filter (fun i => i ∈ S) := by
      ext i
      simp [and_comm]
    have hformula : sampleCov S (leverage leveragePopulation) leverageY =
        -(27783/36352 : ℝ)*(AronowAudit.P005.indicator S 0+AronowAudit.P005.indicator S 1) +
        (3969/18176 : ℝ)*(AronowAudit.P005.indicator S 0*AronowAudit.P005.indicator S 1) :=
      AronowAudit.P005.Wave1.GP005B4b_T3_covariance_formula S hS
    rw [hformula]
    by_cases h0 : (0 : Fin 16) ∈ S <;> by_cases h1 : (1 : Fin 16) ∈ S <;>
      norm_num [W1HighCount, hc, Finset.filter_insert, Finset.filter_singleton,
        AronowAudit.P005.indicator, h0, h1]
  · rw [hv, hb1]; norm_num
  · norm_num
  · change variance 8 (fun S => sampleCov S (leverage leveragePopulation) leverageY) -
      (2*((16 : ℝ)-8)/(8*(16-1))*popMean (fun i => leverage leveragePopulation i^2*leverageY i^2) +
        2*((16 : ℝ)-8)*16/((8 : ℝ)^3*(16-1))*popMean (fun i => leverageY i^2)*
          popMean (fun i => leverage leveragePopulation i^2)) = _
    rw [hv, hb2]; norm_num
  · norm_num
  · rw [hv, hthird]; norm_num
  · rw [hv, hcenter]; norm_num

theorem T4_assembly (h1 : T4_L1) : T4WholeStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n d m P hn hm hmn hP t K hK
    rcases finite_chain P hn hm hmn hP t K hK with
      ⟨hh, hi, hd, huEq, huBound, hvEq, hvBound, hprod, huv, hcov, hfinal⟩
    have huRaw : popMean (fun i => (leverage P i-(d : ℝ))^2) ≤
        popMean (fun i => leverage P i^2) := by
      rw [huEq]
      exact sub_le_self _ (sq_nonneg _)
    have hhRaw : popMean (fun i => leverage P i^2) ≤ n*kappa P*d := by
      calc
        _ ≤ popMean (fun i => ((n : ℝ)*kappa P)*leverage P i) := by
          apply AronowAudit.P005.mean_mono
          intro i _hi
          nlinarith [hi i]
        _ = n*kappa P*d := by
          have hm' : popMean (fun i => ((n : ℝ)*kappa P)*leverage P i) =
              ((n : ℝ)*kappa P)*popMean (leverage P) :=
            AronowAudit.P005.mean_mul univ (leverage P) ((n : ℝ)*kappa P)
          rw [hm', hh]
    exact ⟨hh, hi, hd, huEq, huRaw, hhRaw, hvEq, hvBound, hprod, huv, hcov, hfinal⟩
  · intro n m hn hm hmn t p hp hpalloc
    have hspos : 0 < armSize n m t := by cases t <;> simp only [armSize] <;> omega
    have hsle : armSize n m t ≤ n := by cases t <;> simp only [armSize] <;> omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hps : p*(n : ℝ) ≤ armSize n m t := (lt_div_iff₀ hnpos).mp hpalloc |>.le
    have hc := h1 n (armSize n m t) p 0 0 0 (by exact_mod_cast hn)
      (by exact_mod_cast hspos) (by exact_mod_cast hsle) hp hps (by norm_num) (by norm_num) (by norm_num)
    exact ⟨hc.1, hc.2.1⟩
  · intro d m P K lo hi h t
    rcases h with ⟨hK, hlo, hlohi, hhi, hall, hstd⟩
    let a : ℝ := min lo (1-hi)
    have ha : 0 < a := lt_min hlo (sub_pos.mpr hhi)
    let C : ℝ := 4*K*(1/a+1/a^3)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    let f := fun n (S : Finset (Fin n)) => sampleCov (armSet t S) (leverage (P n))
      (if t = .treated then (P n).yT else (P n).yC)
    let V := fun n => variance (m n) (f n)
    let R := fun n => W1LeverageRHS (P n) (armSize n (m n) t) K
    let r := fun (n : ℕ) => (n : ℝ)*kappa (P n)^2+kappa (P n)*(d n)/n
    have htail : ∀ᶠ n in atTop, 0 ≤ R n ∧ R n ≤ C*r n ∧ 0 ≤ V n ∧ V n ≤ R n ∧ 0 ≤ r n := by
      filter_upwards [hstd, Filter.eventually_ge_atTop (4 : ℕ)] with n hPn hn
      rcases hall n (by omega) with ⟨hd, hm, hmn, hYT, hYC, hx, hlow, hupp⟩
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hκ : 0 ≤ kappa (P n) :=
        (div_nonneg (Nat.cast_nonneg (d n)) hnpos.le).trans
          (AronowAudit.P005.kappa_bounds (toPopulation (P n)) (by omega) hPn.2).1
      have hr : 0 ≤ r n := by dsimp [r]; positivity
      let s := armSize n (m n) t
      have hspos : 0 < s := by cases t <;> simp only [s, armSize] <;> omega
      have hsle : s ≤ n := by cases t <;> simp only [s, armSize] <;> omega
      have hsalloc : a*(n : ℝ) ≤ s := by
        cases t with
        | treated =>
          change a*(n : ℝ) ≤ m n
          have hh : lo*(n : ℝ) < m n := (lt_div_iff₀ hnpos).mp hlow
          exact (mul_le_mul_of_nonneg_right (min_le_left lo (1-hi)) hnpos.le).trans hh.le
        | control =>
          change a*(n : ℝ) ≤ ((n-m n : ℕ) : ℝ)
          rw [Nat.cast_sub hmn.le]
          have hh : (m n : ℝ) < hi*n := (div_lt_iff₀ hnpos).mp hupp
          have ham := mul_le_mul_of_nonneg_right (min_le_right lo (1-hi)) hnpos.le
          nlinarith
      have hnum := h1 n s a (kappa (P n)) (d n) K (by exact_mod_cast hn)
        (by exact_mod_cast hspos) (by exact_mod_cast hsle) ha hsalloc hκ (Nat.cast_nonneg _) hK
      have hR0 : 0 ≤ R n := hnum.2.2.1
      have hRbound : R n ≤ C*r n := hnum.2.2.2
      have hY : popMean (fun i => (if t = .treated then (P n).yT i else (P n).yC i)^2) ≤ K := by
        cases t <;> simp only [reduceCtorEq, ite_true, ite_false] <;> assumption
      rcases finite_chain (P n) hn hm hmn hPn t K hY with
        ⟨_, _, _, _, _, _, _, _, _, hcov, hbound⟩
      exact ⟨hR0, hRbound, AronowAudit.P005.Wave1.t4_variance_nonneg _ _, hcov.trans hbound, hr⟩
    have hRO : Asymptotics.IsBigO atTop R r := by
      apply Asymptotics.IsBigO.of_bound C
      filter_upwards [htail] with n hn
      simpa only [Real.norm_eq_abs, abs_of_nonneg hn.1, abs_of_nonneg hn.2.2.2.2] using hn.2.1
    have hVO : Asymptotics.IsBigO atTop V r := by
      apply Asymptotics.IsBigO.of_bound C
      filter_upwards [htail] with n hn
      simpa only [Real.norm_eq_abs, abs_of_nonneg hn.2.2.1, abs_of_nonneg hn.2.2.2.2]
        using hn.2.2.2.1.trans hn.2.1
    refine ⟨⟨C, hC, ?_⟩, hRO, hVO, ?_, ?_⟩
    · filter_upwards [htail] with n hn
      exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1⟩
    · intro n _hn
      exact variance_div (m n) (f n) n
    · apply Asymptotics.IsBigO.of_bound C
      filter_upwards [htail, Filter.eventually_ge_atTop (4 : ℕ)] with n hn hn4
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hnne := hnpos.ne'
      have hrate : r n/(n : ℝ)^2 = kappa (P n)^2/n+kappa (P n)*(d n)/(n : ℝ)^3 := by
        dsimp [r]
        field_simp [hnne]
      have hvar : 0 ≤ variance (m n) (fun S => f n S/n) := AronowAudit.P005.Wave1.t4_variance_nonneg _ _
      have hrate0 : 0 ≤ r n/(n : ℝ)^2 := div_nonneg hn.2.2.2.2 (sq_nonneg _)
      have hbound : V n ≤ C*r n := hn.2.2.2.1.trans hn.2.1
      have hdiv := div_le_div_of_nonneg_right hbound (sq_nonneg (n : ℝ))
      change ‖variance (m n) (fun S => f n S/n)‖ ≤
        C*‖kappa (P n)^2/n+kappa (P n)*(d n)/(n : ℝ)^3‖
      rw [← hrate, Real.norm_eq_abs, abs_of_nonneg hvar,
        Real.norm_eq_abs, abs_of_nonneg hrate0, variance_div]
      simpa only [V, mul_div_assoc] using hdiv

end
end SAP.P005a.WH.W1
