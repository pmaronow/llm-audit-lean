import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

open Finset Filter
open scoped BigOperators Matrix Topology Matrix.Norms.Operator

noncomputable section

theorem SAP.P005a.WH.W2.T9_L14_proof : SAP.P005a.WH.W2.T9_L14 := by
  change SAP.P005a.WH.W2.finiteGramControl → SAP.P005a.wholeInteractedExpansion
  intro hgram n₀ hn₀ d m P hstand hinv hκ
  change ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n ≥ N,
    SAP.P005a.probability (m n)
      (fun S => |SAP.P005a.interactedATE (P n) S - SAP.P005a.ate (P n) -
        SAP.P005a.armLeading (P n) S| > M * Real.sqrt
          (SAP.P005a.kappa (P n)*d n/n)) < ε
  classical
  rcases hstand with ⟨hsize, ⟨K, hK, hym⟩, hstd, ⟨lo, hi, hlo, hlohi, hhi, halloc⟩⟩
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
  have hd : ∀ᶠ n in atTop, 1 ≤ d n := by
    filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop 3] with n hn0 hn3
    exact (hsize n hn0).1
  have hk : ∀ᶠ n in atTop, 0 ≤ SAP.P005a.kappa (P n) := by
    filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop 3, hstd]
      with n hn0 hn3 hPn
    have hPo : AronowAudit.P005.standardized
        (SAP.P005a.Bridge.toPopulation (P n)) := by
      simpa only [SAP.P005a.Bridge.standardized_eq] using hPn
    have hn : 0 < n := by omega
    have hkold : 0 ≤ AronowAudit.P005.kappa
        (SAP.P005a.Bridge.toPopulation (P n)) :=
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans
        (AronowAudit.P005.kappa_bounds
          (SAP.P005a.Bridge.toPopulation (P n)) hn hPo.2).1
    simpa only [SAP.P005a.Bridge.kappa_eq] using hkold
  have hκmax := (AronowAudit.P005.repaired_log_conditions d
    (fun n => SAP.P005a.kappa (P n)) hd hk).1.mp hκ
  obtain ⟨A, hA, hfg⟩ := hgram (ε/4) (by positivity)
  let M : ℝ := 2*Real.sqrt (32*B^2*(1+B))
  have hM : 0 < M := by dsimp [M]; positivity
  have hsmall : ∀ᶠ n in atTop,
      SAP.P005a.kappa (P n)*Real.log (max (d n) 2 : ℕ) < a/(4*A) :=
    hκmax.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < a/(4*A)))
  refine ⟨M, hM, ?_⟩
  apply Filter.eventually_atTop.mp
  filter_upwards [hstd, hinv, hsmall, eventually_ge_atTop n₀,
    eventually_ge_atTop 3] with n hPn hreg hsm hn0 hn3
  have hnposN : 0 < n := by omega
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnposN
  have hsz := hsize n hn0
  let Pn : AronowAudit.P005.Population n (d n) :=
    SAP.P005a.Bridge.toPopulation (P n)
  have hPnOld : AronowAudit.P005.standardized Pn := by
    dsimp only [Pn]
    rw [SAP.P005a.Bridge.standardized_eq]
    exact hPn
  have hregOld : AronowAudit.P005.interactedRegular Pn (m n) := by
    dsimp only [Pn]
    intro S hS
    have hr := hreg S hS
    constructor
    · rw [SAP.P005a.Bridge.armL_eq]
      exact hr.1
    · rw [SAP.P005a.Bridge.armL_eq]
      simpa [AronowAudit.P005.control, SAP.P005a.control] using hr.2
  have hkp : 0 ≤ AronowAudit.P005.kappa Pn :=
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans
      (AronowAudit.P005.kappa_bounds Pn hnposN hPnOld.2).1
  have hsmOld : AronowAudit.P005.kappa Pn * Real.log (max (d n) 2 : ℕ) < a/(4*A) := by
    dsimp only [Pn]
    rw [SAP.P005a.Bridge.kappa_eq]
    exact hsm
  have hallocT : a*(n : ℝ) ≤ m n := by
    have hh : lo*(n : ℝ) < m n := by
      have hh' := (halloc n hn0).1
      dsimp [SAP.P005a.pT] at hh'
      exact (lt_div_iff₀ hnposR).mp hh'
    exact (mul_le_mul_of_nonneg_right (min_le_left lo (1-hi)) hnposR.le).trans hh.le
  have hallocC : a*(n : ℝ) ≤ (n-m n : ℕ) := by
    rw [Nat.cast_sub (by omega : m n ≤ n)]
    have hh : (m n : ℝ) < hi*n := by
      have hh' := (halloc n hn0).2
      dsimp [SAP.P005a.pT] at hh'
      exact (div_lt_iff₀ hnposR).mp hh'
    have hh' := mul_le_mul_of_nonneg_right (min_le_right lo (1-hi)) hnposR.le
    change a*(n : ℝ) ≤ (1-hi)*n at hh'
    linarith
  have hthresholdOld := AronowAudit.P005.Wave1.CondT8T9_sample_threshold
    Pn hnposN hsz.1 hkp A a hA hsmOld.le
  have hthreshold : A*(2*(n : ℝ)*SAP.P005a.kappa (P n))*
      Real.log (d n+1 : ℕ) ≤ a*n := by
    dsimp only [Pn] at hthresholdOld
    rw [← SAP.P005a.Bridge.kappa_eq (P n)]
    exact hthresholdOld
  have hbT : SAP.P005a.probability (m n)
      (AronowAudit.P005.Wave1.CondT8T9_bad Pn (m n)) < ε/4 := by
    exact hfg (P n) hnposN hsz.1 hPn (Nat.le_of_lt hsz.2.2.2)
      (hthreshold.trans hallocT)
  have hbCOld : AronowAudit.P005.probability (m n)
      (fun S => AronowAudit.P005.Wave1.CondT8T9_bad Pn (n-m n)
        (AronowAudit.P005.control S)) < ε/4 := by
    rw [AronowAudit.P005.Wave1.CondT8T9_probability_control
      (Nat.le_of_lt hsz.2.2.2)]
    exact hfg (P n) hnposN hsz.1 hPn (Nat.sub_le _ _)
      (hthreshold.trans hallocC)
  have hbC : SAP.P005a.probability (m n)
      (fun S => AronowAudit.P005.Wave1.CondT8T9_bad Pn (n-m n)
        (SAP.P005a.control S)) < ε/4 := by
    have hprob : AronowAudit.P005.probability (m n)
        (fun S => AronowAudit.P005.Wave1.CondT8T9_bad Pn (n-m n)
          (SAP.P005a.control S)) = SAP.P005a.probability (m n)
        (fun S => AronowAudit.P005.Wave1.CondT8T9_bad Pn (n-m n)
          (SAP.P005a.control S)) := by rfl
    rw [← hprob]
    simpa only [AronowAudit.P005.control, SAP.P005a.control] using hbCOld
  let Q : Finset (Fin n) → ℝ := fun S =>
    AronowAudit.P005.Wave1.CondT8T9_score Pn S Pn.yT +
      AronowAudit.P005.Wave1.CondT8T9_score Pn (AronowAudit.P005.control S) Pn.yC
  have hQ0 : ∀ S ∈ AronowAudit.P005.design n (m n), 0 ≤ Q S := by
    intro S hS
    exact add_nonneg
      (AronowAudit.P005.Wave1.CondT8T9_score_nonneg Pn hkp S Pn.yT)
      (AronowAudit.P005.Wave1.CondT8T9_score_nonneg Pn hkp
        (AronowAudit.P005.control S) Pn.yC)
  have hQE : AronowAudit.P005.expectation (m n) Q ≤ 2*C := by
    dsimp only [Q]
    rw [AronowAudit.P005.Wave1.t4_expectation_add,
      AronowAudit.P005.Wave1.t4_complement_expectation
        (Nat.le_of_lt hsz.2.2.2)
        (fun S => AronowAudit.P005.Wave1.CondT8T9_score Pn S Pn.yC)]
    have ht := AronowAudit.P005.Wave1.CondT8T9_score_expectation Pn hn3 hsz.1
      hsz.2.2.1 hsz.2.2.2.le hPnOld a ha hallocT Pn.yT K hK (hym n hn0).1
    have hc := AronowAudit.P005.Wave1.CondT8T9_score_expectation Pn hn3 hsz.1
      (by omega) (Nat.sub_le _ _) hPnOld a ha hallocC Pn.yC K hK (hym n hn0).2.1
    change _ ≤ 2*(2/a+2*K/a+K)
    linarith
  have hbQ : AronowAudit.P005.probability (m n) (fun S => B < Q S) ≤ ε/4 := by
    exact ((AronowAudit.P005.Wave1.CondT8T9_markov (m n) Q hQ0 B hB).trans
      (div_le_div_of_nonneg_right hQE hB.le)).trans hmark
  let ET := AronowAudit.P005.Wave1.CondT8T9_bad Pn (m n)
  let EC := fun S => AronowAudit.P005.Wave1.CondT8T9_bad Pn (n-m n)
    (AronowAudit.P005.control S)
  let EQ := fun S => B < Q S
  have hATE : ∀ S, AronowAudit.P005.interactedATE Pn S =
      SAP.P005a.interactedATE (P n) S := by
    intro S
    dsimp only [Pn, SAP.P005a.Bridge.toPopulation,
      AronowAudit.P005.interactedATE, SAP.P005a.interactedATE]
    rfl
  have hate : AronowAudit.P005.ate Pn = SAP.P005a.ate (P n) := by
    dsimp only [Pn, SAP.P005a.Bridge.toPopulation,
      AronowAudit.P005.ate, SAP.P005a.ate]
    rfl
  have hleading : ∀ S, AronowAudit.P005.armLeading Pn S =
      SAP.P005a.armLeading (P n) S := by
    intro S
    dsimp only [Pn, SAP.P005a.Bridge.toPopulation,
      AronowAudit.P005.armLeading, SAP.P005a.armLeading]
    rfl
  have hkEq : AronowAudit.P005.kappa Pn = SAP.P005a.kappa (P n) := by
    dsimp only [Pn]
    exact SAP.P005a.Bridge.kappa_eq (P n)
  have hsub : AronowAudit.P005.probability (m n)
      (fun S => |SAP.P005a.interactedATE (P n) S - SAP.P005a.ate (P n) -
        SAP.P005a.armLeading (P n) S| >
          M*Real.sqrt (SAP.P005a.kappa (P n)*d n/n)) ≤
      SAP.P005a.probability (m n) (fun S => ET S ∨ (EC S ∨ EQ S)) := by
    apply AronowAudit.P005.Wave1.CondT8T9_probability_mono
    intro S hS hlarge
    by_cases ht : ET S
    · exact Or.inl ht
    by_cases hc : EC S
    · exact Or.inr (Or.inl hc)
    by_cases hq : EQ S
    · exact Or.inr (Or.inr hq)
    have hrOld := AronowAudit.P005.Wave1.CondT8T9_remainder_bound Pn hnposN hsz.1
      hPnOld hsz.2.2.1 hsz.2.2.2 S hS hregOld ht hc B hB (le_of_not_gt hq)
    have hr : |SAP.P005a.interactedATE (P n) S - SAP.P005a.ate (P n) -
        SAP.P005a.armLeading (P n) S| ≤ M*Real.sqrt (SAP.P005a.kappa (P n)*d n/n) := by
      simpa only [M, hATE S, hate, hleading S, hkEq] using hrOld
    exact (not_lt_of_ge hr hlarge).elim
  have hu := AronowAudit.P005.Wave1.CondT8T9_probability_union (m n) ET
    (fun S => EC S ∨ EQ S)
  have hu' := AronowAudit.P005.Wave1.CondT8T9_probability_union (m n) EC EQ
  have hbT' : AronowAudit.P005.probability (m n) ET < ε/4 := by
    have hprob : AronowAudit.P005.probability (m n) ET =
        SAP.P005a.probability (m n) ET := by rfl
    rw [hprob]
    simpa only [ET] using hbT
  have hbC' : AronowAudit.P005.probability (m n) EC < ε/4 := by
    have hprob : AronowAudit.P005.probability (m n) EC =
        SAP.P005a.probability (m n) EC := by rfl
    rw [hprob]
    simpa [EC, AronowAudit.P005.control, SAP.P005a.control] using hbC
  have hbQ' : AronowAudit.P005.probability (m n) EQ ≤ ε/4 := by
    simpa only [EQ] using hbQ
  change SAP.P005a.probability (m n)
      (fun S => |SAP.P005a.interactedATE (P n) S - SAP.P005a.ate (P n) -
        SAP.P005a.armLeading (P n) S| > M*Real.sqrt (SAP.P005a.kappa (P n)*d n/n)) < ε
  calc
    _ ≤ AronowAudit.P005.probability (m n) (fun S => ET S ∨ (EC S ∨ EQ S)) := hsub
    _ ≤ AronowAudit.P005.probability (m n) ET +
        AronowAudit.P005.probability (m n) (fun S => EC S ∨ EQ S) := hu
    _ ≤ AronowAudit.P005.probability (m n) ET +
        (AronowAudit.P005.probability (m n) EC + AronowAudit.P005.probability (m n) EQ) := by
          nlinarith [hu']
    _ < ε := by linarith
